{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | This module maintains the TypeInfo data structure, which contains
-- the information about the type and type classes that we need throughout
-- the conversion of code where they are used.
module HsToCoq.ConvertHaskell.TypeInfo
    ( -- * Types
      TypeInfo
    , constructors, constructorTypes, constructorFields
    , recordFieldTypes, classDefns, defaultMethods
    , ConstructorFields(..)
    , _RecordFields
    -- * The Monad
    , runTypeInfoMonad
    , TypeInfoConfig
    , TypeInfoMonad(..)
    -- * Derived utility functions
    , isConstructor
    ) where

import Control.Lens
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Counter
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Writer
import Data.Maybe
import Text.Read (readMaybe)
import qualified Data.Text as T

import System.Directory
import System.IO
import System.Exit

import HsToCoq.Util.GHC.Monad
import HsToCoq.Util.GHC.Exception
import HsToCoq.Util.GHC.DynFlags

import HsToCoq.Coq.Gallina (Qualid, ClassDefinition(..), Term, Qualid(..), ModuleIdent)
import HsToCoq.Coq.Gallina.Util (qualidModule)
import HsToCoq.ConvertHaskell.BuiltIn


data ConstructorFields = NonRecordFields !Int
                       | RecordFields    ![Qualid]
                       deriving (Eq, Ord, Show, Read)
makePrisms ''ConstructorFields

type TypeName        = Qualid
type ConstructorName = Qualid
type ClassName       = Qualid
type MethodName      = Qualid

type DefaultMethods = Map MethodName Term

-- | Did we succeed loading a modules’ interface?
-- (For now, we fail hard if we cannot, so this can only be 'Loaded"
data LoadStatus = Loaded
    deriving (Show, Read)

data TypeInfo = TypeInfo
    { _searchPaths       :: ![FilePath]
    , _ifaceLoadCache    :: !(Map ModuleIdent LoadStatus)
    , _processedModules  :: !(Set ModuleIdent)

    , _constructors      :: !(Map TypeName [ConstructorName])
    , _constructorTypes  :: !(Map ConstructorName TypeName)
    , _constructorFields :: !(Map ConstructorName ConstructorFields)
    , _recordFieldTypes  :: !(Map ConstructorName TypeName)
    , _classDefns        :: !(Map ClassName ClassDefinition)
    , _defaultMethods    :: !(Map ClassName DefaultMethods)
    }
    deriving (Show, Read) -- for cheap serialization for now 

makeLenses ''TypeInfo


data AField where
    AField :: forall a. String -> Lens' TypeInfo (Map Qualid a) -> AField

typeInfoFields :: [AField]
typeInfoFields =
    [ AField "constructors"      constructors
    , AField "constructorTypes"  constructorTypes
    , AField "constructorFields" constructorFields
    , AField "recordFieldTypes"  recordFieldTypes
    , AField "classDefns"        classDefns
    , AField "defaultMethods"    defaultMethods
    ]

newtype TypeInfoT m a = TypeInfoT (StateT TypeInfo m a)
  deriving ( Functor, Applicative, Monad, MonadIO, ExceptionMonad
           , HasDynFlags, MonadTrans)

loadIFace :: forall m. MonadIO m => ModuleIdent -> FilePath -> TypeInfoT m ()
loadIFace m filepath = do
    ifaceContent <- liftIO $ readFile filepath
    case readMaybe ifaceContent of
        Nothing -> parseErr
        Just iface ->
            checkIface iface

    return ()
  where
    checkIface :: TypeInfo -> TypeInfoT m ()
    checkIface iface = do
        unless (null (iface^.searchPaths))      $ shouldBeEmptyErr "seachPaths"
        unless (M.null (iface^.ifaceLoadCache)) $ shouldBeEmptyErr "ifaceLoadCache"
        mapM_ (checkField iface) typeInfoFields

    checkField iface (AField lensName lens) = do
        let badKeys =      [ key
                           | key <- M.keys (iface^.lens)
                           , qualidModule key /= Just m ]
        unless (null badKeys) $ badKeysErr lensName badKeys
        typeInfo <- TypeInfoT get
        let conflictKeys = [ key
                           | key <- M.keys (iface^.lens)
                           , typeInfo & has (lens.ix key) ]
        unless (null conflictKeys) $ conflictKeysErr lensName conflictKeys
        return ()

    parseErr = liftIO $ do
        hPutStrLn stderr $ "Could not parse interface file " ++ filepath
        exitFailure

    shouldBeEmptyErr field = liftIO $ do
        hPutStrLn stderr $ "Field \"" ++ field ++ "\" should be empty."
        hPutStrLn stderr $ "In interface file " ++ filepath
        exitFailure

    badKeysErr field badKeys = liftIO $ do
        hPutStrLn stderr $ "Unexpected keys"
        hPutStrLn stderr $ "In field \"" ++ field ++ "\" of interface file " ++ filepath ++ ":"
        mapM_ (hPutStrLn stderr . show) $ badKeys
        exitFailure

    conflictKeysErr field conflictKeys = liftIO $ do
        hPutStrLn stderr $ "Keys already present in TypeInfo map"
        hPutStrLn stderr $ "In field \"" ++ field ++ "\" of interface file " ++ filepath ++ ":"
        mapM_ (hPutStrLn stderr . show) $ conflictKeys
        exitFailure

findIFace :: forall m. MonadIO m => ModuleIdent -> TypeInfoT m ()
findIFace m = do
    paths <- TypeInfoT $ use searchPaths
    liftIO (findFile paths filename) >>= \case
        Just filepath -> loadIFace m filepath
        Nothing -> notFoundErr paths

  where
    filename = slashIt (T.unpack m) <> ".h2ci"
    slashIt :: String -> FilePath
    slashIt = map go where go '.' = '/'
                           go c = c

    notFoundErr paths = liftIO $ do
        hPutStrLn stderr $ "Could not find " ++ filename  ++ " in any of these directories:"
        mapM_ (hPutStrLn stderr) paths
        exitFailure

needIface :: forall m. MonadIO m => Qualid -> TypeInfoT m ()
needIface qi | Just mi <- qualidModule qi =
    TypeInfoT (use (processedModules.contains mi)) >>= \case
        True -> return () -- This module is being processed, nothing to load
        False -> TypeInfoT (use (ifaceLoadCache.at mi)) >>= \case
            Just _ -> return () -- We already loaded this module
            Nothing -> findIFace mi
needIface _ = return () -- Unqualified name, do nothing


-- | This type class provides an interface to look up type and type class
-- information, and to register such information.
--
-- It will eventually implement, nicely hidden, interface loading and writing
class Monad m => TypeInfoMonad m where
    -- | Indicates that this module is now going to be proceed.
    -- This allows the store operations to work, and prevents
    -- the TypeInfoMonad from trying to load an interface files
    -- for this module
    isProcessedModule       :: ModuleIdent     -> m ()

    lookupConstructors      :: TypeName        -> m (Maybe [ConstructorName])
    lookupConstructorType   :: ConstructorName -> m (Maybe TypeName)
    lookupConstructorFields :: ConstructorName -> m (Maybe ConstructorFields)
    lookupRecordFieldType   :: ConstructorName -> m (Maybe TypeName)
    lookupClassDefn         :: ClassName       -> m (Maybe ClassDefinition)
    lookupDefaultMethods    :: ClassName       -> m (Maybe (Map MethodName Term))

    storeConstructors       :: TypeName        -> [ConstructorName]   -> m ()
    storeConstructorType    :: ConstructorName -> TypeName            -> m ()
    storeConstructorFields  :: ConstructorName -> ConstructorFields   -> m ()
    storeRecordFieldType    :: ConstructorName -> TypeName            -> m ()
    storeClassDefn          :: ClassName       -> ClassDefinition     -> m ()
    storeDefaultMethods     :: ClassName       -> Map MethodName Term -> m ()

lookup' :: MonadIO m => (Lens' TypeInfo (Map Qualid a)) -> Qualid -> TypeInfoT m (Maybe a)
lookup' lens key = do
    needIface key
    TypeInfoT $ use $ lens . at key

store' :: MonadIO m => (Lens' TypeInfo (Map Qualid a)) -> Qualid -> a -> TypeInfoT m ()
store' _ (Bare n) _ = liftIO $ do
    hPutStrLn stderr $ "Cannot store bare name in the TypeInfo map:"
    hPutStrLn stderr $ show n
    exitFailure
store' lens qid@(Qualified mi _) x = do
    TypeInfoT (use (processedModules.contains mi)) >>= \case
        False -> liftIO $ do
            hPutStrLn stderr $ "Cannot store information about " ++ show qid
            exitFailure
        True -> TypeInfoT $ lens . at qid ?= x

instance MonadIO m => TypeInfoMonad (TypeInfoT m) where
    isProcessedModule       mi = TypeInfoT $ processedModules %= S.insert mi

    lookupConstructors      = lookup' constructors
    lookupConstructorType   = lookup' constructorTypes
    lookupConstructorFields = lookup' constructorFields
    lookupRecordFieldType   = lookup' recordFieldTypes
    lookupClassDefn         = lookup' classDefns
    lookupDefaultMethods    = lookup' defaultMethods

    storeConstructors      = store' constructors
    storeConstructorType   = store' constructorTypes
    storeConstructorFields = store' constructorFields
    storeRecordFieldType   = store' recordFieldTypes
    storeClassDefn         = store' classDefns
    storeDefaultMethods    = store' defaultMethods

-- | Interface search paths
type TypeInfoConfig = [FilePath]

runTypeInfoMonad :: Monad m =>
    TypeInfoConfig ->
    TypeInfoT m a -> m a
runTypeInfoMonad paths (TypeInfoT act) = evalStateT act TypeInfo{..}
  where
    _searchPaths       = paths
    _processedModules  = S.empty
    _ifaceLoadCache    = M.empty

    _constructors      = M.fromList [ (t, [d | (d,_) <- ds]) | (t,ds) <- builtInDataCons]
    _constructorTypes  = M.fromList [ (d, t) | (t,ds) <- builtInDataCons, (d,_) <- ds ]
    _constructorFields = M.fromList [ (d, NonRecordFields n) | (_,ds) <- builtInDataCons, (d,n) <- ds ]
    _recordFieldTypes  = M.empty
    _classDefns        = M.fromList [ (i, cls) | cls@(ClassDefinition i _ _ _) <- builtInClasses ]
--    _memberSigs        = M.empty
    _defaultMethods    =   builtInDefaultMethods


isConstructor :: TypeInfoMonad m => Qualid -> m Bool
isConstructor con = isJust <$> lookupConstructorType con

-- Boiler plate instances

instance TypeInfoMonad m => TypeInfoMonad (ReaderT s m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors      ty = lift $ lookupConstructors      ty
    lookupConstructorType   cn = lift $ lookupConstructorType   cn
    lookupConstructorFields cn = lift $ lookupConstructorFields cn
    lookupRecordFieldType   cn = lift $ lookupRecordFieldType   cn
    lookupClassDefn         cl = lift $ lookupClassDefn         cl
    lookupDefaultMethods    cl = lift $ lookupDefaultMethods    cl

    storeConstructors       ty x = lift $ storeConstructors      ty x
    storeConstructorType    cn x = lift $ storeConstructorType   cn x
    storeConstructorFields  cn x = lift $ storeConstructorFields cn x
    storeRecordFieldType    cn x = lift $ storeRecordFieldType   cn x
    storeClassDefn          cl x = lift $ storeClassDefn         cl x
    storeDefaultMethods     cl x = lift $ storeDefaultMethods    cl x

instance TypeInfoMonad m => TypeInfoMonad (CounterT m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors      ty = lift $ lookupConstructors      ty
    lookupConstructorType   cn = lift $ lookupConstructorType   cn
    lookupConstructorFields cn = lift $ lookupConstructorFields cn
    lookupRecordFieldType   cn = lift $ lookupRecordFieldType   cn
    lookupClassDefn         cl = lift $ lookupClassDefn         cl
    lookupDefaultMethods    cl = lift $ lookupDefaultMethods    cl

    storeConstructors       ty x = lift $ storeConstructors      ty x
    storeConstructorType    cn x = lift $ storeConstructorType   cn x
    storeConstructorFields  cn x = lift $ storeConstructorFields cn x
    storeRecordFieldType    cn x = lift $ storeRecordFieldType   cn x
    storeClassDefn          cl x = lift $ storeClassDefn         cl x
    storeDefaultMethods     cl x = lift $ storeDefaultMethods    cl x

instance (TypeInfoMonad m, Monoid s) => TypeInfoMonad (WriterT s m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors      ty = lift $ lookupConstructors      ty
    lookupConstructorType   cn = lift $ lookupConstructorType   cn
    lookupConstructorFields cn = lift $ lookupConstructorFields cn
    lookupRecordFieldType   cn = lift $ lookupRecordFieldType   cn
    lookupClassDefn         cl = lift $ lookupClassDefn         cl
    lookupDefaultMethods    cl = lift $ lookupDefaultMethods    cl

    storeConstructors       ty x = lift $ storeConstructors      ty x
    storeConstructorType    cn x = lift $ storeConstructorType   cn x
    storeConstructorFields  cn x = lift $ storeConstructorFields cn x
    storeRecordFieldType    cn x = lift $ storeRecordFieldType   cn x
    storeClassDefn          cl x = lift $ storeClassDefn         cl x
    storeDefaultMethods     cl x = lift $ storeDefaultMethods    cl x

instance TypeInfoMonad m => TypeInfoMonad (MaybeT m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors      ty = lift $ lookupConstructors      ty
    lookupConstructorType   cn = lift $ lookupConstructorType   cn
    lookupConstructorFields cn = lift $ lookupConstructorFields cn
    lookupRecordFieldType   cn = lift $ lookupRecordFieldType   cn
    lookupClassDefn         cl = lift $ lookupClassDefn         cl
    lookupDefaultMethods    cl = lift $ lookupDefaultMethods    cl

    storeConstructors       ty x = lift $ storeConstructors      ty x
    storeConstructorType    cn x = lift $ storeConstructorType   cn x
    storeConstructorFields  cn x = lift $ storeConstructorFields cn x
    storeRecordFieldType    cn x = lift $ storeRecordFieldType   cn x
    storeClassDefn          cl x = lift $ storeClassDefn         cl x
    storeDefaultMethods     cl x = lift $ storeDefaultMethods    cl x

instance GhcMonad m => GhcMonad (TypeInfoT m) where
  getSession = lift   getSession
  setSession = lift . setSession


