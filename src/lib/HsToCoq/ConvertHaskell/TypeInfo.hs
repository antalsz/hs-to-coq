{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiWayIf #-}

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
import Data.Monoid

import System.Directory
import System.IO
import System.Exit

import HsToCoq.Util.GHC.Monad
import HsToCoq.Util.GHC.Exception
import HsToCoq.Util.GHC.DynFlags

import HsToCoq.Coq.Gallina (Qualid, ClassDefinition(..), Term, Qualid(..), ModuleIdent)
import HsToCoq.Coq.Gallina.Util (qualidModule)
import HsToCoq.Coq.Pretty
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
data LoadStatus
        = Loaded FilePath
        | NotFound
    deriving (Show, Read)

data TypeInfo = TypeInfo
    { _searchPaths       :: ![FilePath]
    , _loadStatus        :: !(Map ModuleIdent LoadStatus)
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

builtIns :: TypeInfo
builtIns = TypeInfo {..}
  where
    _searchPaths       = []
    _processedModules  = S.empty
    _loadStatus    = M.empty

    _constructors      = M.fromList [ (t, [d | (d,_) <- ds]) | (t,ds) <- builtInDataCons]
    _constructorTypes  = M.fromList [ (d, t) | (t,ds) <- builtInDataCons, (d,_) <- ds ]
    _constructorFields = M.fromList [ (d, NonRecordFields n) | (_,ds) <- builtInDataCons, (d,n) <- ds ]
    _recordFieldTypes  = M.empty
    _classDefns        = M.fromList [ (i, cls) | cls@(ClassDefinition i _ _ _) <- builtInClasses ]
    _defaultMethods    = builtInDefaultMethods

emptyTypeInfo :: TypeInfo
emptyTypeInfo = TypeInfo {..}
  where
    _searchPaths       = []
    _processedModules  = S.empty
    _loadStatus    = M.empty

    _constructors      = M.empty
    _constructorTypes  = M.empty
    _constructorFields = M.empty
    _recordFieldTypes  = M.empty
    _classDefns        = M.empty
    _defaultMethods    = M.empty


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

addIface :: Monad m => TypeInfo -> TypeInfoT m ()
addIface newInfo = TypeInfoT $ mapM_ go typeInfoFields
  where go (AField _ lens) = lens %= (M.union (newInfo ^. lens))

loadIFace :: forall m. MonadIO m => ModuleIdent -> FilePath -> TypeInfoT m ()
loadIFace mi filepath = do
    ifaceContent <- liftIO $ readFile filepath
    if | lines ifaceContent == ["all built in"]
       -> return () -- for interface files of manually written modules
       | Just iface <- readMaybe ifaceContent
       -> do
        checkIface iface
        addIface iface
        TypeInfoT $ loadStatus . at mi ?= Loaded filepath

       | otherwise
       -> parseErr
  where
    checkIface :: TypeInfo -> TypeInfoT m ()
    checkIface iface = do
        unless (null (iface^.searchPaths))      $ shouldBeEmptyErr "seachPaths"
        unless (M.null (iface^.loadStatus)) $ shouldBeEmptyErr "loadStatus"
        mapM_ (checkField iface) typeInfoFields

    checkField iface (AField lensName lens) = do
        let badKeys =      [ key
                           | key <- M.keys (iface^.lens)
                           , qualidModule key /= Just mi ]
        unless (null badKeys) $ badKeysErr lensName badKeys
        typeInfo <- TypeInfoT get
        let conflictKeys = [ key
                           | key <- M.keys (iface^.lens)
                           , typeInfo & has (lens.ix key) ]
        unless (null conflictKeys) $ conflictKeysErr lensName conflictKeys
        return ()

    parseErr = liftIO $ do
        hPutStrLn stderr $ "Could not parse interface file " ++ filepath
        hPutStrLn stderr $ "(please delete or regenerate)"
        exitFailure

    shouldBeEmptyErr field = liftIO $ do
        hPutStrLn stderr $ "Field \"" ++ field ++ "\" should be empty."
        hPutStrLn stderr $ "In interface file " ++ filepath
        exitFailure

    badKeysErr field badKeys = liftIO $ do
        hPutStrLn stderr $ "Unexpected keys"
        hPutStrLn stderr $ "In field \"" ++ field ++ "\" of interface file " ++ filepath ++ ":"
        mapM_ (hPutStrLn stderr . showP) $ badKeys
        exitFailure

    conflictKeysErr field conflictKeys = liftIO $ do
        hPutStrLn stderr $ "Keys already present in TypeInfo map"
        hPutStrLn stderr $ "In field \"" ++ field ++ "\" of interface file " ++ filepath ++ ":"
        mapM_ (hPutStrLn stderr . showP) $ conflictKeys
        exitFailure

findIFace :: forall m. MonadIO m => ModuleIdent -> String -> TypeInfoT m ()
findIFace m errContext = do
    paths <- TypeInfoT $ use searchPaths
    liftIO (findFile paths filename) >>= \case
        Just filepath -> loadIFace m filepath
        Nothing -> do
            TypeInfoT $ loadStatus . at m ?= NotFound
            notFoundErr paths

  where
    filename = slashIt (T.unpack m) <> ".h2ci"
    slashIt :: String -> FilePath
    slashIt = map go where go '.' = '/'
                           go c = c

    notFoundErr paths = liftIO $ do
        hPutStrLn stderr errContext
        hPutStrLn stderr $ "Could not find " ++ filename  ++ " in any of these directories:"
        mapM_ (hPutStrLn stderr . ("    * "++)) paths
        hPutStrLn stderr $ "Please either process " ++ T.unpack m ++ "first, or"
        hPutStrLn stderr $ "skip declarations that mention " ++ T.unpack m ++ "."
        -- exitFailure

needIface :: forall m. MonadIO m => Qualid -> String -> TypeInfoT m ()
needIface qi errContext | Just mi <- qualidModule qi =
    TypeInfoT (use (processedModules.contains mi)) >>= \case
        True -> return () -- This module is being processed, nothing to load
        False -> TypeInfoT (use (loadStatus.at mi)) >>= \case
            Just _ -> return () -- We already tried to load this module
            Nothing -> findIFace mi errContext
needIface _ _ = return () -- Unqualified name, do nothing


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

    serializeIfaceFor       :: ModuleIdent -> m String

lookup' :: MonadIO m =>
    String -> (Lens' TypeInfo (Map Qualid a)) ->
    Qualid -> TypeInfoT m (Maybe a)
lookup' _ lens key | Just x <- builtIns ^. lens . at key = pure (Just x)
 -- Looking up a built in thing does not trigger loading an interface
lookup' fieldName lens key = do
    needIface key errContext
    TypeInfoT $ use $ lens . at key
  where
    errContext = "When looking up information about " ++ showP key ++ " in " ++ fieldName

store' :: MonadIO m => (Lens' TypeInfo (Map Qualid a)) -> Qualid -> a -> TypeInfoT m ()
store' _ (Bare n) _ = liftIO $ do
    hPutStrLn stderr $ "Cannot store bare name in the TypeInfo map:"
    hPutStrLn stderr $ T.unpack n
    exitFailure
store' lens key _ | Just _ <- builtIns ^. lens . at key = liftIO $ do
    hPutStrLn stderr $ "Trying to override built-in information about " ++ showP key
    exitFailure
store' lens qid@(Qualified mi _) x = do
    TypeInfoT (use (processedModules.contains mi)) >>= \case
        False -> liftIO $ do
            hPutStrLn stderr $ "Cannot store information about " ++ showP qid
            exitFailure
        True -> TypeInfoT $ lens . at qid ?= x

serializeIfaceFor' :: MonadIO m => ModuleIdent -> TypeInfoT m String
serializeIfaceFor' mi = do
    TypeInfoT (use (processedModules.contains mi)) >>= \case
        False -> liftIO $ do
            hPutStrLn stderr $ "Module " ++ T.unpack mi ++ " is not a processed one."
            exitFailure
        True -> TypeInfoT $ gets (show . go)
  where
    go :: TypeInfo -> TypeInfo
    go = appEndo $ foldMap Endo $
        [ searchPaths      .~ []
        , loadStatus       .~ M.empty
        , processedModules .~ S.empty
        ] ++
        [ field %~ M.filterWithKey inThisMod
        | AField _ field <- typeInfoFields ]

    inThisMod ::  Qualid -> a -> Bool
    inThisMod qid _  = qualidModule qid == Just mi

instance MonadIO m => TypeInfoMonad (TypeInfoT m) where
    isProcessedModule       mi = TypeInfoT $ processedModules %= S.insert mi

    lookupConstructors      = lookup' "constructors"      constructors
    lookupConstructorType   = lookup' "constructorTypes"  constructorTypes
    lookupConstructorFields = lookup' "constructorFields" constructorFields
    lookupRecordFieldType   = lookup' "recordFieldTypes"  recordFieldTypes
    lookupClassDefn         = lookup' "classDefns"        classDefns
    lookupDefaultMethods    = lookup' "defaultMethods"    defaultMethods

    storeConstructors      = store' constructors
    storeConstructorType   = store' constructorTypes
    storeConstructorFields = store' constructorFields
    storeRecordFieldType   = store' recordFieldTypes
    storeClassDefn         = store' classDefns
    storeDefaultMethods    = store' defaultMethods

    serializeIfaceFor = serializeIfaceFor'

-- | Interface search paths
type TypeInfoConfig = [FilePath]


runTypeInfoMonad :: Monad m =>
    TypeInfoConfig ->
    TypeInfoT m a -> m a
runTypeInfoMonad paths (TypeInfoT act) = evalStateT ?? emptyTypeInfo $ do
    searchPaths .= paths
    act


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

    serializeIfaceFor m = lift $ serializeIfaceFor m

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

    serializeIfaceFor m = lift $ serializeIfaceFor m

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

    serializeIfaceFor m = lift $ serializeIfaceFor m

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

    serializeIfaceFor m = lift $ serializeIfaceFor m

instance GhcMonad m => GhcMonad (TypeInfoT m) where
  getSession = lift   getSession
  setSession = lift . setSession


