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
    , explicitMethodArguments, classTypes, superclassCount
    , ConstructorFields(..)
    , _RecordFields
    -- * The Monad
    , runTypeInfoMonad
    , TypeInfoConfig
    , TypeInfoMonad(..)
    -- * Derived utility functions
    , isConstructor
    ) where

import Control.Lens hiding (use)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Reader.Class
import Control.Monad.Trans.Reader (ReaderT, runReaderT)
import Data.IORef
import Data.Maybe
import Data.Monoid
import Data.Foldable
import Text.Read (readMaybe)
import qualified Data.Text as T
import Data.Yaml hiding ((.=))

import System.Directory
import System.IO
import System.Exit

import HsToCoq.Util.GHC.Monad
import HsToCoq.Util.GHC.Exception
import HsToCoq.Util.GHC.DynFlags

import HsToCoq.Coq.Gallina (Qualid, Binder, ClassDefinition(..), Term, Qualid(..), ModuleIdent)
import HsToCoq.Coq.Gallina.Util (qualidModule, qualidToIdent, unsafeIdentToQualid)
import HsToCoq.Coq.Pretty
import HsToCoq.ConvertHaskell.BuiltIn

import qualified Control.Monad.Trans.Identity      as I
import qualified Control.Monad.Trans.Reader        as R
import qualified Control.Monad.Trans.Writer.Strict as WS
import qualified Control.Monad.Trans.Writer.Lazy   as WL
import qualified Control.Monad.Trans.State.Lazy    as SL
import qualified Control.Monad.Trans.State.Strict  as SS
import qualified Control.Monad.Trans.RWS.Strict    as RWSS
import qualified Control.Monad.Trans.RWS.Lazy      as RWSL
import qualified Control.Monad.Trans.Maybe         as M
import qualified Control.Monad.Trans.Except        as E
import qualified Control.Monad.Trans.Cont          as C
import qualified Control.Monad.Trans.Counter       as Ct

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
    { _searchPaths             :: ![FilePath]
    , _loadStatus              :: !(Map ModuleIdent LoadStatus)
    , _processedModules        :: !(Set ModuleIdent)

    , _constructors            :: !(Map TypeName [ConstructorName])
    , _constructorTypes        :: !(Map ConstructorName TypeName)
    , _constructorFields       :: !(Map ConstructorName ConstructorFields)
    , _recordFieldTypes        :: !(Map ConstructorName TypeName)
    , _classDefns              :: !(Map ClassName ClassDefinition)
    , _defaultMethods          :: !(Map ClassName DefaultMethods)
    , _explicitMethodArguments :: !(Map Qualid [Binder])
    , _classTypes              :: !(Map ClassName (Set TypeName))
    , _superclassCount         :: !(Map ClassName Int)
    }
    deriving (Show, Read) -- for cheap serialization for now 

makeLenses ''TypeInfo

builtIns :: TypeInfo
builtIns = TypeInfo {..}
  where
    _searchPaths             = []
    _processedModules        = S.empty
    _loadStatus              = M.empty

    _constructors            = M.fromList [ (t, [d | (d,_) <- ds]) | (t,ds) <- builtInDataCons]
    _constructorTypes        = M.fromList [ (d, t) | (t,ds) <- builtInDataCons, (d,_) <- ds ]
    _constructorFields       = M.fromList [ (d, NonRecordFields n) | (_,ds) <- builtInDataCons, (d,n) <- ds ]
    _recordFieldTypes        = M.empty
    _classDefns              = M.fromList [ (i, cls) | cls@(ClassDefinition i _ _ _) <- builtInClasses ]
    _defaultMethods          = builtInDefaultMethods
    _explicitMethodArguments = M.empty
    _classTypes              = M.empty
    _superclassCount         = M.empty

emptyTypeInfo :: TypeInfo
emptyTypeInfo = TypeInfo {..}
  where
    _searchPaths             = []
    _processedModules        = S.empty
    _loadStatus              = M.empty

    _constructors            = M.empty
    _constructorTypes        = M.empty
    _constructorFields       = M.empty
    _recordFieldTypes        = M.empty
    _classDefns              = M.empty
    _defaultMethods          = M.empty
    _explicitMethodArguments = M.empty
    _classTypes              = M.empty
    _superclassCount         = M.empty

data AField where
    AField :: forall a.
        (Show a, Read a) =>
        String ->
        Lens' TypeInfo (Map Qualid a) ->
        AField

typeInfoFields :: [AField]
typeInfoFields =
    [ AField "constructors"            constructors
    , AField "constructorTypes"        constructorTypes
    , AField "constructorFields"       constructorFields
    , AField "recordFieldTypes"        recordFieldTypes
    , AField "classDefns"              classDefns
    , AField "defaultMethods"          defaultMethods
    , AField "explicitMethodArguments" explicitMethodArguments
    , AField "classTypes"              classTypes
    , AField "superclassCount"         superclassCount
    ]

-- We use a ReaderT with an IORef rather than a StateMonad
-- so that the state (which is mostly a cache) survives error handling
-- in the rest of the application
newtype TypeInfoT m a = TypeInfoT (ReaderT (IORef TypeInfo) m a)
  deriving ( Functor, Applicative, Monad, MonadIO, ExceptionMonad, GhcMonad
           , HasDynFlags, MonadTrans)

get :: (MonadReader (IORef r) m, MonadIO m) => m r
get = do
    ref <- ask
    liftIO $ readIORef ref

use :: (MonadReader (IORef r) m, MonadIO m) => Lens' r a -> m a
use lens = do
    ref <- ask
    v <- liftIO $ readIORef ref
    return $ v^.lens

modify :: (MonadReader (IORef r) m, MonadIO m) => (r -> r) -> m ()
modify f = do
    ref <- ask
    liftIO $ modifyIORef' ref f

addIface :: MonadIO m => TypeInfo -> TypeInfoT m ()
addIface newInfo = TypeInfoT $ modify (appEndo (foldMap (Endo . go) typeInfoFields))
  where go (AField _ lens) = lens %~ M.union (newInfo ^. lens)

loadIFace :: forall m. MonadIO m => ModuleIdent -> FilePath -> TypeInfoT m ()
loadIFace mi filepath = liftIO (decodeFileEither filepath) >>= \case
    Left _err -> parseErr
    Right content -> case deserialize content of
        Nothing -> parseErr
        Just iface -> do
            checkIface iface
            addIface iface
            TypeInfoT $ modify $ loadStatus . at mi ?~ Loaded filepath
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
            TypeInfoT $ modify $ loadStatus . at m ?~ NotFound
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
        hPutStrLn stderr $ "Please either process " ++ T.unpack m ++ " first, or"
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

    lookupConstructors            :: TypeName        -> m (Maybe [ConstructorName])
    lookupConstructorType         :: ConstructorName -> m (Maybe TypeName)
    lookupConstructorFields       :: ConstructorName -> m (Maybe ConstructorFields)
    lookupRecordFieldType         :: ConstructorName -> m (Maybe TypeName)
    lookupClassDefn               :: ClassName       -> m (Maybe ClassDefinition)
    lookupDefaultMethods          :: ClassName       -> m (Maybe (Map MethodName Term))
    lookupExplicitMethodArguments :: TypeName        -> m (Maybe [Binder])
    lookupClassTypes              :: ClassName       -> m (Maybe (Set TypeName))
    lookupSuperclassCount         :: ClassName       -> m (Maybe Int)

    storeConstructors            :: TypeName        -> [ConstructorName]   -> m ()
    storeConstructorType         :: ConstructorName -> TypeName            -> m ()
    storeConstructorFields       :: ConstructorName -> ConstructorFields   -> m ()
    storeRecordFieldType         :: ConstructorName -> TypeName            -> m ()
    storeClassDefn               :: ClassName       -> ClassDefinition     -> m ()
    storeDefaultMethods          :: ClassName       -> Map MethodName Term -> m ()
    storeExplicitMethodArguments :: TypeName        -> [Binder]            -> m ()
    storeClassTypes              :: ClassName       -> Set TypeName        -> m ()
    storeSuperclassCount         :: ClassName       -> Int                 -> m ()

    serializeIfaceFor       :: ModuleIdent -> FilePath -> m ()
    loadedInterfaceFiles    :: m [FilePath]

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
    --exitFailure
store' lens key _ | Just _ <- builtIns ^. lens . at key = liftIO $ do
    hPutStrLn stderr $ "Trying to override built-in information about " ++ showP key
    exitFailure
store' lens qid@(Qualified mi _) x = do
    TypeInfoT (use (processedModules.contains mi)) >>= \case
        False -> liftIO $ do
            hPutStrLn stderr $ "Cannot store information about " ++ showP qid
            --exitFailure
        True -> TypeInfoT $ modify $ lens . at qid ?~ x

deserialize :: M.Map String (M.Map T.Text String) -> Maybe TypeInfo
deserialize ifaceMaps = foldlM go emptyTypeInfo typeInfoFields
  where
    go ti (AField fieldName lens) =
        case M.lookup fieldName ifaceMaps of
            Nothing -> pure ti
            Just m -> do content <- mapM readMaybe m
                         let content' = M.mapKeys unsafeIdentToQualid content
                         pure $ set lens content' ti

serializeIfaceFor' :: MonadIO m => ModuleIdent -> FilePath -> TypeInfoT m ()
serializeIfaceFor' mi filepath =
    TypeInfoT (use (processedModules.contains mi)) >>= \case
        False -> liftIO $ do
            hPutStrLn stderr $ "Module " ++ T.unpack mi ++ " is not a processed one."
            exitFailure
        True -> do
            ti <- TypeInfoT $ get
            liftIO $ encodeFile filepath $ M.fromList
                [ (fieldName, textified)
                | AField fieldName lens <- typeInfoFields
                , let content = ti ^. lens
                , let filtered = M.filterWithKey inThisMod content
                , not (M.null filtered)
                , let textified = M.mapKeys qualidToIdent $ M.map show $ filtered
                ]
  where
    inThisMod ::  Qualid -> a -> Bool
    inThisMod qid _  = qualidModule qid == Just mi

loadedInterfaceFiles' :: MonadIO m => TypeInfoT m [FilePath]
loadedInterfaceFiles' = TypeInfoT $ do
    m <- use loadStatus
    return $ [ fp | Loaded fp <- M.elems m ]

instance MonadIO m => TypeInfoMonad (TypeInfoT m) where
    isProcessedModule       mi = TypeInfoT $ modify $ processedModules %~ S.insert mi

    lookupConstructors            = lookup' "constructors"            constructors
    lookupConstructorType         = lookup' "constructorTypes"        constructorTypes
    lookupConstructorFields       = lookup' "constructorFields"       constructorFields
    lookupRecordFieldType         = lookup' "recordFieldTypes"        recordFieldTypes
    lookupClassDefn               = lookup' "classDefns"              classDefns
    lookupDefaultMethods          = lookup' "defaultMethods"          defaultMethods
    lookupExplicitMethodArguments = lookup' "explicitMethodArguments" explicitMethodArguments
    lookupClassTypes              = lookup' "classTypes"              classTypes
    lookupSuperclassCount         = lookup' "superclassCount"         superclassCount

    storeConstructors            = store' constructors
    storeConstructorType         = store' constructorTypes
    storeConstructorFields       = store' constructorFields
    storeRecordFieldType         = store' recordFieldTypes
    storeClassDefn               = store' classDefns
    storeDefaultMethods          = store' defaultMethods
    storeExplicitMethodArguments = store' explicitMethodArguments
    storeClassTypes              = store' classTypes
    storeSuperclassCount         = store' superclassCount

    serializeIfaceFor    = serializeIfaceFor'
    loadedInterfaceFiles = loadedInterfaceFiles'

-- | Interface search paths
type TypeInfoConfig = [FilePath]


runTypeInfoMonad :: MonadIO m => TypeInfoConfig -> TypeInfoT m a -> m a
runTypeInfoMonad paths (TypeInfoT act) = do
    ref <- liftIO $ newIORef (emptyTypeInfo & searchPaths .~ paths)
    runReaderT act ref


isConstructor :: TypeInfoMonad m => Qualid -> m Bool
isConstructor con = isJust <$> lookupConstructorType con

-- Boilerplate instances -- nothing interesting from hereon out

instance TypeInfoMonad m => TypeInfoMonad (I.IdentityT m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

instance TypeInfoMonad m => TypeInfoMonad (R.ReaderT r m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

instance (TypeInfoMonad m, Monoid w) => TypeInfoMonad (WS.WriterT w m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

instance (TypeInfoMonad m, Monoid w) => TypeInfoMonad (WL.WriterT w m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

instance TypeInfoMonad m => TypeInfoMonad (SS.StateT s m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

instance TypeInfoMonad m => TypeInfoMonad (SL.StateT s m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

instance (TypeInfoMonad m, Monoid w) => TypeInfoMonad (RWSS.RWST r w s m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

instance (TypeInfoMonad m, Monoid w) => TypeInfoMonad (RWSL.RWST r w s m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

instance TypeInfoMonad m => TypeInfoMonad (M.MaybeT m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

instance TypeInfoMonad m => TypeInfoMonad (E.ExceptT e m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

instance TypeInfoMonad m => TypeInfoMonad (C.ContT r m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

instance TypeInfoMonad m => TypeInfoMonad (Ct.CounterT m) where
    isProcessedModule mi = lift $ isProcessedModule mi

    lookupConstructors            ty = lift $ lookupConstructors            ty
    lookupConstructorType         cn = lift $ lookupConstructorType         cn
    lookupConstructorFields       cn = lift $ lookupConstructorFields       cn
    lookupRecordFieldType         cn = lift $ lookupRecordFieldType         cn
    lookupClassDefn               cl = lift $ lookupClassDefn               cl
    lookupDefaultMethods          cl = lift $ lookupDefaultMethods          cl
    lookupExplicitMethodArguments nm = lift $ lookupExplicitMethodArguments nm
    lookupClassTypes              cl = lift $ lookupClassTypes              cl
    lookupSuperclassCount         cl = lift $ lookupSuperclassCount         cl

    storeConstructors            ty x = lift $ storeConstructors            ty x
    storeConstructorType         cn x = lift $ storeConstructorType         cn x
    storeConstructorFields       cn x = lift $ storeConstructorFields       cn x
    storeRecordFieldType         cn x = lift $ storeRecordFieldType         cn x
    storeClassDefn               cl x = lift $ storeClassDefn               cl x
    storeDefaultMethods          cl x = lift $ storeDefaultMethods          cl x
    storeExplicitMethodArguments nm x = lift $ storeExplicitMethodArguments nm x
    storeClassTypes              cl x = lift $ storeClassTypes              cl x
    storeSuperclassCount         cl x = lift $ storeSuperclassCount         cl x

    serializeIfaceFor m fp = lift $ serializeIfaceFor m fp
    loadedInterfaceFiles   = lift $ loadedInterfaceFiles

-- Don't put anything interesting down here!  Boilerplate instances only!
