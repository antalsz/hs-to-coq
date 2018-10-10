{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings, ScopedTypeVariables,
             RankNTypes, ConstraintKinds, FlexibleContexts,
             TemplateHaskell, MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances,
             TypeApplications
  #-}

module HsToCoq.ConvertHaskell.Monad (
  -- * Environments
  GlobalEnv(..), ModuleEnv(..), LocalEnv(..),
  -- * Constraints
  GlobalMonad, ConversionMonad, LocalConvMonad,
  HasEdits(..), HasLeniency(..), HasCurrentModule(..), HasCurrentDefinition(..),
  runGlobalMonad,
  withCurrentModule,
  withCurrentDefinition,
  -- * Convenience views
  currentModuleAxiomatized,
  -- * Leniency
  Leniency(..), whenPermissive, handleIfPermissive,
  -- * Testing skippedness/axiomness
  definitionTask, TranslationTask(..), AxiomatizationMode(..),
  -- * Operations
  fresh, gensym, genqid,
  useProgramHere, renamed,
  -- * Errors
  throwProgramError, convUnsupported, editFailure,
  -- * Modules
  skipModules, skipModulesBy
  ) where

import Control.Lens hiding (Strict)

import Data.Semigroup (Semigroup(..))
import Data.Text (Text)
import qualified Data.Text as T
import HsToCoq.Util.Monad

import Control.Monad.Trans.Counter
import Control.Monad.State
import Control.Monad.Reader

import Data.Set (Set)

import GHC
import Exception

import Panic

import HsToCoq.Coq.Gallina (Qualid, Qualid(..), Ident)
import HsToCoq.Util.GHC.Module (moduleNameText)

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.TypeInfo

--------------------------------------------------------------------------------

-- |How to handle translation errors
data Leniency = Permissive -- ^Try to recover by e.g. introducing an axiom
              | Strict     -- ^Blow up
              deriving (Eq, Ord, Enum, Bounded, Show, Read)              

--------------------------------------------------------------------------------

-- The reader states
--
-- In various stages of the program (top-level, module level, definition level)
-- we need to extend the reader environment with additional data.
--
-- mtl’s ReaderT is not extensible, so we have a concrete data type for
-- all three levels, and use the HasFoo type classes from lens to uniformly
-- access the various fields


data GlobalEnv = GlobalEnv
    { _globalEnvEdits    :: !Edits
    , _globalEnvLeniency :: !Leniency
    } deriving Show

data ModuleEnv = ModuleEnv
    { _moduleEnvEdits         :: !Edits
    , _moduleEnvLeniency      :: !Leniency
    , _moduleEnvCurrentModule :: !ModuleName
    }

data LocalEnv = LocalEnv
    { _localEnvEdits             :: !Edits
    , _localEnvLeniency          :: !Leniency
    , _localEnvCurrentModule     :: !ModuleName
    , _localEnvCurrentDefinition :: !Qualid
    }

makeFields ''GlobalEnv
makeFields ''ModuleEnv
makeFields ''LocalEnv

currentModuleAxiomatized :: (HasEdits s Edits, HasCurrentModule s ModuleName) => Getter  s Bool
currentModuleAxiomatized = to $ \s -> s^.edits.axiomatizedModules.contains (s^.currentModule)

data AxiomatizationMode = SpecificAxiomatize | GeneralAxiomatize
                        deriving (Eq, Ord, Enum, Bounded, Show, Read)

data TranslationTask = SkipIt
                     | AxiomatizeIt AxiomatizationMode
                     | TranslateIt
                     deriving (Eq, Ord, Show, Read)

-- |Should this definition be skipped, axiomatized, or translated?
-- `HasEdits`, and `HasCurrentModule`, but that hardly seems necessary.
definitionTask :: forall s m. (MonadReader s m, HasEdits s Edits, HasCurrentModule s ModuleName)
               => Qualid -> m TranslationTask
definitionTask name =
  let isIn :: Lens' Edits (Set Qualid) -> m Bool
      isIn field = view $ edits.field.contains name
  in ifM (isIn skipped)
       (pure SkipIt)
       (ifM (view currentModuleAxiomatized)
          (ifM (isIn unaxiomatizedDefinitions)
             (pure TranslateIt)
             (pure $ AxiomatizeIt GeneralAxiomatize))
          (ifM (isIn axiomatizedDefinitions)
             (pure $ AxiomatizeIt SpecificAxiomatize)
             (pure TranslateIt)))

-- The constraint aliases, for the three levels of scoping
-- Note that they are subconstraints of each other, so you can call a
-- fuction with a GlobalMonad constraint from one with a LocalConvMonad
-- constraints

-- Unfortunately the r sticks around here, despite being a functional
-- dependency of m

-- | The global monad, used outside specific modules
--
type GlobalMonad r m =
        ( GhcMonad m
        , TypeInfoMonad m
        , MonadReader r m
        , HasEdits r Edits
        , HasLeniency r Leniency
        )

-- | The global monad, used for top-level bindings.
--   Has edits, current module name, access to GHC etc.
type ConversionMonad r m =
        ( GlobalMonad r m
        , HasCurrentModule r ModuleName
        )
-- | The local one monad, additional knows the current function name
--   and a counter for fresh variables
type LocalConvMonad r m =
        ( ConversionMonad r m
        , CounterMonad m
        , HasCurrentDefinition r Qualid
        )

runGlobalMonad :: (GhcMonad m, Monad m) =>
    Edits ->
    Leniency ->
    TypeInfoConfig ->
    (forall r m. GlobalMonad r m => m a) ->
    m a
runGlobalMonad initEdits leniency paths act =
    runTypeInfoMonad paths $
    runReaderT ?? GlobalEnv{_globalEnvEdits = initEdits, _globalEnvLeniency = leniency} $
    act

withCurrentModule :: GlobalMonad r m =>
    ModuleName ->
    (forall r m. ConversionMonad r m => m a) ->
    m a
withCurrentModule newModule act = do
    _edits    <- view edits
    _leniency <- view leniency
    isProcessedModule (moduleNameText newModule) -- Start collecting the interface
    runReaderT act $ ModuleEnv
        { _moduleEnvEdits         = _edits
        , _moduleEnvLeniency      = _leniency
        , _moduleEnvCurrentModule = newModule
        }

withCurrentDefinition :: ConversionMonad r m =>
    Qualid ->
    (forall r m. LocalConvMonad r m => m a) ->
    m a
withCurrentDefinition newDef act = do
    global_edits <- view edits
    local_edits <- view (edits.inEdits.at newDef.non mempty)
    let edits_in_scope = local_edits <> global_edits
    
    _leniency      <- view leniency
    _currentModule <- view currentModule
    withCounterT $ runReaderT act $ LocalEnv
        { _localEnvEdits             = edits_in_scope
        , _localEnvLeniency          = _leniency
        , _localEnvCurrentModule     = _currentModule
        , _localEnvCurrentDefinition = newDef
        }


gensym :: LocalConvMonad r m => Text -> m Ident
gensym name = do u <- fresh
                 pure $ name <> "_" <> T.pack (show u) <> "__"

genqid :: LocalConvMonad r m => Text -> m Qualid
genqid name = Bare <$> gensym name

throwProgramError :: MonadIO m => String -> m a
throwProgramError = liftIO . throwGhcExceptionIO . ProgramError

convUnsupported :: MonadIO m => String -> m a
convUnsupported what = throwProgramError $ what ++ " unsupported"

editFailure :: MonadIO m => String -> m a
editFailure what = throwProgramError $ "Could not apply edit: " ++ what

skipModulesBy :: GlobalMonad r m => (a -> ModuleName) -> [a] -> m [a]
skipModulesBy f = filterM $ \a -> view $ edits.skippedModules.contains (f a).to not

skipModules :: GlobalMonad r m => [ModuleName] -> m [ModuleName]
skipModules = skipModulesBy id

useProgramHere :: LocalConvMonad r m => m Bool
useProgramHere = do
    n <- view currentDefinition
    useProgram n <$> view edits

renamed :: HsNamespace -> Qualid -> Lens' Edits (Maybe Qualid)
renamed ns x = renamings.at (NamespacedIdent ns x)
{-# INLINABLE renamed #-}

whenPermissive :: (MonadReader r m, HasLeniency r Leniency) => a -> m (Maybe a)
whenPermissive x =
  view leniency <&> \case
    Permissive -> Just x
    Strict     -> Nothing

handleIfPermissive :: (ExceptionMonad m, MonadReader r m, HasLeniency r Leniency, Exception e)
                   => (e -> m a) -> m a -> m a
handleIfPermissive onError act =
  view leniency >>= \case
    Permissive -> ghandle onError act
    Strict     -> act
