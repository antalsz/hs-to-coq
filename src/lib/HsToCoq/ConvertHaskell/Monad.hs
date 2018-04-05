{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             RankNTypes, ConstraintKinds, FlexibleContexts,
             TemplateHaskell, MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances,
             TypeApplications
  #-}

module HsToCoq.ConvertHaskell.Monad (
  -- * Constraints
  GlobalMonad, ConversionMonad, LocalConvMonad,
  runGlobalMonad,
  withCurrentModule,
  withCurrentDefinition,
  -- * Types
  edits, currentDefinition, currentModule,
  -- * Operations
  fresh, gensym, genqid,
  useProgramHere, renamed,
  -- * Errors
  throwProgramError, convUnsupported, editFailure,
  -- * Modules
  skipModules, skipModulesBy
  ) where

import Control.Lens

import Data.Semigroup (Semigroup(..))
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad.Trans.Counter

import Control.Monad.State
import Control.Monad.Reader

import GHC

import Panic

import HsToCoq.Coq.Gallina (Qualid, Qualid(..), Ident)

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.TypeInfo


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
    { _globalEnvEdits :: Edits
    }

data ModuleEnv = ModuleEnv
    { _moduleEnvEdits         :: Edits
    , _moduleEnvCurrentModule :: ModuleName
    }

data LocalEnv = LocalEnv
    { _localEnvEdits             :: Edits
    , _localEnvCurrentModule     :: ModuleName
    , _localEnvCurrentDefinition :: Qualid
    }

makeFields ''GlobalEnv
makeFields ''ModuleEnv
makeFields ''LocalEnv


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

runGlobalMonad :: (GhcMonad m, Monad m) => Edits ->
    (forall r m. GlobalMonad r m => m a) ->
    m a
runGlobalMonad initEdits act =
    runTypeInfoMonad $
    runReaderT ?? GlobalEnv{_globalEnvEdits = initEdits} $
    act

withCurrentModule :: GlobalMonad r m =>
    ModuleName ->
    (forall r m. ConversionMonad r m => m a) ->
    m a
withCurrentModule newModule act = do
    _edits <- view edits
    runReaderT act $ ModuleEnv
        { _moduleEnvEdits         = _edits
        , _moduleEnvCurrentModule = newModule
        }

withCurrentDefinition :: ConversionMonad r m =>
    Qualid ->
    (forall r m. LocalConvMonad r m => m a) ->
    m a
withCurrentDefinition newDef act = do
    global_edits <- view edits
    local_edits <- view (edits.inEdits.at newDef.non mempty)
    let edits_in_scope = global_edits <> local_edits

    _currentModule <- view currentModule
    withCounterT $ runReaderT act $ LocalEnv
        { _localEnvEdits             = edits_in_scope
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
