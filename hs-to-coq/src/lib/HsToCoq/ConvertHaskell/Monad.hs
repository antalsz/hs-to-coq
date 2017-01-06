{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             RankNTypes, ConstraintKinds, FlexibleContexts,
             TemplateHaskell #-}

module HsToCoq.ConvertHaskell.Monad (
  -- * Types
  ConversionMonad, ConversionT, evalConversion,
  -- * Types
  ConversionState(),
  currentModule, renamings, edits, constructors, constructorTypes, constructorFields, recordFieldTypes, defaultMethods, renamed,
  ConstructorFields(..), _NonRecordFields, _RecordFields,
  -- * Operations
  maybeWithCurrentModule, withCurrentModule, withNoCurrentModule, withCurrentModuleOrNone,
  fresh, gensym,
  rename,
  localizeConversionState,
  -- * Errors
  throwProgramError, convUnsupported, editFailure
  ) where

import Control.Lens

import Data.Semigroup (Semigroup(..))
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural

import Control.Monad.State
import Control.Monad.Variables

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import GHC
import Panic
import HsToCoq.Util.GHC.Module ()

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.InfixNames
import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Parameters.Edits

--------------------------------------------------------------------------------

data ConstructorFields = NonRecordFields !Int
                       | RecordFields    ![Ident]
                       deriving (Eq, Ord, Show, Read)
makePrisms ''ConstructorFields

data ConversionState = ConversionState { __currentModule    :: !(Maybe ModuleName)
                                       , _renamings         :: !Renamings
                                       , _edits             :: !Edits
                                       , _constructors      :: !(Map Ident [Ident])
                                       , _constructorTypes  :: !(Map Ident Ident)
                                       , _constructorFields :: !(Map Ident ConstructorFields)
                                       , _recordFieldTypes  :: !(Map Ident Ident)
                                       , _defaultMethods    :: !(Map Ident (Map Ident Term))
                                       , __unique           :: !Natural }
               deriving (Eq, Ord, Show)
makeLenses ''ConversionState
-- '_currentModule' and '_unique' are not exported

currentModule :: Getter ConversionState (Maybe ModuleName)
currentModule = _currentModule
{-# INLINABLE currentModule #-}

renamed :: HsNamespace -> Ident -> Lens' ConversionState (Maybe Ident)
renamed ns x = renamings.at (NamespacedIdent ns x)
{-# INLINABLE renamed #-}

type ConversionMonad m = (GhcMonad m, MonadState ConversionState m, MonadVariables Ident () m)
type ConversionT m = StateT ConversionState (VariablesT Ident () m)

evalConversion :: GhcMonad m => Renamings -> Edits -> ConversionT m a -> m a
evalConversion _renamings _edits = evalVariablesT . (evalStateT ?? ConversionState{..}) where
  __currentModule = Nothing
  
  -- TODO Add base types?
  _constructors      = M.empty
  _constructorTypes  = M.empty
  _constructorFields = M.empty
  _recordFieldTypes  = M.empty
  
  _defaultMethods = M.fromList ["Eq" ~>> [ "==" ~> Fun [arg "x", arg "y"] (App1 (Var "negb") $ Infix (Var "x") "/=" (Var "y"))
                                         , "/=" ~> Fun [arg "x", arg "y"] (App1 (Var "negb") $ Infix (Var "x") "==" (Var "y")) ]]
                  
                  where cl ~>> ms = (cl, M.fromList ms)
                        m  ~>  d  = (toCoqName m, d)
                        arg       = Inferred Coq.Explicit . Ident
  
  __unique = 0

withCurrentModuleOrNone :: ConversionMonad m => Maybe ModuleName -> m a -> m a
withCurrentModuleOrNone newModule = gbracket (_currentModule <.= newModule)
                                             (_currentModule  .=)
                                  . const

withNoCurrentModule :: ConversionMonad m => m a -> m a
withNoCurrentModule = withCurrentModuleOrNone Nothing

withCurrentModule :: ConversionMonad m => ModuleName -> m a -> m a
withCurrentModule = withCurrentModuleOrNone . Just

maybeWithCurrentModule :: ConversionMonad m => Maybe ModuleName -> m a -> m a
maybeWithCurrentModule = maybe id withCurrentModule

fresh :: ConversionMonad m => m Natural
fresh = _unique <<+= 1

gensym :: ConversionMonad m => Text -> m Ident
gensym name = do u <- fresh
                 pure $ "__" <> name <> "_" <> T.pack (show u) <> "__"

-- Mostly for point-free use these days
rename :: ConversionMonad m => HsNamespace -> Ident -> Ident -> m ()
rename ns x x' = renamed ns x ?= x'
{-# INLINABLE rename #-}

localizeConversionState :: ConversionMonad m => m a -> m a
localizeConversionState = gbracket get
                                   (\cs -> do u <- use _unique
                                              put $ cs & _unique .~ u)
                        . const

throwProgramError :: MonadIO m => String -> m a
throwProgramError = liftIO . throwGhcExceptionIO . ProgramError

convUnsupported :: MonadIO m => String -> m a
convUnsupported what = throwProgramError $ what ++ " unsupported"

editFailure :: MonadIO m => String -> m a
editFailure what = throwProgramError $ "Could not apply edit: " ++ what
