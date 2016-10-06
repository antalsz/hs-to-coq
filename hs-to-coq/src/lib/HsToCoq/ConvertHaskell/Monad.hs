{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             RankNTypes, ConstraintKinds, FlexibleContexts,
             TemplateHaskell #-}

module HsToCoq.ConvertHaskell.Monad (
  -- * Types
  ConversionMonad, evalConversion,
  -- * Types
  ConversionState(),
  renamings, constructors, constructorTypes, constructorFields, recordFieldTypes, defaultMethods, renamed,
  HsNamespace(..), NamespacedIdent(..), ConstructorFields(..),
  -- * Operations
  fresh, gensym, rename, localizeConversionState,
  -- * Unsupported features
  convUnsupported
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

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.InfixNames

--------------------------------------------------------------------------------

data HsNamespace = ExprNS | TypeNS
                 deriving (Eq, Ord, Show, Read, Enum, Bounded)

data NamespacedIdent = NamespacedIdent { niNS :: !HsNamespace
                                       , niId :: !Ident }
                     deriving (Eq, Ord, Show, Read)

data ConstructorFields = NonRecordFields !Int
                       | RecordFields    ![Ident]
                       deriving (Eq, Ord, Show, Read)

data ConversionState = ConversionState { _renamings         :: !(Map NamespacedIdent Ident)
                                       , _constructors      :: !(Map Ident [Ident])
                                       , _constructorTypes  :: !(Map Ident Ident)
                                       , _constructorFields :: !(Map Ident ConstructorFields)
                                       , _recordFieldTypes  :: !(Map Ident Ident)
                                       , _defaultMethods    :: !(Map Ident (Map Ident Term))
                                       , __unique           :: !Natural }
               deriving (Eq, Ord, Show)
makeLenses ''ConversionState
-- '_unique' is not exported

renamed :: HsNamespace -> Ident -> Lens' ConversionState (Maybe Ident)
renamed ns x = renamings.at (NamespacedIdent ns x)
{-# INLINABLE renamed #-}

type ConversionMonad m = (GhcMonad m, MonadState ConversionState m, MonadVariables Ident () m)

evalConversion :: GhcMonad m => StateT ConversionState (VariablesT Ident () m) a -> m a
evalConversion = evalVariablesT . (evalStateT ?? ConversionState{..}) where
  _renamings = M.fromList [ typ "()" ~> "unit" -- Probably unnecessary
                          , val "()" ~> "tt"
                           
                          , typ "[]" ~> "list"
                          , val "[]" ~> "nil"
                          , val ":"  ~> "::"
                           
                          , typ "Integer" ~> "Z"
                           
                          , typ "Bool"  ~> "bool"
                          , val "True"  ~> "true"
                          , val "False" ~> "false"
                           
                          , typ "String" ~> "string"
                           
                          , typ "Maybe"   ~> "option"
                          , val "Just"    ~> "Some"
                          , val "Nothing" ~> "None"
                           
                          , typ "FastString" ~> "string" ]
             
             where val  = NamespacedIdent ExprNS
                   typ  = NamespacedIdent TypeNS
                   (~>) = (,)

  _constructors      = M.empty -- TODO Add base types?
  
  _constructorTypes  = M.empty -- TODO Add base types?
  
  _constructorFields = M.empty -- TODO Add base types?
  
  _recordFieldTypes  = M.empty -- TODO Add base types?
  
  _defaultMethods = M.fromList ["Eq" ~>> [ "==" ~> Fun [arg "x", arg "y"] (App1 (Var "negb") $ Infix (Var "x") "/=" (Var "y"))
                                         , "/=" ~> Fun [arg "x", arg "y"] (App1 (Var "negb") $ Infix (Var "x") "==" (Var "y")) ]]
                  
                  where cl ~>> ms = (cl, M.fromList ms)
                        m  ~>  d  = (toCoqName m, d)
                        arg       = Inferred Coq.Explicit . Ident
  
  __unique = 0

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
localizeConversionState action = do
  ci <- get
  
  r <- action
  
  u <- use _unique
  put (ci & _unique .~ u)
      
  pure r

convUnsupported :: MonadIO m => String -> m a
convUnsupported what = liftIO . throwGhcExceptionIO . ProgramError $ what ++ " unsupported"
