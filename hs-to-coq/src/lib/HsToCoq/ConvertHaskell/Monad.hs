{-# LANGUAGE TupleSections, LambdaCase, RecordWildCards,
             OverloadedLists, OverloadedStrings,
             RankNTypes, ConstraintKinds, FlexibleContexts,
             TemplateHaskell #-}

module HsToCoq.ConvertHaskell.Monad (
  -- * Types
  ConversionMonad, evalConversion,
  NameInfos(..), renamings, nonterminating, defaultMethods, renaming,
  HsNamespace(..), NamespacedIdent(..),
  -- * Operations
  rename, localRenamings,
  -- * Unsupported features
  convUnsupported
  ) where

import Control.Lens

import Control.Monad.State
import Control.Monad.Variables

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Set (Set)

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

data NameInfos = NameInfos { _renamings      :: !(Map NamespacedIdent Ident)
                           , _nonterminating :: !(Set Ident)
                           , _defaultMethods :: !(Map Ident (Map Ident Term)) }
               deriving (Eq, Ord, Show, Read)
makeLenses ''NameInfos

renaming :: HsNamespace -> Ident -> Lens' NameInfos (Maybe Ident)
renaming ns x = renamings.at (NamespacedIdent ns x)
{-# INLINABLE renaming #-}

type ConversionMonad m = (GhcMonad m, MonadState NameInfos m, MonadVariables Ident () m)

evalConversion :: GhcMonad m => StateT NameInfos (VariablesT Ident () m) a -> m a
evalConversion = evalVariablesT . (evalStateT ?? NameInfos{..}) where
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
                          , val "Nothing" ~> "None" ]
             
             where val  = NamespacedIdent ExprNS
                   typ  = NamespacedIdent TypeNS
                   (~>) = (,)

  _nonterminating = ["error", "undefined", "panic"]
  
  _defaultMethods = M.fromList ["Eq" ~>> [ "==" ~> Fun [arg "x", arg "y"] (App1 (Var "negb") $ Infix (Var "x") "/=" (Var "y"))
                                         , "/=" ~> Fun [arg "x", arg "y"] (App1 (Var "negb") $ Infix (Var "x") "==" (Var "y")) ]]
                  
                  where cl ~>> ms = (cl, M.fromList ms)
                        m  ~>  d  = (toCoqName m, d)
                        arg       = Inferred Coq.Explicit . Ident

rename :: ConversionMonad m => HsNamespace -> Ident -> Ident -> m ()
rename ns x x' = renaming ns x ?= x'
{-# INLINABLE rename #-}

localRenamings :: ConversionMonad m => m a -> m a
localRenamings action = get >>= ((action <*) . put)

convUnsupported :: MonadIO m => String -> m a
convUnsupported what = liftIO . throwGhcExceptionIO . ProgramError $ what ++ " unsupported"
