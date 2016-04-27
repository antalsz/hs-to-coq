{-# LANGUAGE TupleSections, LambdaCase,
             OverloadedStrings,
             ConstraintKinds, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Monad (
  -- * Types
  ConversionMonad, Renaming, HsNamespace(..), evalConversion,
  -- * Operations
  rename, localRenamings,
  -- * Unsupported features
  convUnsupported
  ) where

import Control.Monad.State
import Control.Monad.Variables

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import GHC
import Panic

import HsToCoq.Coq.Gallina

--------------------------------------------------------------------------------

data HsNamespace = ExprNS | TypeNS
                 deriving (Eq, Ord, Show, Read, Enum, Bounded)

type Renaming = Map HsNamespace Ident

type ConversionMonad m = (GhcMonad m, MonadState (Map Ident Renaming) m, MonadVariables Ident () m)

evalConversion :: GhcMonad m => StateT (Map Ident Renaming) (VariablesT Ident () m) a -> m a
evalConversion conv = evalVariablesT . evalStateT conv $ build
                        [ typ "()" ~> "unit" -- Probably unnecessary
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
  where
    val hs = (hs,) . M.singleton ExprNS
    typ hs = (hs,) . M.singleton TypeNS
    (~>)   = ($)

    build = M.fromListWith M.union

rename :: ConversionMonad m => HsNamespace -> Ident -> Ident -> m ()
rename ns x x' = modify' . flip M.alter x $ Just . \case
                   Just m  -> M.insert    ns x' m
                   Nothing -> M.singleton ns x'

localRenamings :: ConversionMonad m => m a -> m a
localRenamings action = get >>= ((action <*) . put)

convUnsupported :: MonadIO m => String -> m a
convUnsupported what = liftIO . throwGhcExceptionIO . ProgramError $ what ++ " unsupported"
