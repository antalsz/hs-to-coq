{-# LANGUAGE RecordWildCards, OverloadedLists, OverloadedStrings #-}

module HsToCoq.ConvertHaskell.Axiomatize (axiomatizeBinding) where

import Data.Semigroup (Semigroup(..))
import qualified Data.Text as T

import Control.Monad.IO.Class

import GHC hiding (Name)
import Panic

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Variables

--------------------------------------------------------------------------------

axiomatizeBinding :: GhcMonad m => HsBind RdrName -> GhcException -> m [Sentence]
axiomatizeBinding FunBind{..} exn = do
  name <- freeVar $ unLoc fun_id
  pure [ CommentSentence . Comment
           $ "Translating `" <> name <> "' failed: " <> T.pack (show exn)
       , AssumptionSentence . Assumption Axiom . UnparenthesizedAssums [name]
           $ Forall [Typed Ungeneralizable Coq.Implicit [Ident "A"] $ Sort Type] (Var "A") ]
axiomatizeBinding _ exn =
  liftIO $ throwGhcExceptionIO exn
