{-# LANGUAGE OverloadedLists, OverloadedStrings #-}

module HsToCoq.ConvertHaskell.Axiomatize (
  translationFailedComment, translationFailedCommentText,
  axiom) where

import Data.Semigroup (Semigroup(..))
import Data.Text (Text)
import qualified Data.Text as T

import GHC hiding (Name)

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

--------------------------------------------------------------------------------

translationFailedCommentText :: Text -> GhcException -> Text
translationFailedCommentText what exn =
  "Translating `" <> what <> "' failed: " <> T.pack (show exn)

translationFailedComment :: Text -> GhcException -> Sentence
translationFailedComment what exn = CommentSentence . Comment $ translationFailedCommentText what exn

axiom :: Ident -> Sentence
axiom name = AssumptionSentence . Assumption Axiom . UnparenthesizedAssums [name]
           $ Forall [Typed Ungeneralizable Coq.Implicit [Ident "A"] $ Sort Type] (Var "A")
