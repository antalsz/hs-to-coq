{-# LANGUAGE OverloadedLists, OverloadedStrings #-}

module HsToCoq.ConvertHaskell.Axiomatize (
  translationFailedComment, translationFailedCommentText,
  axiom, typedAxiom, bottomType,
) where

import HsToCoq.Util.Functor
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

typedAxiom :: Qualid -> Term -> Sentence
typedAxiom name term =
    AssumptionSentence (Assumption Axiom (Assums [name] term))

bottomType :: Term
bottomType = Forall [Typed Ungeneralizable Coq.Implicit [Ident (Bare "A")] $ Sort Type] (Var "A")

axiom :: Qualid -> Sentence
axiom = typedAxiom ?? bottomType
