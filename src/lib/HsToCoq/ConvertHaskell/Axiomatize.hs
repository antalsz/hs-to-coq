{-# LANGUAGE RecordWildCards, OverloadedLists, OverloadedStrings, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Axiomatize (
  translationFailedComment, translationFailedCommentText,
  axiom, typedAxiom, bottomType,
  axiomatizeBinding
) where

import HsToCoq.Util.Functor
import Data.Semigroup (Semigroup(..))
import Data.Text (Text)
import qualified Data.Text as T

import GHC hiding (Name)

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Parameters.Edits

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

axiomatizeBinding :: ConversionMonad r m => HsBind GhcRn -> GhcException -> m (Maybe Qualid, [Sentence])
axiomatizeBinding FunBind{..} exn = do
  name <- var ExprNS (unLoc fun_id)
  pure (Just name, [translationFailedComment (qualidBase name) exn, axiom name])
axiomatizeBinding _ exn =
  pure (Nothing, [CommentSentence $ Comment $
    "While translating non-function binding: " <> T.pack (show exn)])
