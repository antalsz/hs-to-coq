{-# LANGUAGE RecordWildCards, FlexibleContexts, MultiWayIf, OverloadedLists #-}

module HsToCoq.ConvertHaskell.Definitions (
  ConvertedDefinition(..),
  ConvertedBinding(..), withConvertedBinding,
  toProgramFixpointSentence
  ) where

import HsToCoq.Coq.Gallina

import Data.List.NonEmpty (NonEmpty(..), (<|), toList)

import Data.Bifunctor
import HsToCoq.ConvertHaskell.Monad

--------------------------------------------------------------------------------

data ConvertedDefinition = ConvertedDefinition { convDefName  :: !Qualid
                                               , convDefArgs  :: ![Binder]
                                               , convDefType  :: !(Maybe Term)
                                               , convDefBody  :: !Term
                                               }
                         deriving (Eq, Ord, Show, Read)

--------------------------------------------------------------------------------

data ConvertedBinding = ConvertedDefinitionBinding ConvertedDefinition
                      | ConvertedPatternBinding    Pattern Term
                      deriving (Eq, Ord, Show, Read)

withConvertedBinding :: (ConvertedDefinition -> a) -> (Pattern -> Term -> a) -> ConvertedBinding -> a
withConvertedBinding  withDef _withPat (ConvertedDefinitionBinding cdef)    = withDef cdef
withConvertedBinding _withDef  withPat (ConvertedPatternBinding    pat def) = withPat pat def

decomposeFixpoint :: Term -> Maybe (Qualid, Binders, Term)
decomposeFixpoint (Fix (FixOne (FixBody name binders _ _ body)))
    = Just (name, binders, body)
-- This undoes what wfFix does
-- This is a bit of code smell; I should refactor this that the termination
-- argument is part of the “Gallina” AST, and the concrete representation
-- is created by the pretty-printer
decomposeFixpoint (App _wfFix [PosArg _rel, PosArg _measure, PosArg _underscore, PosArg (Fun binders body)])
    | (b:bs) <- init $ toList binders
    , Inferred Explicit (Ident name) <- last $ toList binders
    = Just (name, b :| bs, body)
decomposeFixpoint _
    = Nothing


toProgramFixpointSentence ::
    ConversionMonad r m =>
    ConvertedDefinition -> Order -> Maybe Tactics -> m Sentence
toProgramFixpointSentence (ConvertedDefinition{..}) order tac
    | Nothing <- convDefType
    = editFailure "cannot \"termination\" a definition without a type signature"
    | Just ty <- convDefType
    , Just (name, binders, body) <- decomposeFixpoint convDefBody
    = if | name /= convDefName
         -> editFailure "internal name and external name disagree?"
         | otherwise
         -> do
            (binders', ty') <- moveTyToArgs binders ty
            pure $ ProgramSentence
                (FixpointSentence (Fixpoint [FixBody name (foldr (<|) binders' convDefArgs) (Just order) (Just ty') body] []))
                tac
    | otherwise
    = editFailure "cannot \"termination\" a definition that is not a recursive function"
  where
    moveTyToArgs :: ConversionMonad r m => NonEmpty Binder -> Term -> m (NonEmpty Binder, Term)
        -- Base case
    moveTyToArgs' [] ty = pure ([], ty)

        -- Helper to get avoid [a] vs. NonEmpty confusion
    moveTyToArgs' (x:xs) ty = first toList <$> moveTyToArgs (x :| xs) ty

        -- Good case
    moveTyToArgs (Inferred exp n :| binders) (Arrow at ty)
        = first (Typed Ungeneralizable exp [n] at :|) <$> moveTyToArgs' binders ty
        -- Error cases
    moveTyToArgs (binder :| _) (Arrow _ _)
        = editFailure $ "cannot handle binder to fix of form " ++ show binder
    moveTyToArgs (_ :| _) ty
        = editFailure $ "cannot peel off argument type off " ++ show ty


