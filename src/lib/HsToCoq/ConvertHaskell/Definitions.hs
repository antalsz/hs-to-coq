{-# LANGUAGE RecordWildCards, FlexibleContexts, MultiWayIf, OverloadedLists #-}

module HsToCoq.ConvertHaskell.Definitions (
  ConvertedDefinition(..),
  ConvertedBinding(..), withConvertedBinding,
  toProgramFixpointSentence
  ) where

import HsToCoq.Coq.Gallina

import Data.List.NonEmpty (toList )

import Data.Bifunctor
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Parameters.Edits (TerminationArgument(..))


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

toProgramFixpointSentence ::
    ConversionMonad m =>
    ConvertedDefinition -> TerminationArgument -> m Sentence
toProgramFixpointSentence (ConvertedDefinition{..}) (TerminationArgument order tac)
    | Nothing <- convDefType
    = editFailure "cannot \"termination\" a definition without a type signature"
    | Just ty <- convDefType
    , Fix (FixOne (FixBody name binders _ _ body)) <- convDefBody
    = if | name /= convDefName
         -> editFailure "internal name and external name disagree?"
         | otherwise
         -> do
            (binders', ty') <- moveTyToArgs (toList binders) ty
            pure $ ProgramFixpointSentence (ProgramFixpoint name (convDefArgs ++ binders') order ty' body) tac
    | otherwise
    = editFailure "cannot \"termination\" a definition that is not a recursive function"
  where
    moveTyToArgs :: ConversionMonad m => [Binder] -> Term -> m ([Binder], Term)
        -- Base case
    moveTyToArgs [] ty = pure ([], ty)
        -- Good case
    moveTyToArgs (Inferred exp n : binders) (Arrow at ty)
        = first (Typed Ungeneralizable exp [n] at :) <$> moveTyToArgs binders ty
        -- Error cases
    moveTyToArgs (binder : _) (Arrow _ _)
        = editFailure $ "cannot handle binder to fix of form " ++ show binder
    moveTyToArgs (_ : _) ty
        = editFailure $ "cannot peel off argument type off " ++ show ty


