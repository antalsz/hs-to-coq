{-# LANGUAGE RecordWildCards, FlexibleContexts, MultiWayIf, OverloadedLists #-}

module HsToCoq.ConvertHaskell.Definitions (
  ConvertedDefinition(..), withConvertedDefinition, withConvertedDefinitionDef, withConvertedDefinitionOp,
  ConvertedBinding(..), withConvertedBinding,
  toProgramFixpointSentence
  ) where

import HsToCoq.Util.Functor
import HsToCoq.Coq.Gallina

import Data.List.NonEmpty (toList )

import Data.Text (Text)
import Data.Bifunctor
import HsToCoq.ConvertHaskell.Monad


--------------------------------------------------------------------------------

data ConvertedDefinition = ConvertedDefinition { convDefName  :: !Ident
                                               , convDefArgs  :: ![Binder]
                                               , convDefType  :: !(Maybe Term)
                                               , convDefBody  :: !Term
                                               , convDefInfix :: !(Maybe Op) }
                         deriving (Eq, Ord, Show, Read)

withConvertedDefinition :: Monoid m
                        => (Ident -> [Binder] -> Maybe Term -> Term -> a) -> (a -> m)
                        -> (Op -> Ident -> b)                             -> (b -> m)
                        -> (ConvertedDefinition -> m)
withConvertedDefinition withDef wrapDef withOp wrapOp ConvertedDefinition{..} =
  mappend (wrapDef $ withDef convDefName convDefArgs convDefType convDefBody)
          (maybe mempty (wrapOp . flip withOp convDefName) convDefInfix)

withConvertedDefinitionDef :: (Ident -> [Binder] -> Maybe Term -> Term -> a) -> (ConvertedDefinition -> a)
withConvertedDefinitionDef f ConvertedDefinition{..} = f convDefName convDefArgs convDefType convDefBody

withConvertedDefinitionOp :: (Op -> Ident -> a) -> (ConvertedDefinition -> Maybe a)
withConvertedDefinitionOp f ConvertedDefinition{..} = (f ?? convDefName) <$> convDefInfix

--------------------------------------------------------------------------------

data ConvertedBinding = ConvertedDefinitionBinding ConvertedDefinition
                      | ConvertedPatternBinding    Pattern Term
                      deriving (Eq, Ord, Show, Read)

withConvertedBinding :: (ConvertedDefinition -> a) -> (Pattern -> Term -> a) -> ConvertedBinding -> a
withConvertedBinding  withDef _withPat (ConvertedDefinitionBinding cdef)    = withDef cdef
withConvertedBinding _withDef  withPat (ConvertedPatternBinding    pat def) = withPat pat def

toProgramFixpointSentence ::
    ConversionMonad m =>
    ConvertedDefinition -> Order -> Maybe Text -> m Sentence
toProgramFixpointSentence (ConvertedDefinition{..}) order tac
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


