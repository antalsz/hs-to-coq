{-# LANGUAGE TemplateHaskell, RecordWildCards, FlexibleContexts, MultiParamTypeClasses, MultiWayIf, OverloadedLists #-}

module HsToCoq.ConvertHaskell.Definitions (
  ConvertedDefinition(..), convDefName, convDefArgs, convDefType, convDefBody,
  ConvertedBinding(..),
  toProgramFixpointSentence
  ) where

import Control.Lens

import Data.Maybe
import Data.Either
import Data.List.NonEmpty (NonEmpty(..))
import HsToCoq.Util.List

import HsToCoq.Coq.Gallina
import HsToCoq.Coq.Gallina.UseTypeInBinders
import HsToCoq.Util.FVs

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Parameters.Edits

--------------------------------------------------------------------------------

data ConvertedDefinition = ConvertedDefinition { _convDefName :: !Qualid
                                               , _convDefArgs :: ![Binder]
                                               , _convDefType :: !(Maybe Term)
                                               , _convDefBody :: !Term
                                               }
                         deriving (Eq, Ord, Show, Read)
makeLenses ''ConvertedDefinition

instance HasBV Qualid ConvertedDefinition where
  bvOf cd =  binder (cd^.convDefName)
          <> bindsNothing (foldScopes bvOf (cd^.convDefArgs)
                             $ fvOf (cd^.convDefType) <> fvOf (cd^.convDefBody))

--------------------------------------------------------------------------------

data ConvertedBinding = ConvertedDefinitionBinding ConvertedDefinition
                      | ConvertedPatternBinding    Pattern Term
                      | ConvertedAxiomBinding      Qualid Term
                      | RedefinedBinding           Qualid CoqDefinition
                      | SkippedBinding             Qualid
                      deriving (Eq, Ord, Show, Read)

-- TODO: We /really/ need a better story for pattern bindings
instance HasBV Qualid ConvertedBinding where
  bvOf (ConvertedDefinitionBinding  cdf) = bvOf cdf
  bvOf (ConvertedPatternBinding pat def) = bvOf   pat `telescope` fvOf' def
  bvOf (ConvertedAxiomBinding   axm typ) = binder axm `telescope` fvOf' typ
  bvOf (RedefinedBinding        rnm def) = binder rnm `telescope` bvOf  def
  bvOf (SkippedBinding nam) = binder nam

decomposeFixpoint :: Term -> Maybe (Qualid, Binders, Maybe Term, Term)
decomposeFixpoint (Fix (FixOne (FixBody name binders _ mty body)))
    = Just (name, binders, mty, body)
-- This undoes what wfFix does
-- This is a bit of code smell; I should refactor this that the termination
-- argument is part of the “Gallina” AST, and the concrete representation
-- is created by the pretty-printer
decomposeFixpoint (App _wfFix [PosArg _rel, PosArg _measure, PosArg _underscore, PosArg (Fun binders body)])
    | (b:bs, ExplicitBinder (Ident name)) <- unsnocNEL binders
    = Just (name, b :| bs, Nothing, body)
decomposeFixpoint _
    = Nothing

toProgramFixpointSentence ::
    ConversionMonad r m =>
    ConvertedDefinition -> Order -> Maybe Tactics -> m Sentence
toProgramFixpointSentence (ConvertedDefinition{..}) order tac
    | Nothing <- _convDefType
    = editFailure "cannot \"termination\" a definition without a type signature"
    | Just cty <- _convDefType
    , Just (name, binders, mty, body) <- decomposeFixpoint _convDefBody
    = if name /= _convDefName
      then editFailure "internal name and external name disagree?"
      else let ty = fromMaybe (fromRight cty $ fst <$> useTypeInBinders' cty binders) mty
                      -- Priority list:
                      --   (1) decomposed type;
                      --   (2) stripped converted type (the binders should already have been handled);
                      --   (3) full converted type
           in pure $ ProgramSentence
                       (FixpointSentence $ Fixpoint
                          [FixBody name (_convDefArgs <++ binders) (Just order) (Just ty) body]
                          [])
                       tac
    | otherwise
    = editFailure "cannot \"termination\" a definition that is not a recursive function"
