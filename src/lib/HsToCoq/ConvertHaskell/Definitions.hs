{-# LANGUAGE TemplateHaskell, RecordWildCards, FlexibleContexts, MultiParamTypeClasses, MultiWayIf, OverloadedLists #-}

module HsToCoq.ConvertHaskell.Definitions (
  ConvertedDefinition(..), convDefName, convDefArgs, convDefType, convDefBody,
  ConvertedBinding(..), withConvertedBinding,
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
                      deriving (Eq, Ord, Show, Read)

withConvertedBinding :: (ConvertedDefinition -> a)
                     -> (Pattern -> Term -> a)
                     -> (Qualid -> Term -> a)
                     -> (Qualid -> CoqDefinition -> a)
                     -> ConvertedBinding -> a
withConvertedBinding  withDef _withPat _withAxm _withRdf (ConvertedDefinitionBinding cdf)     = withDef cdf
withConvertedBinding _withDef  withPat _withAxm _withRdf (ConvertedPatternBinding    pat def) = withPat pat def
withConvertedBinding _withDef _withPat  withAxm _withRdf (ConvertedAxiomBinding      axm typ) = withAxm axm typ
withConvertedBinding _withDef _withPat _withAxm  withRdf (RedefinedBinding           rnm def) = withRdf rnm def

-- TODO: We /really/ need a better story for pattern bindings
instance HasBV Qualid ConvertedBinding where
  bvOf = withConvertedBinding bvOf
                              (\pat def -> bvOf   pat `telescope` fvOf' def)
                              (\axm typ -> binder axm `telescope` fvOf' typ)
                              (\rnm def -> binder rnm `telescope` bvOf  def)

decomposeFixpoint :: Term -> Maybe (Qualid, Binders, Maybe Term, Term)
decomposeFixpoint (Fix (FixOne (FixBody name binders _ mty body)))
    = Just (name, binders, mty, body)
-- This undoes what wfFix does
-- This is a bit of code smell; I should refactor this that the termination
-- argument is part of the “Gallina” AST, and the concrete representation
-- is created by the pretty-printer
decomposeFixpoint (App _wfFix [PosArg _rel, PosArg _measure, PosArg _underscore, PosArg (Fun binders body)])
    | (b:bs, Inferred Explicit (Ident name)) <- unsnocNEL binders
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
