{-# LANGUAGE RecordWildCards, OverloadedStrings, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Pattern (convertPat,  convertLPat) where

import Data.List.NonEmpty (nonEmpty)
import qualified Data.Text as T

import GHC hiding (Name)
import BasicTypes
import HsToCoq.Util.GHC.FastString

import HsToCoq.Util.GHC.HsExpr
import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Literals

--------------------------------------------------------------------------------

convertPat :: ConversionMonad m => Pat RdrName -> m Pattern
convertPat (WildPat PlaceHolder) =
  pure UnderscorePat

convertPat (GHC.VarPat x) =
  CoqVarPat <$> freeVar x

convertPat (LazyPat p) =
  convertLPat p

convertPat (GHC.AsPat x p) =
  Coq.AsPat <$> convertLPat p <*> freeVar (unLoc x)

convertPat (ParPat p) =
  convertLPat p

convertPat (BangPat p) =
  convertLPat p

convertPat (ListPat pats PlaceHolder overloaded) =
  if maybe True (isNoSyntaxExpr . snd) overloaded
  then foldr (flip InfixPat "::") (CoqVarPat "nil") <$> traverse convertLPat pats
  else convUnsupported "overloaded list patterns"

convertPat (TuplePat pats boxity _PlaceHolders) =
  case boxity of
    Boxed   -> foldl1 (App2Pat $ Bare "pair") <$> traverse convertLPat pats
    Unboxed -> convUnsupported "unboxed tuple patterns"

convertPat (PArrPat _ _) =
  convUnsupported "parallel array patterns"

convertPat (ConPatIn con conVariety) =
  case conVariety of
    PrefixCon args' -> do
      conVar <- Bare <$> var ExprNS (unLoc con)
      case nonEmpty args' of
        Just args -> ArgsPat conVar <$> traverse convertLPat args
        Nothing   -> pure $ QualidPat conVar
    RecCon _    ->
      convUnsupported "record constructor patterns"
    InfixCon l r  ->
      InfixPat <$> convertLPat l <*> var ExprNS (unLoc con) <*> convertLPat r

convertPat (ConPatOut{}) =
  convUnsupported "[internal?] `ConPatOut' constructor"

convertPat (ViewPat _ _ _) =
  convUnsupported "view patterns"

convertPat (SplicePat _) =
  convUnsupported "pattern splices"

convertPat (QuasiQuotePat _) =
  convUnsupported "pattern quasiquoters"

convertPat (LitPat lit) =
  case lit of
    HsChar       _ c       -> pure $ InScopePat (StringPat $ T.singleton c) "char"
    HsCharPrim   _ _       -> convUnsupported "`Char#' literal patterns"
    HsString     _ fs      -> pure . StringPat $ fsToText fs
    HsStringPrim _ _       -> convUnsupported "`Addr#' literal patterns"
    HsInt        _ _       -> convUnsupported "`Int' literal patterns"
    HsIntPrim    _ _       -> convUnsupported "`Int#' literal patterns"
    HsWordPrim   _ _       -> convUnsupported "`Word#' literal patterns"
    HsInt64Prim  _ _       -> convUnsupported "`Int64#' literal patterns"
    HsWord64Prim _ _       -> convUnsupported "`Word64#' literal patterns"
    HsInteger    _ int _ty -> NumPat <$> convertInteger "`Integer' literal patterns" int
    HsRat        _ _       -> convUnsupported "`Rational' literal patterns"
    HsFloatPrim  _         -> convUnsupported "`Float#' literal patterns"
    HsDoublePrim _         -> convUnsupported "`Double#' literal patterns"

convertPat (NPat (L _ OverLit{..}) _negate _eq) = -- And strings
  case ol_val of
    HsIntegral   _src int -> NumPat <$> convertInteger "integer literal patterns" int
    HsFractional _        -> convUnsupported "fractional literal patterns"
    HsIsString   _src str -> pure . StringPat $ fsToText str

convertPat (NPlusKPat _ _ _ _) =
  convUnsupported "n+k-patterns"

convertPat (SigPatIn _ _) =
  convUnsupported "`SigPatIn' constructor"

convertPat (SigPatOut _ _) =
  convUnsupported "`SigPatOut' constructor"

convertPat (CoPat _ _ _) =
  convUnsupported "coercion patterns"

--------------------------------------------------------------------------------

convertLPat :: ConversionMonad m => LPat RdrName -> m Pattern
convertLPat = convertPat . unLoc
