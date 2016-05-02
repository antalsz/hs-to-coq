{-# LANGUAGE LambdaCase, RecordWildCards, OverloadedStrings, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Pattern (convertPat,  convertLPat) where

import Control.Lens

import Data.Semigroup (Semigroup(..))
import Data.Maybe
import Data.Traversable
import qualified Data.Text as T

import qualified Data.Map.Strict as M

import GHC hiding (Name)
import BasicTypes
import HsToCoq.Util.GHC.FastString

import HsToCoq.Util.GHC.HsExpr
import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util as Coq

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Literals

--------------------------------------------------------------------------------

convertPat :: ConversionMonad m => Pat RdrName -> m Pattern
convertPat (WildPat PlaceHolder) =
  pure UnderscorePat

convertPat (GHC.VarPat x) =
  Coq.VarPat <$> freeVar x

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
  then foldr (InfixPat ?? "::") (Coq.VarPat "nil") <$> traverse convertLPat pats
  else convUnsupported "overloaded list patterns"

convertPat (TuplePat pats boxity _PlaceHolders) =
  case boxity of
    Boxed   -> foldl1 (App2Pat $ Bare "pair") <$> traverse convertLPat pats
    Unboxed -> convUnsupported "unboxed tuple patterns"

convertPat (PArrPat _ _) =
  convUnsupported "parallel array patterns"

convertPat (ConPatIn (L _ hsCon) conVariety) = do
  con <- var ExprNS hsCon
  
  case conVariety of
    PrefixCon args ->
      appListPat (Bare con) <$> traverse convertLPat args
    
    RecCon HsRecFields{..} ->
      use (recordFields . at con) >>= \case
        Just fields -> do
          patterns <- fmap M.fromList . for rec_flds $ \(L _ (HsRecField (L _ hsField) hsPat pun)) -> do
                        field <- var ExprNS hsField
                        pat   <- if pun
                                 then pure $ Coq.VarPat field
                                 else convertLPat hsPat
                        pure (field, pat)
          
          let defaultPat field | isJust rec_dotdot = Coq.VarPat field
                               | otherwise         = UnderscorePat
          
          pure . appListPat (Bare con)
             $ map (\field -> M.findWithDefault (defaultPat field) field patterns) fields
        
        Nothing     ->
          convUnsupported $ "pattern-matching on unknown record constructor `" <> T.unpack con <> "'"
    
    InfixCon l r ->
      InfixPat <$> convertLPat l <*> pure con <*> convertLPat r

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
