{-# LANGUAGE LambdaCase, RecordWildCards, OverloadedStrings, OverloadedLists, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Pattern (
  convertPat,  convertLPat,
  -- * Utility
  Refutability(..), refutability, isSoleConstructor
) where

import Control.Lens hiding ((<|))

import Data.Maybe
import Data.Traversable
import Data.List.NonEmpty (NonEmpty(), (<|))
import qualified Data.Text as T

import Control.Monad.Trans.Maybe

import qualified Data.Map.Strict as M

import GHC hiding (Name, HsChar, HsString)
import qualified GHC
import HsToCoq.Util.GHC.FastString

import HsToCoq.Util.GHC
import HsToCoq.Util.GHC.HsExpr
import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util as Coq

import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables

--------------------------------------------------------------------------------

convertPat :: ConversionMonad m => Pat RdrName -> m Pattern
convertPat (WildPat PlaceHolder) =
  pure UnderscorePat

convertPat (GHC.VarPat (L _ x)) =
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

-- TODO: Mark converted unboxed tuples specially?
convertPat (TuplePat pats _boxity _PlaceHolders) =
  foldl1 (App2Pat $ Bare "pair") <$> traverse convertLPat pats

convertPat (PArrPat _ _) =
  convUnsupported "parallel array patterns"

convertPat (ConPatIn (L _ hsCon) conVariety) = do
  con <- var ExprNS hsCon
  
  case conVariety of
    PrefixCon args ->
      appListPat (Bare con) <$> traverse convertLPat args
    
    RecCon HsRecFields{..} ->
      let recPatUnsupported what = do
            hsConStr <- ghcPpr hsCon
            convUnsupported $  "using a record pattern for the "
                            ++ what ++ " constructor `" ++ T.unpack hsConStr ++ "'"
      
      in use (constructorFields . at con) >>= \case
           Just (RecordFields conFields) -> do
             let defaultPat field | isJust rec_dotdot = Coq.VarPat field
                                  | otherwise         = UnderscorePat
             
             patterns <- fmap M.fromList . for rec_flds $ \(L _ (HsRecField (L _ (FieldOcc (L _ hsField) _)) hsPat pun)) -> do
                           field <- var ExprNS hsField
                           pat   <- if pun
                                    then pure $ Coq.VarPat field
                                    else convertLPat hsPat
                           pure (field, pat)
             pure . appListPat (Bare con)
                  $ map (\field -> M.findWithDefault (defaultPat field) field patterns) conFields
           
           Just (NonRecordFields count)
             | null rec_flds && isNothing rec_dotdot ->
               pure . appListPat (Bare con) $ replicate count UnderscorePat
             
             | otherwise ->
               recPatUnsupported "non-record"
           
           Nothing -> recPatUnsupported "unknown"
    
    InfixCon l r ->
      InfixPat <$> convertLPat l <*> pure con <*> convertLPat r

convertPat (ConPatOut{}) =
  convUnsupported "[internal?] `ConPatOut' constructor"

convertPat (ViewPat _ _ _) =
  convUnsupported "view patterns"

convertPat (SplicePat _) =
  convUnsupported "pattern splices"

convertPat (LitPat lit) =
  case lit of
    GHC.HsChar   _ c       -> pure $ InScopePat (StringPat $ T.singleton c) "char"
    HsCharPrim   _ _       -> convUnsupported "`Char#' literal patterns"
    GHC.HsString _ fs      -> pure . StringPat $ fsToText fs
    HsStringPrim _ _       -> convUnsupported "`Addr#' literal patterns"
    HsInt        _ _       -> convUnsupported "`Int' literal patterns"
    HsIntPrim    _ _       -> convUnsupported "`Int#' literal patterns"
    HsWordPrim   _ _       -> convUnsupported "`Word#' literal patterns"
    HsInt64Prim  _ _       -> convUnsupported "`Int64#' literal patterns"
    HsWord64Prim _ _       -> convUnsupported "`Word64#' literal patterns"
    HsInteger    _ _int _ty -> convUnsupported "`Integer' literal patterns"
                              -- NumPat <$> convertInteger "`Integer' literal patterns" int
    HsRat        _ _       -> convUnsupported "`Rational' literal patterns"
    HsFloatPrim  _         -> convUnsupported "`Float#' literal patterns"
    HsDoublePrim _         -> convUnsupported "`Double#' literal patterns"

convertPat (NPat (L _ OverLit{..}) _negate _eq PlaceHolder) = -- And strings
  case ol_val of
    HsIntegral   _src _int -> convUnsupported "integer literal patterns"
                              -- NumPat <$> convertInteger "integer literal patterns" int
    HsFractional _        -> convUnsupported "fractional literal patterns"
    HsIsString   _src str -> pure . StringPat $ fsToText str

convertPat (NPlusKPat _ _ _ _ _ _) =
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

--------------------------------------------------------------------------------

-- Nothing:    Not a constructor
-- Just True:  Sole constructor
-- Just False: One of many constructors
isSoleConstructor :: ConversionMonad m => Ident -> m (Maybe Bool)
isSoleConstructor con = runMaybeT $ do
  ty    <- MaybeT . use $ constructorTypes . at con
  ctors <-          use $ constructors     . at ty
  pure $ length (fromMaybe [] ctors) == 1

data Refutability = Trivial (Maybe Ident) -- Variables (with `Just`), underscore (with `Nothing`)
                  | SoleConstructor       -- (), (x,y)
                  | Refutable             -- Nothing, Right x, (3,_)
                  deriving (Eq, Ord, Show, Read)

-- Module-local
constructor_refutability :: ConversionMonad m => Qualid -> NonEmpty Pattern -> m Refutability
constructor_refutability con args =
  isSoleConstructor (qualidToIdent con) >>= \case
    Nothing    -> pure Refutable -- Error
    Just True  -> maximum . (SoleConstructor <|) <$> traverse refutability args
    Just False -> pure Refutable

refutability :: ConversionMonad m => Pattern -> m Refutability
refutability (ArgsPat con args)         = constructor_refutability con args
refutability (ExplicitArgsPat con args) = constructor_refutability con args
refutability (InfixPat arg1 con arg2)   = constructor_refutability (Bare con) [arg1,arg2]
refutability (Coq.AsPat pat _)          = refutability pat
refutability (InScopePat _ _)           = pure Refutable -- TODO: Handle scopes
refutability (QualidPat qid)            = let name = qualidToIdent qid
                                          in isSoleConstructor name <&> \case
                                               Nothing    -> Trivial $ Just name
                                               Just True  -> SoleConstructor
                                               Just False -> Refutable
refutability UnderscorePat              = pure $ Trivial Nothing
refutability (NumPat _)                 = pure Refutable
refutability (StringPat _)              = pure Refutable
refutability (OrPats _)                 = pure Refutable -- TODO: Handle or-patterns?
