{-# LANGUAGE LambdaCase,
             OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Type (convertType, convertLType, convertLHsTyVarBndrs, convertLHsSigType, convertLHsSigWcType) where

import Control.Lens

import Data.Traversable
import Data.List.NonEmpty (nonEmpty)

import GHC hiding (Name)
import qualified GHC as GHC
import HsToCoq.Util.GHC.FastString

import HsToCoq.Util.GHC
import HsToCoq.Util.GHC.HsTypes
import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Literals

--------------------------------------------------------------------------------

convertLHsTyVarBndrs :: ConversionMonad m => Explicitness -> [LHsTyVarBndr GHC.Name] -> m [Binder]
convertLHsTyVarBndrs ex tvs = for (map unLoc tvs) $ \case
  UserTyVar   tv   -> Inferred ex . Ident <$> var TypeNS (unLoc tv)
  KindedTyVar tv k -> Typed Ungeneralizable ex <$> (pure . Ident <$> var TypeNS (unLoc tv)) <*> convertLType k

--------------------------------------------------------------------------------

convertType :: ConversionMonad m => HsType GHC.Name -> m Term
convertType (HsForAllTy tvs ty) = do
  explicitTVs <- convertLHsTyVarBndrs Coq.Implicit tvs
  tyBody      <- convertLType ty
  pure . maybe tyBody (Forall ?? tyBody) $ nonEmpty explicitTVs

convertType (HsQualTy (L _ ctx) ty) = do
  classes <- traverse (fmap (Generalized Coq.Implicit) . convertLType) ctx
  tyBody  <- convertLType ty
  pure . maybe tyBody (Forall ?? tyBody) $ nonEmpty classes

convertType (HsTyVar (L _ tv)) =
  Qualid <$> var TypeNS tv

convertType (HsAppTy ty1 ty2) =
  App1 <$> convertLType ty1 <*> convertLType ty2

-- TODO: This constructor handles '*' and deparses it later.  I'm just gonna
-- bank on never seeing any infix type things.
convertType (HsAppsTy tys) =
  let assertPrefix (L _ (HsAppPrefix lty)) = convertLType lty
      assertPrefix (L _ (HsAppInfix _))    = convUnsupported "infix types in type application lists"
  in traverse assertPrefix tys >>= \case
       tyFun:tyArgs ->
         pure $ appList tyFun $ map PosArg tyArgs
       [] ->
         convUnsupported "empty lists of type applications"

convertType (HsFunTy ty1 ty2) =
  Arrow <$> convertLType ty1 <*> convertLType ty2

convertType (HsListTy ty) =
  App1 (Var "list") <$> convertLType ty

convertType (HsPArrTy _ty) =
  convUnsupported "parallel arrays (`[:a:]')"

convertType (HsTupleTy tupTy tys) = do
  case tupTy of
    HsUnboxedTuple           -> pure () -- TODO: Mark converted unboxed tuples specially?
    HsBoxedTuple             -> pure ()
    HsConstraintTuple        -> convUnsupported "constraint tuples"
    HsBoxedOrConstraintTuple -> pure () -- Sure, it's boxed, why not
  case tys of
    []   -> pure $ Var "unit"
    [ty] -> convertLType ty
    _    -> (`InScope` "type") <$> foldl1 (mkInfix ?? "*") <$> traverse convertLType tys

convertType (HsOpTy ty1 op ty2) =
  App2 <$> (Qualid <$> var TypeNS (unLoc op)) <*> convertLType ty1 <*> convertLType ty2   -- ???

convertType (HsParTy ty) =
  Parens <$> convertLType ty

convertType (HsIParamTy (HsIPName ip) lty) = do
  isTyCallStack <- maybe (pure False) (fmap (== "CallStack") . ghcPpr) $ viewLHsTyVar lty
  if isTyCallStack && ip == fsLit "callStack"
    then pure $ "GHC.Stack.CallStack"
    else convUnsupported "implicit parameter constraints"

convertType (HsEqTy _ty1 _ty2) =
  convUnsupported "type equality" -- FIXME

convertType (HsKindSig ty k) =
  HasType <$> convertLType ty <*> convertLType k

convertType (HsSpliceTy _ _) =
  convUnsupported "Template Haskell type splices"

convertType (HsDocTy ty _doc) =
  convertLType ty

convertType (HsBangTy _bang ty) =
  convertLType ty -- Strictness annotations are ignored

convertType (HsRecTy _fields) =
  convUnsupported "record types" -- FIXME

convertType (HsCoreTy _) =
  convUnsupported "[internal] embedded core types"

convertType (HsExplicitListTy PlaceHolder tys) =
  foldr (App2 $ Var "cons") (Var "nil") <$> traverse convertLType tys

convertType (HsExplicitTupleTy _PlaceHolders tys) =
  case tys of
    []   -> pure $ Var "tt"
    [ty] -> convertLType ty
    _    -> foldl1 (App2 $ Var "pair") <$> traverse convertLType tys

convertType (HsTyLit lit) =
  case lit of
    HsNumTy _src int -> Num <$> convertInteger "type-level integers" int
    HsStrTy _src str -> pure $ convertFastString str

convertType (HsWildCardTy _) =
  convUnsupported "wildcards"

--------------------------------------------------------------------------------

convertLType :: ConversionMonad m => LHsType GHC.Name -> m Term
convertLType = convertType . unLoc

--------------------------------------------------------------------------------

convertLHsSigType :: ConversionMonad m => LHsSigType GHC.Name -> m Term
convertLHsSigType (HsIB itvs lty) =
  maybeForall <$> (map (Inferred Coq.Implicit . Ident) <$> traverse (var TypeNS) itvs)
              <*> convertLType lty

convertLHsSigWcType :: ConversionMonad m => LHsSigWcType GHC.Name -> m Term
convertLHsSigWcType (HsIB itvs (HsWC wcs _ss lty))
  | null wcs  = convertLHsSigType (HsIB itvs lty)
  | otherwise = convUnsupported "type wildcards"
