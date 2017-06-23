{-# LANGUAGE LambdaCase,
             OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Type (convertType, convertLType, convertLHsTyVarBndrs) where

import Control.Lens

import Data.Semigroup
import Data.Foldable
import Data.Traversable
import Data.Char
import Data.List.NonEmpty (nonEmpty)
import qualified Data.Text as T

import Control.Monad
import Control.Monad.Variables

import qualified Data.Set as S

import GHC hiding (Name)
import HsToCoq.Util.GHC.FastString

import HsToCoq.Util.GHC
import HsToCoq.Util.GHC.HsTypes
import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.FreeVars

import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Literals

import Debug.Trace
--------------------------------------------------------------------------------

convertLHsTyVarBndrs :: ConversionMonad m => Explicitness -> [LHsTyVarBndr RdrName] -> m [Binder]
convertLHsTyVarBndrs ex tvs = for (map unLoc tvs) $ \case
  UserTyVar   tv   -> Inferred ex . Ident <$> freeVar (unLoc tv)
  KindedTyVar tv k -> Typed Ungeneralizable ex <$> (pure . Ident <$> freeVar (unLoc tv)) <*> convertLType k

--------------------------------------------------------------------------------

convertType :: ConversionMonad m => HsType RdrName -> m Term
convertType (HsForAllTy tvs ty) = do
  explicitTVs <- convertLHsTyVarBndrs Coq.Implicit tvs
  tyBody      <- convertLType ty
  implicitTVs <- do
    -- We need to find all the unquantified type variables.  Since Haskell
    -- never introduces a type variable name beginning with an upper-case
    -- letter, we look for those; however, if we've renamed a Coq value into
    -- one, we need to exclude that too.  (We also exclude all symbolic names,
    -- since Haskell now reserves those for constructors.)
    bindings <- S.fromList . toList <$> use renamings
    fvs      <- fmap (S.filter $ maybe False (((||) <$> isLower <*> (== '_')) . fst) . T.uncons)
              . fmap S.fromDistinctAscList . filterM (fmap not . isBound) . S.toAscList
              $ getFreeVars tyBody S.\\ (  bindings
                                        <> foldMap (S.fromList . toListOf binderIdents) explicitTVs)
    pure . map (Inferred Coq.Implicit . Ident) $ S.toList fvs
  pure . maybe tyBody (Forall ?? tyBody)
       . nonEmpty $ explicitTVs ++ implicitTVs
  -- TODO: We generate the TVs in lexicographic order, Haskell does it in source
  -- code order.  Is this important?
  -- SCW: Important for explicit type applications.

convertType (HsQualTy (L _ ctx) ty) = do
  classes <- traverse (fmap (Generalized Coq.Implicit) . convertLType) ctx
  tyBody  <- convertLType ty
  pure . maybe tyBody (Forall ?? tyBody) $ nonEmpty classes

convertType (HsTyVar (L _ tv)) =
  Var <$> var TypeNS tv

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
    _    -> foldl1 (Infix ?? "*") <$> traverse convertLType tys

convertType (HsOpTy _ty1 _op _ty2) =
  convUnsupported "binary operators" -- FIXME

convertType (HsParTy ty) =
  Parens <$> convertLType ty

convertType (HsIParamTy (HsIPName ip) lty) = do
  isTyCallStack <- maybe (pure False) (fmap (== "CallStack") . ghcPpr) $ viewLHsTyVar lty
  if isTyCallStack && ip == fsLit "callStack"
    then Var <$> var' TypeNS "CallStack"
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

convertLType :: ConversionMonad m => LHsType RdrName -> m Term
convertLType = convertType . unLoc
