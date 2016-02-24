{-# LANGUAGE TupleSections, LambdaCase, PatternSynonyms, OverloadedLists #-}

module HsToCoq.ConvertData (
  -- * Conversion
  convertDataDecl', convertType, convertLType,
  -- ** Names
  showRdrName, showName,
  -- ** Internal
  convertDataDefn, convertConDecl, convertLHsTyVarBndrs,
  -- * Input
  readDataDecls,
  -- * Coq construction
  pattern App1, pattern Var, appList
  ) where

import Data.Foldable
import Data.Traversable
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)

import Control.Monad
import Control.Monad.IO.Class

import GHC hiding (Name)
import qualified GHC
import RdrName
import OccName
import Panic

import HsToCoq.Util.Patterns
import HsToCoq.Util.GHC
import HsToCoq.Coq.Gallina
import HsToCoq.DataDecl
import HsToCoq.ProcessFiles

showRdrName :: GhcMonad m => RdrName -> m String
showRdrName = ghcSDoc . pprOccName . rdrNameOcc

showName :: GhcMonad m => GHC.Name -> m String
showName = showRdrName . nameRdrName

readDataDecls :: GhcMonad m => DynFlags -> FilePath -> m [DataDecl' RdrName]
readDataDecls dflags file =   processFile (pure . getDataDecls) dflags file
                          >>= maybe ( liftIO . throwGhcExceptionIO
                                    . ProgramError $ file ++ ": no parse" )
                                    pure

-- Module-local
conv_unsupported :: MonadIO m => String -> m a
conv_unsupported what = liftIO . throwGhcExceptionIO . ProgramError $ what ++ " unsupported"

pattern App1 f x = App f (PosArg x :| Nil)
pattern Var v    = Qualid (Bare v)

appList :: Term -> [Arg] -> Term
appList f xs = case nonEmpty xs of
                Nothing  -> f
                Just xs' -> App f xs'

convertType :: GhcMonad m => HsType RdrName -> m Term
convertType (HsForAllTy _explicit _ _tvs _ctx _ty) =
  conv_unsupported "forall" -- FIXME

convertType (HsTyVar tv) =
  Var <$> ghcPpr tv -- TODO Check module part?

convertType (HsAppTy ty1 ty2) =
  App1 <$> convertLType ty1 <*> convertLType ty2

convertType (HsFunTy ty1 ty2) =
  Arrow <$> convertLType ty1 <*> convertLType ty2

convertType (HsListTy ty) =
  App1 (Var "list") <$> convertLType ty

convertType (HsPArrTy _ty) =
  conv_unsupported "parallel arrays (`[:a:]')"

convertType (HsTupleTy tupTy tys) = do
  case tupTy of
    HsUnboxedTuple           -> conv_unsupported "unboxed tuples"
    HsBoxedTuple             -> pure ()
    HsConstraintTuple        -> conv_unsupported "constraint tuples"
    HsBoxedOrConstraintTuple -> pure () -- Sure, it's boxed, why not
  case tys of
    []   -> pure $ Var "unit"
    [ty] -> convertLType ty
    _    -> foldl1 (\x t -> App (Var "prod") [PosArg x, PosArg t]) <$> traverse convertLType tys

convertType (HsOpTy _ty1 _op _ty2) =
  conv_unsupported "binary operators" -- FIXME

convertType (HsParTy ty) =
  Parens <$> convertLType ty

convertType (HsIParamTy _ _) =
  conv_unsupported "implicit parameters"

convertType (HsEqTy _ty1 _ty2) =
  conv_unsupported "type equality" -- FIXME

convertType (HsKindSig ty k) =
  HasType <$> convertLType ty <*> convertLType k

convertType (HsQuasiQuoteTy _) =
  conv_unsupported "quasiquoters"

convertType (HsSpliceTy _ _) =
  conv_unsupported "Template Haskell"

convertType (HsDocTy ty _doc) =
  convertLType ty

convertType (HsBangTy _bang ty) =
  convertLType ty -- Strictness annotations are ignored

convertType (HsRecTy _fields) =
  conv_unsupported "record types" -- FIXME

convertType (HsCoreTy _) =
  conv_unsupported "[internal] embedded core types"

convertType (HsExplicitListTy PlaceHolder tys) =
  foldr (\ty l -> App (Var "cons") [PosArg ty, PosArg l]) (Var "nil") <$> traverse convertLType tys

convertType (HsExplicitTupleTy _PlaceHolders tys) =
  case tys of
    []   -> pure $ Var "tt"
    [ty] -> convertLType ty
    _    -> foldl1 (\x t -> App (Var "pair") [PosArg x, PosArg t]) <$> traverse convertLType tys

convertType (HsTyLit lit) =
  case lit of
    HsNumTy _ int | int >= 0  -> pure . Num $ fromInteger int
                  | otherwise -> conv_unsupported "negative type-level integers"
    HsStrTy _ _               -> conv_unsupported "type-level strings"

convertType (HsWrapTy _ _) =
  conv_unsupported "[internal] wrapped types" 

convertType HsWildcardTy =
  pure Underscore

convertType (HsNamedWildcardTy _) =
  conv_unsupported "named wildcards"

convertLType :: GhcMonad m => LHsType RdrName -> m Term
convertLType = convertType . unLoc

type Constructor = (Ident, [Binder], Maybe Term)

convertLHsTyVarBndrs :: GhcMonad m => LHsTyVarBndrs RdrName -> m [Binder]
convertLHsTyVarBndrs (HsQTvs kvs tvs) = do
  kinds <- traverse (fmap (Inferred . Ident) . ghcPpr) kvs
  types <- for (map unLoc tvs) $ \case
             UserTyVar   tv   -> Inferred . Ident <$> ghcPpr tv
             KindedTyVar tv k -> Typed <$> (pure . Ident <$> ghcPpr tv) <*> convertLType k
  pure $ kinds ++ types

convertConDecl :: GhcMonad m => Term -> ConDecl RdrName -> m [Constructor]
convertConDecl curType (ConDecl lnames _explicit lqvs lcxt ldetails lres _doc _old) = do
  unless (null $ unLoc lcxt) $ conv_unsupported "constructor contexts"
  names  <- traverse (ghcPpr . unLoc) lnames
  params <- convertLHsTyVarBndrs lqvs
  resTy  <- case lres of
              ResTyH98       -> pure curType
              ResTyGADT _ ty -> convertLType ty
  args   <- traverse convertLType $ hsConDeclArgTys ldetails
  pure $ map (, params, Just $ foldr Arrow resTy args) names
  
convertDataDefn :: GhcMonad m => Term -> HsDataDefn RdrName -> m (Term, [Constructor])
convertDataDefn curType (HsDataDefn _nd lcxt _ctype ksig cons _derivs) = do
  unless (null $ unLoc lcxt) $ conv_unsupported "data type contexts"
  (,) <$> maybe (pure $ Sort Type) convertLType ksig
      <*> (concat <$> traverse (convertConDecl curType . unLoc) cons)

convertDataDecl' :: GhcMonad m => DataDecl' RdrName -> m Inductive
convertDataDecl' (DataDecl' name tvs defn _fvs) = do
  coqName       <- ghcPpr $ unLoc name
  params        <- convertLHsTyVarBndrs tvs
  let binderNames = foldMap $ \case
                      Inferred x    -> [x]
                      Typed xs _    -> toList xs
                      BindLet _ _ _ -> []
      nameArgs    = map $ PosArg . \case
                      Ident x        -> Var x
                      UnderscoreName -> Underscore
      curType     = appList (Var coqName) . nameArgs $ binderNames params
  (resTy, cons) <- convertDataDefn curType defn
  pure $ Inductive [IndBody coqName params resTy cons]
