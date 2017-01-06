{-# LANGUAGE TupleSections, RecordWildCards, LambdaCase,
             OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.DataType (
  convertDataDecl, convertDataDefn,
  Constructor, convertConDecl,
  addAdditionalConstructorScope, rewriteDataTypeArguments
  ) where

import Control.Lens

import Data.Bifunctor
import Data.Semigroup (Semigroup(..))
import Data.Foldable
import Data.Traversable

import qualified Data.Set        as S
import qualified Data.Map.Strict as M

import Control.Monad

import GHC hiding (Name)

import HsToCoq.Util.GHC
import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Parameters.Renamings
import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type

--------------------------------------------------------------------------------

type Constructor = (Ident, [Binder], Maybe Term)

--------------------------------------------------------------------------------

addAdditionalConstructorScope :: ConversionMonad m => Constructor -> m Constructor
addAdditionalConstructorScope ctor@(_, _, Nothing) =
  pure ctor
addAdditionalConstructorScope ctor@(name, bs, Just resTy) =
  use (edits.additionalScopes.at (SPConstructor,name)) <&> \case
    Just scope -> (name, bs, Just $ resTy `InScope` scope)
    Nothing    -> ctor

--------------------------------------------------------------------------------

convertConDecl :: ConversionMonad m
               => Term -> [Binder] -> ConDecl RdrName -> m [Constructor]
convertConDecl curType extraArgs (ConDecl lnames _explicit lqvs lcxt details lres _doc _old) = do
  unless (null $ unLoc lcxt) $ convUnsupported "constructor contexts"
  
  cons <- for lnames $ \(L _ hsCon) -> do
            con <- ghcPpr hsCon -- We use 'ghcPpr' because we munge the name here ourselves
            use (renamed ExprNS con) >>= \case
              Nothing   -> renamed ExprNS con <?= "Mk_" <> con
              Just con' -> pure con'
  
  params <- convertLHsTyVarBndrs Coq.Implicit lqvs
  resTy  <- case lres of
              ResTyH98       -> pure curType
              ResTyGADT _ ty -> convertLType ty
  args   <- traverse convertLType $ hsConDeclArgTys details
  
  fieldInfo <- case details of
    RecCon (L _ fields) ->
      fmap RecordFields .  traverse freeVar
        $ concatMap (map unLoc . cd_fld_names . unLoc) fields
    _ ->
      pure . NonRecordFields $ length args
  for_ cons $ \con -> constructorFields . at con ?= fieldInfo
  
  traverse addAdditionalConstructorScope $
    map (, params, Just . maybeForall extraArgs $ foldr Arrow resTy args) cons

--------------------------------------------------------------------------------

rewriteDataTypeArguments :: ConversionMonad m => DataTypeArguments -> [Binder] -> m ([Binder], [Binder])
rewriteDataTypeArguments dta bs = do
  let dtaEditFailure what =
        editFailure $ what ++ " when adjusting data type parameters and indices"
  
  let (ibs, ebs) = flip span bs $ (== Coq.Implicit) . \case
                     Inferred ei _     -> ei
                     Typed    _ ei _ _ -> ei
                     _                 -> Coq.Explicit
  
  explicitMap <-
    let extraImplicit  = "non-initial implicit arguments"
        complexBinding = "complex (let/generalized) bindings"
    in either dtaEditFailure (pure . M.fromList . concat) . for ebs $ \case
         Inferred   Coq.Explicit x     -> Right [(x, Inferred Coq.Explicit x)]
         Typed    g Coq.Explicit xs ty -> Right [(x, Typed g Coq.Explicit (pure x) ty) | x <- toList xs]
         
         Inferred   Coq.Implicit _   -> Left extraImplicit
         Typed    _ Coq.Implicit _ _ -> Left extraImplicit
         
         BindLet     _ _ _ -> Left complexBinding
         Generalized _ _   -> Left complexBinding
  
  let editIdents  = S.fromList $ dta^.dtParameters <> dta^.dtIndices
      boundIdents = fmap S.fromList . traverse (view nameToIdent) $ foldMap (toListOf binderNames) ebs
                       -- Underscores are an automatic failure
    in unless (boundIdents == Just editIdents) $
         dtaEditFailure $ "mismatched names"
  
  let coalesceTypedBinders [] = []
      coalesceTypedBinders (Typed g ei xs0 ty : bs) =
        let (tbs, bs') = flip span bs $ \case
                           Typed g' ei' _ ty' -> g == g' && ei == ei' && ty == ty'
                           _                  -> False
        in Typed g ei (foldl' (\xs (Typed _ _ xs' _) -> xs <> xs') xs0 tbs) ty : coalesceTypedBinders bs'
      coalesceTypedBinders (b : bs) =
        b : coalesceTypedBinders bs
      
      getBindersFor = coalesceTypedBinders . map ((explicitMap M.!) . Ident) . (dta^.)
  
  pure (ibs ++ getBindersFor dtParameters, getBindersFor dtIndices)
  
--------------------------------------------------------------------------------
  
convertDataDefn :: ConversionMonad m
                => Term -> [Binder] -> HsDataDefn RdrName
                -> m (Term, [Constructor])
convertDataDefn curType extraArgs (HsDataDefn _nd lcxt _ctype ksig cons _derivs) = do
  unless (null $ unLoc lcxt) $ convUnsupported "data type contexts"
  (,) <$> maybe (pure $ Sort Type) convertLType ksig
      <*> (concat <$> traverse (convertConDecl curType extraArgs . unLoc) cons)

convertDataDecl :: ConversionMonad m
                => Located RdrName -> LHsTyVarBndrs RdrName -> HsDataDefn RdrName
                -> m IndBody
convertDataDecl name tvs defn = do
  coqName   <- freeVar $ unLoc name
  rawParams <- convertLHsTyVarBndrs Coq.Explicit tvs
  
  (params, indices) <-
    use (edits . dataTypeArguments . at coqName) >>= \case
      Just dta -> rewriteDataTypeArguments dta rawParams
      Nothing  -> pure (rawParams, [])
  let conIndices = indices & mapped.binderExplicitness .~ Coq.Implicit
  
  let curType  = appList (Var coqName) . binderArgs $ params ++ indices
  (resTy, cons) <- first (maybeForall indices)
                     <$> convertDataDefn curType conIndices defn
  
  let conNames = [con | (con,_,_) <- cons]
  constructors . at coqName ?= conNames
  for_ conNames $ \con -> do
    constructorTypes . at con ?= coqName
    use (constructorFields . at con) >>= \case
      Just (RecordFields fields) ->
        for_ fields $ \field -> recordFieldTypes . at field ?= coqName
      _ ->
        pure ()
  
  pure $ IndBody coqName params resTy cons
