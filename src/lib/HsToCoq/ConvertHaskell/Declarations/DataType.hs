{-# LANGUAGE TupleSections, RecordWildCards, LambdaCase,
             OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.DataType (
  convertDataDecl,
  ) where

import Control.Lens

import HsToCoq.Util.Function
import Control.Applicative
import Data.Bifunctor
import Data.Semigroup (Semigroup(..))
import Data.Foldable
import Data.Traversable
import Data.Maybe
import HsToCoq.Util.Traversable

import qualified Data.Set        as S
import qualified Data.Map.Strict as M
import HsToCoq.Util.Containers

import Control.Monad
import Control.Monad.Trans.Maybe

import GHC hiding (Name)
import qualified GHC

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Parameters.Edits
import HsToCoq.ConvertHaskell.TypeInfo
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type

import qualified Data.List.NonEmpty as NE

--------------------------------------------------------------------------------

type Constructor = (Qualid, [Binder], Maybe Term)

--------------------------------------------------------------------------------

addAdditionalConstructorScope :: ConversionMonad r m => Constructor -> m Constructor
addAdditionalConstructorScope ctor@(_, _, Nothing) =
  pure ctor
addAdditionalConstructorScope ctor@(name, bs, Just resTy) =
  view (edits.additionalScopes.at (SPConstructor,name)) <&> \case
    Just scope -> (name, bs, Just $ resTy `InScope` scope)
    Nothing    -> ctor

--------------------------------------------------------------------------------

conNameOrSkip :: (ConversionMonad r m, Alternative m) => GHC.Name -> m Qualid
conNameOrSkip name = do
  con <- var ExprNS name
  guard =<< view (edits.skippedConstructors.notContains con)
  pure con

------------------------------------------------------------------------------------------

convertConDecl :: ConversionMonad r m
               => Term -> [Binder] -> ConDecl GhcRn -> m [Constructor]
convertConDecl curType extraArgs (ConDeclH98 lname mlqvs mlcxt details _doc) = fmap fold . runMaybeT $ do
  unless (maybe True (null . unLoc) mlcxt) $ convUnsupported' "constructor contexts"

  con <- conNameOrSkip $ unLoc lname

  -- Only the explicit tyvars are available before renaming, so they're all we
  -- need to consider
  params <- withCurrentDefinition con $ maybe (pure []) (convertLHsTyVarBndrs Coq.Implicit . hsq_explicit) mlqvs
  args   <- withCurrentDefinition con (traverse convertLType $ hsConDeclArgTys details)

  case details of
    RecCon (L _ fields) ->
      do
       let qualids =  traverse (var ExprNS) $
                      map (selectorFieldOcc . unLoc) $
                      concatMap (cd_fld_names . unLoc) fields
       fieldInfo <- fmap RecordFields qualids
       storeConstructorFields con fieldInfo
       qualids <- qualids
       let namedBinders = fmap (\(x,y) -> Typed Ungeneralizable Explicit ( Ident x  NE.:| [] ) y) $ zip qualids args
       pure [(con, params ++ namedBinders , Just . maybeForall extraArgs $ foldr Arrow curType [])]
    _ ->
     do
      fieldInfo <- pure . NonRecordFields $ length args
      storeConstructorFields con fieldInfo
      pure [(con, params , Just . maybeForall extraArgs $ foldr Arrow curType args)]

convertConDecl curType extraArgs (ConDeclGADT lnames sigTy _doc) = do
  fmap catMaybes . for lnames $ \(L _ hsName) -> runMaybeT $ do
    conName         <- conNameOrSkip hsName
    utvm            <- unusedTyVarModeFor conName
    (_, curTypArgs) <- collectArgs curType
    conTy           <- withCurrentDefinition conName 
                       (maybeForall extraArgs <$> convertLHsSigTypeWithExcls utvm sigTy
                         (mapMaybe termHead curTypArgs))
    storeConstructorFields conName $ NonRecordFields 0   -- This is a hack
    pure (conName, [], Just conTy)

--------------------------------------------------------------------------------

rewriteDataTypeArguments :: ConversionMonad r m => DataTypeArguments -> [Binder] -> m ([Binder], [Binder])
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
    in either dtaEditFailure (pure . M.fromList) . forFold ebs $ \case
         Inferred   Coq.Explicit x     -> Right [(x, Inferred Coq.Explicit x)]
         Typed    g Coq.Explicit xs ty -> Right [(x, Typed g Coq.Explicit (pure x) ty) | x <- toList xs]

         Inferred   Coq.Implicit _   -> Left extraImplicit
         Typed    _ Coq.Implicit _ _ -> Left extraImplicit

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

convertDataDefn :: LocalConvMonad r m
                => Term -> [Binder] -> HsDataDefn GhcRn
                -> m (Term, [Constructor])
convertDataDefn curType extraArgs (HsDataDefn _nd lcxt _ctype ksig cons _derivs) = do
  unless (null $ unLoc lcxt) $ convUnsupported' "data type contexts"
  (,) <$> maybe (pure $ Sort Type) convertLType ksig
      <*> (traverse addAdditionalConstructorScope =<<
           foldTraverse (convertConDecl curType extraArgs . unLoc) cons)

convertDataDecl :: ConversionMonad r m
                => Located GHC.Name -> [LHsTyVarBndr GhcRn] -> HsDataDefn GhcRn
                -> m IndBody
convertDataDecl name tvs defn = do
  coqName   <- var TypeNS $ unLoc name

  kinds     <- (++ repeat Nothing) . map Just . maybe [] NE.toList <$> view (edits.dataKinds.at coqName)
  let cvtName tv = Ident <$> var TypeNS (unLoc tv)
  let  go :: ConversionMonad r m => LHsTyVarBndr GhcRn -> Maybe Term -> m Binder
       go (L _ (UserTyVar name))     (Just t) = cvtName name >>= \n -> return $ Typed Ungeneralizable Coq.Explicit (n NE.:| []) t
       go (L _ (UserTyVar name))     Nothing  = cvtName name >>= \n -> return $ Inferred Coq.Explicit n
       go (L _ (KindedTyVar name _)) (Just t) = cvtName name >>= \n -> return $ Typed Ungeneralizable Coq.Explicit (n NE.:| []) t
       go (L _ (KindedTyVar name _)) Nothing  = cvtName name >>= \n -> return $ Inferred Coq.Explicit n  -- dunno if this could happen
  rawParams <- zipWithM go tvs kinds

  (params, indices) <-
    view (edits . dataTypeArguments . at coqName) >>= \case
      Just dta -> rewriteDataTypeArguments dta rawParams
      Nothing  -> pure (rawParams, [])
  let conIndices = indices & mapped.binderExplicitness .~ Coq.Implicit

  let curType  = appList (Qualid coqName) . binderArgs $ params ++ indices
  (resTy, cons) <- first (maybeForall indices)
                     <$> withCurrentDefinition coqName (convertDataDefn curType conIndices defn)

  conNames <- filterM (view . (edits.skippedConstructors.:notContains)) [con | (con,_,_) <- cons]
  storeConstructors coqName conNames
  for_ conNames $ \con -> do
    storeConstructorType con coqName
    lookupConstructorFields con >>= \case
      Just (RecordFields fields) ->
        for_ fields $ \field -> storeRecordFieldType field coqName
      _ ->
        pure ()

  pure $ IndBody coqName params resTy cons
