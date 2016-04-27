{-# LANGUAGE TupleSections, LambdaCase,
             OverloadedStrings,
             FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.DataType (
  convertDataDecl, convertDataDefn,
  Constructor, convertConDecl
  ) where

import Data.Semigroup (Semigroup(..))
import Data.Traversable

import Control.Monad

import GHC hiding (Name)

import HsToCoq.Util.GHC
import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type

--------------------------------------------------------------------------------

type Constructor = (Ident, [Binder], Maybe Term)

convertConDecl :: ConversionMonad m
               => Term -> ConDecl RdrName -> m [Constructor]
convertConDecl curType (ConDecl lnames _explicit lqvs lcxt ldetails lres _doc _old) = do
  unless (null $ unLoc lcxt) $ convUnsupported "constructor contexts"
  names   <- for lnames $ \lname -> do
               name <- ghcPpr $ unLoc lname -- We use 'ghcPpr' because we munge the name here ourselves
               let name' = "Mk_" <> name
               name' <$ rename ExprNS name name'
  params  <- convertLHsTyVarBndrs Coq.Implicit lqvs
  resTy   <- case lres of
               ResTyH98       -> pure curType
               ResTyGADT _ ty -> convertLType ty
  args    <- traverse convertLType $ hsConDeclArgTys ldetails
  pure $ map (, params, Just $ foldr Arrow resTy args) names
  
--------------------------------------------------------------------------------
  
convertDataDefn :: ConversionMonad m
                => Term -> HsDataDefn RdrName
                -> m (Term, [Constructor])
convertDataDefn curType (HsDataDefn _nd lcxt _ctype ksig cons _derivs) = do
  unless (null $ unLoc lcxt) $ convUnsupported "data type contexts"
  (,) <$> maybe (pure $ Sort Type) convertLType ksig
      <*> (concat <$> traverse (convertConDecl curType . unLoc) cons)

convertDataDecl :: ConversionMonad m
                => Located RdrName -> LHsTyVarBndrs RdrName -> HsDataDefn RdrName
                -> m IndBody
convertDataDecl name tvs defn = do
  coqName <- freeVar $ unLoc name
  params  <- convertLHsTyVarBndrs Coq.Explicit tvs
  let nameArgs = map $ PosArg . \case
                   Ident x        -> Var x
                   UnderscoreName -> Underscore
      curType  = appList (Var coqName) . nameArgs $ foldMap binderNames params
  (resTy, cons) <- convertDataDefn curType defn
  pure $ IndBody coqName params resTy cons
