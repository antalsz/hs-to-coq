{-# LANGUAGE RecordWildCards, LambdaCase, FlexibleContexts #-}

module HsToCoq.ConvertHaskell.Declarations.Class (ClassBody(..), convertClassDecl) where

import Control.Lens

import Data.Traversable
import Data.List.NonEmpty (nonEmpty)

import Control.Monad

import qualified Data.Map.Strict as M

import GHC hiding (Name)
import Bag
import Class

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.FreeVars

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.InfixNames
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Sigs
import HsToCoq.ConvertHaskell.Declarations.Notations

--------------------------------------------------------------------------------

data ClassBody = ClassBody ClassDefinition [Notation]
               deriving (Eq, Ord, Read, Show)

instance FreeVars ClassBody where
  freeVars (ClassBody cls nots) = binding' cls $ freeVars (NoBinding nots)

convertClassDecl :: ConversionMonad m
                 => LHsContext RdrName                   -- ^@tcdCtxt@
                 -> Located RdrName                      -- ^@tcdLName@
                 -> [LHsTyVarBndr RdrName]               -- ^@tcdTyVars@
                 -> [Located (FunDep (Located RdrName))] -- ^@tcdFDs@
                 -> [LSig RdrName]                       -- ^@tcdSigs@
                 -> LHsBinds RdrName                     -- ^@tcdMeths@
                 -> [LFamilyDecl RdrName]                -- ^@tcdATs@
                 -> [LTyFamDefltEqn RdrName]             -- ^@tcdATDefs@
                 -> m ClassBody
convertClassDecl (L _ hsCtx) (L _ hsName) ltvs fds lsigs defaults types typeDefaults = do
  unless (null       fds)          $ convUnsupported "functional dependencies"
  unless (null       types)        $ convUnsupported "associated types"
  unless (null       typeDefaults) $ convUnsupported "default associated type definitions"

  name <- freeVar hsName
  ctx  <- traverse (fmap (Generalized Coq.Implicit) . convertLType) hsCtx
  args <- convertLHsTyVarBndrs Coq.Explicit ltvs
  sigs <- binding' args $ convertLSigs lsigs

  defs <- fmap M.fromList $ for (bagToList defaults) $ convertTypedBinding Nothing . unLoc >=> \case
            Just (ConvertedDefinitionBinding ConvertedDefinition{..}) -> pure (convDefName, maybe id Fun (nonEmpty convDefArgs) convDefBody)
            Just (ConvertedPatternBinding    _ _)                     -> convUnsupported "pattern bindings in class declarations"
            Nothing                                                   -> convUnsupported $ "skipping a type class method in" ++ show name
  unless (null defs) $ defaultMethods.at name ?= defs

  pure $ ClassBody (ClassDefinition name (args ++ ctx) Nothing (bimap toCoqName sigType <$> M.toList sigs))
                   (concatMap (buildInfixNotations sigs <*> infixToCoq) . filter identIsOperator $ M.keys sigs)
