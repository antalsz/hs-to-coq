{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module HsToCoq.ConvertHaskell.Declarations.TypeSynonym (SynBody(..), convertSynDecl) where

import Prelude hiding (Num)

import Control.Lens

import GHC hiding (Name)
import qualified GHC

import qualified Data.List.NonEmpty as NE
import qualified Data.Set as S

import HsToCoq.Coq.Gallina as Coq
import HsToCoq.Coq.Gallina.Util
import HsToCoq.Coq.FreeVars

import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.Type
import HsToCoq.ConvertHaskell.Parameters.Edits

--------------------------------------------------------------------------------

data SynBody = SynBody Qualid [Binder] (Maybe Term) Term
             deriving (Eq, Ord, Read, Show)

instance FreeVars SynBody where
  freeVars (SynBody _name args oty def) = binding' args $ freeVars oty *> freeVars def

convertSynDecl :: ConversionMonad m
               => Located GHC.Name -> [LHsTyVarBndr GHC.Name] -> LHsType GHC.Name
               -> m SynBody
convertSynDecl name args def  = do
  coqName <- freeVar $ unLoc name
  params <- convertLHsTyVarBndrs Coq.Explicit args
  rhs    <- convertLType def
  let (params', rhs') = etaContract params rhs
  SynBody <$> var TypeNS (unLoc name)
          <*> pure params'
          <*> use (edits.typeSynonymTypes . at coqName . to (fmap Var))
          <*> pure (rhs' `InScope` "type")

-- Eta-contracting type synonyms allows Coq’s instance resolution mechanism
-- to look though type synonym more easily.
etaContract :: [Binder] -> Term -> ([Binder], Term)
etaContract bndrs (App f args)
    = let (rbinders, rargs) = go (reverse bndrs) (reverse (NE.toList args))
      in (reverse rbinders, appList f (reverse rargs))
  where
    go (b:bs) (a:as)
        | PosArg (Qualid v) <- a
        , [v'] <- toListOf binderIdents b
        , v == v'
        , v' `S.notMember` getFreeVars f
        , v' `S.notMember` getFreeVars as
        = go bs as
    go bs as = (bs, as)
etaContract b t = (b,t)


