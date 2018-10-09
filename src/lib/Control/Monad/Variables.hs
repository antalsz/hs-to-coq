{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}

module Control.Monad.Variables (
  -- * The 'Variables' monad
  Variables, runVariables, execVariables, evalVariables,
  bind, bindAll,
  free, frees,
  bound, allBound,
  occurrence, occurrences,
  isBound, areBound,
  ) where

import HsToCoq.Util.Generics

import HsToCoq.Util.Monad
import Control.Monad.Reader
import Control.Monad.Writer.Strict

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Set (Set)
import qualified Data.Set as S

-- | Set of free variables
newtype FVs i = FVs { getFVs :: Set i } deriving (Eq, Ord, Show, Read, Generic)
instance Ord i => Semigroup (FVs i) where (<>)   = (%<>)
instance Ord i => Monoid    (FVs i) where mempty = gmempty

-- | An object capable of binding something has
-- a set of variables
data BVs i = BVs { getBVars :: Set i -- Variables bound by this binder
                 , getBFVs  :: Set i -- Free variables of this object
                 }
           deriving (Eq, Ord, Show, Read, Generic)
instance Ord i => Semigroup (BVs i) where (<>)   = (%<>)
instance Ord i => Monoid    (BVs i) where mempty = gmempty

scopesOver :: BVs i -> FVs i -> FVs i
scopesOver (BVs bvs fvs1 fvs2) = fvs1 <> (fvs2 `S.difference` bvs1)

scopesOverRev :: BVs i -> FVs i -> FVs i
scopesOverRev (BVs bvs fvs1 fvs2) = (fvs1 <> fvs2) `S.difference` bvs1

class BindsVariables i a where
    bvOf :: a -> BVs i

class HasFV i a where
    fvOf :: a -> FVs i
    default fvOf :: BindsVariables i a => a -> FVs i
    fvOf x = FVs (getBFVs (bvOf x))


