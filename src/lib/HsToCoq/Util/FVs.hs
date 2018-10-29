{-# LANGUAGE MultiParamTypeClasses, DefaultSignatures, FlexibleInstances,
             GeneralizedNewtypeDeriving, DeriveTraversable, DeriveGeneric, DeriveDataTypeable #-}

module HsToCoq.Util.FVs where

import HsToCoq.Util.Generics

import Data.Set (Set)
import qualified Data.Set as S
import Data.Foldable

-- For instances
import Control.Lens
import Data.Bifoldable
import Data.Bitraversable
import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Error.Class
import Data.Data (Data)

--------------------------------------------------------------------------------

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

binder :: i -> BVs i
binder x = BVs (S.singleton x) S.empty

binders :: (Ord i, Foldable f) => f i -> BVs i
binders s = BVs (S.fromList (toList s)) S.empty

occurrence :: i -> FVs i
occurrence x = FVs (S.singleton x)

bindsNothing :: FVs i -> BVs i
bindsNothing (FVs fvs) = BVs S.empty fvs

forgetBinders :: BVs i -> FVs i
forgetBinders bv = FVs (getBFVs bv)

scopesOver :: Ord i => BVs i -> FVs i -> FVs i
scopesOver (BVs bvs fvs1) (FVs fvs2) = FVs $ fvs1 <> (fvs2 `S.difference` bvs)

scopesMutually :: (Ord i, Foldable f) => (a -> BVs i) -> f a -> BVs i
scopesMutually f xs =
    binders (foldMap (getBVars . f) xs)
       `telescope` bindsNothing (foldMap (forgetBinders . f) xs)

telescope :: Ord i => BVs i -> BVs i -> BVs i
telescope (BVs bvs1 fvs1) (BVs bvs2 fvs2)
    = BVs (bvs1 <> bvs2) (fvs1 <> (fvs2 `S.difference` bvs1))

foldTelescope :: (Ord i, Foldable f) => (a -> BVs i) -> f a -> BVs i
foldTelescope f = foldr (\x -> (f x `telescope`)) mempty

foldScopes :: (Ord i, Foldable f) => (a -> BVs i) -> f a -> FVs i -> FVs i
foldScopes f xs x = foldr (\x -> (f x `scopesOver`)) x xs

class HasBV i a where
  bvOf :: a -> BVs i

class HasFV i a where
  fvOf :: a -> FVs i
  default fvOf :: HasBV i a => a -> FVs i
  fvOf = forgetBinders . bvOf

instance HasBV i (BVs i) where
  bvOf = id

-- | Convenient functions for things that don’t bind variables, but occur
-- as subterms in binders
fvOf' :: HasFV i a => a -> BVs i
fvOf' x = bindsNothing (fvOf x)

--------------------------------------------------------------------------------

-- |Wraps 'HasBV' and 'HasFV' for the 'Right' values, and reports that the left
-- values contain nothing.
newtype ErrOrVars e a = ErrOrVars { getErrOrVars :: Either e a }
                      deriving ( -- Stock
                                 Eq, Ord, Show, Read
                                 -- Generics
                               , Data, Generic
                                 -- Iterating
                               , Foldable, Traversable
                               , Bifoldable
                                 -- Functor, monad, etc.
                               , Functor, Applicative, Monad
                               , Bifunctor
                               , Alternative, MonadPlus
                               , MonadFix
                               , MonadError e )

instance Bitraversable ErrOrVars where
  bitraverse l r (ErrOrVars e) = ErrOrVars <$> bitraverse l r e
  {-# INLINE bitraverse #-}

instance Swapped ErrOrVars where
  swapped = iso swap swap
    where swap (ErrOrVars e) = ErrOrVars (either Right Left e)
          {-# INLINE swap #-}
  {-# INLINE swapped #-}

instance HasBV i a => HasBV i (ErrOrVars e a) where
  bvOf = either (const $ BVs S.empty S.empty) bvOf . getErrOrVars

instance HasFV i a => HasFV i (ErrOrVars e a) where
  fvOf = either (const $ FVs S.empty) fvOf . getErrOrVars
