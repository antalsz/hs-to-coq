{-# LANGUAGE TypeOperators, EmptyCase, TypeApplications, ScopedTypeVariables, FlexibleContexts,
             InstanceSigs, DeriveGeneric, UndecidableInstances #-}

module HsToCoq.Util.Generics (
  -- * Re-export the class
  Generic(..),
  -- * Default instances
  GSemigroup(..), (%<>),
  GMonoid(..), gmempty,
  -- * Generic instance wrappers
  WithGSemigroup(..), WithGMonoid(..)
) where

import GHC.Generics
import Data.Coerce

class GSemigroup f where
  (%<>%) :: f p -> f p -> f p

instance GSemigroup V1 where
  (%<>%) = \v1 _ -> case v1 of {}
  {-# INLINE (%<>%) #-}

instance GSemigroup U1 where
  (%<>%) = \_ _ -> U1
  {-# INLINE (%<>%) #-}

instance (GSemigroup f, GSemigroup g) => GSemigroup (f :*: g) where
  (%<>%) = \(fst1 :*: snd1) (fst2 :*: snd2) -> (fst1 %<>% fst2) :*: (snd1 %<>% snd2)
  {-# INLINE (%<>%) #-}

instance Semigroup c => GSemigroup (K1 i c) where
  (%<>%) = coerce @(c -> c -> c) (<>)
  {-# INLINE (%<>%) #-}

instance GSemigroup f => GSemigroup (M1 i t f) where
  (%<>%) :: forall p. M1 i t f p -> M1 i t f p -> M1 i t f p
  (%<>%) = coerce @(f p -> f p -> f p) (%<>%)
  {-# INLINE (%<>%) #-}

(%<>) :: (Generic a, GSemigroup (Rep a)) => a -> a -> a
(%<>) = \s t -> to $ from s %<>% from t
{-# INLINE (%<>) #-}

class GSemigroup f => GMonoid f where
  gmempty' :: f p

instance GMonoid U1 where
  gmempty' = U1
  {-# INLINE gmempty' #-}

instance (GMonoid f, GMonoid g) => GMonoid (f :*: g) where
  gmempty' = gmempty' :*: gmempty'
  {-# INLINE gmempty' #-}

instance Monoid c => GMonoid (K1 i c) where
  gmempty' = K1 mempty
  {-# INLINE gmempty' #-}

instance GMonoid f => GMonoid (M1 i t f) where
  gmempty' = M1 gmempty'
  {-# INLINE gmempty' #-}

gmempty :: forall a. (Generic a, GMonoid (Rep a)) => a
gmempty = to gmempty'
{-# INLINE gmempty #-}
  
newtype WithGSemigroup a = WithGSemigroup { unWithGSemigroup :: a } deriving (Generic)
instance (Generic a, GSemigroup (Rep a)) => Semigroup (WithGSemigroup a) where
  (<>) = coerce @(a -> a -> a) (%<>)
  {-# INLINE (<>) #-}
  
newtype WithGMonoid a = WithGMonoid { unWithGMonoid :: a } deriving (Generic)
instance (Generic a, GSemigroup (Rep a)) => Semigroup (WithGMonoid a) where
  (<>) = coerce @(a -> a -> a) (%<>)
  {-# INLINE (<>) #-}
instance (Generic a, GMonoid (Rep a)) => Monoid (WithGMonoid a) where
  mempty = coerce @a gmempty
  {-# INLINE mempty #-}
