module HsToCoq.Util.Traversable (foldTraverse, forFold, traversePartitionEithers, partitionA) where

import HsToCoq.Util.Function
import HsToCoq.Util.Functor
import Data.Bifunctor
import Data.Foldable
import Data.Either

foldTraverse :: (Monoid m, Applicative f, Traversable t) => (a -> f m) -> t a -> f m
foldTraverse = fmap fold .: traverse

forFold :: (Monoid m, Applicative f, Traversable t) => t a -> (a -> f m) -> f m
forFold = flip foldTraverse

traversePartitionEithers :: (Applicative f, Foldable g) => (a -> f (Either b c)) -> g a -> f ([b],[c])
traversePartitionEithers f = fmap partitionEithers . traverse f . toList

partitionA :: (Applicative f, Foldable g) => (a -> f Bool) -> g a -> f ([a],[a])
partitionA f = foldr (\x ps -> (decide ?? (x:)) <$> f x <*> ps) (pure ([],[])) where
  decide True  = first
  decide False = second
  {-# INLINE decide #-}
{-# INLINABLE partitionA #-}
