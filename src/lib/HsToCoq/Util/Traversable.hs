module HsToCoq.Util.Traversable (foldTraverse, forFold, traversePartitionEithers) where

import HsToCoq.Util.Function
import Data.Foldable
import Data.Either

foldTraverse :: (Monoid m, Applicative f, Traversable t) => (a -> f m) -> t a -> f m
foldTraverse = fmap fold .: traverse

forFold :: (Monoid m, Applicative f, Traversable t) => t a -> (a -> f m) -> f m
forFold = flip foldTraverse

traversePartitionEithers :: (Applicative f, Traversable t) => (a -> f (Either b c)) -> t a -> f ([b],[c])
traversePartitionEithers f = fmap partitionEithers . traverse f . toList
