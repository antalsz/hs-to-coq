module HsToCoq.Util.Traversable (foldTraverse, forFold) where

import Data.Foldable
import HsToCoq.Util.Function

foldTraverse :: (Monoid m, Applicative f, Traversable t) => (a -> f m) -> t a -> f m
foldTraverse = fmap fold .: traverse

forFold :: (Monoid m, Applicative f, Traversable t) => t a -> (a -> f m) -> f m
forFold = flip foldTraverse
