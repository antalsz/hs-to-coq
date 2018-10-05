module HsToCoq.Util.Foldable (asumFmap, mapPartitionEithers, findM) where

import Control.Applicative
import Control.Monad.Trans.Maybe
import Data.Foldable
import Data.Monoid
import Data.Either

asumFmap :: (Alternative f, Foldable t) => (a -> b) -> t (f a) -> f b
asumFmap f = getAlt . foldMap (Alt . fmap f)

mapPartitionEithers :: Foldable f => (a -> Either b c) -> f a -> ([b],[c])
mapPartitionEithers f = partitionEithers . map f . toList

-- From Petr Pudlák's answer to the Stack Overfloq question "implementing a
-- “findM” in Haskell?", by Justin L.
-- <https://stackoverflow.com/a/18556504/237428>
findM :: (Monad m, Foldable f) => (a -> m (Maybe b)) -> f a -> m (Maybe b)
findM f = runMaybeT . getAlt . foldMap (Alt . MaybeT . f)
