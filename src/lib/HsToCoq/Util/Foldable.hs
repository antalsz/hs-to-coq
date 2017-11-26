module HsToCoq.Util.Foldable (asumFmap) where

import Control.Applicative
import Data.Foldable
import HsToCoq.Util.Function

asumFmap :: (Alternative f, Functor t, Foldable t)
         => (a -> b) -> t (f a) -> f b
asumFmap = asum .: fmap . fmap
