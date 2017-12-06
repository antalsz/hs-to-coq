module Endo where

import Prelude hiding (Monoid)

class Monoid a where
        mempty  :: a
        mappend :: a -> a -> a
        mconcat :: [a] -> a

newtype Endo a = MkEndo { appEndo :: a -> a }

instance Monoid (Endo a) where
        mempty = MkEndo id
        MkEndo f `mappend` MkEndo g = MkEndo (f . g)
        mconcat = foldr Endo.mappend Endo.mempty
