module Endo where

import Prelude hiding (Monoid)

class Monoid a where
        mempty  :: a
        mappend :: a -> a -> a
        mconcat :: [a] -> a

newtype Endo a = Endo { appEndo :: a -> a }

instance Monoid (Endo a) where
        mempty = Endo id
        Endo f `mappend` Endo g = Endo (f . g)
        mconcat = foldr Endo.mappend Endo.mempty
