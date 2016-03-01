module HsToCoq.Util.Monad (
  -- * Booleans
  andM, orM,
  -- * Conditionals
  ifM, whenM, unlessM
  ) where

import Data.Bool

andM :: Monad m => m Bool -> m Bool -> m Bool
andM b1 b2 = bool (pure False) b2 =<< b1

orM :: Monad m => m Bool -> m Bool -> m Bool
orM b1 b2 = bool b2 (pure True) =<< b1

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM c t f = c >>= bool f t

whenM :: Monad m => m Bool -> m () -> m ()
whenM c t = ifM c t (pure ())

unlessM :: Monad m => m Bool -> m () -> m ()
unlessM c f = ifM c (pure ()) f
