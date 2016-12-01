{-# LANGUAGE LambdaCase #-}

module HsToCoq.Util.Monad (
  -- * Booleans
  andM, orM,
  -- * Conditionals
  ifM, whenM, unlessM,
  -- * Lists
  spanM,
  -- * Looping
  untilJustM,
  -- * Kleisli arrow combinators
  (<***>), (<&&&>), (<+++>), (<|||>),
  -- * Errors
  exceptEither
  ) where

import Control.Arrow
import Control.Monad.Except
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

spanM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
spanM p = go where
  go []         = pure ([], [])
  go xxs@(x:xs) = p x >>= \case
                    True  -> first (x:) <$> go xs
                    False -> pure ([], xxs)

untilJustM :: Monad m => m (Maybe a) -> m a
untilJustM act = maybe (untilJustM act) pure =<< act

-- Module-local
via_Kleisli :: (Kleisli m a a' -> Kleisli m b b' -> Kleisli m r r')
            -> (a -> m a') -> (b -> m b') -> r -> m r'
via_Kleisli (>><<) f g = runKleisli $ Kleisli f >><< Kleisli g

(<***>) :: Monad m => (a -> m b) -> (a' -> m b') -> (a,a') -> m (b,b')
(<***>) = via_Kleisli (***)
infixr 3 <***>

(<&&&>) :: Monad m => (a -> m b) -> (a -> m b') -> a -> m (b, b')
(<&&&>) = via_Kleisli (&&&)
infixr 3 <&&&>

(<+++>) :: Monad m => (a -> m b) -> (a' -> m b') -> Either a a' -> m (Either b b')
(<+++>) = via_Kleisli (+++)
infixr 2 <+++>

(<|||>) :: Monad m => (a -> m b) -> (a' -> m b) -> Either a a' -> m b
(<|||>) = via_Kleisli (|||)
infixr 2 <|||>

exceptEither :: MonadError e m => Either e a -> m a
exceptEither = either throwError pure
