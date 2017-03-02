module StructuralIsomorphism.Util (
  -- * Basic functions
  (<&>),
  -- * Parallel traversal/equal-length applicative zip
  traverseBothOr, traverseBothWithOr,
  traverseBoth,   traverseBothWith,
  forBothOr,      forBothWithOr,
  forBoth,        forBothWith,
  -- * Error manipulation
  mapError, failWith,
  -- * Adapter types
  ApplicativeMonoid(..)
) where

import Data.Function
import Control.Applicative
import Control.Monad.Error.Class

(<&>) :: Functor f => f a -> (a -> b) -> f b
x <&> f = f <$> x
infixl 1 <&>
{-# INLINE (<&>) #-}

traverseBothOr :: Applicative f => f [c] -> (a -> b -> f c) -> [a] -> [b] -> f [c]
traverseBothOr _   _ []     []     = pure []
traverseBothOr err f (a:as) (b:bs) = (:) <$> f a b <*> traverseBothOr err f as bs
traverseBothOr err _ _      _      = err

traverseBothWithOr :: Applicative f
                   => f [c] -> (a -> [b]) -> (b -> b -> f c) -> a -> a -> f [c]
traverseBothWithOr err f g = traverseBothOr err g `on` f

traverseBoth :: Alternative f => (a -> b -> f c) -> [a] -> [b] -> f [c]
traverseBoth = traverseBothOr empty

traverseBothWith :: Alternative f => (a -> [b]) -> (b -> b -> f c) -> a -> a -> f [c]
traverseBothWith = traverseBothWithOr empty

forBothOr :: Applicative f => f [c] -> [a] -> [b] -> (a -> b -> f c) -> f [c]
forBothOr err as bs f = traverseBothOr err f as bs

forBothWithOr :: Applicative f => f [c] -> (a -> [b]) -> a -> a -> (b -> b -> f c) -> f [c]
forBothWithOr err f = forBothOr err `on` f

forBoth :: Alternative f => [a] -> [b] -> (a -> b -> f c) -> f [c]
forBoth = forBothOr empty

forBothWith :: Alternative f => (a -> [b]) -> a -> a -> (b -> b -> f c) -> f [c]
forBothWith = forBothWithOr empty

mapError :: MonadError e m => (e -> e) -> m a -> m a
mapError f act = act `catchError` (throwError . f)

failWith :: MonadError e m => e -> m a -> m a
failWith = mapError . const

-- Better name?
newtype ApplicativeMonoid f a = ApplicativeMonoid { getApplicativeMonoid :: f a }
                              deriving (Eq, Ord, Show, Read)
instance (Applicative f, Monoid a) => Monoid (ApplicativeMonoid f a) where
  mempty  = ApplicativeMonoid $ pure mempty
  mappend (ApplicativeMonoid x) (ApplicativeMonoid y) =
    ApplicativeMonoid $ liftA2 mappend x y
