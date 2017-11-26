module Poly where

-- This test demonstrates the problem with classes with
-- polymorphic member functions.

class U a where
  g :: a -> a

class F1 t where
  -- just a polymorphic method
  f1 :: t a -> a -> ()
  f1 _ _ = ()

  -- with a class context too
  f2 :: (U u) => t u -> ()
  f2 _ = ()

instance F1 Two where


class Func t where
  fmap :: (a -> b) -> t a -> t b

data Two a = M a a

-- This works (only with the signature)
fmap_Two :: (a -> b) -> Two a -> Two b
fmap_Two f (M x y) = M (f x) (f y)

-- This does not
instance Func Two where
  fmap f (M x y) = M (f x) (f y)
