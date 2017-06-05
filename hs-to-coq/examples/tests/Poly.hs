-- This test demonstrates the problem with classes with
-- polymorphic member functions.

class Func t where
  fmap :: (a -> b) -> t a -> t b

data Two a = M a a

-- This works (only with the signature)
fmap_Two :: (a -> b) -> Two a -> Two b
fmap_Two f (M x y) = M (f x) (f y)

-- This does not
instance Func Two where
  fmap f (M x y) = M (f x) (f y)
