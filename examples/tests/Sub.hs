module Sub where

-- Cannot create instances of subclasses
-- How is this supposed to work in Coq

class A a where
  f :: a -> a

class A a => B a where
  g :: a -> a

instance A () where
  f = \x -> x

instance B () where
  g = \x -> x

-- TODO: This gets injected in the wrong order now, which means it fails to
-- compile
