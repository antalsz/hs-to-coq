module Self where

class C a where
   f1 :: a -> a
   f2 :: a -> a

data T = K

-- Not actually recursive, just one function defined in terms of the others
instance C T where
   f1 = \x -> x
   f2 = f1
