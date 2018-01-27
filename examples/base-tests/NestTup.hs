{-# LANGUAGE FlexibleInstances #-}
module NestTup where
  
class Foo a where
  foo :: a

-- These two instances have different types, but their names in the
-- output are the same

instance Foo ((Int,Int),Int) where
  foo = ((1,2),3)

instance Foo (Int,(Int,Int)) where
  foo = (1,(2,3))
