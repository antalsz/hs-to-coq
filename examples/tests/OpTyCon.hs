{-# LANGUAGE FlexibleInstances #-}
module OpTyCon where

x :: ((->) Int Int)
x = \y -> y

class C t where
   m :: a -> t a -> t a

instance C ((->) Int) where
   m = \_ x -> x
