{-# LANGUAGE FlexibleInstances #-}

module MutrecInst where

-- Two class member functions that are mutually recursive

class C a where
  f1 :: a -> a
  f2 :: a -> a

data T = K

instance C [T] where
  f1 []     = []
  f1 (x:xs) = (x : f2 xs)

  f2 []     = []
  f2 (y:ys) = (y : f1 ys)
