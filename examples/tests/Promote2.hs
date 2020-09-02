module Promote2 where

  data Ty1 = A Bool

  h :: Ty1 -> Ty1
  h x = x

  g :: Ty1 -> Ty1
  g x = h x

  f :: Ty1 -> Ty1
  f x = g x

  i :: Ty1 -> Ty1
  i x = x


