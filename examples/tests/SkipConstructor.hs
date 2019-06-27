module SkipConstructor where

data T = U
       | D (T -> T)

f :: T -> T
f U     = U
f (D l) = l (f (D l))
