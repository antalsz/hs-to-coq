module Deriv where

data Option a = Just a | None deriving (Eq, Ord)

data MyBool = MyFalse | MyTrue deriving (Eq, Ord)
-- data Bar a = Bar a deriving Eq

data F a = G a a deriving (Eq, Ord)
