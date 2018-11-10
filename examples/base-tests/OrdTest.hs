module OrdTest where

data Test = A | B deriving Eq

instance Ord Test where
  A <= _ = True
  B <= B = True
  _ <= _ = False