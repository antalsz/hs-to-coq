{-# LANGUAGE ScopedTypeVariables #-}
module InstVar where

class Def a where def :: a

data X a = MkX a

instance Def a => Def (X a) where def = MkX (def :: a)
