{-# LANGUAGE ScopedTypeVariables #-}
module InstVar where

class Def a where def :: a

data X a = X a

instance Def a => Def (X a) where def = X (def :: a)
