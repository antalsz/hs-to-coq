module BitsRewrite where

infixl 7 .&.

class Bits a where
    (.&.) :: a -> a -> a
    xor :: a -> a -> a
    complement :: a -> a

foo :: Bits a => a -> a -> a
foo x y = x BitsRewrite..&. complement y

bar :: Bits a => a -> a -> a
bar x y = x `xor` (x .&. y)
