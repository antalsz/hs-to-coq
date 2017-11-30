{-# LANGUAGE FlexibleInstances #-}
module Bits where

infixl 7 .&.
infixl 5 .|.

class Bits a where
    -- | Bitwise \"and\"
    (.&.) :: a -> a -> a

    -- | Bitwise \"or\"
    (.|.) :: a -> a -> a

testBitDefault :: Bits a => a -> a -> a
testBitDefault = \x i -> (x .&. i)

testBitDefault2 :: Bits a => a -> a -> a
testBitDefault2 = (.&.)

popCountDefault :: (Bits a) =>
    a -> (a -> a) -> (a -> a) -> (a -> Bool) -> a -> a
popCountDefault zero inc dec isZero = go zero
 where
   go c w = if isZero w
            then c
            else go (inc c) (w .&. (dec w))
