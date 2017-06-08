{-# LANGUAGE FlexibleInstances #-}
infixl 7 .&.
infixl 5 .|.

class Eq a => Bits a where
    -- | Bitwise \"and\"
    (.&.) :: a -> a -> a

    -- | Bitwise \"or\"
    (.|.) :: a -> a -> a

testBitDefault :: Bits a => a -> a -> a
testBitDefault = \x i -> (x .&. i)

popCountDefault :: (Bits a, Num a) => a -> Int
popCountDefault = go 0
 where
   go c 0 = c
   go c w = go (c+1) (w .&. (w - 1))
