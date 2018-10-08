module ExtractedString where

import Data.Char
import Data.Bits

default (Int)

data Vector a = Nil | Cons a Int (Vector a)

{-- If this appears, you're using Ascii internals. Please don't --}
asciiToChar :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
            -> Char
asciiToChar b0 b1 b2 b3 b4 b5 b6 b7 =
    let f b i = if b
                then shiftL 1 i
                else 0
    in chr (f b0 0 + f b1 1 + f b2 2 +
            f b3 3 + f b4 4 + f b5 5 +
            f b6 6 + f b7 7)

{-- If this appears, you're using Ascii internals. Please don't --}
foldChar :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> t)
         -> Char -> t
foldChar f c =
    let n   = ord c;
        h i = (.&.) n (shiftL 1 i) /= 0
    in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7)
