module HsToCoq.Util.Coerce ((#.)) where

import Data.Coerce

-- |Coercing function composition.  Ignores its left-hand argument.
--
-- This trick was taken from the implementation of "Data.Foldable", which uses
-- it for efficiency.
(#.) :: Coercible b b' => (b -> b') -> (a -> b) -> a -> b'
(#.) _ = coerce
{-# INLINE (#.) #-}
infix 0 #.
