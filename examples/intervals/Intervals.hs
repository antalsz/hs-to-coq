{-# LANGUAGE LambdaCase, DeriveGeneric #-}

module Intervals where

--import qualified Data.ByteString.Lazy as BS
--import Text.Printf
import Data.List hiding (union, intersect)
import Data.Monoid ((<>))
--import Data.Yaml (ToJSON, FromJSON)
--import GHC.Generics (Generic)
import Data.Function
import Data.Int
import Prelude hiding (subtract)

type Offset = Int64

data Interval = I { from :: Offset, to :: Offset }
    -- deriving (Show,Generic)

newtype Intervals = Intervals [Interval]
    -- deriving (Show,Generic)

mkInterval :: Offset -> Offset -> Intervals
mkInterval f t | f < t     = Intervals [I f t]
               | otherwise = Intervals []

fullIntervals :: Offset -> Intervals
fullIntervals len = mkInterval 0 len

nullInterval :: Intervals
nullInterval = Intervals []

size :: Intervals -> Offset
size (Intervals is) = sum [ t - f | I f t <- is ]

isEmpty :: Intervals -> Bool
isEmpty (Intervals is) = null is

subSetOf :: Intervals -> Intervals -> Bool
subSetOf a b = isEmpty (a `subtract` b)

intersects :: Intervals -> Intervals -> Bool
intersects a b = not $ isEmpty (a `intersect` b)

intersect :: Intervals -> Intervals -> Intervals
intersect (Intervals is1) (Intervals is2) = Intervals $ go is1 is2
  where
    go _ [] = []
    go [] _ = []
    go (i1:is1) (i2:is2)
        -- reorder for symmetry
        | to i1 < to i2 = go (i2:is2) (i1:is1)
        -- disjoint
        | from i1 >= to i2 = go (i1:is1) is2
        -- subset
        | to i1 == to i2 = I f' (to i2) : go is1 is2
        -- overlapping
        | otherwise = I f' (to i2) : go (i1 { from = to i2} : is1) is2
      where f' = max (from i1) (from i2)


union :: Intervals -> Intervals -> Intervals
union (Intervals is1) (Intervals is2) = Intervals $ go is1 is2
  where
    go is [] = is
    go [] is = is
    go (i1:is1) (i2:is2)
        -- reorder for symmetry
        | to i1 < to i2 = go (i2:is2) (i1:is1)
        -- disjoint
        | from i1 > to i2 = i2 : go (i1:is1) is2
        -- overlapping
        | otherwise  = go (i1 { from = f'} : is1) is2
      where f' = min (from i1) (from i2)

subtract :: Intervals -> Intervals -> Intervals
subtract (Intervals is1) (Intervals is2) = Intervals $ go is1 is2
  where
    go is [] = is
    go [] _  = []
    go (i1:is1) (i2:is2)
        -- i2 past i1
        | to i1 <= from i2 = i1 : go is1 (i2:is2)
        -- i1 past i2
        | to i2 <= from i1 = go (i1:is1) is2
        -- i1 contained in i2
        | from i2 <= from i1 , to i1 <= to i2 = go is1 (i2:is2)
        -- i2 covers beginning of i1
        | from i1 >= from i2 = go (i1 { from = to i2} : is1) is2
        -- i2 covers end of i1
        | to i1 <= to i2     = i1 { to = from i2} : go is1 (i2:is2)
        -- i2 in the middle of i1
        | otherwise = I (from i1) (from i2) :
                      go (I (to i2) (to i1) : is1) is2


-- setZeros :: BS.ByteString -> Intervals -> BS.ByteString
-- setZeros s (Intervals is) = foldl' go s is
--   where
--     go s (I f t) = prefix <> zeroes <> postfix
--       where
--         (tmp, postfix)     = BS.splitAt t s
--         (prefix, _discard) = BS.splitAt f tmp
--         zeroes = BS.replicate (t-f) 0

-- ppInterval :: Interval -> String
-- ppInterval (I f t) = printf "0x%04X-0x%04X" f t
-- 
-- ppIntervals :: Intervals -> String
-- ppIntervals (Intervals xs) = intercalate " " (map ppInterval xs)

--instance FromJSON Interval
--instance ToJSON Interval
--instance FromJSON Intervals
--instance ToJSON Intervals
