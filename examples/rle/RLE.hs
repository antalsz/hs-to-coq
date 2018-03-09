{-# LANGUAGE FlexibleContexts #-}
module RLE where

import GHC.List

-- This used to all be  polymorphic in the element type,
-- to show to to work with an unconstrainted `patternFailure` term.
--
-- Now `patternFailure` has [`{Default E}] and this does no longer work.
-- So I changed this example to be monomorphic...

type E = Int

hd :: [E] -> E
hd (x:xs) = x

tl :: [E] -> [E]
tl (x:xs) = xs

group                   :: Eq E => [E] -> [[E]]
group                   =  groupBy (==)

-- | The 'groupBy' function is the non-overloaded version of 'group'.
{- Not accepted by coqs termination checker. Function would probably work.
groupBy                 :: (E -> E -> Bool) -> [E] -> [[E]]
groupBy _  []           =  []
groupBy eq (x:xs)       =  (x:ys) : groupBy eq zs
                           where (ys,zs) = span (eq x) xs
-}

-- Structurally recursive version of groupBy
groupBy                 :: (E -> E -> Bool) -> [E] -> [[E]]
groupBy f [] = []
groupBy f (x:xs) = case groupBy f xs of
    [] -> [[x]]
    (y:ys) : yss | f x y     -> (x:y:ys) : yss
                 | otherwise -> [x] :(y:ys) : yss

rle :: Eq E => [E] -> [(E,Int)]
rle ys = map (\x -> (hd x, GHC.List.length x)) (group ys)

bad_rle :: Eq E => [E] -> [(E,Int)]
bad_rle ys = map (\x -> (hd (tl x), GHC.List.length x)) (group ys)
