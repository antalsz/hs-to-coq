module Histogram where

import GHC.List

hd :: [a] -> a
hd (x:xs) = x

group                   :: Eq a => [a] -> [[a]]
group                   =  groupBy (==)

-- | The 'groupBy' function is the non-overloaded version of 'group'.
{- Not accepted by coqs termination checker. Function would probably work.
groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _  []           =  []
groupBy eq (x:xs)       =  (x:ys) : groupBy eq zs
                           where (ys,zs) = span (eq x) xs
-}

-- Structurally recursive version of groupBy
groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy f [] = []
groupBy f (x:xs) = case groupBy f xs of
    [] -> [[x]]
    (y:ys) : yss | f x y     -> (x:y:ys) : yss
                 | otherwise -> [x] :(y:ys) : yss

hist :: Eq a => [a] -> [(a,Int)]
hist ys = map (\x -> (hd x, GHC.List.length x)) (group ys)
