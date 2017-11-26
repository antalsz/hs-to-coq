module RLE where

import GHC.List

hd :: [a] -> a
hd (x:xs) = x

tl :: [a] -> [a]
tl (x:xs) = xs

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

rle :: Eq a => [a] -> [(a,Int)]
rle ys = map (\x -> (hd x, GHC.List.length x)) (group ys)

bad_rle :: Eq a => [a] -> [(a,Int)]
bad_rle ys = map (\x -> (hd (tl x), GHC.List.length x)) (group ys)
