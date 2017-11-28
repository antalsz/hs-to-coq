module Guard where

f :: Int -> Int
f x | x == 1    = 1
    | otherwise = 2

g :: Int -> Int
g 1 = 1
g _ = 2

h :: Int -> Int
h x = if x == 1 then 1 else 2
