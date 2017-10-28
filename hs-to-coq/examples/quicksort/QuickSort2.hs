module QuickSort2 where

import Data.List

quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (p:xs) = quicksort lesser ++ [p] ++ quicksort greater
    where
        (lesser, greater) = partition (<p) xs
