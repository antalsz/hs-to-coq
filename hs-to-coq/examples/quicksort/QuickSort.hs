module QuickSort where

import Data.List

-- polymorphism does not work nicely yet!
quicksort :: Ord a => [a] -> [a]
quicksort [] = []
quicksort (p:xs) = quicksort lesser ++ [p] ++ quicksort greater
    where
        (lesser, greater) = partition (<p) xs
