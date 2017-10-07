module QuickSort where

import Data.List

-- polymorphism does not work nicely yet!
quicksort :: [Int] -> [Int]
quicksort [] = []
quicksort (p:xs) = quicksort lesser ++ [p] ++ quicksort greater
    where
        (lesser, greater) = partition (<p) xs
