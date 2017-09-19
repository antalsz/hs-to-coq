module QuickSort where

-- polymorphism does not work nicely yet!
quicksort :: [Int] -> [Int]
quicksort [] = []
quicksort (p:xs) = (quicksort lesser) ++ [p] ++ (quicksort greater)
    where
        lesser = filter (< p) xs
        greater = filter (>= p) xs
