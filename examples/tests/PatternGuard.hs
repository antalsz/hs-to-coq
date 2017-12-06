module PatternGuard where

-- The otherwise case just gets lost!
-- This bug shows up in ghc/Demand.splitFVs

g :: [Bool] -> Bool
g (x:xs) | True <- x = g xs
         | otherwise = False
g [] = True
