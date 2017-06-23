module PatternGuard where

checkNum :: Int -> Bool
checkNum 2 = True
checkNum _ = False

take                   :: Int -> [a] -> [a]
take n _      | n <= 0 =  []
take _ []              =  []
take n (x:xs)          =  x : take (n-1) xs
