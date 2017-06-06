
-- Mutually recursive functions

data T = K

f1 :: [T] -> [T]
f1 []     = []
f1 (x:xs) = (x : f2 xs)

f2 :: [T] -> [T]
f2 []     = []
f2 (y:ys) = (y : f1 ys)
