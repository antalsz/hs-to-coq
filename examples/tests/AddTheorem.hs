module AddTheorem where

behead :: [a] -> [a]
behead (_:xs) = xs
behead []     = []

oddPositions :: [a] -> [a]
oddPositions xs = case behead xs of
                    []   -> []
                    y:ys -> y : oddPositions ys
