module SplitAt where

{- This will not work 
splitAt :: Int -> [a] -> [[a]]
splitAt n xs | n <= 0    = [xs]
             | otherwise = go xs
  where go [] = []
        go xs = take n xs : go (drop n xs)
-}

splitAt :: Int -> [a] -> [[a]]
splitAt n xs | n <= 0    = [xs]
             | otherwise =
  let go [] = []
      go xs = take n xs : go (drop n xs)
  in go xs
