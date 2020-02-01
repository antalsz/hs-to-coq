module StringUtil (sSplit, sStartsWith, sBreak, readString) where

import           Data.Char

sSplit :: String -> String -> (String, String, Bool)
sSplit s sep = sSplitHelper s sep [] (length sep)

sStartsWith :: String -> String -> Bool
sStartsWith _ [] = True
sStartsWith [] _ = False
sStartsWith (c1:s1) (c2:s2) | c1 == c2  = sStartsWith s1 s2
                            | otherwise = False

sBreak :: String -> String -> (String, String)
sBreak s sep = let (a, b, _) = sSplit s sep in (a, b)

readString :: String -> Maybe Int
readString = flip readStringHelper 0

-- Internal functions

sSplitHelper :: String -> String -> String -> Int -> (String, String, Bool)
sSplitHelper [] _ pre _ = (reverse pre, [], False)
sSplitHelper s@(c:t) sep pre l =
  if sStartsWith s sep then (reverse pre, drop l s, True)
  else sSplitHelper t sep (c:pre) l

readStringHelper :: String -> Int -> Maybe Int
readStringHelper [] n    = Just n
readStringHelper (c:s) n | isNumber c = readStringHelper s $
                                        n * 10 + ord c - ord '0'
                         | otherwise  = Nothing
