module HsToCoq.Util.List (uncons, assertUncons, unsnoc, assertUnsnoc) where

import Data.Bifunctor
import Data.Maybe

uncons :: [a] -> Maybe (a,[a])
uncons []     = Nothing
uncons (x:xs) = Just (x,xs)

assertUncons :: [a] -> (a,[a])
assertUncons = fromMaybe (error "assertUncons: empty list") . uncons

unsnoc :: [a] -> Maybe ([a],a)
unsnoc []     = Nothing
unsnoc (x:xs) = Just $ go x xs where
  go y []      = ([],y)
  go y (y':ys) = first (y:) $ go y' ys

assertUnsnoc :: [a] -> ([a],a)
assertUnsnoc = fromMaybe (error "assertUnsnoc: empty list") . unsnoc
