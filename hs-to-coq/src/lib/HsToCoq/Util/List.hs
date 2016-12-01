module HsToCoq.Util.List (
  -- * Lists
  uncons, assertUncons, unsnoc, assertUnsnoc,
  -- * Nonempty lists
  unconsNEL, unsnocNEL,
) where

import Data.Bifunctor
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))

unconsNEL :: NonEmpty a -> (a, [a])
unconsNEL (x :| xs) = (x, xs)

uncons :: [a] -> Maybe (a,[a])
uncons []     = Nothing
uncons (x:xs) = Just (x,xs)

assertUncons :: [a] -> (a,[a])
assertUncons = fromMaybe (error "assertUncons: empty list") . uncons

unsnocNEL :: NonEmpty a -> ([a],a)
unsnocNEL (x :| xs) = go x xs where
  go y []      = ([],y)
  go y (y':ys) = first (y:) $ go y' ys

unsnoc :: [a] -> Maybe ([a],a)
unsnoc []     = Nothing
unsnoc (x:xs) = Just . unsnocNEL $ x :| xs

assertUnsnoc :: [a] -> ([a],a)
assertUnsnoc = fromMaybe (error "assertUnsnoc: empty list") . unsnoc
