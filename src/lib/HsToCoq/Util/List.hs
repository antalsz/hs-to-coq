module HsToCoq.Util.List (
  -- * Lists
  uncons, assertUncons, unsnoc, assertUnsnoc,
  -- * Sorted lists
  insertSorted, insertSortedBy,
  -- * Nonempty lists
  unconsNEL, unsnocNEL, (|:), (|>), snocNEL,
  (<++), (++>)
) where

import Data.Bifunctor
import Data.Foldable
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..), (<|))

unconsNEL :: NonEmpty a -> (a, [a])
unconsNEL (x :| xs) = (x, xs)

uncons :: [a] -> Maybe (a,[a])
uncons []     = Nothing
uncons (x:xs) = Just (x,xs)

assertUncons :: [a] -> (a,[a])
assertUncons = fromMaybe (error "assertUncons: empty list") . uncons

(|:) :: [a] -> a -> NonEmpty a
[]     |: y = y :| []
(x:xs) |: y = x <| (xs |: y)
infixl 5 |:

(|>) :: NonEmpty a -> a -> NonEmpty a
(x :| xs) |> y = x :| (xs ++ [y])
infixr 5 |>

snocNEL :: NonEmpty a -> a -> NonEmpty a
snocNEL = (|>)

(<++) :: Foldable f => f a -> NonEmpty a -> NonEmpty a
(<++) = flip $ foldr (<|)
infixr 5 <++

(++>) :: Foldable f => NonEmpty a -> f a -> NonEmpty a
(x :| xs) ++> ys = x :| (xs ++ toList ys)
infixr 5 ++>

unsnocNEL :: NonEmpty a -> ([a],a)
unsnocNEL (x :| xs) = go x xs where
  go y []      = ([],y)
  go y (y':ys) = first (y:) $ go y' ys

unsnoc :: [a] -> Maybe ([a],a)
unsnoc []     = Nothing
unsnoc (x:xs) = Just . unsnocNEL $ x :| xs

assertUnsnoc :: [a] -> ([a],a)
assertUnsnoc = fromMaybe (error "assertUnsnoc: empty list") . unsnoc


insertSortedBy :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertSortedBy _   y []     = [y]
insertSortedBy cmp y (x:xs) = case y `cmp` x of
                                LT -> y : x : xs
                                EQ -> y : xs
                                GT -> x : insertSortedBy cmp y xs

insertSorted :: Ord a => a -> [a] -> [a]
insertSorted = insertSortedBy compare
