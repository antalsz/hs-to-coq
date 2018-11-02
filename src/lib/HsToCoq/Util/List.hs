{-# LANGUAGE LambdaCase, RankNTypes #-}

module HsToCoq.Util.List (
  -- * Lists
  uncons, assertUncons, unsnoc, assertUnsnoc,
  splitCommonPrefix,
  -- ** Lensy variants
  unconsOf, unsnocOf, splitCommonPrefixOf,
  -- * Sorted lists
  insertSorted, insertSortedBy,
  -- * Nonempty lists
  unconsNEL, unsnocNEL, (|:), (|>), snocNEL,
  (<++), (++>),
  -- * English
  explainItems, explainStrItems
) where

import Control.Lens hiding (uncons, unsnoc, (<|), (|>))

import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.State.Lazy   as Lazy

import Data.Bifunctor
import Data.Foldable
import Control.Applicative

import HsToCoq.Util.Function
import Data.Maybe
import Data.Tuple

import Data.List.NonEmpty (NonEmpty(..), (<|))

import Data.Text (Text)
import qualified Data.Text as T

unconsNEL :: NonEmpty a -> (a, [a])
unconsNEL (x :| xs) = (x, xs)

uncons :: [a] -> Maybe (a,[a])
uncons []     = Nothing
uncons (x:xs) = Just (x,xs)

unconsOf :: Lens' s [a] -> s -> Maybe (a, s)
unconsOf l = Strict.runStateT . zoom l $ Strict.StateT uncons

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

unsnocNEL :: NonEmpty a -> ([a],a)
unsnocNEL (x :| xs) = go x xs where
  go y []      = ([],y)
  go y (y':ys) = first (y:) $ go y' ys

unsnoc :: [a] -> Maybe ([a],a)
unsnoc []     = Nothing
unsnoc (x:xs) = Just . unsnocNEL $ x :| xs

unsnocOf :: Lens' s [a] -> s -> Maybe (s, a)
unsnocOf l = fmap swap .: Strict.runStateT . zoom l $ Strict.StateT (fmap swap . unsnoc)

assertUnsnoc :: [a] -> ([a],a)
assertUnsnoc = fromMaybe (error "assertUnsnoc: empty list") . unsnoc

(<++) :: Foldable f => f a -> NonEmpty a -> NonEmpty a
(<++) = flip $ foldr (<|)
infixr 5 <++

(++>) :: Foldable f => NonEmpty a -> f a -> NonEmpty a
(x :| xs) ++> ys = x :| (xs ++ toList ys)
infixr 5 ++>

insertSortedBy :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertSortedBy _   y []     = [y]
insertSortedBy cmp y (x:xs) = case y `cmp` x of
                                LT -> y : x : xs
                                EQ -> y : xs
                                GT -> x : insertSortedBy cmp y xs

insertSorted :: Ord a => a -> [a] -> [a]
insertSorted = insertSortedBy compare

splitCommonPrefixOf :: (Traversable t, Eq a) => Lens' s [a] -> t s -> ([a], t s)
splitCommonPrefixOf l ss =
  case (Lazy.runStateT ?? Nothing) $ traverse (maybe empty trimSameHead . unconsOf l) ss of
    Just (ss', Just x) -> first (x:) $ splitCommonPrefixOf l ss'
    _                  -> ([], ss)
  where
    -- The state starts empty and fills with the first head we find.  If the
    -- head of the list (first item of the pair) is the same as that head (or
    -- the very first one), we can happily return the full object containing the
    -- tail (second item of the pair); otherwise, this is not a common prefix.
    --
    -- This is essentially a combination of `unzip` and `x:xs -> all (== x) xs`.
    trimSameHead (x,s') = Lazy.get >>= \case
      Just x' | x == x'   -> pure s'
              | otherwise -> empty
      Nothing             -> s' <$ Lazy.put (Just x)

splitCommonPrefix :: (Traversable t, Eq a) => t [a] -> ([a], t [a])
splitCommonPrefix = splitCommonPrefixOf id

-- TODO: Differentiate arguments somehow
explainItems :: Foldable f => (a -> Text) -> Text -> Text -> Text -> Text -> Text -> f a -> Text
explainItems disp no sep conj item items stuff =
  case unsnoc $ disp <$> toList stuff of
    Nothing                    -> no <+> items
    Just ([], thing)           -> item <+> thing
    Just ([thing1], thing2)    -> items <+> thing1 <+> conj <+> thing2
    Just (things,   lastThing) -> items <+> T.intercalate (sep <> space) things <> sep <+> conj <+> lastThing
  where
    s1 <+> s2 | T.null s1 = s2
              | T.null s2 = s1
              | otherwise = s1 <> space <> s2
    infixr 5 <+>
    
    space = T.singleton ' '

-- TODO: Differentiate arguments somehow
explainStrItems :: Foldable f => (a -> String) -> String -> String -> String -> String -> String -> f a -> String
explainStrItems disp no sep conj item items =
  T.unpack . explainItems (T.pack . disp) (T.pack no) (T.pack sep) (T.pack conj) (T.pack item) (T.pack items)
