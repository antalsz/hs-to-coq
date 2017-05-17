module HsToCoq.Util.List (
  -- * Lists
  uncons, assertUncons, unsnoc, assertUnsnoc,
  -- * Nonempty lists
  unconsNEL, unsnocNEL,
  -- * Missing monadic functions
  partitionM, spanM, groupByM,
  -- * Group for the whole list
  groupAllBy, groupAllByM
) where

import Data.Bifunctor
import Data.Bitraversable
import Data.Maybe
import Data.List (partition)
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

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM _ []     = pure ([], [])
partitionM p (x:xs) = do px     <- p x 
                         ~(t,f) <- partitionM p xs
                         pure $ if px
                                then (x:t,   f)
                                else (  t, x:f)

spanM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
spanM _ []         = pure ([],[])
spanM p xxs@(x:xs) = do px <- p x
                        if px
                        then first (x:) <$> spanM p xs
                        else pure ([], xxs)

groupByM :: Monad m => (a -> a -> m Bool) -> [a] -> m [[a]]
groupByM (~~) = go where
  go []     = pure []
  go (x:xs) = fmap (uncurry (:)) . bitraverse (pure . (x:)) go =<< spanM (x ~~) xs

groupAllBy :: (a -> a -> Bool) -> [a] -> [[a]]
groupAllBy (~~) = go where
  go []     = []
  go (x:xs) = uncurry (:) . bimap (x:) go $ partition (x ~~) xs

groupAllByM :: Monad m => (a -> a -> m Bool) -> [a] -> m [[a]]
groupAllByM (~~) = go where
  go []     = pure []
  go (x:xs) = fmap (uncurry (:)) . bitraverse (pure . (x:)) go =<< partitionM (x ~~) xs
