-- (c) 2000-2005 by Martin Erwig [see file COPYRIGHT]
-- | Inward directed trees as lists of paths.
module Data.Graph.Inductive.Internal.RootPath (
    -- * Types
    RTree,LRTree,
    -- * Operations
    getPath,getLPath,
    getDistance,
    getLPathNodes
) where

import Data.Graph.Inductive.Graph

type LRTree a = [LPath a]
type RTree = [Path]

first :: ([a] -> Bool) -> [[a]] -> [a]
first p xss  = case filter p xss of
                 []   -> []
                 x:_  -> x

-- | Find the first path in a tree that starts with the given node.
--
--   Returns an empty list if there is no such path.
findP :: Node -> LRTree a -> [LNode a]
findP _ []                                = []
findP v (LP []:ps)                        = findP v ps
findP v (LP (p@((w,_):_)):ps) | v==w      = p
                              | otherwise = findP v ps

getPath :: Node -> RTree -> Path
getPath v = reverse . first (\(w:_)->w==v)

getLPath :: Node -> LRTree a -> LPath a
getLPath v = LP . reverse . findP v

-- | Return the distance to the given node in the given tree.
--
--   Returns 'Nothing' if the given node is not reachable.
getDistance :: Node -> LRTree a -> Maybe a
getDistance v t = case findP v t of
  []      -> Nothing
  (_,d):_ -> Just d

getLPathNodes :: Node -> LRTree a -> Path
getLPathNodes v = (\(LP p)->map fst p) . getLPath v
