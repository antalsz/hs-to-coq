-- (c) 2000-2005 by Martin Erwig [see file COPYRIGHT]

-- | Shortest path algorithms
module Data.Graph.Inductive.Query.SP(
      spTree
    , sp
    , spLength
    , dijkstra
    , LRTree
    , H.Heap
) where

import qualified Data.Graph.Inductive.Internal.Heap as H

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Internal.RootPath

expand :: (Real b) => b -> LPath b -> Context a b -> [H.Heap b (LPath b)]
expand d (LP p) (_,_,_,s) = map (\(l,v)->H.unit (l+d) (LP ((v,l+d):p))) s

-- | Dijkstra's shortest path algorithm.
--
--   The edge labels of type @b@ are the edge weights; negative edge
--   weights are not supported.
dijkstra :: (Graph gr, Real b)
    => H.Heap b (LPath b) -- ^ Initial heap of known paths and their lengths.
    -> gr a b
    -> LRTree b
dijkstra h g | H.isEmpty h || isEmpty g = []
dijkstra h g =
    case match v g of
         (Just c,g')  -> p:dijkstra (H.mergeAll (h':expand d p c)) g'
         (Nothing,g') -> dijkstra h' g'
    where (_,p@(LP ((v,d):_)),h') = H.splitMin h

-- | Tree of shortest paths from a certain node to the rest of the
--   (reachable) nodes.
--
--   Corresponds to 'dijkstra' applied to a heap in which the only known node is
--   the starting node, with a path of length 0 leading to it.
--
--   The edge labels of type @b@ are the edge weights; negative edge
--   weights are not supported.
spTree :: (Graph gr, Real b)
    => Node
    -> gr a b
    -> LRTree b
spTree v = dijkstra (H.unit 0 (LP [(v,0)]))

-- | Length of the shortest path between two nodes, if any.
--
--   Returns 'Nothing' if there is no path, and @'Just' <path length>@
--   otherwise.
--
--   The edge labels of type @b@ are the edge weights; negative edge
--   weights are not supported.
spLength :: (Graph gr, Real b)
    => Node -- ^ Start
    -> Node -- ^ Destination
    -> gr a b
    -> Maybe b
spLength s t = getDistance t . spTree s

-- | Shortest path between two nodes, if any.
--
--   Returns 'Nothing' if the destination is not reachable from the
--   start node, and @'Just' <path>@ otherwise.
--
--   The edge labels of type @b@ are the edge weights; negative edge
--   weights are not supported.
sp :: (Graph gr, Real b)
    => Node -- ^ Start
    -> Node -- ^ Destination
    -> gr a b
    -> Maybe Path
sp s t g = case getLPathNodes t (spTree s g) of
  [] -> Nothing
  p  -> Just p
