-- (c) 2000-2005 by Martin Erwig [see file COPYRIGHT]
-- | Graph Voronoi Diagram
--
--   These functions can be used to create a /shortest path forest/
--   where the roots are specified.
module Data.Graph.Inductive.Query.GVD (
    Voronoi,LRTree,
    gvdIn,gvdOut,
    voronoiSet,nearestNode,nearestDist,nearestPath,
--    vd,nn,ns,
--    vdO,nnO,nsO
) where

import Data.List  (nub)
import Data.Maybe (listToMaybe)

import qualified Data.Graph.Inductive.Internal.Heap as H

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Internal.RootPath
import Data.Graph.Inductive.Query.SP          (dijkstra)

-- | Representation of a shortest path forest.
type Voronoi a = LRTree a

-- | Produce a shortest path forest (the roots of which are those
--   nodes specified) from nodes in the graph /to/ one of the root
--   nodes (if possible).
gvdIn :: (DynGraph gr, Real b) => [Node] -> gr a b -> Voronoi b
gvdIn vs g = gvdOut vs (grev g)

-- | Produce a shortest path forest (the roots of which are those
--   nodes specified) from nodes in the graph /from/ one of the root
--   nodes (if possible).
gvdOut :: (Graph gr, Real b) => [Node] -> gr a b -> Voronoi b
gvdOut vs = dijkstra (H.build (zip (repeat 0) (map (\v->LP [(v,0)]) vs)))

-- | Return the nodes reachable to/from (depending on how the
--   'Voronoi' was constructed) from the specified root node (if the
--   specified node is not one of the root nodes of the shortest path
--   forest, an empty list will be returned).
voronoiSet :: Node -> Voronoi b -> [Node]
voronoiSet v = nub . concat . filter (\p->last p==v) . map (map fst . unLPath)

-- | Try to construct a path to/from a specified node to one of the
--   root nodes of the shortest path forest.
maybePath :: Node -> Voronoi b -> Maybe (LPath b)
maybePath v = listToMaybe . filter ((v==) . fst . head . unLPath)

-- | Try to determine the nearest root node to the one specified in the
--   shortest path forest.
nearestNode :: Node -> Voronoi b -> Maybe Node
nearestNode v = fmap (fst . last . unLPath) . maybePath v

-- | The distance to the 'nearestNode' (if there is one) in the
--   shortest path forest.
nearestDist :: Node -> Voronoi b -> Maybe b
nearestDist v = fmap (snd . head . unLPath) . maybePath v

-- | Try to construct a path to/from a specified node to one of the
--   root nodes of the shortest path forest.
nearestPath :: Node -> Voronoi b -> Maybe Path
nearestPath v = fmap (map fst . unLPath) . maybePath v


-- vd = gvdIn [4,5] vor
-- vdO = gvdOut [4,5] vor
-- nn = map (flip nearestNode vd) [1..8]
-- nnO = map (flip nearestNode vdO) [1..8]
-- ns = map (flip voronoiSet vd) [1..8]
-- nsO = map (flip voronoiSet vdO) [1..8]
