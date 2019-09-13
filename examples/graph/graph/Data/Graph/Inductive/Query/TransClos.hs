module Data.Graph.Inductive.Query.TransClos(
    trc, rc, tc
) where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.BFS (bfen)

{-|
Finds the transitive closure of a directed graph.
Given a graph G=(V,E), its transitive closure is the graph:
G* = (V,E*) where E*={(i,j): i,j in V and there is a path from i to j in G}
-}
tc :: (DynGraph gr) => gr a b -> gr a ()
tc g = newEdges `insEdges` insNodes ln empty
  where
    ln       = labNodes g
    newEdges = [ (u, v, ()) | (u, _) <- ln, (_, v) <- bfen (outU g u) g ]
    outU gr  = map toEdge . out gr

{-|
Finds the transitive, reflexive closure of a directed graph.
Given a graph G=(V,E), its transitive closure is the graph:
G* = (V,E*) where E*={(i,j): i,j in V and either i = j or there is a path from i to j in G}
-}
trc :: (DynGraph gr) => gr a b -> gr a ()
trc g = newEdges `insEdges` insNodes ln empty
  where
    ln       = labNodes g
    newEdges = [ (u, v, ()) | (u, _) <- ln, (_, v) <- bfen [(u, u)] g ]

{-|
Finds the reflexive closure of a directed graph.
Given a graph G=(V,E), its transitive closure is the graph:
G* = (V,Er union E) where Er = {(i,i): i in V}
-}
rc :: (DynGraph gr) => gr a b -> gr a ()
rc g = newEdges `insEdges` insNodes ln empty
  where
    ln       = labNodes g
    newEdges = [ (u, u, ()) | (u, _) <- ln ]
