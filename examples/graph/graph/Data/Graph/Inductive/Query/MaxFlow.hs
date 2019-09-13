-- | Maximum Flow algorithm
--
-- We are given a flow network @G=(V,E)@ with source @s@ and sink @t@
-- where each edge @(u,v)@ in @E@ has a nonnegative capacity
-- @c(u,v)>=0@, and we wish to find a flow of maximum value from @s@
-- to @t@.
--
-- A flow in @G=(V,E)@ is a real-valued function @f:VxV->R@ that
-- satisfies:
--
-- @
-- For all u,v in V, f(u,v)\<=c(u,v)
-- For all u,v in V, f(u,v)=-f(v,u)
-- For all u in V-{s,t}, Sum{f(u,v):v in V } = 0
-- @
--
-- The value of a flow f is defined as @|f|=Sum {f(s,v)|v in V}@, i.e.,
-- the total net flow out of the source.
--
-- In this module we implement the Edmonds-Karp algorithm, which is
-- the Ford-Fulkerson method but using the shortest path from @s@ to
-- @t@ as the augmenting path along which the flow is incremented.

module Data.Graph.Inductive.Query.MaxFlow(
    getRevEdges, augmentGraph, updAdjList, updateFlow, mfmg, mf, maxFlowgraph,
    maxFlow
) where


import Data.List

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
--import Data.Graph.Inductive.Tree
import Data.Graph.Inductive.Query.BFS

-- |
-- @
--                 i                                 0
-- For each edge a--->b this function returns edge b--->a .
--          i
-- Edges a\<--->b are ignored
--          j
-- @
getRevEdges :: (Num b) => [Edge] -> [LEdge b]
getRevEdges [] = []
getRevEdges ((u,v):es) | (v,u) `notElem` es = (v,u,0):getRevEdges es
                       | otherwise          = getRevEdges (delete (v,u) es)

-- |
-- @
--                 i                                  0
-- For each edge a--->b insert into graph the edge a\<---b . Then change the
--                            i         (i,0,i)
-- label of every edge from a---->b to a------->b
-- @
--
-- where label (x,y,z)=(Max Capacity, Current flow, Residual capacity)
augmentGraph :: (DynGraph gr, Num b) => gr a b -> gr a (b,b,b)
augmentGraph g = emap (\i->(i,0,i)) (insEdges (getRevEdges (edges g)) g)

-- | Given a successor or predecessor list for node @u@ and given node @v@, find
--   the label corresponding to edge @(u,v)@ and update the flow and
--   residual capacity of that edge's label. Then return the updated
--   list.
updAdjList::(Num b) => Adj (b,b,b) -> Node -> b -> Bool -> Adj (b,b,b)
updAdjList s v cf fwd = rs ++ ((x,y+cf',z-cf'),w) : rs'
  where
    (rs, ((x,y,z),w):rs') = break ((v==) . snd) s

    cf' = if fwd
             then cf
             else negate cf

-- | Update flow and residual capacity along augmenting path from @s@ to @t@ in
--   graph @@G. For a path @[u,v,w,...]@ find the node @u@ in @G@ and
--   its successor and predecessor list, then update the corresponding
--   edges @(u,v)@ and @(v,u)@ on those lists by using the minimum
--   residual capacity of the path.
updateFlow :: (DynGraph gr, Num b) => Path -> b -> gr a (b,b,b) -> gr a (b,b,b)
updateFlow []        _ g = g
updateFlow [_]       _ g = g
updateFlow (u:v:vs) cf g = case match u g of
                             (Nothing,g')         -> g'
                             (Just (p,u',l,s),g') -> (p',u',l,s') & g2
                               where
                                 g2 = updateFlow (v:vs) cf g'
                                 s' = updAdjList s v cf True
                                 p' = updAdjList p v cf False

-- | Compute the flow from @s@ to @t@ on a graph whose edges are labeled with
--   @(x,y,z)=(max capacity,current flow,residual capacity)@ and all
--   edges are of the form @a\<---->b@. First compute the residual
--   graph, that is, delete those edges whose residual capacity is
--   zero. Then compute the shortest augmenting path from @s@ to @t@,
--   and finally update the flow and residual capacity along that path
--   by using the minimum capacity of that path. Repeat this process
--   until no shortest path from @s@ to @t@ exist.
mfmg :: (DynGraph gr, Num b, Ord b) => gr a (b,b,b) -> Node -> Node -> gr a (b,b,b)
mfmg g s t
  | null augPath = g
  | otherwise    = mfmg (updateFlow augPath minC g) s t
  where
    minC        = minimum (map ((\(_,_,z)->z).snd)(tail augLPath))
    augPath     = map fst augLPath
    LP augLPath = lesp s t gf
    gf          = elfilter (\(_,_,z)->z/=0) g

-- | Compute the flow from s to t on a graph whose edges are labeled with
--   @x@, which is the max capacity and where not all edges need to be
--   of the form a\<---->b. Return the flow as a graph whose edges are
--   labeled with (x,y,z)=(max capacity,current flow,residual
--   capacity) and all edges are of the form a\<---->b
mf :: (DynGraph gr, Num b, Ord b) => gr a b -> Node -> Node -> gr a (b,b,b)
mf g = mfmg (augmentGraph g)

-- | Compute the maximum flow from s to t on a graph whose edges are labeled
--   with x, which is the max capacity and where not all edges need to
--   be of the form a\<---->b. Return the flow as a graph whose edges
--   are labeled with (y,x) = (current flow, max capacity).
maxFlowgraph :: (DynGraph gr, Num b, Ord b) => gr a b -> Node -> Node -> gr a (b,b)
maxFlowgraph g s t = emap (\(u,v,_)->(v,u))
                     . elfilter (\(x,_,_) -> x/=0 )
                     $ mf g s t

-- | Compute the value of a maximumflow
maxFlow :: (DynGraph gr, Num b, Ord b) => gr a b -> Node -> Node -> b
maxFlow g s t = sum (map (fst . edgeLabel) (out (maxFlowgraph g s t) s))

------------------------------------------------------------------------------
-- Some test cases: clr595 is from the CLR textbook, page 595. The value of
-- the maximum flow for s=1 and t=6 (23) coincides with the example but the
-- flow itself is slightly different since the textbook does not compute the
-- shortest augmenting path from s to t, but just any path. However remember
-- that for a given flow graph the maximum flow is not unique.
-- (gr595 is defined in GraphData.hs)
------------------------------------------------------------------------------
