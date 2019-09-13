-- (c) 2000 - 2005 by Martin Erwig [see file COPYRIGHT]

-- | Depth-first search algorithms.
--
-- Names consist of:
--
--   1. An optional direction parameter, specifying which nodes to visit next.
--
--      [@u@] undirectional: ignore edge direction
--      [@r@] reversed: walk edges in reverse
--      [@x@] user defined: speciy which paths to follow
--
--   2. "df" for depth-first
--   3. A structure parameter, specifying the type of the result.
--
--       [@s@] Flat list of results
--       [@f@] Structured 'Tree' of results
--
--   4. An optional \"With\", which instead of putting the found nodes directly
--      into the result, adds the result of a computation on them into it.
--   5. An optional prime character, in which case all nodes of the graph will
--      be visited, instead of a user-given subset.
module Data.Graph.Inductive.Query.DFS (

    CFun,

    -- * Standard
    dfs, dfs', dff, dff',
    dfsWith,  dfsWith', dffWith, dffWith',
    xdfsWith, xdfWith, xdffWith,

    -- * Undirected
    udfs, udfs', udff, udff',
    udffWith, udffWith',

    -- * Reversed
    rdff, rdff', rdfs, rdfs',
    rdffWith, rdffWith',

    -- * Applications of depth first search/forest
    topsort, topsort', scc, reachable,

    -- * Applications of undirected depth first search/forest
    components, noComponents, isConnected, condensation

) where

import Data.Graph.Inductive.Basic
import Data.Graph.Inductive.Graph
import Data.Tree
import qualified Data.Map as Map
import Control.Monad (liftM2)
import Data.Tuple (swap)


-- | Many functions take a list of nodes to visit as an explicit argument.
--   fixNodes is a convenience function that adds all the nodes present in a
--   graph as that list.
fixNodes :: (Graph gr) => ([Node] -> gr a b -> c) -> gr a b -> c
fixNodes f g = f (nodes g) g


type CFun a b c = Context a b -> c

-- | Most general DFS algorithm to create a list of results. The other
--   list-returning functions such as 'dfs' are all defined in terms of this
--   one.
--
-- @
-- 'xdfsWith' d f vs = 'preorderF' . 'xdffWith' d f vs
-- @
xdfsWith :: (Graph gr)
    => CFun a b [Node] -- ^ Mapping from a node to its neighbours to be visited
                       --   as well. 'suc'' for example makes 'xdfsWith'
                       --   traverse the graph following the edge directions,
                       --   while 'pre'' means reversed directions.
    -> CFun a b c      -- ^ Mapping from the 'Context' of a node to a result
                       --   value.
    -> [Node]          -- ^ Nodes to be visited.
    -> gr a b
    -> [c]
xdfsWith _ _ []     _             = []
xdfsWith _ _ _      g | isEmpty g = []
xdfsWith d f (v:vs) g = case match v g of
                         (Just c,g')  -> f c:xdfsWith d f (d c++vs) g'
                         (Nothing,g') -> xdfsWith d f vs g'


-- | Depth-first search.
dfs :: (Graph gr) => [Node] -> gr a b -> [Node]
dfs = dfsWith node'

dfsWith :: (Graph gr) => CFun a b c -> [Node] -> gr a b -> [c]
dfsWith = xdfsWith suc'

dfsWith' :: (Graph gr) => CFun a b c -> gr a b -> [c]
dfsWith' f = fixNodes (dfsWith f)

dfs' :: (Graph gr) => gr a b -> [Node]
dfs' = dfsWith' node'


-- | Undirected depth-first search, obtained by following edges regardless
--   of their direction.
udfs :: (Graph gr) => [Node] -> gr a b -> [Node]
udfs = xdfsWith neighbors' node'

udfs' :: (Graph gr) => gr a b -> [Node]
udfs' = fixNodes udfs


-- | Reverse depth-first search, obtained by following predecessors.
rdfs :: (Graph gr) => [Node] -> gr a b -> [Node]
rdfs = xdfsWith pre' node'

rdfs' :: (Graph gr) => gr a b -> [Node]
rdfs' = fixNodes rdfs


-- | Most general DFS algorithm to create a forest of results, otherwise very
--   similar to 'xdfsWith'. The other forest-returning functions such as 'dff'
--   are all defined in terms of this one.
xdfWith :: (Graph gr)
    => CFun a b [Node]
    -> CFun a b c
    -> [Node]
    -> gr a b
    -> ([Tree c],gr a b)
xdfWith _ _ []     g             = ([],g)
xdfWith _ _ _      g | isEmpty g = ([],g)
xdfWith d f (v:vs) g = case match v g of
                        (Nothing,g1) -> xdfWith d f vs g1
                        (Just c,g1)  -> (Node (f c) ts:ts',g3)
                                 where (ts,g2)  = xdfWith d f (d c) g1
                                       (ts',g3) = xdfWith d f vs g2

-- | Discard the graph part of the result of 'xdfWith'.
--
-- @
-- xdffWith d f vs g = fst (xdfWith d f vs g)
-- @
xdffWith :: (Graph gr)
    => CFun a b [Node]
    -> CFun a b c
    -> [Node]
    -> gr a b
    -> [Tree c]
xdffWith d f vs g = fst (xdfWith d f vs g)



-- | Directed depth-first forest.
dff :: (Graph gr) => [Node] -> gr a b -> [Tree Node]
dff = dffWith node'

dffWith :: (Graph gr) => CFun a b c -> [Node] -> gr a b -> [Tree c]
dffWith = xdffWith suc'

dffWith' :: (Graph gr) => CFun a b c -> gr a b -> [Tree c]
dffWith' f = fixNodes (dffWith f)

dff' :: (Graph gr) => gr a b -> [Tree Node]
dff' = dffWith' node'



-- | Undirected depth-first forest, obtained by following edges regardless
--   of their direction.
udff :: (Graph gr) => [Node] -> gr a b -> [Tree Node]
udff = udffWith node'

udffWith :: (Graph gr) => CFun a b c -> [Node] -> gr a b -> [Tree c]
udffWith = xdffWith neighbors'

udffWith' :: (Graph gr) => CFun a b c -> gr a b -> [Tree c]
udffWith' f = fixNodes (udffWith f)

udff' :: (Graph gr) => gr a b -> [Tree Node]
udff' = udffWith' node'


-- | Reverse depth-first forest, obtained by following predecessors.
rdff :: (Graph gr) => [Node] -> gr a b -> [Tree Node]
rdff = rdffWith node'

rdffWith :: (Graph gr) => CFun a b c -> [Node] -> gr a b -> [Tree c]
rdffWith = xdffWith pre'

rdffWith' :: (Graph gr) => CFun a b c -> gr a b -> [Tree c]
rdffWith' f = fixNodes (rdffWith f)

rdff' :: (Graph gr) => gr a b -> [Tree Node]
rdff' = rdffWith' node'


----------------------------------------------------------------------
-- ALGORITHMS BASED ON DFS
----------------------------------------------------------------------

-- | Collection of connected components
components :: (Graph gr) => gr a b -> [[Node]]
components = map preorder . udff'

-- | Number of connected components
noComponents :: (Graph gr) => gr a b -> Int
noComponents = length . components

-- | Is the graph connected?
isConnected :: (Graph gr) => gr a b -> Bool
isConnected = (==1) . noComponents

-- | Flatten a 'Tree' in reverse order
postflatten :: Tree a -> [a]
postflatten (Node v ts) = postflattenF ts ++ [v]

-- | Flatten a forest in reverse order
postflattenF :: [Tree a] -> [a]
postflattenF = concatMap postflatten

-- | <http://en.wikipedia.org/wiki/Topological_sorting Topological sorting>,
--   i.e. a list of 'Node's so that if there's an edge between a source and a
--   target node, the source appears earlier in the result.
topsort :: (Graph gr) => gr a b -> [Node]
topsort = reverse . postflattenF . dff'

-- | 'topsort', returning only the labels of the nodes.
topsort' :: (Graph gr) => gr a b -> [a]
topsort' = reverse . postorderF . dffWith' lab'

-- | Collection of strongly connected components
scc :: (Graph gr) => gr a b -> [[Node]]
scc g = map preorder (rdff (topsort g) g)

-- | Collection of nodes reachable from a starting point.
reachable :: (Graph gr) => Node -> gr a b -> [Node]
reachable v g = preorderF (dff [v] g)

-- | The condensation of the given graph, i.e., the graph of its
-- strongly connected components.
condensation :: Graph gr => gr a b -> gr [Node] ()
condensation gr = mkGraph vs es
  where
    sccs = scc gr
    vs = zip [1..] sccs
    vMap = Map.fromList $ map swap vs

    getN = (vMap Map.!)
    es = [ (getN c1, getN c2, ()) | c1 <- sccs, c2 <- sccs
                                  , (c1 /= c2) && any (hasEdge gr) (liftM2 (,) c1 c2) ]
