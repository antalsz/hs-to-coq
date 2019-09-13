module Data.Graph.Inductive.Query.ArtPoint(
    ap
) where

import Data.Graph.Inductive.Graph


------------------------------------------------------------------------------
-- Tree for storing the DFS numbers and back edges for each node in the graph.
-- Each node in this tree is of the form (v,n,b) where v is the vertex number,
-- n is its DFS number and b is the list of nodes (and their DFS numbers) that
-- lead to back back edges for that vertex v.
------------------------------------------------------------------------------
data DFSTree a = B (a,a,[(a,a)]) [DFSTree a]
     deriving (Eq, Show, Read)

------------------------------------------------------------------------------
-- Tree for storing the DFS and low numbers for each node in the graph.
-- Each node in this tree is of the form (v,n,l) where v is the vertex number,
-- n is its DFS number and l is its low number.
------------------------------------------------------------------------------
data LOWTree a = Brc (a,a,a) [LOWTree a]
     deriving (Eq, Show, Read)

------------------------------------------------------------------------------
-- Finds the back edges for a given node.
------------------------------------------------------------------------------
getBackEdges :: Node -> [[(Node,Int)]] -> [(Node,Int)]
getBackEdges _ [] = []
getBackEdges v ls   = map head (filter (elem (v,0)) (tail ls))

------------------------------------------------------------------------------
-- Builds a DFS tree for a given graph. Each element (v,n,b) in the tree
-- contains: the node number v, the DFS number n, and a list of backedges b.
------------------------------------------------------------------------------
dfsTree :: (Graph gr) => Int -> Node -> [Node] -> [[(Node,Int)]] ->
                       gr a b -> ([DFSTree Int],gr a b,Int)
dfsTree n _ []      _ g             = ([],g,n)
dfsTree n _ _       _ g | isEmpty g = ([],g,n)
dfsTree n u (v:vs) ls g = case match v g of
                            (Nothing, g1) -> dfsTree n u vs ls g1
                            (Just c , g1) -> (B (v,n+1,bck) ts:ts', g3, k)
                             where  bck        = getBackEdges v ls
                                    (ts, g2,m) = dfsTree (n+1) v sc ls' g1
                                    (ts',g3,k) = dfsTree m v vs ls g2
                                    ls'        = ((v,n+1):sc'):ls
                                    sc'        = map (\x->(x,0)) sc
                                    sc         = suc' c

------------------------------------------------------------------------------
-- Finds the minimum between a dfs number and a list of back edges' dfs
-- numbers.
------------------------------------------------------------------------------
minbckEdge :: Int -> [(Node,Int)] -> Int
minbckEdge n [] = n
minbckEdge n bs = min n (minimum (map snd bs))

------------------------------------------------------------------------------
-- Returns the low number for a node in a subtree.
------------------------------------------------------------------------------
getLow :: LOWTree Int -> Int
getLow (Brc (_,_,l) _) = l

------------------------------------------------------------------------------
-- Builds a low tree from a DFS tree. Each element (v,n,low) in the tree
-- contains: the node number v, the DFS number n, and the low number low.
------------------------------------------------------------------------------
lowTree :: DFSTree Int -> LOWTree Int
lowTree (B (v,n,[]  ) [] ) = Brc (v,n,n) []
lowTree (B (v,n,bcks) [] ) = Brc (v,n,minbckEdge n bcks) []
lowTree (B (v,n,bcks) trs) = Brc (v,n,lowv) ts
                             where lowv     = min (minbckEdge n bcks) lowChild
                                   lowChild = minimum (map getLow ts)
                                   ts       = map lowTree trs

------------------------------------------------------------------------------
-- Builds a low tree for a given graph. Each element (v,n,low) in the tree
-- contains: the node number v, the DFS number n, and the low number low.
------------------------------------------------------------------------------
getLowTree :: (Graph gr) => gr a b -> Node -> LOWTree Int
getLowTree g v = lowTree (head dfsf)
                  where (dfsf, _, _) = dfsTree 0 0 [v] [] g

------------------------------------------------------------------------------
-- Tests if a node in a subtree is an articulation point. An non-root node v
-- is an articulation point iff there exists at least one child w of v such
-- that lowNumber(w) >= dfsNumber(v). The root node is an articulation point
-- iff it has two or more children.
------------------------------------------------------------------------------
isap :: LOWTree Int -> Bool
isap (Brc (_,_,_) []) = False
isap (Brc (_,1,_) ts) = length ts > 1
isap (Brc (_,n,_) ts) = not (null ch)
                        where ch = filter ( >=n) (map getLow ts)

------------------------------------------------------------------------------
-- Finds the articulation points by traversing the low tree.
------------------------------------------------------------------------------
arp :: LOWTree Int -> [Node]
arp (Brc (v,1,_) ts) | length ts > 1         = v:concatMap arp ts
                     | otherwise             =   concatMap arp ts
arp (Brc (v,n,l) ts) | isap (Brc (v,n,l) ts) = v:concatMap arp ts
                     | otherwise             =   concatMap arp ts

------------------------------------------------------------------------------
-- Finds the articulation points of a graph starting at a given node.
------------------------------------------------------------------------------
artpoints :: (Graph gr) => gr a b -> Node -> [Node]
artpoints g v = arp (getLowTree g v)

{-|
   Finds the articulation points for a connected undirected graph,
   by using the low numbers criteria:

   a) The root node is an articulation point iff it has two or more children.

   b) An non-root node v is an articulation point iff there exists at least
      one child w of v such that lowNumber(w) >= dfsNumber(v).
-}
ap :: (Graph gr) => gr a b -> [Node]
ap g = artpoints g v where ((_,v,_,_),_) = matchAny g
