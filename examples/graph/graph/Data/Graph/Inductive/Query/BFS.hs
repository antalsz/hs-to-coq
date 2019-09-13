-- (c) 2000-2005 by Martin Erwig [see file COPYRIGHT]
-- | Breadth-First Search Algorithms

module Data.Graph.Inductive.Query.BFS(

    -- * BFS Node List
    bfs, bfsn, bfsWith, bfsnWith,

    -- * Node List With Depth Info
    level, leveln,

    -- * BFS Edges
    bfe, bfen,

    -- * BFS Tree
    bft, lbft, RTree,

    -- * Shortest Path (Number of Edges)
    esp, lesp

) where


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Internal.Queue
import Data.Graph.Inductive.Internal.RootPath

-- bfs (node list ordered by distance)
--
bfsnInternal :: (Graph gr) => (Context a b -> c) -> Queue Node -> gr a b -> [c]
bfsnInternal f q g | queueEmpty q || isEmpty g = []
                   | otherwise                 =
       case match v g of
        (Just c, g')  -> f c:bfsnInternal f (queuePutList (suc' c) q') g'
        (Nothing, g') -> bfsnInternal f q' g'
        where (v,q') = queueGet q

bfsnWith :: (Graph gr) => (Context a b -> c) -> [Node] -> gr a b -> [c]
bfsnWith f vs = bfsnInternal f (queuePutList vs mkQueue)

bfsn :: (Graph gr) => [Node] -> gr a b -> [Node]
bfsn = bfsnWith node'

bfsWith :: (Graph gr) => (Context a b -> c) -> Node -> gr a b -> [c]
bfsWith f v = bfsnInternal f (queuePut v mkQueue)

bfs :: (Graph gr) => Node -> gr a b -> [Node]
bfs = bfsWith node'


-- level (extension of bfs giving the depth of each node)
--
level :: (Graph gr) => Node -> gr a b -> [(Node,Int)]
level v = leveln [(v,0)]

suci :: Context a b -> Int -> [(Node, Int)]
suci c i = zip (suc' c) (repeat i)

leveln :: (Graph gr) => [(Node,Int)] -> gr a b -> [(Node,Int)]
leveln []         _             = []
leveln _          g | isEmpty g = []
leveln ((v,j):vs) g = case match v g of
                        (Just c,g')  -> (v,j):leveln (vs++suci c (j+1)) g'
                        (Nothing,g') -> leveln vs g'


-- bfe (breadth first edges)
-- remembers predecessor information
--
bfenInternal :: (Graph gr) => Queue Edge -> gr a b -> [Edge]
bfenInternal q g | queueEmpty q || isEmpty g = []
                 | otherwise                 =
      case match v g of
        (Just c, g')  -> (u,v):bfenInternal (queuePutList (outU c) q') g'
        (Nothing, g') -> bfenInternal q' g'
        where ((u,v),q') = queueGet q

bfen :: (Graph gr) => [Edge] -> gr a b -> [Edge]
bfen vs = bfenInternal (queuePutList vs mkQueue)

bfe :: (Graph gr) => Node -> gr a b -> [Edge]
bfe v = bfen [(v,v)]

outU :: Context a b -> [Edge]
outU c = map toEdge (out' c)


-- bft (breadth first search tree)
-- here: with inward directed trees
--
-- bft :: Node -> gr a b -> IT.InTree Node
-- bft v g = IT.build $ map swap $ bfe v g
--           where swap (x,y) = (y,x)
--
-- sp (shortest path wrt to number of edges)
--
-- sp :: Node -> Node -> gr a b -> [Node]
-- sp s t g = reverse $ IT.rootPath (bft s g) t


-- faster shortest paths
-- here: with root path trees
--
bft :: (Graph gr) => Node -> gr a b -> RTree
bft v = bf (queuePut [v] mkQueue)

bf :: (Graph gr) => Queue Path -> gr a b -> RTree
bf q g | queueEmpty q || isEmpty g = []
       | otherwise                 =
       case match v g of
         (Just c, g')  -> p:bf (queuePutList (map (:p) (suc' c)) q') g'
         (Nothing, g') -> bf q' g'
         where (p@(v:_),q') = queueGet q

esp :: (Graph gr) => Node -> Node -> gr a b -> Path
esp s t = getPath t . bft s


-- lesp is a version of esp that returns labeled paths
-- Note that the label of the first node in a returned path is meaningless;
-- all other nodes are paired with the label of their incoming edge.
--
lbft :: (Graph gr) => Node -> gr a b -> LRTree b
lbft v g = case out g v of
             []         -> [LP []]
             (v',_,l):_ -> lbf (queuePut (LP [(v',l)]) mkQueue) g

lbf :: (Graph gr) => Queue (LPath b) -> gr a b -> LRTree b
lbf q g | queueEmpty q || isEmpty g = []
        | otherwise                 =
       case match v g of
         (Just c, g') ->
             LP p:lbf (queuePutList (map (\v' -> LP (v':p)) (lsuc' c)) q') g'
         (Nothing, g') -> lbf q' g'
         where (LP (p@((v,_):_)),q') = queueGet q

lesp :: (Graph gr) => Node -> Node -> gr a b -> LPath b
lesp s t = getLPath t . lbft s
