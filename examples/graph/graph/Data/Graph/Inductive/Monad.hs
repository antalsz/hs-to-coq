{-# LANGUAGE CPP, MultiParamTypeClasses #-}

-- (c) 2002 by Martin Erwig [see file COPYRIGHT]
-- | Monadic Graphs
module Data.Graph.Inductive.Monad(
    -- * Classes
    GraphM(..),
    -- * Operations
    -- ** Graph Folds and Maps
    ufoldM,
    -- ** Graph Projection
    nodesM,edgesM,newNodesM,
    -- ** Graph Construction and Destruction
    delNodeM,delNodesM,
    mkUGraphM,
    -- ** Graph Inspection
    contextM,labM
) where


import Data.Graph.Inductive.Graph
#if MIN_VERSION_base(4,12,0)
import Control.Monad.Fail
import Prelude hiding (fail)
#endif

{-# ANN module "HLint: ignore Redundant lambda" #-}

----------------------------------------------------------------------
-- MONADIC GRAPH CLASS
----------------------------------------------------------------------

--
-- Currently, we define just one monadic graph class:
--
--   GraphM:    static, decomposable graphs
--              static means that a graph itself cannot be changed
--
-- Later we might also define DynGraphM for dynamic, extensible graphs
--



-- Monadic Graph
--
class
#if MIN_VERSION_base(4,12,0)
 (MonadFail m)
#else
 (Monad m)
#endif
  => GraphM m gr where
  {-# MINIMAL emptyM, isEmptyM, matchM, mkGraphM, labNodesM #-}

  emptyM     :: m (gr a b)

  isEmptyM   :: m (gr a b) -> m Bool

  matchM     :: Node -> m (gr a b) -> m (Decomp gr a b)

  mkGraphM   :: [LNode a] -> [LEdge b] -> m (gr a b)

  labNodesM  :: m (gr a b) -> m [LNode a]

  matchAnyM  :: m (gr a b) -> m (GDecomp gr a b)
  matchAnyM g = do vs <- labNodesM g
                   case vs of
                     []      -> fail "Match Exception, Empty Graph"
                     (v,_):_ -> do (Just c,g') <- matchM v g
                                   return (c,g')

  noNodesM   :: m (gr a b) -> m Int
  noNodesM = labNodesM >>. length

  nodeRangeM :: m (gr a b) -> m (Node,Node)
  nodeRangeM g = do isE <- isEmptyM g
                    if isE
                       then fail "nodeRangeM of empty graph"
                       else do vs <- nodesM g
                               return (minimum vs,maximum vs)

  labEdgesM  :: m (gr a b) -> m [LEdge b]
  labEdgesM = ufoldM (\(p,v,_,s)->((map (i v) p ++ map (o v) s)++)) []
    where
      o v = \(l,w)->(v,w,l)
      i v = \(l,w)->(w,v,l)


-- composing a monadic function with a non-monadic one
--
(>>.) :: (Monad m) => (m a -> m b) -> (b -> c) -> m a -> m c
f >>. g = (>>= return . g) . f


----------------------------------------------------------------------
-- DERIVED GRAPH OPERATIONS
----------------------------------------------------------------------

-- graph folds and maps
--

-- | graph fold
ufoldM :: (GraphM m gr) => (Context a b -> c -> c) -> c -> m (gr a b) -> m c
ufoldM f u g = do b <- isEmptyM g
                  if b then return u
                       else do (c,g') <- matchAnyM g
                               x <- ufoldM f u (return g')
                               return (f c x)


-- (additional) graph projection
-- [noNodes, nodeRange, labNodes, labEdges are defined in class Graph]
--
nodesM :: (GraphM m gr) => m (gr a b) -> m [Node]
nodesM = labNodesM >>. map fst

edgesM :: (GraphM m gr) => m (gr a b) -> m [Edge]
edgesM =  labEdgesM >>. map (\(v,w,_)->(v,w))

newNodesM :: (GraphM m gr) => Int -> m (gr a b) -> m [Node]
newNodesM i g = do isE <- isEmptyM g
                   if isE
                      then return [0..i-1]
                      else do (_,n) <- nodeRangeM g
                              return [n+1..n+i]


-- graph construction & destruction
--
delNodeM :: (GraphM m gr) => Node -> m (gr a b) -> m (gr a b)
delNodeM v = delNodesM [v]

delNodesM :: (GraphM m gr) => [Node] -> m (gr a b) -> m (gr a b)
delNodesM []     g = g
delNodesM (v:vs) g = do (_,g') <- matchM v g
                        delNodesM vs (return g')

mkUGraphM :: (GraphM m gr) => [Node] -> [Edge] -> m (gr () ())
mkUGraphM vs es = mkGraphM (labUNodes vs) (labUEdges es)

labUEdges :: [Edge] -> [LEdge ()]
labUEdges = map (`toLEdge` ())

labUNodes :: [Node] -> [LNode ()]
labUNodes = map (\v->(v,()))


-- graph inspection (for a particular node)
--
onMatch :: (GraphM m gr) => (Context a b -> c) -> c -> m (gr a b) -> Node -> m c
onMatch f u g v = do (x,_) <- matchM v g
                     return (case x of {Nothing -> u; Just c -> f c})

contextM :: (GraphM m gr) => m (gr a b) -> Node -> m (Context a b)
contextM g v = onMatch id (error ("Match Exception, Node: "++show v)) g v

labM :: (GraphM m gr) => m (gr a b) -> Node -> m (Maybe a)
labM = onMatch (Just . lab') Nothing

{-
neighbors :: (GraphM m gr) => m (gr a b) -> Node -> [Node]
neighbors = (\(p,_,_,s) -> map snd (p++s)) .: context

suc :: (GraphM m gr) => m (gr a b) -> Node -> [Node]
suc = map snd .: context4

pre :: (GraphM m gr) => m (gr a b) -> Node -> [Node]
pre = map snd .: context1

lsuc :: (GraphM m gr) => m (gr a b) -> Node -> [(Node,b)]
lsuc = map flip2 .: context4

lpre :: (GraphM m gr) => m (gr a b) -> Node -> [(Node,b)]
lpre = map flip2 .: context1

out :: (GraphM m gr) => m (gr a b) -> Node -> [LEdge b]
out g v = map (\(l,w)->(v,w,l)) (context4 g v)

inn :: (GraphM m gr) => m (gr a b) -> Node -> [LEdge b]
inn g v = map (\(l,w)->(w,v,l)) (context1 g v)

outdeg :: (GraphM m gr) => m (gr a b) -> Node -> Int
outdeg = length .: context4

indeg :: (GraphM m gr) => m (gr a b) -> Node -> Int
indeg  = length .: context1

deg :: (GraphM m gr) => m (gr a b) -> Node -> Int
deg = (\(p,_,_,s) -> length p+length s) .: context
--

-- -- context inspection
-- --
-- node' :: Context a b -> Node
-- node' (_,v,_,_) = v
--
-- lab' :: Context a b -> a
-- lab' (_,_,l,_) = l
--
-- labNode' :: Context a b -> LNode a
-- labNode' (_,v,l,_) = (v,l)
--
-- neighbors' :: Context a b -> [Node]
-- neighbors' (p,_,_,s) = map snd p++map snd s
--
-- suc' :: Context a b -> [Node]
-- suc' (_,_,_,s) = map snd s
--
-- pre' :: Context a b -> [Node]
-- pre' (p,_,_,_) = map snd p
--
-- lpre' :: Context a b -> [(Node,b)]
-- lpre' (p,_,_,_) = map flip2 p
--
-- lsuc' :: Context a b -> [(Node,b)]
-- lsuc' (_,_,_,s) = map flip2 s
--
-- out' :: Context a b -> [LEdge b]
-- out' (_,v,_,s) = map (\(l,w)->(v,w,l)) s
--
-- inn' :: Context a b -> [LEdge b]
-- inn' (p,v,_,_) = map (\(l,w)->(w,v,l)) p
--
-- outdeg' :: Context a b -> Int
-- outdeg' (_,_,_,s) = length s
--
-- indeg' :: Context a b -> Int
-- indeg' (p,_,_,_) = length p
--
-- deg' :: Context a b -> Int
-- deg' (p,_,_,s) = length p+length s


-- graph equality
--
nodeComp :: (Eq b) => LNode b -> LNode b -> Ordering
nodeComp n@(v,a) n'@(w,b) | n == n'   = EQ
                          | v<w       = LT
                          | otherwise = GT

slabNodes :: (Eq a,Graph gr) => m (gr a b) -> [LNode a]
slabNodes = sortBy nodeComp . labNodes

edgeComp :: (Eq b) => LEdge b -> LEdge b -> Ordering
edgeComp e@(v,w,a) e'@(x,y,b) | e == e'              = EQ
                              | v<x || (v==x && w<y) = LT
                              | otherwise            = GT

slabEdges :: (Eq b,Graph gr) => m (gr a b) -> [LEdge b]
slabEdges = sortBy edgeComp . labEdges

instance (Eq a,Eq b,Graph gr) => Eq (m (gr a b)) where
  g == g' = slabNodes g == slabNodes g' && slabEdges g == slabEdges g'


-}
