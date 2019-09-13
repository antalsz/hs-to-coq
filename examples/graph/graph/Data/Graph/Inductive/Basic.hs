-- (c) 1999 - 2002 by Martin Erwig [see file COPYRIGHT]
-- | Basic Graph Algorithms
module Data.Graph.Inductive.Basic
(
    -- * Graph Operations
    grev,
    undir,unlab,
    gsel, gfold,
    -- * Filter Operations
    efilter,elfilter,
    -- * Predicates and Classifications
    hasLoop,isSimple,
    -- * Tree Operations
    postorder, postorderF, preorder, preorderF
)
where


import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Internal.Thread (Collect, Split, SplitM, threadList,
                                             threadMaybe)

import Data.List (nub)
import Data.Tree

-- | Reverse the direction of all edges.
grev :: (DynGraph gr) => gr a b -> gr a b
grev = gmap (\(p,v,l,s)->(s,v,l,p))

-- | Make the graph undirected, i.e. for every edge from A to B, there
-- exists an edge from B to A.
undir :: (Eq b,DynGraph gr) => gr a b -> gr a b
undir = gmap (\(p,v,l,s)->let ps = nub (p++s) in (ps,v,l,ps))
-- this version of undir considers edge lables and keeps edges with
-- different labels, an alternative is the definition below:
--   undir = gmap (\(p,v,l,s)->
--           let ps = nubBy (\x y->snd x==snd y) (p++s) in (ps,v,l,ps))

-- | Remove all labels.
unlab :: (DynGraph gr) => gr a b -> gr () ()
unlab = gmap (\(p,v,_,s)->(unlabAdj p,v,(),unlabAdj s))
        where unlabAdj = map (\(_,v)->((),v))
-- alternative:
--    unlab = nmap (\_->()) . emap (\_->())

-- | Return all 'Context's for which the given function returns 'True'.
gsel :: (Graph gr) => (Context a b -> Bool) -> gr a b -> [Context a b]
gsel p = ufold (\c cs->if p c then c:cs else cs) []


-- filter operations
--
-- efilter  : filter based on edge property
-- elfilter : filter based on edge label property
--

-- | Filter based on edge property.
efilter :: (DynGraph gr) => (LEdge b -> Bool) -> gr a b -> gr a b
efilter f = ufold cfilter empty
            where cfilter (p,v,l,s) g = (p',v,l,s') & g
                   where p' = filter (\(b,u)->f (u,v,b)) p
                         s' = filter (\(b,w)->f (v,w,b)) s

-- | Filter based on edge label property.
elfilter :: (DynGraph gr) => (b -> Bool) -> gr a b -> gr a b
elfilter f = efilter (\(_,_,b)->f b)


-- some predicates and classifications
--

-- | 'True' if the graph has any edges of the form (A, A).
hasLoop :: (Graph gr) => gr a b -> Bool
hasLoop = not . null . gsel (\c->node' c `elem` suc' c)

-- | The inverse of 'hasLoop'.
isSimple :: (Graph gr) => gr a b -> Bool
isSimple = not . hasLoop

threadGraph :: (Graph gr) => (Context a b -> r -> t)
               -> Split (gr a b) (Context a b) r -> SplitM (gr a b) Node t
threadGraph f c = threadMaybe f c match

-- gfold1 f d b u = threadGraph (\c->d (labNode' c)) (\c->gfoldn f d b u (f c))
gfold1 :: (Graph gr) => (Context a b -> [Node]) -> (Context a b -> r -> t)
          -> Collect (Maybe t) r -> SplitM (gr a b) Node t
gfold1 f d b = threadGraph d (gfoldn f d b . f)

gfoldn :: (Graph gr) => (Context a b -> [Node]) -> (Context a b -> r -> t)
          -> Collect (Maybe t) r -> [Node] -> gr a b -> (r, gr a b)
gfoldn f d b = threadList b (gfold1 f d b)

-- gfold :: ((Context a b) -> [Node]) -> ((Node,a) -> c -> d) ->
--          (Maybe d -> c -> c) -> c -> [Node] -> Graph a b -> c
-- gfold f d b u l g = fst (gfoldn f d b u l g)

-- type Dir a b    = (Context a b) -> [Node]  -- direction of fold
-- type Dagg a b c = (Node,a) -> b -> c       -- depth aggregation
-- type Bagg a b   = (Maybe a -> b -> b,b)    -- breadth/level aggregation
--
-- gfold :: (Dir a b) -> (Dagg a c d) -> (Bagg d c) -> [Node] -> Graph a b -> c
-- gfold f d (b,u) l g = fst (gfoldn f d b u l g)

-- | Directed graph fold.
gfold :: (Graph gr) =>   (Context a b -> [Node])    -- ^ direction of fold
        -> (Context a b -> c -> d)    -- ^ depth aggregation
        -> (Maybe d -> c -> c, c)      -- ^ breadth\/level aggregation
        -> [Node]
        -> gr a b
        -> c
gfold f d b l g = fst (gfoldn f d b l g)

-- not finished yet ...
--
-- undirBy :: (b -> b -> b) -> Graph a b -> Graph a b
-- undirBy = gmap (\(p,v,l,s)->let ps = nub (p++s) in (ps,v,l,ps))

-- | Flatten a 'Tree', returning the elements in post-order.
postorder :: Tree a -> [a]
postorder (Node v ts) = postorderF ts ++ [v]

-- | Flatten multiple 'Tree's in post-order.
postorderF :: [Tree a] -> [a]
postorderF = concatMap postorder

-- | Flatten a 'Tree', returning the elements in pre-order.  Equivalent to
--'flatten' in 'Data.Tree'.
preorder :: Tree a -> [a]
preorder = flatten

-- | Flatten multiple 'Tree's in pre-order.
preorderF :: [Tree a] -> [a]
preorderF = concatMap preorder
