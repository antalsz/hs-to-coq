-- (c) 2000-2005 by Martin Erwig [see file COPYRIGHT]
-- | Minimum-Spanning-Tree Algorithms

module Data.Graph.Inductive.Query.MST (
    msTreeAt,msTree,
    -- * Path in MST
    msPath,
    -- * Types used
    LRTree
) where

import           Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Internal.Heap     as H
import           Data.Graph.Inductive.Internal.RootPath


newEdges :: LPath b -> Context a b -> [H.Heap b (LPath b)]
newEdges (LP p) (_,_,_,s) = map (\(l,v)->H.unit l (LP ((v,l):p))) s

prim :: (Graph gr,Real b) => H.Heap b (LPath b) -> gr a b -> LRTree b
prim h g | H.isEmpty h || isEmpty g = []
prim h g =
    case match v g of
         (Just c,g')  -> p:prim (H.mergeAll (h':newEdges p c)) g'
         (Nothing,g') -> prim h' g'
    where (_,p@(LP ((v,_):_)),h') = H.splitMin h

msTreeAt :: (Graph gr,Real b) => Node -> gr a b -> LRTree b
msTreeAt v = prim (H.unit 0 (LP [(v,0)]))

msTree :: (Graph gr,Real b) => gr a b -> LRTree b
msTree g = msTreeAt v g where ((_,v,_,_),_) = matchAny g

msPath :: LRTree b -> Node -> Node -> Path
msPath t a b = joinPaths (getLPathNodes a t) (getLPathNodes b t)

joinPaths :: Path -> Path -> Path
joinPaths p = joinAt (head p) p

joinAt :: Node -> Path -> Path -> Path
joinAt _ (v:vs) (w:ws) | v==w = joinAt v vs ws
joinAt x p      q             = reverse p++(x:q)
