-- Find Dominators of a graph.
--
-- Author: Bertram Felgenhauer <int-e@gmx.de>
--
-- Implementation based on
-- Keith D. Cooper, Timothy J. Harvey, Ken Kennedy,
-- "A Simple, Fast Dominance Algorithm",
-- (http://citeseer.ist.psu.edu/cooper01simple.html)

module Data.Graph.Inductive.Query.Dominators (
    dom,
    iDom
) where

import           Data.Array
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.Query.DFS
import           Data.IntMap                    (IntMap)
import qualified Data.IntMap                    as I
import           Data.Tree                      (Tree (..))
import qualified Data.Tree                      as T

{-# ANN iDom "HLint: ignore Use ***" #-}
-- | return immediate dominators for each node of a graph, given a root
iDom :: (Graph gr) => gr a b -> Node -> [(Node,Node)]
iDom g root = let (result, toNode, _) = idomWork g root
              in  map (\(a, b) -> (toNode ! a, toNode ! b)) (assocs result)

-- | return the set of dominators of the nodes of a graph, given a root
dom :: (Graph gr) => gr a b -> Node -> [(Node,[Node])]
dom g root = let
    (iD, toNode, fromNode) = idomWork g root
    dom' = getDom toNode iD
    nodes' = nodes g
    rest = I.keys (I.filter (-1 ==) fromNode)
  in
    [(toNode ! i, dom' ! i) | i <- range (bounds dom')] ++
    [(n, nodes') | n <- rest]

-- internal node type
type Node' = Int
-- array containing the immediate dominator of each node, or an approximation
-- thereof. the dominance set of a node can be found by taking the union of
-- {node} and the dominance set of its immediate dominator.
type IDom = Array Node' Node'
-- array containing the list of predecessors of each node
type Preds = Array Node' [Node']
-- arrays for translating internal nodes back to graph nodes and back
type ToNode = Array Node' Node
type FromNode = IntMap Node'

idomWork :: (Graph gr) => gr a b -> Node -> (IDom, ToNode, FromNode)
idomWork g root = let
    -- use depth first tree from root do build the first approximation
    trees@(~[tree]) = dff [root] g
    -- relabel the tree so that paths from the root have increasing nodes
    (s, ntree) = numberTree 0 tree
    -- the approximation iDom0 just maps each node to its parent
    iD0 = array (1, s-1) (tail $ treeEdges (-1) ntree)
    -- fromNode translates graph nodes to relabeled (internal) nodes
    fromNode = I.unionWith const (I.fromList (zip (T.flatten tree) (T.flatten ntree))) (I.fromList (zip (nodes g) (repeat (-1))))
    -- toNode translates internal nodes to graph nodes
    toNode = array (0, s-1) (zip (T.flatten ntree) (T.flatten tree))
    preds = array (1, s-1) [(i, filter (/= -1) (map (fromNode I.!)
                            (pre g (toNode ! i)))) | i <- [1..s-1]]
    -- iteratively improve the approximation to find iDom.
    iD = fixEq (refineIDom preds) iD0
  in
    if null trees then error "Dominators.idomWork: root not in graph"
                  else (iD, toNode, fromNode)

-- for each node in iDom, find the intersection of all its predecessor's
-- dominating sets, and update iDom accordingly.
refineIDom :: Preds -> IDom -> IDom
refineIDom preds iD = fmap (foldl1 (intersect iD)) preds

-- find the intersection of the two given dominance sets.
intersect :: IDom -> Node' -> Node' -> Node'
intersect iD a b = case a `compare` b of
    LT -> intersect iD a (iD ! b)
    EQ -> a
    GT -> intersect iD (iD ! a) b

-- convert an IDom to dominance sets. we translate to graph nodes here
-- because mapping later would be more expensive and lose sharing.
getDom :: ToNode -> IDom -> Array Node' [Node]
getDom toNode iD = let
    res = array (0, snd (bounds iD)) ((0, [toNode ! 0]) :
          [(i, toNode ! i : res ! (iD ! i)) | i <- range (bounds iD)])
  in
    res

-- relabel tree, labeling vertices with consecutive numbers in depth first order
numberTree :: Node' -> Tree a -> (Node', Tree Node')
numberTree n (Node _ ts) = let (n', ts') = numberForest (n+1) ts
                           in  (n', Node n ts')

-- same as numberTree, for forests.
numberForest :: Node' -> [Tree a] -> (Node', [Tree Node'])
numberForest n []     = (n, [])
numberForest n (t:ts) = let (n', t')   = numberTree n t
                            (n'', ts') = numberForest n' ts
                        in  (n'', t':ts')

-- return the edges of the tree, with an added dummy root node.
treeEdges :: a -> Tree a -> [(a,a)]
treeEdges a (Node b ts) = (b,a) : concatMap (treeEdges b) ts

-- find a fixed point of f, iteratively
fixEq :: (Eq a) => (a -> a) -> a -> a
fixEq f v | v' == v   = v
          | otherwise = fixEq f v'
    where v' = f v

{-
:m +Data.Graph.Inductive
let g0 = mkGraph [(i,()) | i <- [0..4]] [(a,b,()) | (a,b) <- [(0,1),(1,2),(0,3),(3,2),(4,0)]] :: Gr () ()
let g1 = mkGraph [(i,()) | i <- [0..4]] [(a,b,()) | (a,b) <- [(0,1),(1,2),(2,3),(1,3),(3,4)]] :: Gr () ()
let g2,g3,g4 :: Int -> Gr () (); g2 n = mkGraph [(i,()) | i <- [0..n-1]] ([(a,a+1,()) | a <- [0..n-2]] ++ [(a,a+2,()) | a <- [0..n-3]]); g3 n =mkGraph [(i,()) | i <- [0..n-1]] ([(a,a+2,()) | a <- [0..n-3]] ++ [(a,a+1,()) | a <- [0..n-2]]); g4 n =mkGraph [(i,()) | i <- [0..n-1]] ([(a+2,a,()) | a <- [0..n-3]] ++ [(a+1,a,()) | a <- [0..n-2]])
:m -Data.Graph.Inductive
-}
