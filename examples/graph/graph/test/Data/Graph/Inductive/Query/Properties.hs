{-# LANGUAGE CPP, FlexibleContexts #-}

{- |
   Module      : Data.Graph.Inductive.Query.Properties
   Description : Properties for Query modules
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : BSD3
   Maintainer  : Ivan.Miljenovic@gmail.com

Rather than having an individual module of properties for each
`Data.Graph.Inductive.Query.*` module, this combines all such
properties and tests into one module.

 -}
module Data.Graph.Inductive.Query.Properties where

import Data.Graph.Inductive.Arbitrary
import Data.Graph.Inductive.Example      (clr595, vor)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Proxy
import Data.Graph.Inductive.Query

import Test.Hspec      (Spec, describe, it, shouldBe, shouldMatchList,
                        shouldSatisfy)
import Test.QuickCheck

import           Control.Arrow (second)
import           Data.List     (delete, sort, unfoldr, group, (\\))
import           Data.Maybe    (fromJust, isJust, isNothing)
import qualified Data.Set      as S

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<*>))
#endif

{-# ANN module "HLint: ignore Use camelCase" #-}

-- -----------------------------------------------------------------------------
-- Articulation Points

-- | Deleting the articulation points should increase the number of
--   components.
test_ap :: (ArbGraph gr) => Proxy (gr a b) -> Undirected gr a b -> Property
test_ap _ ug = not (isEmpty g) ==>
                 null points || noComponents (delNodes points g) > noComponents g
  where
    g = toBaseGraph ug

    points = ap g

-- -----------------------------------------------------------------------------
-- BCC

-- | Test that the bi-connected components are indeed composed solely
--   from the original graph (and comprise the entire original graph).
test_bcc :: (ArbGraph gr, Ord b) => Proxy (gr a b) -> UConnected gr a b -> Bool
test_bcc _ cg = sort (concatMap labEdges bgs) == sort (labEdges g)
                                    -- Don't test labNodes as a node
                                    -- may be repeated in multiple
                                    -- bi-connected components.
  where
    g = connGraph cg

    bgs = bcc g

-- -----------------------------------------------------------------------------
-- BFS

test_bfs :: (ArbGraph gr) => Proxy (gr a b) -> UConnected gr a b -> Bool
test_bfs _ cg = sort (bfs (connNode cg) g) == sort (nodes g)
  where
    g = connGraph cg

test_level :: (ArbGraph gr) => Proxy (gr a b) -> UConnected gr a b -> Bool
test_level _ cg = sort expect == sort (level cn g)
  where
    g = connGraph cg

    cn = connNode cg

    vs = delete cn (nodes g)

    expect = (cn,0) : map (flip (,) 1) vs

-- esp tested as part of test_sp

-- -----------------------------------------------------------------------------
-- DFS

-- TODO: flesh out

-- | The 'components' function should never return an empty list, and
--   none of its sub-lists should be empty (unless the graph is
--   empty).  All nodes in the graph should be in precisely one of the
--   components.
test_components :: (ArbGraph gr) => Proxy (gr a b) -> UConnected gr a b -> Bool
test_components _ cg = all (not . null) cs && sort (concat cs) == sort (nodes g)
  where
    g = connGraph cg

    cs = components g

-- | The strongly connected components should be a partitioning of the
--   nodes of a graph.
test_scc :: (Graph gr) => Proxy (gr a b) -> gr a b -> Bool
test_scc _ g = sort (concat (scc g)) == sort (nodes g)

-- | Every node in an undirected connected graph should be reachable.
test_reachable :: (ArbGraph gr) => Proxy (gr a b) -> UConnected gr a b -> Property
test_reachable _ cg = not (isEmpty g) ==> sort (reachable v g) == sort (nodes g)
  where
    g = connGraph cg

    v = node' . fst . matchAny $ g

-- | The nodes of the condensation should be exactly the connected
-- components, and the edges of the condensation should correspond
-- exactly to the edges between the connected components.
test_condensation :: (Graph gr) => Proxy (gr a b) -> gr a b -> Bool
test_condensation _ g = sort sccs == sort (map snd $ labNodes cdg)
                        && and [ or [ hasEdge g (v,w) == hasEdge cdg (cv,cw)
                                    | v <- sccv, w <- sccw ]
                               | (cv,sccv) <- labNodes cdg
                               , (cw,sccw) <- labNodes cdg
                               , cv /= cw
                               ]
  where
    sccs = scc g
    cdg = condensation g

-- -----------------------------------------------------------------------------
-- Dominators

test_dom :: Spec
test_dom = it "dom" $
  sortIt (dom domGraph 1) `shouldMatchList` [ (1, [1])
                                            , (2, [1,2])
                                            , (3, [1,2,3])
                                            , (4, [1,2,4])
                                            , (5, [1,2,5])
                                            , (6, [1,2,6])
                                            ]
  where
    sortIt = map (second sort)

test_iDom :: Spec
test_iDom = it "iDom" $
  iDom domGraph 1 `shouldMatchList` [(2,1),(3,2),(4,2),(5,2),(6,2)]

-- Taken from <https://en.wikipedia.org/wiki/Dominator_%28graph_theory%29>
domGraph :: Gr () ()
domGraph = mkUGraph [1..6]
                    [ (1,2)
                    , (2,3)
                    , (2,4)
                    , (2,6)
                    , (3,5)
                    , (4,5)
                    , (5,2)
                    ]

-- -----------------------------------------------------------------------------
-- GVD

test_voronoiSet :: Spec
test_voronoiSet = describe "voronoiSet" $ do
  describe "inwards" $ do
    it "with root node" (voronoiSet 4 vd `shouldMatchList` [1,2,4])
    it "other node"     (voronoiSet 1 vd `shouldSatisfy`   null)
  describe "outwards" $ do
    it "with root node" (voronoiSet 4 vd0 `shouldMatchList` [2,4,6,7])
    it "other node"     (voronoiSet 1 vd0 `shouldSatisfy`   null)

test_nearestNode :: Spec
test_nearestNode = describe "nearestNode" $ do
  describe "inwards" $ do
    it "reachable"   (nearestNode 6 vd `shouldBe` Just 5)
    it "unreachable" (nearestNode 7 vd `shouldBe` Nothing)
  describe "outwards" $ do
    it "reachable"   (nearestNode 6 vd0 `shouldBe` Just 4)
    it "unreachable" (nearestNode 1 vd0 `shouldBe` Nothing)

test_nearestDist :: Spec
test_nearestDist = describe "nearestDist" $ do
  describe "inwards" $ do
    it "root"        (nearestDist 4 vd `shouldBe` Just 0)
    it "reachable"   (nearestDist 1 vd `shouldBe` Just 3)
    it "unreachable" (nearestDist 7 vd `shouldBe` Nothing)
  describe "outwards" $ do
    it "root"        (nearestDist 5 vd0 `shouldBe` Just 0)
    it "reachable"   (nearestDist 7 vd0 `shouldBe` Just 4)
    it "unreachable" (nearestDist 1 vd0 `shouldBe` Nothing)

test_nearestPath :: Spec
test_nearestPath = describe "nearestPath" $ do
  describe "inwards" $ do
    it "reachable"   (nearestPath 1 vd `shouldBe` Just [1,4])
    it "unreachable" (nearestPath 7 vd `shouldBe` Nothing)
  describe "outwards" $ do
    it "reachable"   (nearestPath 7 vd0 `shouldBe` Just [7,6,4])
    it "unreachable" (nearestPath 1 vd0 `shouldBe` Nothing)

vd :: Voronoi Int
vd = gvdIn [4,5] vor

vd0 :: Voronoi Int
vd0 = gvdOut [4,5] vor

-- -----------------------------------------------------------------------------
-- Indep

-- TODO: how to prove that the found independent set is /maximal/?

-- | Make sure the size of independent sets is indeed accurate.
test_indepSize :: (ArbGraph gr) => Proxy (gr a b) -> gr a b -> Bool
test_indepSize _ ag = uncurry ((==) . length) (indepSize g)
  where
    g = toBaseGraph ag

-- | Is this really an independent set?
test_indep :: (ArbGraph gr) => Proxy (gr a b) -> gr a b -> Bool
test_indep _ ag = and . unfoldr checkSet . S.fromList $ indep g
  where
    g = toBaseGraph ag

    checkSet = fmap checkVal . S.minView

    checkVal (v,ws) = (S.null (S.fromList (neighbors g v) `S.intersection` ws), ws)

-- -----------------------------------------------------------------------------
-- MaxFlow2

-- As it is difficult to generate a suitable arbitrary graph for which
-- there /is/ a valid flow, we instead use unit tests based upon the
-- examples in the source code.

-- | Maximum flow of 2000
exampleNetwork1 :: Network
exampleNetwork1 = emap (flip (,) 0 . fromIntegral) exampleFlowGraph1

-- | Taken from "Introduction to Algorithms" (Cormen, Leiserson, Rivest).
--   This network has a maximum flow of 23
exampleNetwork2 :: Network
-- Names of nodes in "Introduction to Algorithms":
-- 1: s
-- 2: v1
-- 3: v2
-- 4: v3
-- 5: v4
-- 6: t
exampleNetwork2 = nemap (const ()) (flip (,) 0 . fromIntegral) clr595

clr595_network :: Network
clr595_network = maxFlowgraph clr595' 1 6
  where
    clr595' = nemap (const ()) fromIntegral clr595

test_maxFlow2_with :: String -> (Network -> Node -> Node -> (Network,Double)) -> Spec
test_maxFlow2_with nm f = it nm $ do
  snd (f exampleNetwork1 1 4) `shouldBe` 2000
  snd (f exampleNetwork2 1 6) `shouldBe` 23

test_maxFlow2 :: Spec
test_maxFlow2 = describe "MaxFlow2" $ do
  test_maxFlow2_with "ekSimple" ekSimple
  test_maxFlow2_with "ekFused"  ekFused
  test_maxFlow2_with "ekList"   ekList

-- -----------------------------------------------------------------------------
-- MaxFlow

-- TODO: test other exported functions.

exampleFlowGraph1 :: Gr () Int
exampleFlowGraph1 = mkGraph [ (1,()), (2,()), (3,()), (4,()) ]
                            [ (1,2,1000), (1,3,1000)
                            , (2,3,1), (2,4,1000), (3,4,1000)
                            ]

test_maxFlow :: Spec
test_maxFlow = it "maxFlow" $ do
  maxFlow exampleFlowGraph1 1 4 `shouldBe` 2000
  maxFlow clr595            1 6 `shouldBe` 23

-- -----------------------------------------------------------------------------
-- MST

-- | A minimum spanning tree of a connected, undirected graph should
--   cover all nodes, and all edges in the tree should be present in
--   the original graph.
test_msTree :: (ArbGraph gr) => Proxy (gr a b) -> UConnected gr () Int -> Bool
test_msTree _ cg = ns == mstNs && S.isSubsetOf mstEs es
  where
    g = connGraph cg -- a Connected graph is always non-empty

    mst = map unLPath (msTree g)

    ns = S.fromList (nodes g)
    es = S.fromList (labEdges g)

    mstNs = S.unions (map (S.fromList . map fst) mst)
    mstEs = S.unions (map (S.fromList . (zipWith toE <*> tail)) mst)

    toE (w,l) (v,_) = (v,w,l)

-- -----------------------------------------------------------------------------
-- SP

test_sp :: (ArbGraph gr) => Proxy (gr a b) -> UConnected gr () (Positive Int) -> Bool
test_sp _ cg = all test_p (map unLPath (msTree g))
  where
    -- Use Positive to avoid problems with distances containing
    -- negative lengths. The shortest path algorithm is Dijkstra's,
    -- which doesn't support negative weights.
    g = emap getPositive (connGraph cg)

    gCon = emap (const 1) g `asTypeOf` g

               -- Length-based test
    test_p p = length p >= len_gCon
               && length (esp v w gCon) == len_gCon
               -- Weighting-based test
               && sum (map snd p) >= fromJust (spLength v w g)
      where
        v = fst (head p)
        w = fst (last p)

        len_gCon = length (fromJust $ sp v w gCon)

-- | Test that 'spLength' and 'sp' return a length and an connecting
--   path when destination is reachable from source.
test_sp_Just :: (ArbGraph gr, Graph gr, Real b) =>
  Proxy (gr a b) -> gr a b -> Property
test_sp_Just _ g =
  (noNodes g >= 2 && v `elem` bfs u g) ==>
  isJust (spLength u v g) &&
  isJust maybePath &&
  not (null path) &&
  head path == u &&
  last path == v
  where
    [u,v] = take 2 (nodes g)
    maybePath@(Just path) = sp u v g

-- | Test that 'spLength' and 'sp' return 'Nothing' when destination
--   is not reachable from source.
test_sp_Nothing :: (ArbGraph gr, Graph gr, Real b) =>
  Proxy (gr a b) -> gr a b -> Property
test_sp_Nothing _ g =
  (noNodes g >= 2 && not (v `elem` bfs u g)) ==>
  isNothing (spLength u v g) &&
  isNothing (sp u v g)
  where
    [u,v] = take 2 (nodes g)

-- -----------------------------------------------------------------------------
-- TransClos

-- | The transitive, reflexive closure of a graph means that every
-- node is a successor of itself, and also that if (a, b) is an edge,
-- and (b, c) is an edge, then (a, c) must also be an edge.
test_trc :: DynGraph gr => Proxy (gr a b) -> (NoMultipleEdges gr) a b -> Bool
test_trc _ nme = all valid $ nodes gTrans
  where
    g       = emap (const ()) (nmeGraph nme)
    gTrans  = trc g
    valid n =
      -- For each node n, check that:
      --   the successors for n in gTrans are a superset of the successors for n in g.
      null (suc g n \\ suc gTrans n) &&
      --   the successors for n in gTrans are exactly equal to the reachable nodes for n in g, plus n.
      sort (suc gTrans n) == map head (group (sort (n:[ v | u <- suc g n, v <- reachable u g ])))

-- | The transitive closure of a graph means that if (a, b) is an
-- edge, and (b, c) is an edge, then (a, c) must also be an edge.
test_tc :: DynGraph gr => Proxy (gr a b) -> (NoMultipleEdges gr) a b -> Bool
test_tc _ nme = all valid $ nodes gTrans
  where
    g       = nmeGraph nme
    gTrans  = tc g
    valid n =
      -- For each node n, check that:
      --   the successors for n in gTrans are a superset of the successors for n in g.
      null (suc g n \\ suc gTrans n) &&
      --   the successors for n in gTrans are exactly equal to the reachable nodes for n in g.
      sort (suc gTrans n) == map head (group (sort [ v | u <- suc g n, v <- reachable u g ]))

-- | The reflexive closure of a graph means that all nodes are a
-- successor of themselves.
test_rc :: DynGraph gr => Proxy (gr a b) -> gr a b -> Bool
test_rc _ g = and [ n `elem` suc gRefl n | n <- nodes gRefl ]
  where
    gRefl = rc g

-- -----------------------------------------------------------------------------
-- Utility functions

type UConnected gr a b = Connected (Undirected gr) a b
