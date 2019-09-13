{-# LANGUAGE CPP #-}

{- |
   Module      : Data.Graph.Inductive.Properties
   Description : Expected properties of inductive graphs
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : BSD3
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Graph.Inductive.Graph.Properties where

import Data.Graph.Inductive
import Data.Graph.Inductive.Arbitrary
import Data.Graph.Inductive.Proxy

import Test.QuickCheck

import           Control.Applicative (liftA2)
import           Control.Arrow       ((***))
import           Data.Function       (on)
import           Data.List           (groupBy, sort, sortBy)
import qualified Data.Set            as S

#if __GLASGOW_HASKELL__ < 710
import Data.Functor ((<$>))
#endif

{-# ANN module "HLint: ignore Use camelCase" #-}

-- -----------------------------------------------------------------------------
-- Non-dynamic graphs

-- | Ensure that a custom 'Eq' instance matches the behaviour of the
--   'equal' function.
valid_Eq :: (Graph gr, Eq a, Eq b, Eq (gr a b)) => gr a b -> gr a b -> Bool
valid_Eq g1 g2 = (equal g1 g1 && g1 == g1)
                 && (equal g2 g2 && g2 == g2)
                 && (equal g1 g2 == (g1 == g2))

-- | Ensure that the definition of 'noNodes' matches the default
--   implementation.
valid_node_count :: (Graph gr) => gr a b -> Bool
valid_node_count g = noNodes g == length (nodes g)

-- | Ensure that the definition of 'nodeRange' matches the default
--   implementation.
valid_nodeRange :: (Graph gr) => gr a b -> Property
valid_nodeRange g = not (isEmpty g) ==>
                        nodeRange g == (minimum vs, maximum vs)
  where
    vs = nodes g

-- | Make sure that a graph created with specified nodes contains
--   those nodes (and only those nodes) and no edges are created.
valid_mkGraph_nodes :: (Graph gr, Arbitrary a, Eq a) => Proxy (gr a b) -> Gen Bool
valid_mkGraph_nodes p = do ns <- arbitraryNodes
                           let g = mkGraph ns [] `asProxyTypeOf` p
                           return ( sortOn fst (labNodes g) == ns
                                    && null (labEdges g))

-- | Make sure that a graph created with specified edges contains
--   those edges (and only those edges), and that no additional nodes
--   are created.
valid_mkGraph_edges :: (Graph gr, Eq a, Eq b) => Proxy (gr a b)
                       -> GraphNodesEdges a b  -> Bool
valid_mkGraph_edges p (GNEs ns es) = sortOn toEdge (labEdges g) == es'
                                     && sortOn fst (labNodes g) == ns
  where
    es' = uniqBy toEdge es

    g = mkGraph ns es' `asProxyTypeOf` p

-- | The resultant graph shouldn't matter on the order of nodes and
--   edges provided.
valid_mkGraph_order :: (Graph gr, Eq a, Eq b) => Proxy (gr a b)
                       -> GraphNodesEdges a b -> Bool
valid_mkGraph_order p (GNEs ns es) = all (equal g)
                                         [ mkGraph ns  esR
                                         , mkGraph nsR es
                                         , mkGraph nsR esR
                                         ]
  where
    g = mkGraph ns es `asProxyTypeOf` p

    nsR = reverse ns
    esR = reverse es

-- | Ensure that when a node is matched, it is indeed removed from the
--   resulting graph.
valid_match :: (Graph gr) => gr a b -> Property
valid_match g = not (isEmpty g) ==> check_match <$> elements (nodes g)
  where
    ordr = noNodes g

    check_match n = maybe False check_context mc
      where
        (mc, g') = match n g

        check_context c = (node' c `notElem` nodes g')
                          && (noNodes g' == ordr - 1)
                          -- Edges were previously in the graph
                          && all (elem (node' c) . pre g) (sucC c)
                          && all (elem (node' c) . suc g) (preC c)
                          -- Edges not in new graph
                          && all (notElem (node' c) . pre g') (sucC c)
                          && all (notElem (node' c) . suc g') (preC c)

-- | Ensure that 'matchAny' is valid by verifying that it achieves the
--   same result as matching for that node specifically.
valid_matchAny :: (Graph gr, Eq a, Ord b) => gr a b -> Property
valid_matchAny g = not (isEmpty g) ==>
                     (uncurry (&&)
                     . (maybe False ((c'==) . sortContext) *** equal g')
                     $ match (node' c) g)
  where
    (c,g') = matchAny g

    c' = sortContext c

-- | newNodes should return Nodes that aren't already in the graph.
newNodes_really_new :: (Graph gr) => gr a b -> NonNegative Int -> Bool
newNodes_really_new g (NonNegative n) = liftA2 (&&) (all (not . (`gelem`g)))
                                                 ((n==) . length)
                                       (newNodes n g)

-- | ufold should create a Context for each node.
ufold_all_nodes :: (Graph gr) => gr a b -> Bool
ufold_all_nodes g = sort (ufold ((:) . node') [] g)
                    == sort (nodes g)

-- | All nodes should indeed be elements of the graph.
all_nodes_gelem :: (Graph gr) => gr a b -> Bool
all_nodes_gelem g = all (`gelem`g) (nodes g)

-- | If a potential 'Node' is 'gelem' then it should also be in the
--   output of 'nodes'.
gelem_in_nodes :: (Graph gr) => gr a b -> [Node] -> Bool
gelem_in_nodes g = all (liftA2 (==) (`gelem`g) (`S.member`ns))
  where
    ns = S.fromList $ nodes g

-- | Check that having a labelled edge in a graph is equivalent to
-- 'hasNeighborAdj' reporting that the edge is there.
valid_hasNeighborAdj :: (Graph gr, Eq b) => gr a b -> Node -> Node -> b -> Bool
valid_hasNeighborAdj gr v w l = any (`elem` [(v,w,l), (w,v,l)]) (labEdges gr)
                                == (hasNeighborAdj gr v (l,w) && hasNeighborAdj gr w (l,v))

-- | Check that having an edge in a graph is equivalent to
-- 'hasNeighbor' reporting that the edge is there.
valid_hasNeighbor :: (Graph gr) => gr a b -> Node -> Node -> Bool
valid_hasNeighbor gr v w =
  any (`elem` [(v,w), (w,v)]) (edges gr) == (hasNeighbor gr v w && hasNeighbor gr w v)

-- | Check that having a labelled edge in a graph is equivalent to
-- 'hasLEdge' reporting that the edge is there.
valid_hasLEdge :: (Graph gr, Eq b) => gr a b -> LEdge b -> Bool
valid_hasLEdge gr e = (e `elem` labEdges gr) == hasLEdge gr e

-- -----------------------------------------------------------------------------
-- Dynamic graphs

-- | Ensure that matching and then merging using '&' produces the
--   original graph again.
--
--   We do it this way because it isn't possible to generate an
--   arbitrary 'Context' to test against; 'valid_match' \"proves\"
--   that matching is valid, so if merging produces the original graph
--   again then it must be valid as well.
valid_merge :: (DynGraph gr, Eq a, Eq b) => gr a b -> Property
valid_merge g = not (isEmpty g) ==> check_merge <$> elements (nodes g)
  where
    -- Using equal here rather than requiring an Eq instance.
    check_merge n = maybe False (equal g . (&g')) mc
      where
        (mc, g') = match n g

-- | Applying a mapping over contexts shouldn't actually change the
--   structure of the graph.
--
--   Note that 'nmap', 'emap' and 'nemap' are specialised versions of
--   'gmap' and thus this property also covers those.
gmap_id :: (DynGraph gr, Eq a, Eq b) => gr a b -> Bool
gmap_id g = equal (gmap id g) g

-- | 'insNode' inserts a single node and doesn't add or delete any
--   edges.
--
--   This is technically also tested using 'valid_insEdge'.
--
--   Note that we specifically use 'newNodes' to test this, as the
--   current behaviour is to throw an error if an existing node is
--   used.
valid_insNode :: (DynGraph gr, Ord a, Ord b) => gr a b -> a -> Bool
valid_insNode g l = gelem v g'
                    && sort (labNodes g') == sort (vl : labNodes g)
                    && sort (labEdges g') == sort (labEdges g)
                    -- Note: not testing whether this changes
                    -- nodeRange because newNodes /might/ return
                    -- unused nodes in the middle.
  where
    [v] = newNodes 1 g

    vl = (v,l)

    g' = insNode vl g

-- | Insert a node for every label in the list, but don't add any new
--   edges.
--
--   Note that we specifically use 'newNodes' to test this, as the
--   current behaviour is to throw an error if an existing node is
--   used.
valid_insNodes :: (DynGraph gr, Ord a, Ord b) => gr a b -> [a] -> Bool
valid_insNodes g as = all (`gelem`g') ns
                      && sort (labNodes g') == sort (lns ++ labNodes g)
                      && sort (labEdges g') == sort (labEdges g)
  where
    c = length as

    ns = newNodes c g
    lns = zip ns as

    g' = insNodes lns g

-- | Test inserting an edge.  This could possibly be a multiple edge
--   or loop.
valid_insEdge :: (DynGraph gr, Ord a, Ord b) => gr a b -> b -> Property
valid_insEdge g b = not (isEmpty g) ==>
                    do v <- pickN
                       w <- pickN
                       let el = (v,w,b)
                           g' = insEdge el g
                       return ( sort (labEdges g') == sort (el : labEdges g)
                                && sort (labNodes g') == sort (labNodes g))

  where
    pickN = elements (nodes g)

-- | Insert an edge for every label in the list.  Multiple edges and
--   loops allowed.
valid_insEdges :: (DynGraph gr, Ord a, Ord b) => gr a b -> [b] -> Property
valid_insEdges g bs = not (isEmpty g) ==>
                      do es <- mapM toLE bs
                         let g' = insEdges es g
                         return ( sort (labEdges g') == sort (es ++ labEdges g)
                                  && sort (labNodes g') == sort (labNodes g))
  where
    pickN = elements (nodes g)

    toLE b = do v <- pickN
                w <- pickN
                return (v,w,b)

-- | Explicitly test adding multiple edges.
valid_insEdges_multiple :: (DynGraph gr, Ord b) => gr a b -> b -> NonNegative Int
                           -> Property
valid_insEdges_multiple g b (NonNegative c) = not (isEmpty g) ==>
                                              do v <- pickN
                                                 w <- pickN
                                                 let bes = replicate c (v,w,b)
                                                     g' = insEdges bes g
                                                     es' = bes ++ es
                                                 return $ sort (labEdges g') == sort es'
  where
    pickN = elements (nodes g)

    es = labEdges g

-- | Delete a node, and ensure there are no edges
--   referencing that node afterwards.
valid_delNode :: (DynGraph gr) => gr a b -> Node -> Bool
valid_delNode g v = not (gelem v g')
                    && (v `S.notMember` S.fromList (esToNs (labEdges g')))
  where
    g' = delNode v g

-- | Test deleting a sub-set of nodes.
valid_delNodes :: (DynGraph gr) => gr a b -> [Node] -> Bool
valid_delNodes g vs = all (liftA2 (&&) (not . (`gelem` g')) (`S.notMember` ens)) vs
  where
    g' = delNodes vs g
    ens = S.fromList (esToNs (labEdges g'))

-- | Delete an edge, and ensure that the nodes from that
--   edge are still there (if that edge was present in the graph to
--   start with).
valid_delEdge :: (DynGraph gr) => gr a b -> (Node,Node) -> Bool
valid_delEdge g e@(v,w) = notElem e (edges g')
                          && ifOrig v
                          && ifOrig w
  where
    g' = delEdge e g

    ifOrig n = not (n `gelem` g) || (n `gelem` g')

-- | Test deleting multiple edges.
valid_delEdges :: (DynGraph gr) => gr a b -> [Edge] -> Bool
valid_delEdges g es = all check_E es
  where
    origEs = S.fromList (edges g)

    g' = delEdges es g

    newEs = S.fromList (edges g')

    check_E e@(v,w) = (e `S.notMember` origEs)
                      || ( (e `S.notMember` newEs)
                           && (v `gelem` g')
                           && (w `gelem` g')
                         )

-- | Add a 'LEdge' then delete it; the resulting graph should be the
--   same as the original graph.
valid_delLEdge :: (DynGraph gr, Eq a, Eq b) => gr a b -> b -> Property
valid_delLEdge g b = not (isEmpty g) ==>
                     do v <- pickN
                        w <- pickN
                        let le = (v,w,b)
                            g' = insEdge le g
                            g'' = delLEdge le g'
                        return (equal g g'')
  where
    pickN = elements (nodes g)

-- | Test deleting all labelled edges equal to the specified one, by
--   adding the specified number to the graph and then deleting them.
valid_delAllLEdge :: (DynGraph gr, Eq a, Eq b) => gr a b -> NonNegative Int
                     -> a -> a -> b -> Bool
valid_delAllLEdge g (NonNegative c) a1 a2 b = equal g' (delAllLEdge le g'')
  where
    [v,w] = newNodes 2 g
    g' = insNodes [(v,a1),(w,a2)] g
    le = (v,w,b)
    g'' = insEdges (replicate c le) g'

-- | There is a version of 'mkGraph' in its documentation that uses
--   'DynGraph' (hence why it isn't used by default).  This ensures
--   that the optimised variants match this \"default\" definition.
valid_mkGraph :: (DynGraph gr, Eq a, Eq b) => Proxy (gr a b)
                 -> GraphNodesEdges a b -> Bool
valid_mkGraph p (GNEs ns es) = equal mkGr (mkGraph ns es)
  where
    mkGr = (insEdges es . insNodes ns) empty `asProxyTypeOf` p

-- | 'buildGr' re-creates the original graph after 'ufold' obtains all
--   the contexts.
valid_buildGr :: (DynGraph gr, Eq a, Eq b) => gr a b -> Bool
valid_buildGr g = equal g (buildGr cs)
  where
    cs = ufold (:) [] g

-- | Tests `gfiltermap` with a function accepting all contexts.
gfiltermap_id :: (DynGraph gr, Eq a, Eq b) => gr a b -> Bool
gfiltermap_id g = equal (gfiltermap Just g) g

-- | Tests `nfilter` with a function accepting all nodes.
nfilter_true :: (DynGraph gr, Eq a, Eq b) => gr a b -> Bool
nfilter_true g = equal (nfilter (const True) g) g

-- | Tests `labnfilter` with a function accepting all nodes.
labnfilter_true :: (DynGraph gr, Eq a, Eq b) => gr a b -> Bool
labnfilter_true g = equal (labnfilter (const True) g) g

-- | Tests `labnfilter` with a function accepting all nodes.
labfilter_true :: (DynGraph gr, Eq a, Eq b) => gr a b -> Bool
labfilter_true g = equal (labfilter (const True) g) g

-- | The subgraph induced by a list of nodes should contain exactly
-- the nodes from this list, as well as all edges between these nodes.
valid_subgraph :: (DynGraph gr, Ord b) => gr a b -> Gen Bool
valid_subgraph gr = do
  vs <- sublistOf $ nodes gr
  let sg = subgraph vs gr
      svs = S.fromList vs
      subedges = filter (\(v,w,_) -> v `S.member` svs && w `S.member` svs) $ labEdges gr
  return $ sort (nodes sg) == sort vs && sort (labEdges sg) == sort subedges

-- -----------------------------------------------------------------------------
-- Miscellaneous

-- | Ensure the edge projection functions work as intended.
edge_projections :: (Eq b) => LEdge b -> Bool
edge_projections le = le == toLEdge (toEdge le) (edgeLabel le)

-- -----------------------------------------------------------------------------

esToNs :: [LEdge b] -> [Node]
esToNs = uniqBy id . concatMap (\(v,w,_) -> [v,w])

uniqBy :: (Ord b) => (a -> b) -> [a] -> [a]
uniqBy f = map head . groupBy ((==) `on` f) . sortOn f

sortOn :: (Ord b) => (a -> b) -> [a] -> [a]
sortOn f = sortBy (compare `on` f)

-- | As with suc', but also remove any loops
sucC :: Context a b -> [Node]
sucC c = filter (/= node' c) (suc' c)

-- | As with pre', but also remove any loops
preC :: Context a b -> [Node]
preC c = filter (/= node' c) (pre' c)

-- In case a Context is produced with the Adj lists in different
-- orders, sort them so that they can then be equality tested.
sortContext :: (Ord b) => Context a b -> Context a b
sortContext (p,v,l,s) = (sort p, v, l, sort s)
