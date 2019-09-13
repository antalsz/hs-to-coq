{-# LANGUAGE CPP, FlexibleContexts, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{- |
   Module      : Data.Graph.Inductive.Arbitrary
   Description : Arbitrary definition for fgl graphs
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : BSD3
   Maintainer  : Ivan.Miljenovic@gmail.com

This module provides default definitions for use with QuickCheck's
'Arbitrary' class.

Both "Data.Graph.Inductive.Tree"- and
"Data.Graph.Inductive.PatriciaTree"-based graph implementations have
'Arbitrary' instances.  In most cases, this is all you will need.

If, however, you want to create arbitrary custom graph-like data
structures, then you will probably want to do some custom processing
from an arbitrary 'GraphNodesEdges' value, either directly or with a
custom 'ArbGraph' instance.

 -}
module Data.Graph.Inductive.Arbitrary
       ( -- * Explicit graph creation
         -- $explicit
         arbitraryGraph
       , arbitraryGraphWith
       , shrinkGraph
       , shrinkGraphWith
         -- * Types of graphs
       , ArbGraph(..)
       , GrProxy(..)
       , shrinkF
       , arbitraryGraphBy
         -- ** Specific graph structures
       , NoMultipleEdges(..)
       , NoLoops(..)
       , SimpleGraph
       , Undirected(..)
         -- ** Connected graphs
       , Connected(..)
       , connGraph
         -- * Node and edge lists
       , arbitraryNodes
       , arbitraryEdges
       , GraphNodesEdges(..)
       ) where

import           Data.Graph.Inductive.Graph        (DynGraph, Graph, LEdge,
                                                    LNode, Node, delNode,
                                                    insEdges, insNode, mkGraph,
                                                    newNodes, nodes, toEdge)
import qualified Data.Graph.Inductive.PatriciaTree as P
import qualified Data.Graph.Inductive.Tree         as T

import Test.QuickCheck (Arbitrary (..), Gen, elements, listOf)

import Control.Applicative (liftA3)
import Control.Arrow       (second)
import Data.Function       (on)
import Data.List           (deleteBy, groupBy, sortBy)
import Data.Maybe          (mapMaybe)

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative ((<$>), (<*>))
#endif

-- -----------------------------------------------------------------------------

-- | Generally a list of labelled nodes.
arbitraryNodes :: (Arbitrary a) => Gen [LNode a]
arbitraryNodes = arbitrary >>= mapM ((<$> arbitrary) . (,)) . uniq

-- | Given a specified list of nodes, generate a list of edges.
arbitraryEdges :: (Arbitrary b) => [LNode a] -> Gen [LEdge b]
arbitraryEdges lns
  | null lns  = return []
  | otherwise = listOf (liftA3 (,,) nGen nGen arbitrary)
  where
    nGen = elements (map fst lns)

-- | Defined so as to be able to generate valid 'arbitrary' node and
--   edge lists.
--
--   If any specific structure (no multiple edges, no loops, etc.) is
--   required then you will need to post-process this after generating
--   it, or else create a new instance of 'ArbGraph'.
data GraphNodesEdges a b = GNEs { graphNodes :: [LNode a]
                                , graphEdges :: [LEdge b]
                                }
  deriving (Eq, Ord, Show, Read)

instance (Arbitrary a, Arbitrary b) => Arbitrary (GraphNodesEdges a b) where
  arbitrary = do ns <- arbitraryNodes
                 GNEs ns <$> arbitraryEdges ns

  shrink (GNEs ns es) = case ns of
                          _:_:_ -> map delN ns
                          _     -> []
    where
      delN ln@(n,_) = GNEs ns' es'
        where
          ns' = deleteBy ((==)`on`fst) ln ns
          es' = filter (not . hasN) es

          hasN (v,w,_) = v == n || w == n

-- -----------------------------------------------------------------------------

-- | Representation of generating arbitrary graph structures.
--
--   Typically, you would only use this for the 'toBaseGraph' function
--   or if you wanted to make a custom graph wrapper.
--
--   The intent of this class is to simplify defining and using
--   different wrappers on top of graphs (e.g. you may wish to have an
--   'Undirected' graph, or one with 'NoLoops', or possibly both!).
class (DynGraph (BaseGraph ag)) => ArbGraph ag where
  type BaseGraph ag :: * -> * -> *

  toBaseGraph :: ag a b -> BaseGraph ag a b

  fromBaseGraph :: BaseGraph ag a b -> ag a b

  -- | Any manipulation of edges that should be done to satisfy the
  --   requirements of the specified wrapper.
  edgeF :: GrProxy ag -> [LEdge b] -> [LEdge b]

  -- | Shrinking function (assuming only one node is removed at a
  --   time) which also returns the node that is removed.
  shrinkFWith :: ag a b -> [(Node, ag a b)]

-- | In most cases, for an instance of 'ArbGraph' the 'Arbitrary'
--   instance definition will\/can have @shrink = shrinkF@.
shrinkF :: (ArbGraph ag) => ag a b -> [ag a b]
shrinkF = map snd . shrinkFWith

instance ArbGraph T.Gr where
  type BaseGraph T.Gr = T.Gr

  toBaseGraph = id
  fromBaseGraph = id

  edgeF _ = id

  shrinkFWith = shrinkGraphWith

instance ArbGraph P.Gr where
  type BaseGraph P.Gr = P.Gr

  toBaseGraph = id
  fromBaseGraph = id

  edgeF _ = id

  shrinkFWith = shrinkGraphWith

-- | A simple graph-specific proxy type.
data GrProxy (gr :: * -> * -> *) = GrProxy
  deriving (Eq, Ord, Show, Read)

-- -----------------------------------------------------------------------------

{- $explicit

If you wish to explicitly create a generated graph value (rather than
using the 'Arbitrary' class) then you will want to use these
functions.

-}

-- | Generate an arbitrary graph.  Multiple edges are allowed.
arbitraryGraph :: (Graph gr, Arbitrary a, Arbitrary b) => Gen (gr a b)
arbitraryGraph = arbitraryGraphWith id

-- | Generate an arbitrary graph, using the specified function to
--   manipulate the generated list of edges (e.g. remove multiple
--   edges).
arbitraryGraphWith :: (Graph gr, Arbitrary a, Arbitrary b)
                      => ([LEdge b] -> [LEdge b]) -> Gen (gr a b)
arbitraryGraphWith f = do GNEs ns es <- arbitrary
                          let es' = f es
                          return (mkGraph ns es')

-- | Generate an instance of 'ArbGraph' using the class methods.
arbitraryGraphBy :: forall ag a b. (ArbGraph ag, Arbitrary a, Arbitrary b)
                    => Gen (ag a b)
arbitraryGraphBy = fromBaseGraph
                   <$> arbitraryGraphWith (edgeF (GrProxy :: GrProxy ag))

-- Ensure we have a list of unique Node values; this will also sort
-- the list, but that shouldn't matter.
uniq :: [Node] -> [Node]
uniq = uniqBy id

uniqBy :: (Ord b) => (a -> b) -> [a] -> [a]
uniqBy f = map head . groupBy ((==) `on` f) . sortBy (compare `on` f)

-- | For a graph with at least two nodes, return every possible way of
--   deleting a single node (i.e. will never shrink to an empty
--   graph).
shrinkGraph :: (Graph gr) => gr a b -> [gr a b]
shrinkGraph = map snd . shrinkGraphWith

-- | As with 'shrinkGraph', but also return the node that was deleted.
shrinkGraphWith :: (Graph gr) => gr a b -> [(Node, gr a b)]
shrinkGraphWith gr = case nodes gr of
                       -- Need to have at least 2 nodes before we delete one!
                       ns@(_:_:_) -> map ((,) <*> (`delNode` gr)) ns
                       _          -> []

instance (Arbitrary a, Arbitrary b) => Arbitrary (T.Gr a b) where
  arbitrary = arbitraryGraph

  shrink = shrinkGraph

instance (Arbitrary a, Arbitrary b) => Arbitrary (P.Gr a b) where
  arbitrary = arbitraryGraph

  shrink = shrinkGraph

-- | A newtype wrapper to generate a graph without multiple edges
--   (loops allowed).
newtype NoMultipleEdges gr a b = NME { nmeGraph :: gr a b }
                                 deriving (Eq, Show, Read)

instance (ArbGraph gr) => ArbGraph (NoMultipleEdges gr) where
  type BaseGraph (NoMultipleEdges gr) = BaseGraph gr

  toBaseGraph = toBaseGraph. nmeGraph
  fromBaseGraph = NME . fromBaseGraph

  edgeF _ = uniqBy toEdge . edgeF (GrProxy :: GrProxy gr)

  shrinkFWith = map (second NME) . shrinkFWith . nmeGraph

instance (ArbGraph gr, Arbitrary a, Arbitrary b) => Arbitrary (NoMultipleEdges gr a b) where
  arbitrary = arbitraryGraphBy

  shrink = shrinkF

-- | A newtype wrapper to generate a graph without loops (multiple
--   edges allowed).
newtype NoLoops gr a b = NL { looplessGraph :: gr a b }
                         deriving (Eq, Show, Read)

instance (ArbGraph gr) => ArbGraph (NoLoops gr) where
  type BaseGraph (NoLoops gr) = BaseGraph gr

  toBaseGraph = toBaseGraph . looplessGraph
  fromBaseGraph = NL . fromBaseGraph

  edgeF _ = filter notLoop . edgeF (GrProxy :: GrProxy gr)

  shrinkFWith = map (second NL) . shrinkFWith . looplessGraph

notLoop :: LEdge b -> Bool
notLoop (v,w,_) = v /= w

instance (ArbGraph gr, Arbitrary a, Arbitrary b) => Arbitrary (NoLoops gr a b) where
  arbitrary = arbitraryGraphBy

  shrink = shrinkF

-- | A wrapper to generate a graph without multiple edges and
--   no loops.
type SimpleGraph gr = NoLoops (NoMultipleEdges gr)

-- | A newtype wrapper such that each (non-loop) edge also has its
--   reverse in the graph.
--
--   Note that there is no way to guarantee this after any additional
--   edges are added or removed.
--
--  You should also apply this wrapper /after/ 'NoMultipleEdges' or
--  else the wrong reverse edge might be removed.
newtype Undirected gr a b = UG { undirGraph :: gr a b }
                            deriving (Eq, Show, Read)

instance (ArbGraph gr) => ArbGraph (Undirected gr) where
  type BaseGraph (Undirected gr) = BaseGraph gr

  toBaseGraph = toBaseGraph . undirGraph
  fromBaseGraph = UG . fromBaseGraph

  edgeF _ = undirect . edgeF (GrProxy :: GrProxy gr)

  shrinkFWith = map (second UG) . shrinkFWith . undirGraph

undirect :: [LEdge b] -> [LEdge b]
undirect = concatMap undir
  where
    undir le@(v,w,b)
      | notLoop le = [le, (w,v,b)]
      | otherwise  = [le]

instance (ArbGraph gr, Arbitrary a, Arbitrary b) => Arbitrary (Undirected gr a b) where
  arbitrary = arbitraryGraphBy

  shrink = shrinkF

-- -----------------------------------------------------------------------------

-- | A brute-force approach to generating connected graphs.
--
--   The resultant graph (obtained with 'connGraph') will /never/ be
--   empty: it will, at the very least, contain an additional
--   connected node (obtained with 'connNode').
--
--   Note that this is /not/ an instance of 'ArbGraph' as it is not
--   possible to arbitrarily layer a transformer on top of this.
data Connected ag a b = CG { connNode     :: Node
                           , connArbGraph :: ag a b
                           }
                        deriving (Eq, Show, Read)

instance (ArbGraph ag, Arbitrary a, Arbitrary b) => Arbitrary (Connected ag a b) where
  arbitrary = arbitraryGraphBy >>= toConnGraph

  shrink = shrinkConnGraph

toConnGraph :: forall ag a b. (ArbGraph ag, Arbitrary a, Arbitrary b)
               => ag a b -> Gen (Connected ag a b)
toConnGraph ag = do a <- arbitrary
                    ces <- concat <$> mapM mkE ws
                    return $ CG { connNode     = v
                                , connArbGraph = fromBaseGraph
                                                 . insEdges ces
                                                 . insNode (v,a)
                                                 $ g
                                }
  where
    g = toBaseGraph ag

    [v] = newNodes 1 g

    ws = nodes g

    mkE w = do b <- arbitrary
               return (edgeF p [(v,w,b)])

    p :: GrProxy ag
    p = GrProxy

shrinkConnGraph :: (ArbGraph ag) => Connected ag a b -> [Connected ag a b]
shrinkConnGraph cg = mapMaybe keepConn . shrinkFWith $ g
  where
    v = connNode cg
    g = connArbGraph cg

    keepConn (w,sgs) | v == w    = Nothing
                     | otherwise = Just (cg { connArbGraph = sgs })

-- | The underlying graph represented by this 'Connected' value.
connGraph :: (ArbGraph ag) => Connected ag a b -> BaseGraph ag a b
connGraph = toBaseGraph . connArbGraph

-- -----------------------------------------------------------------------------
