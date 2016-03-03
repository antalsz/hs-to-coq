module HsToCoq.Util.Containers (
  invertMap,
  connectedComponents,
  stronglyConnComp', connectedComponents'
  ) where

import           Data.Set (Set)
import qualified Data.Set as S

import           Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as M

import Data.Graph

invertMap :: (Ord k, Ord v) => Map k (Set v) -> Map v (Set k)
invertMap m = M.unionsWith S.union [M.fromSet (const $ S.singleton k) vs | (k,vs) <- M.toList m]

connectedComponents :: Ord key => [(node, key, [key])] -> [SCC node]
connectedComponents graph =
  let edges = M.unionWith S.union <*> invertMap $
                M.fromList [(k, S.fromList vs) | (_, k, vs) <- graph]
  in stronglyConnComp [(n, k, S.toList $ edges ! k) | (n,k,_) <- graph]

-- Module-local
simple_ccs :: Ord vertex
           => ([(vertex, vertex, [vertex])] -> [SCC vertex])
           -> [(vertex, [vertex])] -> [[vertex]]
simple_ccs makeCCs graph = map flattenSCC $ makeCCs [(v,v,es) | (v,es) <- graph]

stronglyConnComp' :: Ord vertex => [(vertex, [vertex])] -> [[vertex]]
stronglyConnComp' = simple_ccs stronglyConnComp

connectedComponents' :: Ord vertex => [(vertex, [vertex])] -> [[vertex]]
connectedComponents' = simple_ccs connectedComponents
