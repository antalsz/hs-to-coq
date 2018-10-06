{-# LANGUAGE FlexibleContexts #-}

module HsToCoq.Util.Containers (
  setMapMaybe,
  setMapMaybeM,
  invertMap,
  connectedComponents,
  stronglyConnCompNE, connectedComponentsNE,
  stronglyConnComp', connectedComponents',
  transitiveClosure, transitiveClosureBy,
  reachableFrom,
  Reflexivity(..),
  ) where

import Control.Arrow
import HsToCoq.Util.Monad
import Control.Monad.State
import Data.Foldable

import Data.List.NonEmpty (NonEmpty(..))

import           Data.Set (Set)
import qualified Data.Set as S

import           Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as M
import Data.Maybe

import Data.Graph

setMapMaybe :: Ord b => (a -> Maybe b) -> Set a -> Set b
setMapMaybe f = S.foldr (\x s -> maybe s (`S.insert` s) $ f x) S.empty

setMapMaybeM :: (Applicative m, Ord b) => (a -> m (Maybe b)) -> Set a -> m (Set b)
setMapMaybeM f s = S.fromList . catMaybes <$> traverse f (S.toList s)

invertMap :: (Ord k, Ord v) => Map k (Set v) -> Map v (Set k)
invertMap m = M.unionsWith S.union [M.fromSet (const $ S.singleton k) vs | (k,vs) <- M.toList m]

connectedComponents :: Ord key => [(node, key, [key])] -> [SCC node]
connectedComponents graph =
  let edges = M.unionWith S.union <*> invertMap $
                M.fromList [(k, S.fromList vs) | (_, k, vs) <- graph]
  in stronglyConnComp [(n, k, S.toList $ edges ! k) | (n,k,_) <- graph]

-- Module-local
nonEmpty_SCC :: SCC a -> NonEmpty a
nonEmpty_SCC (AcyclicSCC v)      = v :| []
nonEmpty_SCC (CyclicSCC  (v:vs)) = v :| vs
nonEmpty_SCC (CyclicSCC  [])     = error "[internal] nonEmpty_SCC: empty connected component!"

stronglyConnCompNE :: Ord key => [(node, key, [key])] -> [NonEmpty node]
stronglyConnCompNE = map nonEmpty_SCC . stronglyConnComp

connectedComponentsNE :: Ord key => [(node, key, [key])] -> [NonEmpty node]
connectedComponentsNE = map nonEmpty_SCC . connectedComponents

-- Module-local
simple_sccs :: Ord vertex
            => ([(vertex, vertex, [vertex])] -> [SCC vertex])
            -> [(vertex, [vertex])] -> [NonEmpty vertex]
simple_sccs makeCCs graph = map nonEmpty_SCC $ makeCCs [(v,v,es) | (v,es) <- graph] where

stronglyConnComp' :: Ord vertex => [(vertex, [vertex])] -> [NonEmpty vertex]
stronglyConnComp' = simple_sccs stronglyConnComp

connectedComponents' :: Ord vertex => [(vertex, [vertex])] -> [NonEmpty vertex]
connectedComponents' = simple_sccs connectedComponents

data Reflexivity = Irreflexive | Reflexive deriving (Eq, Ord, Enum, Bounded, Show, Read)

reachableFrom :: Ord a => Reflexivity -> Map a (Set a) -> a -> Set a
reachableFrom refl adjacencies v0 = execState (go v0) initial where
  go v = for_ (M.findWithDefault mempty v adjacencies) $ \v' ->
           unlessM (gets (v' `elem`)) $ modify (S.insert v') *> go v'
  
  initial = case refl of
    Irreflexive -> S.empty
    Reflexive   -> S.singleton v0

transitiveClosure :: Ord a => Reflexivity -> Map a (Set a) -> Map a (Set a)
transitiveClosure refl adjacencies =
  M.fromSet (reachableFrom refl adjacencies) $ M.keysSet adjacencies <> fold adjacencies

transitiveClosureBy :: (Foldable f, Ord a) => Reflexivity -> (a -> Set a) -> f a -> Map a (Set a)
transitiveClosureBy refl neighbors =
  transitiveClosure refl . M.fromList . map (id &&& neighbors) . toList
