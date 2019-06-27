{-# LANGUAGE RankNTypes, FlexibleContexts #-}

module HsToCoq.Util.Containers (
  -- * Optics
  notContains,
  -- * Sets
  setMapMaybe,
  setMapMaybeM,
  -- * Maps
  invertMap,
  -- * Graphs
  -- ** Connected components
  connectedComponents,
  stronglyConnCompNE, connectedComponentsNE,
  stronglyConnComp', connectedComponents',
  -- ** Topological sort
  stableTopoSortBy, stableTopoSortByPlus,
  -- ** Transitive closure and reachability
  transitiveClosure, transitiveClosureBy,
  reachableFrom,
  Reflexivity(..),
  ) where

import Control.Lens

import Control.Arrow
import HsToCoq.Util.Monad
import Control.Monad.State
import Control.Monad.RWS
import Data.Foldable

import Data.List.NonEmpty (NonEmpty(..))

import qualified Data.IntSet as IS

import           Data.Set (Set)
import qualified Data.Set as S

import           Data.Map.Strict (Map, (!))
import qualified Data.Map.Strict as M
import Data.Maybe

import Data.Graph

notContains :: Contains m => Index m -> Lens' m Bool
notContains i = lens (^.contains i.to not) (\m b -> m & contains i .~ not b)
{-# INLINE notContains #-}

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

-- |Implements a relatively stable topological sort.  Given
--
-- > stableTopoSortBy names dependencies objs = sorted
--
-- Then @sorted@ is a permutation of @objs@ such that, for any object @obj@ in
-- @objs@, all objects named by @dependencies obj@ precede it.  The names of an
-- object are given by @names obj@.  This algorithm is best-effort if there are
-- cycles.  See also 'stableTopoSortByPlus'.
--
-- This algorithm was inspired by pshub's answer to grimner's Stack Overflow
-- question "Stable topological sort"
-- <https://stackoverflow.com/a/11236027/237428>.  However, it doesn't implement
-- the full priority queue solution.
stableTopoSortBy :: (Foldable f1, Foldable f2, Foldable f3, Ord k)
                 => (a -> f1 k) -- ^ The names of each object
                 -> (a -> f2 k) -- ^ The dependencies of each object (they will /precede/ it)
                 -> f3 a        -- ^ The objects to sort
                 -> [a]
stableTopoSortBy names dependencies objs =
  (`appEndo` []) . snd $ execRWS (traverse_ visit $ M.keysSet objsById) () IS.empty
  where
    objsById  = M.fromList $ zip [0..] (toList objs)
    idsByName = M.fromList $ [ (name, oid)
                             | (oid, obj) <- M.assocs objsById
                             , name <- toList $ names obj ]
    
    visit oid = unlessM (use $ contains oid) $ do
                  contains oid .= True
                  let obj = objsById M.! oid
                  traverse_ (traverse_ visit . (M.lookup ?? idsByName)) $ dependencies obj
                  tell . Endo $ (obj :)

-- |Like 'stableTopoSortBy', but includes extra by-name dependencies.  Given
--
-- > stableTopoSortByPlus names dependencies extraDependencies objs = sorted
--
-- Then if an object @obj@ has the name @n@, it also must be preceded by every
-- element of @extraDependencies n@.
stableTopoSortByPlus :: (Foldable f1, Foldable f2, Foldable f3, Foldable f4, Ord k)
                     => (a -> f1 k) -> (a -> f2 k) -> (k -> f3 k) -> f4 a -> [a]
stableTopoSortByPlus names dependencies extraDependencies =
  stableTopoSortBy names $ \obj ->
    toList (dependencies obj) ++ foldMap (toList . extraDependencies) (names obj)

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
