{-# LANGUAGE BangPatterns #-}
module Main where

import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Criterion.Main (bench, defaultMain, whnf)
import qualified Data.List (foldl')
import qualified Data.Foldable (fold)

import Base
import Datatypes
import qualified ExtractedSet as S

import qualified Data.Set as S1

main = do
    let s = S.fromAscList elems :: S.Set Int
        s_even = S.fromAscList elems_even :: S.Set Int
        s_odd = S.fromAscList elems_odd :: S.Set Int
    evaluate $ rnf [s, s_even, s_odd]
    defaultMain
        [ bench "member" $ whnf (member elems) s
        , bench "insert" $ whnf (ins elems) S.empty
        , bench "map" $ whnf (S.map (+ 1)) s
        , bench "filter" $ whnf (S.filter ((== 0) . (`mod` 2))) s
        , bench "partition" $ whnf (S.partition ((== 0) . (`mod` 2))) s
        , bench "fold" $ whnf (S.fold (:) []) s
        , bench "delete" $ whnf (del elems) s
--        , bench "findMin" $ whnf S.findMin s
--        , bench "findMax" $ whnf S.findMax s
--        , bench "deleteMin" $ whnf S.deleteMin s
--        , bench "deleteMax" $ whnf S.deleteMax s
        , bench "unions" $ whnf S.unions [s_even, s_odd]
        , bench "union" $ whnf (S.union s_even) s_odd
        , bench "difference" $ whnf (S.difference s) s_even
        , bench "intersection" $ whnf (S.intersection s) s_even
        , bench "fromList" $ whnf S.fromList elems
        , bench "fromList-desc" $ whnf S.fromList (reverse elems)
        , bench "fromAscList" $ whnf S.fromAscList elems
        , bench "fromDistinctAscList" $ whnf S.fromDistinctAscList elems
        , bench "disjoint:false" $ whnf (S.disjoint s) s_even
        , bench "disjoint:true" $ whnf (S.disjoint s_odd) s_even
        , bench "null.intersection:false" $ whnf (S.null. S.intersection s) s_even
        , bench "null.intersection:true" $ whnf (S.null. S.intersection s_odd) s_even
        ]
  where
    elems = [1..2^12]
    elems_even = [2,4..2^12]
    elems_odd = [1,3..2^12]

member :: [Int] -> S.Set Int -> Int
member xs s = Data.List.foldl' (\n x -> if S.member x s then n + 1 else n) 0 xs

ins :: [Int] -> S.Set Int -> S.Set Int
ins xs s0 = Data.List.foldl' (\s a -> S.insert a s) s0 xs

del :: [Int] -> S.Set Int -> S.Set Int
del xs s0 = Data.List.foldl' (\s k -> S.delete k s) s0 xs



{-
s1 = S1.fromAscList elems :: S1.Set Int
s2 = S2.fromAscList elems :: S2.Set Int
elems = [0..1000]

main = do
--    evaluate $ rnf [s]
    defaultMain
      [ bench "member (Haskell)" $ whnf (member1 elems) s1
      , bench "member (Coq)"     $ whnf (member2 elems) s2]

member1 :: [Int] -> S1.Set Int -> Bool
member1 xs s = all (\x -> S1.member x s) xs

member2 :: [Int] -> S2.Set Int -> Bool
member2 xs s = all (\x -> S2.member x s) xs
-}

{- Unfortunately, does not work, because Base.Eq_ is a tricky type synonym:
    type Eq_ a = () -> ((Eq___Dict a) -> Any) -> Any

class ToHaskell ct hs | ct -> hs where toHaskell :: ct -> hs

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

instance (Prelude.Eq a, ToHaskell b1 b2) => ToHaskell (Base.Eq_ a -> b1) b2 where
    toHaskell f = toHaskell $ f (Base.Eq___Dict_Build (==) (/=))
instance (Prelude.Ord a, ToHaskell b1 b2) => ToHaskell (Base.Ord a -> b1) b2 where
    toHaskell f = toHaskell $ f (ord_default Prelude.compare (Base.Eq___Dict_Build (==) (/=)))
instance ToHaskell b1 b2 => ToHaskell (a -> b1) (a -> b2) where
    toHaskell f = \x -> toHaskell (f x)
instance ToHaskell a a where
    toHaskell x = x
-}

