module Main where

import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Criterion.Main (bench, defaultMain, whnf)
import List (fold_left)
import qualified Data.Set as S1

import Base
import Datatypes
import qualified Internal as S2
eq_int :: Base.Eq_ Int
eq_int _ f = f (Base.Eq___Dict_Build (==) (/=))

ord_int :: Base.Ord Int
ord_int _ = ord_default Prelude.compare eq_int

s1 = S1.fromAscList elems :: S1.Set Int
s2 = S2.fromAscList eq_int elems :: S2.Set_ Int
elems = [0..1000]

main = do
--    evaluate $ rnf [s]
    defaultMain
      [ bench "member (Haskell)" $ whnf (member1 elems) s1
      , bench "member (Coq)"     $ whnf (member2 elems) s2]

member1 :: [Int] -> S1.Set Int -> Bool
member1 xs s = all (\x -> S1.member x s) xs

member2 :: [Int] -> S2.Set_ Int -> Bool
member2 xs s = all (\x -> S2.member eq_int ord_int x s) xs

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

