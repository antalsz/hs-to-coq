module Bench where

import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Criterion.Main (bench, defaultMain, whnf)
import List (fold_left)

import Base
import Datatypes
import qualified Internal as S


eq_int :: Base.Eq_ Int
eq_int _ f = f (Base.Eq___Dict_Build (==) (/=))

ord_int :: Base.Ord Int
ord_int _ = ord_default Prelude.compare eq_int

s = S.fromAscList eq_int elems :: S.Set_ Int
elems = (Coq_cons 2 Coq_nil) -- (Coq_cons 3 (Coq_cons 4 Coq_nil)))

main = do
--    evaluate $ rnf [s]
    defaultMain
      [ bench "member" $ whnf (member elems) s ]

   

member :: Datatypes.Coq_list Int -> S.Set_ Int -> Int
member xs s = fold_left (\n x -> if S.member eq_int ord_int x s then n + 1 else n) xs 0 
