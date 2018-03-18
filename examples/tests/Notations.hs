module Notations where

test :: Int -> Int -> Int
test x y =
  let q | x == 2 && y == -1 = x
        | y == 0 = -1
        | otherwise = quot x y
  in q * 2

{- 

-- The goal of this test is to add edits to
-- transform the above into something like this:

Require Import Coq.ZArith.BinInt.

Open Scope bool_scope.
Open Scope Z_scope.

Definition test(x y: Z) :=
  let q := if (x =? 2) && (y =? -1) then x
           else if (y =? 0) then -1
           else x / y
  in q * 2.

-- The closest I can get so far is

Definition test : Z -> Z -> Z :=
  fun x y =>
    let q :=
      if andb (eqb x #2) (eqb y (GHC.Num.negate #1)) : bool
      then x
      else if eqb y #0 : bool
           then GHC.Num.negate #1
           else quot x y in
    mul q #2.

-- We need to still get rid of the
-- GHC.Num.fromInteger and GHC.Num.negate
-- and provide a way to specify notations in the edit file

-}

