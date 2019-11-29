Require Import GHC.Base.
Require Import GHC.Num.
Require Import GHC.Real.
Require Import Coq.micromega.OrderedRing.
Require Import Proofs.GHC.Base.
Require Import OrdTactic.

(*Instances of GHC.Real do not necessarily need to be an ordered ring, but if they are, they
  should satify the following laws, which allows us to use OrderedRing tactics and theorems  *)

Class RealRing (b: Type) {Heq: Eq_ b} {Hord: Ord b} {Heqlaws: EqLaws b} {Hnum: Num b}
  {Hreal: Real b}  := {
  real_ring: @SOR b #0 #1 op_zp__ op_zt__ op_zm__ negate (fun x y => x == y = true)
    (fun x y => x <= y = true) (fun x y => x < y = true);
  rplus_eq: forall x y : b, (x == y) = true -> 
    forall x0 y0 : b, (x0 == y0) = true -> (_+_ x x0 == _+_ y y0) = true;
  rtimes_eq: forall x y : b, (x == y) = true -> 
    forall x0 y0 : b, (x0 == y0) = true -> (_*_ x x0 == _*_ y y0) = true;
  negate_eq: forall x y : b, (x == y) = true -> (negate x == negate y) = true;
  rle_eq: forall x y : b, (x == y) = true -> 
    forall x0 y0 : b, (x0 == y0) = true -> (x <= x0) = true <-> (y <= y0) = true;
  rlt_eq: forall x y : b, (x == y) = true -> 
    forall x0 y0 : b, (x0 == y0) = true -> (x < x0) = true <-> (y < y0) = true
}.

