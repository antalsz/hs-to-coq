(* Preamble *)
Require Import GHC.Base.
Require Import GHC.Num.
Require Import GHC.List.
Require Import GHC.Enum.
Import GHC.Base.Notations.

Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This file is very different from the standard library so that it
   can take advantage of Coq's existing formalization of
   rational numbers. *)

(* Rational numbers *)

Require Import ZArith.
Require Import QArith.
Require Import QArith.QArith_base.

Definition Rational := QArith_base.Q.

Definition Qabs (q : Rational) : Rational :=
  match ((QArith_base.Qnum q) ?= 0)%Z with
    | Lt => QArith_base.Qinv q
    | _ => q
  end.

Definition Qsignum (q : Rational) : Rational :=
  QArith_base.Qmake (Z.sgn (QArith_base.Qnum q)) (QArith_base.Qden q).

Instance Num_Q__ : Num Rational := {
  op_zp__   := QArith_base.Qplus;
  op_zm__   := QArith_base.Qminus;
  op_zt__   := QArith_base.Qmult;
  abs         := Qabs;
  fromInteger := fun x => QArith_base.Qmake x 1;
  negate      := QArith_base.Qinv;
  signum      := Qsignum; }.


 Instance Eq_Q : Eq_ Rational := fun _ k => k {|
   op_zeze____ := Qeq_bool;
   op_zsze____ := fun x y => negb (Qeq_bool x y)
 |}.

 Instance Ord_Q : Ord Rational :=
   ord_default Qcompare.


Definition numerator := QArith_base.Qnum.
Definition denominator := QArith_base.Qden.


Class Real a `{(Num a)} `{(Ord a)} := {
  toRational : (a -> Rational) }.

Class Integral a `{(Real a)} `{(Enum a)} := {
  div : (a -> (a -> a)) ;
  divMod : (a -> (a -> (a * a))) ;
  mod_ : (a -> (a -> a)) ;
  quot : (a -> (a -> a)) ;
  quotRem : (a -> (a -> (a * a))) ;
  rem : (a -> (a -> a)) ;
  toInteger : (a -> Z) }.

Class Fractional a `{((Num a))} := {
  op_zs__ : (a -> (a -> a)) ;
  fromRational : (Rational -> a) ;
  recip : (a -> a) }.

Infix "/" := (op_zs__) (left associativity, at level 40).

Notation "'_/_'" := (op_zs__).

Class RealFrac a `{(Real a)} `{(Fractional a)} := {
  ceiling : (forall {b}, (forall `{((Integral b))}, (a -> b))) ;
  floor : (forall {b}, (forall `{((Integral b))}, (a -> b))) ;
  properFraction : (forall {b}, (forall `{((Integral b))}, (a -> (b * a)))) ;
  round : (forall {b}, (forall `{((Integral b))}, (a -> b))) ;
  truncate : (forall {b}, (forall `{((Integral b))}, (a -> b))) }.

Definition realToFrac {a} {b} `{(Real a)} `{(Fractional b)} : (a -> b) :=
  (fromRational ∘ toRational).

Definition ratioPrec : Int := #7.

Definition ratioPrec1 : Int := (ratioPrec + #1)%Z.

Definition fromIntegral {a} {b} `{(Integral a)} `{(Num b)} : (a -> b) :=
  (fromInteger ∘ toInteger).

Instance instance__Real_Int__72__ : (Real Int) := {
  toRational := (fun x => QArith_base.Qmake x 1)
}.

Instance instance__Integral_Int__74__ : (Integral Int) := {
  toInteger := id ;
  quot := Z.quot ;
  rem := Z.rem ;
  div := Z.rem ;
  mod_ := Z.modulo ;
  quotRem := Z.quotrem ;
  divMod := fun x y => (Z.div x y, Z.modulo x y) }.

Instance instance__Real_Word : (Real Word) := {
  toRational := (fun x => QArith_base.Qmake (Z.of_N x) 1)
}.

Instance instance__Integral_Word : (Integral Word) := {
  toInteger := Z.of_N ;
  quot := N.div ;
  rem := N.modulo ;
  div := N.div ;
  mod_ := N.modulo ;
  quotRem := fun x y => (N.div x y, N.modulo x y) ;
  divMod := fun x y => (N.div x y, N.modulo x y) }.


Definition even {a} `{Integral a} : a -> bool :=
  fun a => (rem a (fromInteger 2) GHC.Base.== fromInteger 0).
Definition odd {a} `{Integral a} : a -> bool :=
  fun a => negb (even a).

Module Notations.
Infix "GHC.Real./" := (op_zs__) (left associativity, at level 40).
Notation "'_GHC.Real./_'" := (op_zs__).
End Notations.

