(* Preamble *)
Require Import GHC.Base.
Require Import GHC.Num.
Require Import GHC.List.
Require Import GHC.Enum.

Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This file is very different from the standard library so that it
   can take advantage of Coq's existing formalization of
   rational numbers. *)

(* Rational numbers *)

Require Import ZArith.
Require Import QArith.
Module Q := Coq.QArith.QArith_base.
Definition Rational := Q.Q.

Definition Qabs (q : Rational) : Rational :=
  match ((Q.Qnum q) ?= 0)%Z with
    | Lt => Q.Qinv q
    | _ => q
  end.

Definition Qsignum (q : Rational) : Rational :=
  Q.Qmake (Z.sgn (Q.Qnum q)) (Q.Qden q).

Instance Num_Q__ : Num Rational := {
  op_zp__   := Q.Qplus;
  op_zm__   := Q.Qminus;
  op_zt__   := Q.Qmult;
  abs         := Qabs;
  fromInteger := fun x => Q.Qmake x 1;
  negate      := Q.Qinv;
  signum      := Qsignum; }.


Definition numerator := Q.Qnum.
Definition denominator := Q.Qden.


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
  toRational := (fun x => Q.Qmake x 1)
}.


Instance instance__Integral_Int__74__ : (Integral Int) := {
  toInteger := id ;
  quot := Z.quot ;
  rem := Z.rem ;
  div := Z.rem ;
  mod_ := Z.modulo ;
  quotRem := Z.quotrem ;
  divMod := fun x y => (Z.div x y, Z.modulo x y) }.
