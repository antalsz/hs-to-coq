(* The Num class and the Int, Integer and Word Types *)

Require Export ZArith.
Definition Integer  := Z.

Definition Int      := Z.   (* A lie. Sorta. But it is signed. *)

(*
-- TODO: support Int#
Definition IntHash : Type := Z.
Notation "Int#" := IntHash.

Inductive Int := IHash : Int# -> Int.
Notation "I#" := IHash.

Definition TupleHash : Type -> Type -> Type := prod.
Notation "(# a , b #)" := (TupleHash a b).
*)


Require Export NArith.
Definition Word     := N.

Class Num a := {
  op_zp__     : a -> a -> a ;   (* plus *)
  op_zm__     : a -> a -> a ;   (* minus *)
  op_zt__     : a -> a -> a ;   (* times *)
  abs         : a -> a ;
  fromInteger : Z -> a ;
  negate      : a -> a ;
  signum      : a -> a
}.

Infix    "+"     := op_zp__ (at level 50, left associativity).
Notation "'_+_'" := op_zp__.

Infix    "-"     := op_zm__ (at level 50, left associativity).
Notation "'_-_'" := op_zm__.

Infix    "*"     := op_zt__ (at level 40, left associativity).
Notation "'_*_'" := op_zt__.

Notation "'#' n" := (fromInteger n) (at level 1, format "'#' n").

Instance Num_Int__ : Num Int := {
  op_zp__   := Z.add %Z;
  op_zm__   := Z.sub %Z;
  op_zt__   := Z.mul %Z;
  abs         := Z.abs %Z;
  fromInteger := fun x => x;
  negate      := Z.opp %Z;
  signum      := Z.sgn %Z; }.

Instance Num_Integer__ : Num Integer := {
  op_zp__   := Z.add %Z;
  op_zm__   := Z.sub %Z;
  op_zt__   := Z.mul %Z;
  abs         := Z.abs %Z;
  fromInteger := fun x => x;
  negate      := Z.opp %Z;
  signum      := Z.sgn %Z; }.

Instance Num_Word__ : Num Word := {
  op_zp__   := N.add %N;
  op_zm__   := N.sub %N;
  op_zt__   := N.mul %N;
  abs         := fun x => x;
  fromInteger := Z.to_N;
  negate      := fun x => x;
  signum      := fun x => match x with | N0 => N0 | _ => 1%N  end }.

Module Notations.
Infix    "GHC.Num.+"     := op_zp__ (at level 50, left associativity).
Notation "'_GHC.Num.+_'" := op_zp__.

Infix    "GHC.Num.-"     := op_zm__ (at level 50, left associativity).
Notation "'_GHC.Num.-_'" := op_zm__.

Infix    "GHC.Num.*"     := op_zt__ (at level 40, left associativity).
Notation "'_GHC.Num.*_'" := op_zt__.
End Notations.
