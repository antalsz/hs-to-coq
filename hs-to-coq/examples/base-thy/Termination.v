(** This module contains auxillary definitions for termination proofs,
  in particular a well-founded relation for Int and Integer. *)

Require Import Proofs.GHC.Base.
Require Import ZArith.


(* < on Z is well-founded when restricted to the non-negatives. *)
Definition NonNeg  (x:Z) (y:Z) : Prop :=
  (0 <= x /\ x < y)%Z.