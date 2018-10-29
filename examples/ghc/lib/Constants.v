(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Nat.

(* Converted imports: *)

Require GHC.Num.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition wORD64_SIZE : nat :=
  #8.

Definition tARGET_MAX_CHAR : nat :=
  #1114111.

Definition mAX_TUPLE_SIZE : nat :=
  #62.

Definition mAX_SUM_SIZE : nat :=
  #62.

Definition mAX_SOLVER_ITERATIONS : nat :=
  #4.

Definition mAX_REDUCTION_DEPTH : nat :=
  #200.

Definition mAX_CTUPLE_SIZE : nat :=
  #62.

Definition fLOAT_SIZE : nat :=
  #4.

(* External variables:
     nat GHC.Num.fromInteger
*)
