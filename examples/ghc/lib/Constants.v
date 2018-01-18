(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Num.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition mAX_CTUPLE_SIZE : GHC.Num.Int :=
  GHC.Num.fromInteger 62.

Definition mAX_REDUCTION_DEPTH : GHC.Num.Int :=
  GHC.Num.fromInteger 200.

Definition mAX_SOLVER_ITERATIONS : GHC.Num.Int :=
  GHC.Num.fromInteger 4.

Definition mAX_TUPLE_SIZE : GHC.Num.Int :=
  GHC.Num.fromInteger 62.

Definition tARGET_MAX_CHAR : GHC.Num.Int :=
  GHC.Num.fromInteger 1114111.

Definition wORD64_SIZE : GHC.Num.Int :=
  GHC.Num.fromInteger 8.

(* Unbound variables:
     GHC.Num.Int
*)
