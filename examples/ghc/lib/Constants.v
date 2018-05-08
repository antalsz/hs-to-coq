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

Require BinNums.
Require GHC.Num.
Import GHC.Num.Notations.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition fLOAT_SIZE : BinNums.N :=
  #4.

Definition mAX_CTUPLE_SIZE : BinNums.N :=
  #62.

Definition mAX_REDUCTION_DEPTH : BinNums.N :=
  #200.

Definition mAX_SOLVER_ITERATIONS : BinNums.N :=
  #4.

Definition mAX_SUM_SIZE : BinNums.N :=
  #62.

Definition mAX_TUPLE_SIZE : BinNums.N :=
  #62.

Definition tARGET_MAX_CHAR : BinNums.N :=
  #1114111.

Definition wORD64_SIZE : BinNums.N :=
  #8.

(* External variables:
     BinNums.N GHC.Num.fromInteger
*)
