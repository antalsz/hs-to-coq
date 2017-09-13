(* Default settings (from HsToCoq.Coq.Preamble) *)

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Axiom patternFailure : forall {a}, a.

(* Preamble *)

(* Successfully converted the following code: *)
Definition op_za__ {a} {b} : a -> ((a -> b) -> b) :=
  fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | x , f => f x end.
Infix "&" := (op_za__) (at level 99).
Notation "'_&_'" := (op_za__).
