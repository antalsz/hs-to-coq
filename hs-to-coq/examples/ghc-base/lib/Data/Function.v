(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Preamble *)

Definition on {a}{b}{c} (op : b -> b -> c) (f: a -> b) := fun x y => op (f x) (f y).
(* No imports to convert. *)

(* Converted declarations: *)

Definition op_za__ {a} {b} : a -> (a -> b) -> b :=
  fun arg_0__ arg_1__ => match arg_0__ , arg_1__ with | x , f => f x end.

Infix "&" := (op_za__) (at level 99).

Notation "'_&_'" := (op_za__).
