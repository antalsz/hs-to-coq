(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Definition on {a}{b}{c} (op : b -> b -> c) (f: a -> b) := fun x y => op (f x) (f y).
(* No imports to convert. *)

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition op_za__ {a} {b} : a -> (a -> b) -> b :=
  fun x f => f x.

Infix "&" := (op_za__) (at level 99).

Notation "'_&_'" := (op_za__).
