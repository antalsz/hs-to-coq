(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* No imports to convert. *)

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition on {b} {c} {a} : (b -> b -> c) -> (a -> b) -> a -> a -> c :=
  fun op_ziztzi__ f => fun x y => op_ziztzi__ (f x) (f y).

Definition op_za__ {a} {b} : a -> (a -> b) -> b :=
  fun x f => f x.

Infix "&" := (op_za__) (at level 99).

Notation "'_&_'" := (op_za__).

Module Notations.
Infix "Data.Function.&" := (op_za__) (at level 99).
Notation "'_Data.Function.&_'" := (op_za__).
End Notations.
