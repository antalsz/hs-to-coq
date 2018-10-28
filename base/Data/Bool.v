(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* No imports to convert. *)

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition bool {a} : a -> a -> bool -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, _, false => f
    | _, t, true => t
    end.

(* External variables:
     bool false true
*)
