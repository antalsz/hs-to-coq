(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Import Data.Foldable.
Require Import GHC.Base.
Require Import Types.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition simpleCountFile : String -> Counts :=
  foldMap countChar.

(* External variables:
     Counts String countChar foldMap
*)
