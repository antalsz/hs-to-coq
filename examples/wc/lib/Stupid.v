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
Require Data.OldList.
Require Import GHC.Base.
Require Import Types.

(* No type declarations to convert. *)

(* Midamble *)

Fixpoint length {a} (xs : list a) : Int :=
  match xs with 
  | nil => # 0
  | cons _ ys => (1 + (length ys))%Z
  end.

(* Converted value declarations: *)

Definition stupidCountFile : String -> Counts :=
  fun s =>
    fromTuple (pair (pair (length s) (length (Data.OldList.words s))) (length
                     (Data.OldList.lines s))).

(* External variables:
     Counts String fromTuple length pair Data.OldList.lines Data.OldList.words
*)
