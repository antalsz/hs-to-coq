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

(* Converted type declarations: *)

Inductive BitQueueB : Type := BQB : GHC.Num.Word -> GHC.Num.Word -> BitQueueB.

Inductive BitQueue : Type := BQ : BitQueueB -> BitQueue.
(* Converted value declarations: *)

Axiom emptyQB : forall {A : Type}, A.

Axiom toListQ : forall {A : Type}, A.

Axiom unconsQ : forall {A : Type}, A.

Axiom snocQB : forall {A : Type}, A.

Axiom shiftQBR1 : forall {A : Type}, A.

Axiom buildQ : forall {A : Type}, A.

Axiom nullQ : forall {A : Type}, A.

(* Unbound variables:
     GHC.Num.Word
*)
