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

Axiom emptyQB : BitQueueB.

Axiom toListQ : BitQueue -> list bool.

Axiom unconsQ : BitQueue -> option (bool * BitQueue)%type.

Axiom snocQB : BitQueueB -> bool -> BitQueueB.

Axiom shiftQBR1 : BitQueueB -> BitQueueB.

Axiom buildQ : BitQueueB -> BitQueue.

Axiom nullQ : BitQueue -> bool.

(* Unbound variables:
     bool list op_zt__ option GHC.Num.Word
*)
