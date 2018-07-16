Require Import Proofs.ScopeInvariant.
Goal WellScopedProgram program.
repeat (lazy; constructor).
(* This is for the NoDup goals: *)
all: rewrite ?IntSetProofs.In_cons_iff; intuition congruence.
Qed.