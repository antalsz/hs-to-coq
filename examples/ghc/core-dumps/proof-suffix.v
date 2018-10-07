Require Import Proofs.ScopeInvariant.
Goal WellScopedProgram program.
Proof.
repeat (lazy; constructor).
(* This is for the NoDup goals: *)
all: rewrite ?IntSetProofs.In_cons_iff; intuition congruence.
Qed.
Require Import Proofs.JoinPointInvariants.
Goal isJoinPointsValidProgram program.
Proof.
repeat (lazy; constructor).
Qed.