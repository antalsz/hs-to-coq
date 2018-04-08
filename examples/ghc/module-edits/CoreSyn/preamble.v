Require Import Coq.ZArith.ZArith.
Require Import Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.