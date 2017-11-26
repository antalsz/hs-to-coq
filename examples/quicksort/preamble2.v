Require Proofs.Data.OldList.
Require Omega.
Require Import Coq.Lists.List.
Ltac solve_quicksort_termination :=
  Coq.Program.Tactics.program_simpl;
  match goal with [ H : (_,_) = OldList.partition _ _ |- _ ] =>
    rewrite Proofs.Data.OldList.hs_coq_partition in H end;
  match goal with [ H : (_,_) = partition _ _ |- _ ] =>
    symmetry in H end;
  match goal with [ H : partition _ _ = (_,_) |- _ ] =>
    apply partition_length in H end;
  simpl;Omega.omega.
