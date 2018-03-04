Require Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

Fixpoint set_size {a} (s : Set_ a) : nat :=
  match s with
  | Tip => 0
  | Bin _ _ s1 s2 => 1 + set_size s1 + set_size s2
  end.

Require Import GHC.Err.

Instance Set_Default {a} : Default (Set_ a) :=
  Build_Default _ Tip.
Instance MergeSetDefault {a} : Default (MergeSet a) :=
  Build_Default _ (Mk_MergeSet default).
