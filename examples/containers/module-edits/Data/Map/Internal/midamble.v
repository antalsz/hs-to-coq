Require Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

Fixpoint map_size {a} {b} (s : Map a b) : nat :=
  match s with
  | Tip => 0
  | Bin _ _ _ s1 s2 => 1 + map_size s1 + map_size s2
  end.

Require Import GHC.Err.

Instance Map_Default {k}{v} : Default (Map k v) :=
  Build_Default _ Tip.
Instance AlteredDefault {k}{v} : Default (Altered k v) :=
  Build_Default _ AltSame.
