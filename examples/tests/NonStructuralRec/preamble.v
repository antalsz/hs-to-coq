Require Coq.Program.Tactics.
Require Omega.
Ltac prog_omega := Coq.Program.Tactics.program_simpl;simpl;Omega.omega.
