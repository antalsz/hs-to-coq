Instance Default_Step {a} : GHC.Err.Default (Step a) :=
  GHC.Err.Build_Default _ Done.
Instance Default_Value : GHC.Err.Default Value :=
  GHC.Err.Build_Default _ (LitVal GHC.Err.default).
Instance Default_StackElem : GHC.Err.Default StackElem :=
  GHC.Err.Build_Default _ (Update GHC.Err.default).

(* ----------- termination metric for step function --------------- *)

Require Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

Ltac solve_step_obligations :=
  repeat split; intros; try discriminate; termination_by_omega.

Definition step_measure (conf : Conf) : nat := 
  match conf with 
  | (heap , expr, stack ) => CoreSyn.size_Expr expr 
  end.

(* ----------- ----------------------------------- --------------- *)