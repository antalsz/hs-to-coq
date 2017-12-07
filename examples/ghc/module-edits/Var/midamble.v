Instance Unique_Var : Unique.Uniquable Var := {}.
Admitted.

Require Import Panic.
Instance Default_IdScope : Default IdScope := Build_Default _ GlobalId.
Instance Default_Var : Default Var := Build_Default _ (Mk_Id default default default default default default).

