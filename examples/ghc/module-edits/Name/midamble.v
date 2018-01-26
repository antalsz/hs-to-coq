(* BUG: record selctors are not fully qualified. *)
Import OccName.
Import Module.

(* Default values *)
Require Import GHC.Err.
Instance Default_NameSort : Default NameSort := Build_Default _ System.
Instance Default_Name : Default Name := Build_Default _ (Mk_Name default default default default).


Instance Unique_Name : Unique.Uniquable Name.Name := {}.
Admitted.
