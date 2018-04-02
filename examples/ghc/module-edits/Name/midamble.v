(* BUG: record selctors are not fully qualified. *)
Import OccName.
Import Module.

(* Default values *)
Require Import GHC.Err.
Instance Default__NameSort : Default NameSort := Build_Default _ System.
Instance Default__Name : Default Name := Build_Default _ (Mk_Name default default default default).


Instance Unique_Name : Unique.Uniquable Name := {}.
Admitted.
