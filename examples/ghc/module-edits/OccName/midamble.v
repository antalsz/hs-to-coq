(* records field accesses are not fully qualified. *)
Require Import Module.

Instance Uniquable_OccName : Unique.Uniquable OccName := {}.
Admitted.

(* Default values *)
Import Panic.
Instance Default_NameSpace : Default NameSpace := Build_Default _ VarName.
Instance Default_OccName : Default OccName := Build_Default _ (Mk_OccName default default).
