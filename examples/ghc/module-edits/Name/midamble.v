(* BUG: record selctors are not fully qualified. *)
Import OccName.
Import Module.

(* Default values *)
Import Panic.

Instance Unique_Name : Unique.Uniquable Name.Name := {}.
Admitted.
