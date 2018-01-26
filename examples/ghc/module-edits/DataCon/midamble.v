Import FieldLabel.

Require GHC.Err.
Instance Default_DataCon : GHC.Err.Default DataCon := {}.
Admitted.

Instance Uniqable_DataCon : Unique.Uniquable DataCon := {}.
Admitted.

(* Parameter dataConRepArgTys : DataCon -> list unit. *)
