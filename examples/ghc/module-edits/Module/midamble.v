Require Import GHC.Err.

Instance Default__UnitId : Default UnitId := Build_Default _ (PId default).
Instance Default__ModuleName : Default ModuleName :=
  Build_Default _ (Mk_ModuleName default).
Instance Default__Module : Default Module :=
  Build_Default _ (Mk_Module default default).
Instance Default__NDModule : Default NDModule :=
  Build_Default _ (Mk_NDModule default).
Instance Default__ModLocation : Default ModLocation :=
  Build_Default _ (Mk_ModLocation default default default).


Instance instance_Uniquable_ModuleName : Unique.Uniquable ModuleName := {}.
Admitted.
Instance instance_Uniquable_UnitId : Unique.Uniquable UnitId := {}.
Admitted.

Instance Unpeel_UnitId : Prim.Unpeel UnitId FastString.FastString :=
  Prim.Build_Unpeel _ _ (fun arg_102__ => match arg_102__ with | PId fs => fs end) PId.
Instance Unpeel_ModuleName : Prim.Unpeel ModuleName FastString.FastString :=
  Prim.Build_Unpeel _ _ (fun arg_142__ => match arg_142__ with | Mk_ModuleName mod_ => mod_ end) Mk_ModuleName.
Instance Unpeel_NDModule : Prim.Unpeel NDModule Module :=
  Prim.Build_Unpeel _ _ (fun arg_142__ => match arg_142__ with | Mk_NDModule mod_ => mod_ end) Mk_NDModule.




(*
Definition moduleNameSlashes : ModuleName -> GHC.Base.String := fun x => default.
Definition mkModuleName : GHC.Base.String -> ModuleName := fun x => default.
*)