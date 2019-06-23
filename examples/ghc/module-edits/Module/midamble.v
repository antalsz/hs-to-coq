Require Import GHC.Err.

Instance Default__InstalledUnitId : Default InstalledUnitId := 
  Build_Default _ (Mk_InstalledUnitId default ).
Instance Default__DefUnitId : Default DefUnitId := 
  Build_Default _ (Mk_DefUnitId default).
Instance Default__UnitId : Default UnitId := 
  Build_Default _ (DefiniteUnitId default).
Instance Default__ModuleName : Default ModuleName :=
  Build_Default _ (Mk_ModuleName default).
Instance Default__Module : Default Module :=
  Build_Default _ (Mk_Module default default).
Instance Default__NDModule : Default NDModule :=
  Build_Default _ (Mk_NDModule default).
Instance Default__ModLocation : Default ModLocation :=
  Build_Default _ (Mk_ModLocation default default default).

Instance Unpeel_DefUnitId : Prim.Unpeel DefUnitId InstalledUnitId :=
  Prim.Build_Unpeel _ _ (fun arg_102__ => match arg_102__ with | Mk_DefUnitId fs => fs end) Mk_DefUnitId.
Instance Unpeel_NDModule : Prim.Unpeel NDModule Module :=
  Prim.Build_Unpeel _ _ (fun arg_142__ => match arg_142__ with | Mk_NDModule mod_ => mod_ end) Mk_NDModule.

