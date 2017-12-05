(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require Data.Set.Base.
Require FastString.
Require GHC.Base.
Require GHC.Prim.
Require UniqFM.
Require Unique.
Require Util.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UnitId : Type := PId : FastString.FastString -> UnitId.

Definition ModuleNameEnv :=
  UniqFM.UniqFM%type.

Inductive ModuleName : Type := Mk_ModuleName
                              : FastString.FastString -> ModuleName.

Inductive ModuleEnv (elt : Type) : Type := Mk_ModuleEnv.

Inductive Module : Type := Mk_Module : UnitId -> ModuleName -> Module.

Inductive NDModule : Type := Mk_NDModule : Module -> NDModule.

Definition ModuleSet :=
  (Data.Set.Base.Set_ NDModule)%type.

Inductive ModLocation : Type := Mk_ModLocation : option
                                                 GHC.Base.String -> GHC.Base.String -> GHC.Base.String -> ModLocation.

Record HasModule__Dict m := HasModule__Dict_Build {
  getModule__ : m Module }.

Definition HasModule m :=
  forall r, (HasModule__Dict m -> r) -> r.

Existing Class HasModule.

Definition getModule `{g : HasModule m} : m Module :=
  g _ (getModule__ m).

Record ContainsModule__Dict t := ContainsModule__Dict_Build {
  extractModule__ : t -> Module }.

Definition ContainsModule t :=
  forall r, (ContainsModule__Dict t -> r) -> r.

Existing Class ContainsModule.

Definition extractModule `{g : ContainsModule t} : t -> Module :=
  g _ (extractModule__ t).

Definition moduleName (arg_0__ : Module) :=
  match arg_0__ with
    | Mk_Module _ moduleName => moduleName
  end.

Definition moduleUnitId (arg_1__ : Module) :=
  match arg_1__ with
    | Mk_Module moduleUnitId _ => moduleUnitId
  end.

Definition unNDModule (arg_2__ : NDModule) :=
  match arg_2__ with
    | Mk_NDModule unNDModule => unNDModule
  end.

Definition ml_hi_file (arg_3__ : ModLocation) :=
  match arg_3__ with
    | Mk_ModLocation _ ml_hi_file _ => ml_hi_file
  end.

Definition ml_hs_file (arg_4__ : ModLocation) :=
  match arg_4__ with
    | Mk_ModLocation ml_hs_file _ _ => ml_hs_file
  end.

Definition ml_obj_file (arg_5__ : ModLocation) :=
  match arg_5__ with
    | Mk_ModLocation _ _ ml_obj_file => ml_obj_file
  end.
(* Midamble *)

Import Panic.

Instance Default_UnitId : Default UnitId := Build_Default _ (PId default).
Instance Default_ModuleName : Default ModuleName :=
  Build_Default _ (Mk_ModuleName default).
Instance Default_Module : Default Module :=
  Build_Default _ (Mk_Module default default).
Instance Default_NDModule : Default NDModule :=
  Build_Default _ (Mk_NDModule default).
Instance Default_ModLocation : Default ModLocation :=
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
(* Converted value declarations: *)

(* Translating `instance Outputable.Outputable Module.ModLocation' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Unique.Uniquable Module.ModuleName' failed: OOPS!
   Cannot find information for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition Eq___ModuleName_op_zeze__ : ModuleName -> ModuleName -> bool :=
  fun nm1 nm2 => Unique.getUnique nm1 GHC.Base.== Unique.getUnique nm2.

Local Definition Eq___ModuleName_op_zsze__ : ModuleName -> ModuleName -> bool :=
  fun x y => negb (Eq___ModuleName_op_zeze__ x y).

Local Definition Ord__ModuleName_compare
    : ModuleName -> ModuleName -> comparison :=
  fun nm1 nm2 => Eq.

Local Definition Ord__ModuleName_op_zg__ : ModuleName -> ModuleName -> bool :=
  fun x y => _GHC.Base.==_ (Ord__ModuleName_compare x y) Gt.

Local Definition Ord__ModuleName_op_zgze__ : ModuleName -> ModuleName -> bool :=
  fun x y => _GHC.Base./=_ (Ord__ModuleName_compare x y) Lt.

Local Definition Ord__ModuleName_op_zl__ : ModuleName -> ModuleName -> bool :=
  fun x y => _GHC.Base.==_ (Ord__ModuleName_compare x y) Lt.

Local Definition Ord__ModuleName_op_zlze__ : ModuleName -> ModuleName -> bool :=
  fun x y => _GHC.Base./=_ (Ord__ModuleName_compare x y) Gt.

Local Definition Ord__ModuleName_max : ModuleName -> ModuleName -> ModuleName :=
  fun x y => if Ord__ModuleName_op_zlze__ x y : bool then y else x.

Local Definition Ord__ModuleName_min : ModuleName -> ModuleName -> ModuleName :=
  fun x y => if Ord__ModuleName_op_zlze__ x y : bool then x else y.

(* Translating `instance Outputable.Outputable Module.ModuleName' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Binary.Binary Module.ModuleName' failed: OOPS! Cannot
   find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance GHC.PackageDb.BinaryStringRep Module.ModuleName'
   failed: OOPS! Cannot find information for class Qualified "GHC.PackageDb"
   "BinaryStringRep" unsupported *)

(* Translating `instance Data.Data.Data Module.ModuleName' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Control.DeepSeq.NFData Module.ModuleName' failed: OOPS!
   Cannot find information for class Qualified "Control.DeepSeq" "NFData"
   unsupported *)

(* Translating `instance Unique.Uniquable Module.Module' failed: OOPS! Cannot
   find information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Outputable.Outputable Module.Module' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Binary.Binary Module.Module' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Data.Data.Data Module.Module' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Control.DeepSeq.NFData Module.Module' failed: OOPS!
   Cannot find information for class Qualified "Control.DeepSeq" "NFData"
   unsupported *)

(* Translating `instance Unique.Uniquable Module.UnitId' failed: OOPS! Cannot
   find information for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition Ord__UnitId_compare : UnitId -> UnitId -> comparison :=
  fun nm1 nm2 => Eq.

Local Definition Ord__UnitId_op_zg__ : UnitId -> UnitId -> bool :=
  fun x y => _GHC.Base.==_ (Ord__UnitId_compare x y) Gt.

Local Definition Ord__UnitId_op_zgze__ : UnitId -> UnitId -> bool :=
  fun x y => _GHC.Base./=_ (Ord__UnitId_compare x y) Lt.

Local Definition Ord__UnitId_op_zl__ : UnitId -> UnitId -> bool :=
  fun x y => _GHC.Base.==_ (Ord__UnitId_compare x y) Lt.

Local Definition Ord__UnitId_op_zlze__ : UnitId -> UnitId -> bool :=
  fun x y => _GHC.Base./=_ (Ord__UnitId_compare x y) Gt.

Local Definition Ord__UnitId_max : UnitId -> UnitId -> UnitId :=
  fun x y => if Ord__UnitId_op_zlze__ x y : bool then y else x.

Local Definition Ord__UnitId_min : UnitId -> UnitId -> UnitId :=
  fun x y => if Ord__UnitId_op_zlze__ x y : bool then x else y.

(* Translating `instance Data.Data.Data Module.UnitId' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Control.DeepSeq.NFData Module.UnitId' failed: OOPS!
   Cannot find information for class Qualified "Control.DeepSeq" "NFData"
   unsupported *)

(* Translating `instance Outputable.Outputable Module.UnitId' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Binary.Binary Module.UnitId' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance GHC.PackageDb.BinaryStringRep Module.UnitId' failed:
   OOPS! Cannot find information for class Qualified "GHC.PackageDb"
   "BinaryStringRep" unsupported *)

Local Definition Ord__NDModule_compare : NDModule -> NDModule -> comparison :=
  fun arg_55__ arg_56__ =>
    match arg_55__ , arg_56__ with
      | Mk_NDModule (Mk_Module p1 n1) , Mk_NDModule (Mk_Module p2 n2) => Util.thenCmp
                                                                         (GHC.Base.compare (Unique.getUnique p1)
                                                                                           (Unique.getUnique p2))
                                                                         (GHC.Base.compare (Unique.getUnique n1)
                                                                                           (Unique.getUnique n2))
    end.

Local Definition Ord__NDModule_op_zg__ : NDModule -> NDModule -> bool :=
  fun x y => _GHC.Base.==_ (Ord__NDModule_compare x y) Gt.

Local Definition Ord__NDModule_op_zgze__ : NDModule -> NDModule -> bool :=
  fun x y => _GHC.Base./=_ (Ord__NDModule_compare x y) Lt.

Local Definition Ord__NDModule_op_zl__ : NDModule -> NDModule -> bool :=
  fun x y => _GHC.Base.==_ (Ord__NDModule_compare x y) Lt.

Local Definition Ord__NDModule_op_zlze__ : NDModule -> NDModule -> bool :=
  fun x y => _GHC.Base./=_ (Ord__NDModule_compare x y) Gt.

Local Definition Ord__NDModule_max : NDModule -> NDModule -> NDModule :=
  fun x y => if Ord__NDModule_op_zlze__ x y : bool then y else x.

Local Definition Ord__NDModule_min : NDModule -> NDModule -> NDModule :=
  fun x y => if Ord__NDModule_op_zlze__ x y : bool then x else y.

Local Definition Eq___UnitId_op_zeze__ : UnitId -> UnitId -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___UnitId_op_zsze__ : UnitId -> UnitId -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___UnitId : GHC.Base.Eq_ UnitId := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___UnitId_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___UnitId_op_zsze__ |}.

Program Instance Eq___ModuleName : GHC.Base.Eq_ ModuleName := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___ModuleName_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___ModuleName_op_zsze__ |}.

Local Definition Eq___Module_op_zeze__ : Module -> Module -> bool :=
  fun arg_8__ arg_9__ =>
    match arg_8__ , arg_9__ with
      | Mk_Module a1 a2 , Mk_Module b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2
                                                   GHC.Base.== b2)))
    end.

Local Definition Eq___Module_op_zsze__ : Module -> Module -> bool :=
  fun a b => negb (Eq___Module_op_zeze__ a b).

Program Instance Eq___Module : GHC.Base.Eq_ Module := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Module_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Module_op_zsze__ |}.

Local Definition Eq___NDModule_op_zeze__ : NDModule -> NDModule -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___NDModule_op_zsze__ : NDModule -> NDModule -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___NDModule : GHC.Base.Eq_ NDModule := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___NDModule_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___NDModule_op_zsze__ |}.

Program Instance Ord__UnitId : GHC.Base.Ord UnitId := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__UnitId_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__UnitId_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__UnitId_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__UnitId_op_zgze__ ;
      GHC.Base.compare__ := Ord__UnitId_compare ;
      GHC.Base.max__ := Ord__UnitId_max ;
      GHC.Base.min__ := Ord__UnitId_min |}.

Program Instance Ord__ModuleName : GHC.Base.Ord ModuleName := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__ModuleName_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__ModuleName_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__ModuleName_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__ModuleName_op_zgze__ ;
      GHC.Base.compare__ := Ord__ModuleName_compare ;
      GHC.Base.max__ := Ord__ModuleName_max ;
      GHC.Base.min__ := Ord__ModuleName_min |}.

Local Definition Ord__Module_compare : Module -> Module -> comparison :=
  fun a b =>
    match a with
      | Mk_Module a1 a2 => match b with
                             | Mk_Module b1 b2 => let scrut_13__ := (GHC.Base.compare a1 b1) in
                                                  match scrut_13__ with
                                                    | Lt => Lt
                                                    | Eq => (GHC.Base.compare a2 b2)
                                                    | Gt => Gt
                                                  end
                           end
    end.

Local Definition Ord__Module_op_zg__ : Module -> Module -> bool :=
  fun a b =>
    match a with
      | Mk_Module a1 a2 => match b with
                             | Mk_Module b1 b2 => match Ord__UnitId_compare a1 b1 with
                                                    | Lt => false
                                                    | Eq => a2 GHC.Base.> b2
                                                    | Gt => true
                                                  end
                           end
    end.

Local Definition Ord__Module_op_zgze__ : Module -> Module -> bool :=
  fun a b =>
    match a with
      | Mk_Module a1 a2 => match b with
                             | Mk_Module b1 b2 => match Ord__UnitId_compare a1 b1 with
                                                    | Lt => false
                                                    | Eq => a2 GHC.Base.>= b2
                                                    | Gt => true
                                                  end
                           end
    end.

Local Definition Ord__Module_op_zl__ : Module -> Module -> bool :=
  fun a b =>
    match a with
      | Mk_Module a1 a2 => match b with
                             | Mk_Module b1 b2 => match Ord__UnitId_compare a1 b1 with
                                                    | Lt => true
                                                    | Eq => a2 GHC.Base.< b2
                                                    | Gt => false
                                                  end
                           end
    end.

Local Definition Ord__Module_op_zlze__ : Module -> Module -> bool :=
  fun a b =>
    match a with
      | Mk_Module a1 a2 => match b with
                             | Mk_Module b1 b2 => match Ord__UnitId_compare a1 b1 with
                                                    | Lt => true
                                                    | Eq => a2 GHC.Base.<= b2
                                                    | Gt => false
                                                  end
                           end
    end.

Local Definition Ord__Module_max : Module -> Module -> Module :=
  fun x y => if Ord__Module_op_zlze__ x y : bool then y else x.

Local Definition Ord__Module_min : Module -> Module -> Module :=
  fun x y => if Ord__Module_op_zlze__ x y : bool then x else y.

Program Instance Ord__Module : GHC.Base.Ord Module := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Module_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Module_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Module_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Module_op_zgze__ ;
      GHC.Base.compare__ := Ord__Module_compare ;
      GHC.Base.max__ := Ord__Module_max ;
      GHC.Base.min__ := Ord__Module_min |}.

Program Instance Ord__NDModule : GHC.Base.Ord NDModule := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__NDModule_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__NDModule_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__NDModule_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__NDModule_op_zgze__ ;
      GHC.Base.compare__ := Ord__NDModule_compare ;
      GHC.Base.max__ := Ord__NDModule_max ;
      GHC.Base.min__ := Ord__NDModule_min |}.

(* Translating `instance GHC.Show.Show Module.ModLocation' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

Axiom addBootSuffixLocn : forall {A : Type}, A.

Axiom addBootSuffix_maybe : forall {A : Type}, A.

Axiom addBootSuffix : forall {A : Type}, A.

Axiom stableModuleCmp : forall {A : Type}, A.

Axiom stableModuleNameCmp : forall {A : Type}, A.

Axiom pprModule : forall {A : Type}, A.

Axiom pprModuleName : forall {A : Type}, A.

Axiom moduleNameFS : forall {A : Type}, A.

Axiom moduleNameColons : forall {A : Type}, A.

Axiom moduleNameSlashes : forall {A : Type}, A.

Axiom moduleStableString : forall {A : Type}, A.

Axiom moduleNameString : forall {A : Type}, A.

Axiom mkModuleName : forall {A : Type}, A.

Axiom mkModuleNameFS : forall {A : Type}, A.

Axiom mkModule : forall {A : Type}, A.

Axiom pprPackagePrefix : forall {A : Type}, A.

Axiom stableUnitIdCmp : forall {A : Type}, A.

Axiom isHoleModule : forall {A : Type}, A.

Axiom holeUnitId : forall {A : Type}, A.

Axiom mainUnitId : forall {A : Type}, A.

Axiom isInteractiveModule : forall {A : Type}, A.

Axiom interactiveUnitId : forall {A : Type}, A.

Axiom wiredInUnitIds : forall {A : Type}, A.

Axiom thisGhcUnitId : forall {A : Type}, A.

Axiom dphParUnitId : forall {A : Type}, A.

Axiom dphSeqUnitId : forall {A : Type}, A.

Axiom thUnitId : forall {A : Type}, A.

Axiom rtsUnitId : forall {A : Type}, A.

Axiom baseUnitId : forall {A : Type}, A.

Axiom integerUnitId : forall {A : Type}, A.

Axiom primUnitId : forall {A : Type}, A.

Axiom stringToUnitId : forall {A : Type}, A.

Axiom fsToUnitId : forall {A : Type}, A.

Axiom unitIdString : forall {A : Type}, A.

Axiom unitIdFS : forall {A : Type}, A.

Axiom filterModuleEnv : forall {A : Type}, A.

Axiom elemModuleEnv : forall {A : Type}, A.

Axiom extendModuleEnv : forall {A : Type}, A.

Axiom extendModuleEnvWith : forall {A : Type}, A.

Axiom extendModuleEnvList : forall {A : Type}, A.

Axiom extendModuleEnvList_C : forall {A : Type}, A.

Axiom plusModuleEnv_C : forall {A : Type}, A.

Axiom delModuleEnvList : forall {A : Type}, A.

Axiom delModuleEnv : forall {A : Type}, A.

Axiom plusModuleEnv : forall {A : Type}, A.

Axiom lookupModuleEnv : forall {A : Type}, A.

Axiom lookupWithDefaultModuleEnv : forall {A : Type}, A.

Axiom mapModuleEnv : forall {A : Type}, A.

Axiom mkModuleEnv : forall {A : Type}, A.

Axiom emptyModuleEnv : forall {A : Type}, A.

Axiom moduleEnvKeys : forall {A : Type}, A.

Axiom moduleEnvElts : forall {A : Type}, A.

Axiom moduleEnvToList : forall {A : Type}, A.

Axiom unitModuleEnv : forall {A : Type}, A.

Axiom isEmptyModuleEnv : forall {A : Type}, A.

Axiom foldModuleEnv : forall {A : Type}, A.

Axiom emptyModuleSet : forall {A : Type}, A.

Axiom mkModuleSet : forall {A : Type}, A.

Axiom extendModuleSet : forall {A : Type}, A.

Axiom moduleSetElts : forall {A : Type}, A.

Axiom elemModuleSet : forall {A : Type}, A.

(* Unbound variables:
     Eq Gt Lt Type andb bool comparison false negb option true Data.Set.Base.Set_
     FastString.FastString GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String GHC.Base.compare
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zl__
     GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.Prim.coerce UniqFM.UniqFM
     Unique.getUnique Util.thenCmp
*)
