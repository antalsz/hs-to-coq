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

Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Map.Base.
Require Data.OldList.
Require Data.Ord.
Require Data.Set.Base.
Require Data.Tuple.
Require FastString.
Require FiniteMap.
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

Inductive Module : Type := Mk_Module : UnitId -> ModuleName -> Module.

Inductive NDModule : Type := Mk_NDModule : Module -> NDModule.

Inductive ModuleEnv elt : Type := Mk_ModuleEnv : (Data.Map.Base.Map NDModule
                                                 elt) -> ModuleEnv elt.

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

Arguments Mk_ModuleEnv {_} _.

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
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
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
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
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
                             | Mk_Module b1 b2 => let scrut_0__ := (GHC.Base.compare a1 b1) in
                                                  match scrut_0__ with
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

Definition delModuleEnvList {a} : ModuleEnv a -> list Module -> ModuleEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_ModuleEnv e , ms => Mk_ModuleEnv (FiniteMap.deleteList (GHC.Base.map
                                                                  Mk_NDModule ms) e)
    end.

Definition elemModuleEnv {a} : Module -> ModuleEnv a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | m , Mk_ModuleEnv e => Data.Map.Base.member (Mk_NDModule m) e
    end.

Definition elemModuleSet : Module -> ModuleSet -> bool :=
  Data.Set.Base.member GHC.Base.∘ GHC.Prim.coerce.

Definition emptyModuleEnv {a} : ModuleEnv a :=
  Mk_ModuleEnv Data.Map.Base.empty.

Definition emptyModuleSet : ModuleSet :=
  Data.Set.Base.empty.

Definition extendModuleEnv {a} : ModuleEnv a -> Module -> a -> ModuleEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | Mk_ModuleEnv e , m , x => Mk_ModuleEnv (Data.Map.Base.insert (Mk_NDModule m) x
                                               e)
    end.

Definition extendModuleEnvList {a} : ModuleEnv a -> list (Module *
                                                         a)%type -> ModuleEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_ModuleEnv e , xs => Mk_ModuleEnv (FiniteMap.insertList
                                            (let cont_2__ arg_3__ :=
                                              match arg_3__ with
                                                | pair k v => cons (pair (Mk_NDModule k) v) nil
                                              end in
                                            Coq.Lists.List.flat_map cont_2__ xs) e)
    end.

Definition extendModuleEnvList_C {a} : (a -> a -> a) -> ModuleEnv a -> list
                                       (Module * a)%type -> ModuleEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , Mk_ModuleEnv e , xs => Mk_ModuleEnv (FiniteMap.insertListWith f
                                                (let cont_3__ arg_4__ :=
                                                  match arg_4__ with
                                                    | pair k v => cons (pair (Mk_NDModule k) v) nil
                                                  end in
                                                Coq.Lists.List.flat_map cont_3__ xs) e)
    end.

Definition extendModuleEnvWith {a} : (a -> a -> a) -> ModuleEnv
                                     a -> Module -> a -> ModuleEnv a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__ , arg_1__ , arg_2__ , arg_3__ with
      | f , Mk_ModuleEnv e , m , x => Mk_ModuleEnv (Data.Map.Base.insertWith f
                                                   (Mk_NDModule m) x e)
    end.

Definition extendModuleSet : ModuleSet -> Module -> ModuleSet :=
  fun s m => Data.Set.Base.insert (Mk_NDModule m) s.

Definition filterModuleEnv {a} : (Module -> a -> bool) -> ModuleEnv
                                 a -> ModuleEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , Mk_ModuleEnv e => Mk_ModuleEnv (Data.Map.Base.filterWithKey (f GHC.Base.∘
                                                                        unNDModule) e)
    end.

Definition foldModuleEnv {a} {b} : (a -> b -> b) -> b -> ModuleEnv a -> b :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , x , Mk_ModuleEnv e => FiniteMap.foldRightWithKey (fun arg_3__ arg_4__ =>
                                                               match arg_3__ , arg_4__ with
                                                                 | _ , v => f v
                                                               end) x e
    end.

Definition fsToUnitId : FastString.FastString -> UnitId :=
  PId.

Definition holeUnitId : UnitId :=
  fsToUnitId (FastString.fsLit (GHC.Base.hs_string__ "hole")).

Definition isHoleModule : Module -> bool :=
  fun mod_ => moduleUnitId mod_ GHC.Base.== holeUnitId.

Definition interactiveUnitId : UnitId :=
  fsToUnitId (FastString.fsLit (GHC.Base.hs_string__ "interactive")).

Definition isInteractiveModule : Module -> bool :=
  fun mod_ => moduleUnitId mod_ GHC.Base.== interactiveUnitId.

Definition mainUnitId : UnitId :=
  fsToUnitId (FastString.fsLit (GHC.Base.hs_string__ "main")).

Definition primUnitId : UnitId :=
  fsToUnitId (FastString.fsLit (GHC.Base.hs_string__ "ghc-prim")).

Definition rtsUnitId : UnitId :=
  fsToUnitId (FastString.fsLit (GHC.Base.hs_string__ "rts")).

Definition stringToUnitId : GHC.Base.String -> UnitId :=
  fsToUnitId GHC.Base.∘ FastString.mkFastString.

Definition thUnitId : UnitId :=
  fsToUnitId (FastString.fsLit (GHC.Base.hs_string__ "template-haskell")).

Definition thisGhcUnitId : UnitId :=
  fsToUnitId (FastString.fsLit (GHC.Base.hs_string__ "ghc")).

Definition dphSeqUnitId : UnitId :=
  fsToUnitId (FastString.fsLit (GHC.Base.hs_string__ "dph-seq")).

Definition dphParUnitId : UnitId :=
  fsToUnitId (FastString.fsLit (GHC.Base.hs_string__ "dph-par")).

Definition baseUnitId : UnitId :=
  fsToUnitId (FastString.fsLit (GHC.Base.hs_string__ "base")).

Definition integerUnitId : UnitId :=
  default.

Definition wiredInUnitIds : list UnitId :=
  cons primUnitId (cons integerUnitId (cons baseUnitId (cons rtsUnitId (cons
                                                             thUnitId (cons thisGhcUnitId (cons dphSeqUnitId (cons
                                                                                                dphParUnitId nil))))))).

Definition isEmptyModuleEnv {a} : ModuleEnv a -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_ModuleEnv e => Data.Map.Base.null e end.

Definition lookupModuleEnv {a} : ModuleEnv a -> Module -> option a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_ModuleEnv e , m => Data.Map.Base.lookup (Mk_NDModule m) e
    end.

Definition lookupWithDefaultModuleEnv {a} : ModuleEnv a -> a -> Module -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | Mk_ModuleEnv e , x , m => Data.Map.Base.findWithDefault x (Mk_NDModule m) e
    end.

Definition mapModuleEnv {a} {b} : (a -> b) -> ModuleEnv a -> ModuleEnv b :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | f , Mk_ModuleEnv e => Mk_ModuleEnv (Data.Map.Base.mapWithKey (fun arg_2__
                                                                          arg_3__ =>
                                                                       match arg_2__ , arg_3__ with
                                                                         | _ , v => f v
                                                                       end) e)
    end.

Definition mkModule : UnitId -> ModuleName -> Module :=
  Mk_Module.

Definition mkModuleNameFS : FastString.FastString -> ModuleName :=
  fun s => Mk_ModuleName s.

Definition moduleEnvKeys {a} : ModuleEnv a -> list Module :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_ModuleEnv e => Data.OldList.sort GHC.Base.$ (GHC.Base.map unNDModule
                          GHC.Base.$ Data.Map.Base.keys e)
    end.

Definition moduleEnvToList {a} : ModuleEnv a -> list (Module * a)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_ModuleEnv e => Data.OldList.sortBy (Data.Ord.comparing Data.Tuple.fst)
                          (let cont_1__ arg_2__ :=
                            match arg_2__ with
                              | pair (Mk_NDModule m) v => cons (pair m v) nil
                            end in
                          Coq.Lists.List.flat_map cont_1__ (Data.Map.Base.toList e))
    end.

Definition moduleEnvElts {a} : ModuleEnv a -> list a :=
  fun e => GHC.Base.map Data.Tuple.snd GHC.Base.$ moduleEnvToList e.

Definition moduleNameFS : ModuleName -> FastString.FastString :=
  fun arg_0__ => match arg_0__ with | Mk_ModuleName mod_ => mod_ end.

Definition stableModuleNameCmp : ModuleName -> ModuleName -> comparison :=
  fun n1 n2 => GHC.Base.compare (moduleNameFS n1) (moduleNameFS n2).

Definition moduleNameString : ModuleName -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_ModuleName mod_ => FastString.unpackFS mod_
    end.

Definition moduleNameColons : ModuleName -> GHC.Base.String :=
  let dots_to_colons :=
    GHC.Base.map (fun c =>
                   if c GHC.Base.== GHC.Char.hs_char__ "." : bool
                   then GHC.Char.hs_char__ ":"
                   else c) in
  dots_to_colons GHC.Base.∘ moduleNameString.

Definition moduleSetElts : ModuleSet -> list Module :=
  Data.OldList.sort GHC.Base.∘ (GHC.Prim.coerce GHC.Base.∘ Data.Set.Base.toList).

Definition plusModuleEnv {a} : ModuleEnv a -> ModuleEnv a -> ModuleEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_ModuleEnv e1 , Mk_ModuleEnv e2 => Mk_ModuleEnv (Data.Map.Base.union e1 e2)
    end.

Definition plusModuleEnv_C {a} : (a -> a -> a) -> ModuleEnv a -> ModuleEnv
                                 a -> ModuleEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__ , arg_1__ , arg_2__ with
      | f , Mk_ModuleEnv e1 , Mk_ModuleEnv e2 => Mk_ModuleEnv (Data.Map.Base.unionWith
                                                              f e1 e2)
    end.

Definition unitIdFS : UnitId -> FastString.FastString :=
  fun arg_0__ => match arg_0__ with | PId fs => fs end.

Definition unitIdString : UnitId -> GHC.Base.String :=
  FastString.unpackFS GHC.Base.∘ unitIdFS.

Definition moduleStableString : Module -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Module moduleUnitId moduleName => Coq.Init.Datatypes.app
                                             (GHC.Base.hs_string__ "$") (Coq.Init.Datatypes.app (unitIdString
                                                                                                moduleUnitId)
                                                                                                (Coq.Init.Datatypes.app
                                                                                                (GHC.Base.hs_string__
                                                                                                "$") (moduleNameString
                                                                                                moduleName)))
    end.

Definition stableUnitIdCmp : UnitId -> UnitId -> comparison :=
  fun p1 p2 => GHC.Base.compare (unitIdFS p1) (unitIdFS p2).

Definition stableModuleCmp : Module -> Module -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_Module p1 n1 , Mk_Module p2 n2 => Util.thenCmp (stableUnitIdCmp p1 p2)
                                                          (stableModuleNameCmp n1 n2)
    end.

Definition unitModuleEnv {a} : Module -> a -> ModuleEnv a :=
  fun m x => Mk_ModuleEnv (Data.Map.Base.singleton (Mk_NDModule m) x).

(* Unbound variables:
     Eq Gt Lt andb bool comparison cons default false list negb nil op_zt__ option
     pair true Coq.Init.Datatypes.app Coq.Lists.List.flat_map Data.Map.Base.Map
     Data.Map.Base.empty Data.Map.Base.filterWithKey Data.Map.Base.findWithDefault
     Data.Map.Base.insert Data.Map.Base.insertWith Data.Map.Base.keys
     Data.Map.Base.lookup Data.Map.Base.mapWithKey Data.Map.Base.member
     Data.Map.Base.null Data.Map.Base.singleton Data.Map.Base.toList
     Data.Map.Base.union Data.Map.Base.unionWith Data.OldList.sort
     Data.OldList.sortBy Data.Ord.comparing Data.Set.Base.Set_ Data.Set.Base.empty
     Data.Set.Base.insert Data.Set.Base.member Data.Set.Base.toList Data.Tuple.fst
     Data.Tuple.snd FastString.FastString FastString.fsLit FastString.mkFastString
     FastString.unpackFS FiniteMap.deleteList FiniteMap.foldRightWithKey
     FiniteMap.insertList FiniteMap.insertListWith GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.String GHC.Base.compare GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.Prim.coerce
     UniqFM.UniqFM Unique.getUnique Util.thenCmp
*)
