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
Require Data.ByteString.
Require Data.ByteString.Char8.
Require Data.ByteString.Unsafe.
Require Data.Foldable.
Require Data.Function.
Require Data.Map.Internal.
Require Data.OldList.
Require Data.Ord.
Require Data.Set.Internal.
Require Data.Tuple.
Require DynFlags.
Require Encoding.
Require FastString.
Require FiniteMap.
Require GHC.Base.
Require GHC.Fingerprint.
Require GHC.Fingerprint.Type.
Require GHC.IO.Unsafe.
Require GHC.PackageDb.
Require GHC.Prim.
Require GHC.Ptr.
Require Packages.
Require Panic.
Require Text.ParserCombinators.ReadP.
Require UniqDFM.
Require UniqDSet.
Require UniqFM.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import Text.ParserCombinators.ReadP.Notations.

(* Converted type declarations: *)

Definition ModuleNameEnv :=
  UniqFM.UniqFM%type.

Inductive ModuleName : Type
  := Mk_ModuleName : FastString.FastString -> ModuleName.

Inductive ModLocation : Type
  := Mk_ModLocation
   : option GHC.Base.String -> GHC.Base.String -> GHC.Base.String -> ModLocation.

Inductive InstalledUnitId : Type
  := InstalledUnitId : FastString.FastString -> InstalledUnitId.

Inductive InstalledModule : Type
  := InstalledModule : InstalledUnitId -> ModuleName -> InstalledModule.

Inductive InstalledModuleEnv elt : Type
  := InstalledModuleEnv
   : (Data.Map.Internal.Map InstalledModule elt) -> InstalledModuleEnv elt.

Inductive DefUnitId : Type := DefUnitId : InstalledUnitId -> DefUnitId.

Definition DModuleNameEnv :=
  UniqDFM.UniqDFM%type.

Inductive ComponentId : Type
  := ComponentId : FastString.FastString -> ComponentId.

Inductive IndefUnitId : Type
  := IndefUnitId
   : FastString.FastString ->
     Unique.Unique ->
     ComponentId ->
     list (ModuleName * Module)%type -> UniqDSet.UniqDSet ModuleName -> IndefUnitId
with Module : Type := Mk_Module : UnitId -> ModuleName -> Module
with UnitId : Type
  := IndefiniteUnitId : IndefUnitId -> UnitId
  |  DefiniteUnitId : DefUnitId -> UnitId.

Inductive IndefModule : Type
  := IndefModule : IndefUnitId -> ModuleName -> IndefModule.

Record ContainsModule__Dict t := ContainsModule__Dict_Build {
  extractModule__ : t -> Module }.

Definition ContainsModule t :=
  forall r, (ContainsModule__Dict t -> r) -> r.

Existing Class ContainsModule.

Definition extractModule `{g : ContainsModule t} : t -> Module :=
  g _ (extractModule__ t).

Record HasModule__Dict m := HasModule__Dict_Build {
  getModule__ : m Module }.

Definition HasModule m :=
  forall r, (HasModule__Dict m -> r) -> r.

Existing Class HasModule.

Definition getModule `{g : HasModule m} : m Module :=
  g _ (getModule__ m).

Inductive NDModule : Type := Mk_NDModule : Module -> NDModule.

Inductive ModuleEnv elt : Type
  := Mk_ModuleEnv : (Data.Map.Internal.Map NDModule elt) -> ModuleEnv elt.

Definition ModuleSet :=
  (Data.Set.Internal.Set_ NDModule)%type.

Definition ShHoleSubst :=
  (ModuleNameEnv Module)%type.

Arguments InstalledModuleEnv {_} _.

Arguments Mk_ModuleEnv {_} _.

Definition installedUnitIdFS (arg_0__ : InstalledUnitId) :=
  let 'InstalledUnitId installedUnitIdFS := arg_0__ in
  installedUnitIdFS.

Definition installedModuleName (arg_1__ : InstalledModule) :=
  let 'InstalledModule _ installedModuleName := arg_1__ in
  installedModuleName.

Definition installedModuleUnitId (arg_2__ : InstalledModule) :=
  let 'InstalledModule installedModuleUnitId _ := arg_2__ in
  installedModuleUnitId.

Definition unDefUnitId (arg_3__ : DefUnitId) :=
  let 'DefUnitId unDefUnitId := arg_3__ in
  unDefUnitId.

Definition indefUnitIdComponentId (arg_4__ : IndefUnitId) :=
  let 'IndefUnitId _ _ indefUnitIdComponentId _ _ := arg_4__ in
  indefUnitIdComponentId.

Definition indefUnitIdFS (arg_5__ : IndefUnitId) :=
  let 'IndefUnitId indefUnitIdFS _ _ _ _ := arg_5__ in
  indefUnitIdFS.

Definition indefUnitIdFreeHoles (arg_6__ : IndefUnitId) :=
  let 'IndefUnitId _ _ _ _ indefUnitIdFreeHoles := arg_6__ in
  indefUnitIdFreeHoles.

Definition indefUnitIdInsts (arg_7__ : IndefUnitId) :=
  let 'IndefUnitId _ _ _ indefUnitIdInsts _ := arg_7__ in
  indefUnitIdInsts.

Definition indefUnitIdKey (arg_8__ : IndefUnitId) :=
  let 'IndefUnitId _ indefUnitIdKey _ _ _ := arg_8__ in
  indefUnitIdKey.

Definition moduleName (arg_9__ : Module) :=
  let 'Mk_Module _ moduleName := arg_9__ in
  moduleName.

Definition moduleUnitId (arg_10__ : Module) :=
  let 'Mk_Module moduleUnitId _ := arg_10__ in
  moduleUnitId.

Definition indefModuleName (arg_11__ : IndefModule) :=
  let 'IndefModule _ indefModuleName := arg_11__ in
  indefModuleName.

Definition indefModuleUnitId (arg_12__ : IndefModule) :=
  let 'IndefModule indefModuleUnitId _ := arg_12__ in
  indefModuleUnitId.

Definition unNDModule (arg_13__ : NDModule) :=
  let 'Mk_NDModule unNDModule := arg_13__ in
  unNDModule.
(* Midamble *)

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
(* Converted value declarations: *)

Local Definition Ord__NDModule_compare : NDModule -> NDModule -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_NDModule (Mk_Module p1 n1), Mk_NDModule (Mk_Module p2 n2) =>
        Util.thenCmp (Unique.nonDetCmpUnique (Unique.getUnique p1) (Unique.getUnique
                                              p2)) (Unique.nonDetCmpUnique (Unique.getUnique n1) (Unique.getUnique n2))
    end.

Local Definition Ord__NDModule_op_zg__ : NDModule -> NDModule -> bool :=
  fun x y => Ord__NDModule_compare x y GHC.Base.== Gt.

Local Definition Ord__NDModule_op_zgze__ : NDModule -> NDModule -> bool :=
  fun x y => Ord__NDModule_compare x y GHC.Base./= Lt.

Local Definition Ord__NDModule_op_zl__ : NDModule -> NDModule -> bool :=
  fun x y => Ord__NDModule_compare x y GHC.Base.== Lt.

Local Definition Ord__NDModule_op_zlze__ : NDModule -> NDModule -> bool :=
  fun x y => Ord__NDModule_compare x y GHC.Base./= Gt.

Local Definition Ord__NDModule_max : NDModule -> NDModule -> NDModule :=
  fun x y => if Ord__NDModule_op_zlze__ x y : bool then y else x.

Local Definition Ord__NDModule_min : NDModule -> NDModule -> NDModule :=
  fun x y => if Ord__NDModule_op_zlze__ x y : bool then x else y.

(* Translating `instance Outputable__IndefModule' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Uniquable__Module' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Outputable__Module' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__Module' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Data__Module' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance NFData__Module' failed: OOPS! Cannot find information
   for class Qualified "Control.DeepSeq" "NFData" unsupported *)

(* Translating `instance
   DbUnitIdModuleRep__InstalledUnitId__ComponentId__UnitId__ModuleName__Module'
   failed: type class instance head:App (App (App (App (App (Qualid (Qualified
   "GHC.PackageDb" "DbUnitIdModuleRep")) (PosArg (Qualid (Qualified "Module"
   "InstalledUnitId")) :| [])) (PosArg (Qualid (Qualified "Module" "ComponentId"))
   :| [])) (PosArg (Qualid (Qualified "Module" "UnitId")) :| [])) (PosArg (Qualid
   (Qualified "Module" "ModuleName")) :| [])) (PosArg (Qualid (Qualified "Module"
   "Module")) :| []) unsupported *)

Local Definition Eq___IndefUnitId_op_zeze__
   : IndefUnitId -> IndefUnitId -> bool :=
  fun u1 u2 => indefUnitIdKey u1 GHC.Base.== indefUnitIdKey u2.

Local Definition Eq___IndefUnitId_op_zsze__
   : IndefUnitId -> IndefUnitId -> bool :=
  fun x y => negb (Eq___IndefUnitId_op_zeze__ x y).

Program Instance Eq___IndefUnitId : GHC.Base.Eq_ IndefUnitId :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___IndefUnitId_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___IndefUnitId_op_zsze__ |}.

Local Definition Ord__IndefUnitId_compare
   : IndefUnitId -> IndefUnitId -> comparison :=
  fun u1 u2 => GHC.Base.compare (indefUnitIdFS u1) (indefUnitIdFS u2).

Local Definition Ord__IndefUnitId_op_zg__
   : IndefUnitId -> IndefUnitId -> bool :=
  fun x y => Ord__IndefUnitId_compare x y GHC.Base.== Gt.

Local Definition Ord__IndefUnitId_op_zgze__
   : IndefUnitId -> IndefUnitId -> bool :=
  fun x y => Ord__IndefUnitId_compare x y GHC.Base./= Lt.

Local Definition Ord__IndefUnitId_op_zl__
   : IndefUnitId -> IndefUnitId -> bool :=
  fun x y => Ord__IndefUnitId_compare x y GHC.Base.== Lt.

Local Definition Ord__IndefUnitId_op_zlze__
   : IndefUnitId -> IndefUnitId -> bool :=
  fun x y => Ord__IndefUnitId_compare x y GHC.Base./= Gt.

Local Definition Ord__IndefUnitId_max
   : IndefUnitId -> IndefUnitId -> IndefUnitId :=
  fun x y => if Ord__IndefUnitId_op_zlze__ x y : bool then y else x.

Local Definition Ord__IndefUnitId_min
   : IndefUnitId -> IndefUnitId -> IndefUnitId :=
  fun x y => if Ord__IndefUnitId_op_zlze__ x y : bool then x else y.

Program Instance Ord__IndefUnitId : GHC.Base.Ord IndefUnitId :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__IndefUnitId_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__IndefUnitId_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__IndefUnitId_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__IndefUnitId_op_zgze__ ;
         GHC.Base.compare__ := Ord__IndefUnitId_compare ;
         GHC.Base.max__ := Ord__IndefUnitId_max ;
         GHC.Base.min__ := Ord__IndefUnitId_min |}.

(* Translating `instance Binary__IndefUnitId' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__IndefUnitId' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Show__UnitId' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Uniquable__UnitId' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition Ord__UnitId_compare : UnitId -> UnitId -> comparison :=
  fun nm1 nm2 => Eq.

Local Definition Ord__UnitId_op_zg__ : UnitId -> UnitId -> bool :=
  fun x y => Ord__UnitId_compare x y GHC.Base.== Gt.

Local Definition Ord__UnitId_op_zgze__ : UnitId -> UnitId -> bool :=
  fun x y => Ord__UnitId_compare x y GHC.Base./= Lt.

Local Definition Ord__UnitId_op_zl__ : UnitId -> UnitId -> bool :=
  fun x y => Ord__UnitId_compare x y GHC.Base.== Lt.

Local Definition Ord__UnitId_op_zlze__ : UnitId -> UnitId -> bool :=
  fun x y => Ord__UnitId_compare x y GHC.Base./= Gt.

Local Definition Ord__UnitId_max : UnitId -> UnitId -> UnitId :=
  fun x y => if Ord__UnitId_op_zlze__ x y : bool then y else x.

Local Definition Ord__UnitId_min : UnitId -> UnitId -> UnitId :=
  fun x y => if Ord__UnitId_op_zlze__ x y : bool then x else y.

(* Translating `instance Data__UnitId' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance NFData__UnitId' failed: OOPS! Cannot find information
   for class Qualified "Control.DeepSeq" "NFData" unsupported *)

(* Translating `instance Outputable__UnitId' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__UnitId' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__DefUnitId' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__DefUnitId' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__InstalledModule' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__InstalledUnitId' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance BinaryStringRep__InstalledUnitId' failed: OOPS! Cannot
   find information for class Qualified "GHC.PackageDb" "BinaryStringRep"
   unsupported *)

Local Definition Ord__InstalledUnitId_compare
   : InstalledUnitId -> InstalledUnitId -> comparison :=
  fun u1 u2 => GHC.Base.compare (installedUnitIdFS u1) (installedUnitIdFS u2).

Local Definition Ord__InstalledUnitId_op_zg__
   : InstalledUnitId -> InstalledUnitId -> bool :=
  fun x y => Ord__InstalledUnitId_compare x y GHC.Base.== Gt.

Local Definition Ord__InstalledUnitId_op_zgze__
   : InstalledUnitId -> InstalledUnitId -> bool :=
  fun x y => Ord__InstalledUnitId_compare x y GHC.Base./= Lt.

Local Definition Ord__InstalledUnitId_op_zl__
   : InstalledUnitId -> InstalledUnitId -> bool :=
  fun x y => Ord__InstalledUnitId_compare x y GHC.Base.== Lt.

Local Definition Ord__InstalledUnitId_op_zlze__
   : InstalledUnitId -> InstalledUnitId -> bool :=
  fun x y => Ord__InstalledUnitId_compare x y GHC.Base./= Gt.

Local Definition Ord__InstalledUnitId_max
   : InstalledUnitId -> InstalledUnitId -> InstalledUnitId :=
  fun x y => if Ord__InstalledUnitId_op_zlze__ x y : bool then y else x.

Local Definition Ord__InstalledUnitId_min
   : InstalledUnitId -> InstalledUnitId -> InstalledUnitId :=
  fun x y => if Ord__InstalledUnitId_op_zlze__ x y : bool then x else y.

Program Instance Ord__InstalledUnitId : GHC.Base.Ord InstalledUnitId :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__InstalledUnitId_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__InstalledUnitId_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__InstalledUnitId_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__InstalledUnitId_op_zgze__ ;
         GHC.Base.compare__ := Ord__InstalledUnitId_compare ;
         GHC.Base.max__ := Ord__InstalledUnitId_max ;
         GHC.Base.min__ := Ord__InstalledUnitId_min |}.

(* Translating `instance Uniquable__InstalledUnitId' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Outputable__InstalledUnitId' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance BinaryStringRep__ComponentId' failed: OOPS! Cannot find
   information for class Qualified "GHC.PackageDb" "BinaryStringRep" unsupported *)

(* Translating `instance Uniquable__ComponentId' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Outputable__ComponentId' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__ComponentId' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Uniquable__ModuleName' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition Eq___ModuleName_op_zeze__ : ModuleName -> ModuleName -> bool :=
  fun nm1 nm2 => Unique.getUnique nm1 GHC.Base.== Unique.getUnique nm2.

Local Definition Eq___ModuleName_op_zsze__ : ModuleName -> ModuleName -> bool :=
  fun x y => negb (Eq___ModuleName_op_zeze__ x y).

Local Definition Ord__ModuleName_compare
   : ModuleName -> ModuleName -> comparison :=
  fun nm1 nm2 => Eq.

Local Definition Ord__ModuleName_op_zg__ : ModuleName -> ModuleName -> bool :=
  fun x y => Ord__ModuleName_compare x y GHC.Base.== Gt.

Local Definition Ord__ModuleName_op_zgze__ : ModuleName -> ModuleName -> bool :=
  fun x y => Ord__ModuleName_compare x y GHC.Base./= Lt.

Local Definition Ord__ModuleName_op_zl__ : ModuleName -> ModuleName -> bool :=
  fun x y => Ord__ModuleName_compare x y GHC.Base.== Lt.

Local Definition Ord__ModuleName_op_zlze__ : ModuleName -> ModuleName -> bool :=
  fun x y => Ord__ModuleName_compare x y GHC.Base./= Gt.

Local Definition Ord__ModuleName_max : ModuleName -> ModuleName -> ModuleName :=
  fun x y => if Ord__ModuleName_op_zlze__ x y : bool then y else x.

Local Definition Ord__ModuleName_min : ModuleName -> ModuleName -> ModuleName :=
  fun x y => if Ord__ModuleName_op_zlze__ x y : bool then x else y.

(* Translating `instance Outputable__ModuleName' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__ModuleName' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance BinaryStringRep__ModuleName' failed: OOPS! Cannot find
   information for class Qualified "GHC.PackageDb" "BinaryStringRep" unsupported *)

(* Translating `instance Data__ModuleName' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance NFData__ModuleName' failed: OOPS! Cannot find
   information for class Qualified "Control.DeepSeq" "NFData" unsupported *)

(* Translating `instance Outputable__ModLocation' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

Local Definition Ord__IndefModule_compare
   : IndefModule -> IndefModule -> comparison :=
  fun a b =>
    let 'IndefModule a1 a2 := a in
    let 'IndefModule b1 b2 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => Lt
    | Eq => (GHC.Base.compare a2 b2)
    | Gt => Gt
    end.

Local Definition Ord__IndefModule_op_zl__
   : IndefModule -> IndefModule -> bool :=
  fun a b =>
    let 'IndefModule a1 a2 := a in
    let 'IndefModule b1 b2 := b in
    match (Ord__IndefModule_compare a1 b1) with
    | Lt => true
    | Eq => (a2 GHC.Base.< b2)
    | Gt => false
    end.

Local Definition Ord__IndefModule_op_zg__
   : IndefModule -> IndefModule -> bool :=
  fun a b => Ord__IndefModule_op_zl__ b a.

Local Definition Ord__IndefModule_op_zgze__
   : IndefModule -> IndefModule -> bool :=
  fun a b => negb (Ord__IndefModule_op_zl__ a b).

Local Definition Ord__IndefModule_op_zlze__
   : IndefModule -> IndefModule -> bool :=
  fun a b => negb (Ord__IndefModule_op_zl__ b a).

Local Definition Ord__IndefModule_max
   : IndefModule -> IndefModule -> IndefModule :=
  fun x y => if Ord__IndefModule_op_zlze__ x y : bool then y else x.

Local Definition Ord__IndefModule_min
   : IndefModule -> IndefModule -> IndefModule :=
  fun x y => if Ord__IndefModule_op_zlze__ x y : bool then x else y.

Program Instance Ord__IndefModule : GHC.Base.Ord IndefModule :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__IndefModule_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__IndefModule_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__IndefModule_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__IndefModule_op_zgze__ ;
         GHC.Base.compare__ := Ord__IndefModule_compare ;
         GHC.Base.max__ := Ord__IndefModule_max ;
         GHC.Base.min__ := Ord__IndefModule_min |}.

Local Definition Eq___IndefModule_op_zeze__
   : IndefModule -> IndefModule -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | IndefModule a1 a2, IndefModule b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___IndefModule_op_zsze__
   : IndefModule -> IndefModule -> bool :=
  fun x y => negb (Eq___IndefModule_op_zeze__ x y).

Program Instance Eq___IndefModule : GHC.Base.Eq_ IndefModule :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___IndefModule_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___IndefModule_op_zsze__ |}.

Local Definition Ord__DefUnitId_compare
   : DefUnitId -> DefUnitId -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__DefUnitId_max : DefUnitId -> DefUnitId -> DefUnitId :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__DefUnitId_min : DefUnitId -> DefUnitId -> DefUnitId :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__DefUnitId_op_zg__ : DefUnitId -> DefUnitId -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__DefUnitId_op_zgze__ : DefUnitId -> DefUnitId -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__DefUnitId_op_zl__ : DefUnitId -> DefUnitId -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__DefUnitId_op_zlze__ : DefUnitId -> DefUnitId -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Program Instance Ord__DefUnitId : GHC.Base.Ord DefUnitId :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__DefUnitId_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__DefUnitId_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__DefUnitId_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__DefUnitId_op_zgze__ ;
         GHC.Base.compare__ := Ord__DefUnitId_compare ;
         GHC.Base.max__ := Ord__DefUnitId_max ;
         GHC.Base.min__ := Ord__DefUnitId_min |}.

Local Definition Eq___DefUnitId_op_zeze__ : DefUnitId -> DefUnitId -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___DefUnitId_op_zsze__ : DefUnitId -> DefUnitId -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___DefUnitId : GHC.Base.Eq_ DefUnitId :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___DefUnitId_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___DefUnitId_op_zsze__ |}.

Local Definition Ord__InstalledModule_compare
   : InstalledModule -> InstalledModule -> comparison :=
  fun a b =>
    let 'InstalledModule a1 a2 := a in
    let 'InstalledModule b1 b2 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => Lt
    | Eq => (GHC.Base.compare a2 b2)
    | Gt => Gt
    end.

Local Definition Ord__InstalledModule_op_zl__
   : InstalledModule -> InstalledModule -> bool :=
  fun a b =>
    let 'InstalledModule a1 a2 := a in
    let 'InstalledModule b1 b2 := b in
    match (Ord__InstalledModule_compare a1 b1) with
    | Lt => true
    | Eq => (a2 GHC.Base.< b2)
    | Gt => false
    end.

Local Definition Ord__InstalledModule_op_zg__
   : InstalledModule -> InstalledModule -> bool :=
  fun a b => Ord__InstalledModule_op_zl__ b a.

Local Definition Ord__InstalledModule_op_zgze__
   : InstalledModule -> InstalledModule -> bool :=
  fun a b => negb (Ord__InstalledModule_op_zl__ a b).

Local Definition Ord__InstalledModule_op_zlze__
   : InstalledModule -> InstalledModule -> bool :=
  fun a b => negb (Ord__InstalledModule_op_zl__ b a).

Local Definition Ord__InstalledModule_max
   : InstalledModule -> InstalledModule -> InstalledModule :=
  fun x y => if Ord__InstalledModule_op_zlze__ x y : bool then y else x.

Local Definition Ord__InstalledModule_min
   : InstalledModule -> InstalledModule -> InstalledModule :=
  fun x y => if Ord__InstalledModule_op_zlze__ x y : bool then x else y.

Program Instance Ord__InstalledModule : GHC.Base.Ord InstalledModule :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__InstalledModule_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__InstalledModule_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__InstalledModule_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__InstalledModule_op_zgze__ ;
         GHC.Base.compare__ := Ord__InstalledModule_compare ;
         GHC.Base.max__ := Ord__InstalledModule_max ;
         GHC.Base.min__ := Ord__InstalledModule_min |}.

Local Definition Eq___InstalledModule_op_zeze__
   : InstalledModule -> InstalledModule -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InstalledModule a1 a2, InstalledModule b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___InstalledModule_op_zsze__
   : InstalledModule -> InstalledModule -> bool :=
  fun x y => negb (Eq___InstalledModule_op_zeze__ x y).

Program Instance Eq___InstalledModule : GHC.Base.Eq_ InstalledModule :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___InstalledModule_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___InstalledModule_op_zsze__ |}.

Local Definition Ord__ComponentId_compare
   : ComponentId -> ComponentId -> comparison :=
  GHC.Prim.coerce GHC.Base.compare.

Local Definition Ord__ComponentId_max
   : ComponentId -> ComponentId -> ComponentId :=
  GHC.Prim.coerce GHC.Base.max.

Local Definition Ord__ComponentId_min
   : ComponentId -> ComponentId -> ComponentId :=
  GHC.Prim.coerce GHC.Base.min.

Local Definition Ord__ComponentId_op_zg__
   : ComponentId -> ComponentId -> bool :=
  GHC.Prim.coerce _GHC.Base.>_.

Local Definition Ord__ComponentId_op_zgze__
   : ComponentId -> ComponentId -> bool :=
  GHC.Prim.coerce _GHC.Base.>=_.

Local Definition Ord__ComponentId_op_zl__
   : ComponentId -> ComponentId -> bool :=
  GHC.Prim.coerce _GHC.Base.<_.

Local Definition Ord__ComponentId_op_zlze__
   : ComponentId -> ComponentId -> bool :=
  GHC.Prim.coerce _GHC.Base.<=_.

Program Instance Ord__ComponentId : GHC.Base.Ord ComponentId :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__ComponentId_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__ComponentId_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__ComponentId_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__ComponentId_op_zgze__ ;
         GHC.Base.compare__ := Ord__ComponentId_compare ;
         GHC.Base.max__ := Ord__ComponentId_max ;
         GHC.Base.min__ := Ord__ComponentId_min |}.

Local Definition Eq___ComponentId_op_zeze__
   : ComponentId -> ComponentId -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___ComponentId_op_zsze__
   : ComponentId -> ComponentId -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___ComponentId : GHC.Base.Eq_ ComponentId :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___ComponentId_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___ComponentId_op_zsze__ |}.

(* Translating `instance Show__ModLocation' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

Definition delInstalledModuleEnv {a}
   : InstalledModuleEnv a -> InstalledModule -> InstalledModuleEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InstalledModuleEnv e, m => InstalledModuleEnv (Data.Map.Internal.delete m e)
    end.

Definition delModuleEnv {a} : ModuleEnv a -> Module -> ModuleEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_ModuleEnv e, m => Mk_ModuleEnv (Data.Map.Internal.delete (Mk_NDModule m) e)
    end.

Definition delModuleEnvList {a} : ModuleEnv a -> list Module -> ModuleEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_ModuleEnv e, ms =>
        Mk_ModuleEnv (FiniteMap.deleteList (GHC.Base.map Mk_NDModule ms) e)
    end.

Definition delModuleSet : ModuleSet -> Module -> ModuleSet :=
  GHC.Prim.coerce (GHC.Base.flip Data.Set.Internal.delete).

Definition elemModuleEnv {a} : Module -> ModuleEnv a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | m, Mk_ModuleEnv e => Data.Map.Internal.member (Mk_NDModule m) e
    end.

Definition elemModuleSet : Module -> ModuleSet -> bool :=
  Data.Set.Internal.member GHC.Base.∘ GHC.Prim.coerce.

Definition emptyInstalledModuleEnv {a} : InstalledModuleEnv a :=
  InstalledModuleEnv Data.Map.Internal.empty.

Definition emptyModuleEnv {a} : ModuleEnv a :=
  Mk_ModuleEnv Data.Map.Internal.empty.

Definition emptyModuleSet : ModuleSet :=
  Data.Set.Internal.empty.

Definition extendInstalledModuleEnv {a}
   : InstalledModuleEnv a -> InstalledModule -> a -> InstalledModuleEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | InstalledModuleEnv e, m, x =>
        InstalledModuleEnv (Data.Map.Internal.insert m x e)
    end.

Definition extendModuleEnv {a} : ModuleEnv a -> Module -> a -> ModuleEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_ModuleEnv e, m, x =>
        Mk_ModuleEnv (Data.Map.Internal.insert (Mk_NDModule m) x e)
    end.

Definition extendModuleEnvList {a}
   : ModuleEnv a -> list (Module * a)%type -> ModuleEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_ModuleEnv e, xs =>
        Mk_ModuleEnv (FiniteMap.insertList (let cont_2__ arg_3__ :=
                                              let 'pair k v := arg_3__ in
                                              cons (pair (Mk_NDModule k) v) nil in
                                            Coq.Lists.List.flat_map cont_2__ xs) e)
    end.

Definition extendModuleEnvList_C {a}
   : (a -> a -> a) -> ModuleEnv a -> list (Module * a)%type -> ModuleEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, Mk_ModuleEnv e, xs =>
        Mk_ModuleEnv (FiniteMap.insertListWith f (let cont_3__ arg_4__ :=
                                                    let 'pair k v := arg_4__ in
                                                    cons (pair (Mk_NDModule k) v) nil in
                                                  Coq.Lists.List.flat_map cont_3__ xs) e)
    end.

Definition extendModuleEnvWith {a}
   : (a -> a -> a) -> ModuleEnv a -> Module -> a -> ModuleEnv a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | f, Mk_ModuleEnv e, m, x =>
        Mk_ModuleEnv (Data.Map.Internal.insertWith f (Mk_NDModule m) x e)
    end.

Definition extendModuleSet : ModuleSet -> Module -> ModuleSet :=
  fun s m => Data.Set.Internal.insert (Mk_NDModule m) s.

Definition extendModuleSetList : ModuleSet -> list Module -> ModuleSet :=
  fun s ms =>
    Data.Foldable.foldl' (GHC.Prim.coerce GHC.Base.∘
                          GHC.Base.flip Data.Set.Internal.insert) s ms.

Definition filterInstalledModuleEnv {a}
   : (InstalledModule -> a -> bool) ->
     InstalledModuleEnv a -> InstalledModuleEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, InstalledModuleEnv e =>
        InstalledModuleEnv (Data.Map.Internal.filterWithKey f e)
    end.

Definition filterModuleEnv {a}
   : (Module -> a -> bool) -> ModuleEnv a -> ModuleEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_ModuleEnv e =>
        Mk_ModuleEnv (Data.Map.Internal.filterWithKey (f GHC.Base.∘ unNDModule) e)
    end.

Definition fingerprintByteString
   : GHC.Base.String -> GHC.Fingerprint.Type.Fingerprint :=
  fun bs =>
    (GHC.IO.Unsafe.unsafePerformIO GHC.Base.∘
     Data.ByteString.Unsafe.unsafeUseAsCStringLen bs) (fun arg_0__ =>
                                                         let 'pair p l := arg_0__ in
                                                         GHC.Fingerprint.fingerprintData (GHC.Ptr.castPtr p) l).

Definition fingerprintUnitId
   : GHC.Base.String -> GHC.Fingerprint.Type.Fingerprint -> GHC.Base.String :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | prefix, GHC.Fingerprint.Type.Fingerprint a b =>
        Data.ByteString.concat (cons prefix (cons (Data.ByteString.Char8.singleton
                                                   (GHC.Char.hs_char__ "-")) (cons (Data.ByteString.Char8.pack
                                                                                    (Encoding.toBase62Padded a)) (cons
                                                                                    (Data.ByteString.Char8.pack
                                                                                     (Encoding.toBase62Padded b))
                                                                                    nil))))
    end.

Definition fsToInstalledUnitId : FastString.FastString -> InstalledUnitId :=
  fun fs => InstalledUnitId fs.

Definition stringToInstalledUnitId : GHC.Base.String -> InstalledUnitId :=
  fsToInstalledUnitId GHC.Base.∘ FastString.mkFastString.

Definition componentIdToInstalledUnitId : ComponentId -> InstalledUnitId :=
  fun arg_0__ => let 'ComponentId fs := arg_0__ in fsToInstalledUnitId fs.

Definition splitUnitIdInsts
   : UnitId -> (InstalledUnitId * option IndefUnitId)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | IndefiniteUnitId iuid =>
        pair (componentIdToInstalledUnitId (indefUnitIdComponentId iuid)) (Some iuid)
    | DefiniteUnitId (DefUnitId uid) => pair uid None
    end.

Definition installedUnitIdEq : InstalledUnitId -> UnitId -> bool :=
  fun iuid uid => Data.Tuple.fst (splitUnitIdInsts uid) GHC.Base.== iuid.

Definition splitModuleInsts
   : Module -> (InstalledModule * option IndefModule)%type :=
  fun m =>
    let 'pair uid mb_iuid := splitUnitIdInsts (moduleUnitId m) in
    pair (InstalledModule uid (moduleName m)) (GHC.Base.fmap (fun iuid =>
                                                                IndefModule iuid (moduleName m)) mb_iuid).

Definition installedModuleEq : InstalledModule -> Module -> bool :=
  fun imod mod_ => Data.Tuple.fst (splitModuleInsts mod_) GHC.Base.== imod.

Definition toInstalledUnitId : UnitId -> InstalledUnitId :=
  fun arg_0__ =>
    match arg_0__ with
    | DefiniteUnitId (DefUnitId iuid) => iuid
    | IndefiniteUnitId indef =>
        componentIdToInstalledUnitId (indefUnitIdComponentId indef)
    end.

Definition fsToUnitId : FastString.FastString -> UnitId :=
  DefiniteUnitId GHC.Base.∘ (DefUnitId GHC.Base.∘ InstalledUnitId).

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

Definition newSimpleUnitId : ComponentId -> UnitId :=
  fun arg_0__ => let 'ComponentId fs := arg_0__ in fsToUnitId fs.

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

Definition indefUnitIdToUnitId : DynFlags.DynFlags -> IndefUnitId -> UnitId :=
  fun dflags iuid =>
    Packages.improveUnitId (Packages.getPackageConfigMap dflags) (IndefiniteUnitId
                                                                  iuid).

Definition installedUnitIdKey : InstalledUnitId -> Unique.Unique :=
  Unique.getUnique GHC.Base.∘ installedUnitIdFS.

Definition unitIdKey : UnitId -> Unique.Unique :=
  fun arg_0__ =>
    match arg_0__ with
    | IndefiniteUnitId x => indefUnitIdKey x
    | DefiniteUnitId (DefUnitId x) => installedUnitIdKey x
    end.

Local Definition Eq___UnitId_op_zeze__ : UnitId -> UnitId -> bool :=
  fun uid1 uid2 => unitIdKey uid1 GHC.Base.== unitIdKey uid2.

Local Definition Eq___UnitId_op_zsze__ : UnitId -> UnitId -> bool :=
  fun x y => negb (Eq___UnitId_op_zeze__ x y).

Program Instance Eq___UnitId : GHC.Base.Eq_ UnitId :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___UnitId_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___UnitId_op_zsze__ |}.

Program Instance Eq___ModuleName : GHC.Base.Eq_ ModuleName :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___ModuleName_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___ModuleName_op_zsze__ |}.

Local Definition Eq___Module_op_zeze__ : Module -> Module -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Module a1 a2, Mk_Module b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___Module_op_zsze__ : Module -> Module -> bool :=
  fun x y => negb (Eq___Module_op_zeze__ x y).

Program Instance Eq___Module : GHC.Base.Eq_ Module :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Module_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Module_op_zsze__ |}.

Local Definition Eq___NDModule_op_zeze__ : NDModule -> NDModule -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___NDModule_op_zsze__ : NDModule -> NDModule -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___NDModule : GHC.Base.Eq_ NDModule :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___NDModule_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___NDModule_op_zsze__ |}.

Program Instance Ord__UnitId : GHC.Base.Ord UnitId :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__UnitId_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__UnitId_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__UnitId_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__UnitId_op_zgze__ ;
         GHC.Base.compare__ := Ord__UnitId_compare ;
         GHC.Base.max__ := Ord__UnitId_max ;
         GHC.Base.min__ := Ord__UnitId_min |}.

Program Instance Ord__ModuleName : GHC.Base.Ord ModuleName :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__ModuleName_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__ModuleName_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__ModuleName_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__ModuleName_op_zgze__ ;
         GHC.Base.compare__ := Ord__ModuleName_compare ;
         GHC.Base.max__ := Ord__ModuleName_max ;
         GHC.Base.min__ := Ord__ModuleName_min |}.

Local Definition Ord__Module_compare : Module -> Module -> comparison :=
  fun a b =>
    let 'Mk_Module a1 a2 := a in
    let 'Mk_Module b1 b2 := b in
    match (GHC.Base.compare a1 b1) with
    | Lt => Lt
    | Eq => (GHC.Base.compare a2 b2)
    | Gt => Gt
    end.

Local Definition Ord__Module_op_zg__ : Module -> Module -> bool :=
  fun a b =>
    let 'Mk_Module a1 a2 := a in
    let 'Mk_Module b1 b2 := b in
    match Ord__UnitId_compare a1 b1 with
    | Lt => false
    | Eq => a2 GHC.Base.> b2
    | Gt => true
    end.

Local Definition Ord__Module_op_zgze__ : Module -> Module -> bool :=
  fun a b =>
    let 'Mk_Module a1 a2 := a in
    let 'Mk_Module b1 b2 := b in
    match Ord__UnitId_compare a1 b1 with
    | Lt => false
    | Eq => a2 GHC.Base.>= b2
    | Gt => true
    end.

Local Definition Ord__Module_op_zl__ : Module -> Module -> bool :=
  fun a b =>
    let 'Mk_Module a1 a2 := a in
    let 'Mk_Module b1 b2 := b in
    match Ord__UnitId_compare a1 b1 with
    | Lt => true
    | Eq => a2 GHC.Base.< b2
    | Gt => false
    end.

Local Definition Ord__Module_op_zlze__ : Module -> Module -> bool :=
  fun a b =>
    let 'Mk_Module a1 a2 := a in
    let 'Mk_Module b1 b2 := b in
    match Ord__UnitId_compare a1 b1 with
    | Lt => true
    | Eq => a2 GHC.Base.<= b2
    | Gt => false
    end.

Local Definition Ord__Module_max : Module -> Module -> Module :=
  fun x y => if Ord__Module_op_zlze__ x y : bool then y else x.

Local Definition Ord__Module_min : Module -> Module -> Module :=
  fun x y => if Ord__Module_op_zlze__ x y : bool then x else y.

Program Instance Ord__Module : GHC.Base.Ord Module :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Module_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Module_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Module_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Module_op_zgze__ ;
         GHC.Base.compare__ := Ord__Module_compare ;
         GHC.Base.max__ := Ord__Module_max ;
         GHC.Base.min__ := Ord__Module_min |}.

Program Instance Ord__NDModule : GHC.Base.Ord NDModule :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__NDModule_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__NDModule_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__NDModule_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__NDModule_op_zgze__ ;
         GHC.Base.compare__ := Ord__NDModule_compare ;
         GHC.Base.max__ := Ord__NDModule_max ;
         GHC.Base.min__ := Ord__NDModule_min |}.

Local Definition Eq___InstalledUnitId_op_zeze__
   : InstalledUnitId -> InstalledUnitId -> bool :=
  fun uid1 uid2 => installedUnitIdKey uid1 GHC.Base.== installedUnitIdKey uid2.

Local Definition Eq___InstalledUnitId_op_zsze__
   : InstalledUnitId -> InstalledUnitId -> bool :=
  fun x y => negb (Eq___InstalledUnitId_op_zeze__ x y).

Program Instance Eq___InstalledUnitId : GHC.Base.Eq_ InstalledUnitId :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___InstalledUnitId_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___InstalledUnitId_op_zsze__ |}.

Definition installedUnitIdString : InstalledUnitId -> GHC.Base.String :=
  FastString.unpackFS GHC.Base.∘ installedUnitIdFS.

Definition integerUnitId : UnitId :=
  default.

Definition wiredInUnitIds : list UnitId :=
  cons primUnitId (cons integerUnitId (cons baseUnitId (cons rtsUnitId (cons
                                                              thUnitId (cons thisGhcUnitId (cons dphSeqUnitId (cons
                                                                                                  dphParUnitId
                                                                                                  nil))))))).

Definition intersectModuleSet : ModuleSet -> ModuleSet -> ModuleSet :=
  GHC.Prim.coerce Data.Set.Internal.intersection.

Definition isEmptyModuleEnv {a} : ModuleEnv a -> bool :=
  fun arg_0__ => let 'Mk_ModuleEnv e := arg_0__ in Data.Map.Internal.null e.

Definition lookupInstalledModuleEnv {a}
   : InstalledModuleEnv a -> InstalledModule -> option a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InstalledModuleEnv e, m => Data.Map.Internal.lookup m e
    end.

Definition lookupModuleEnv {a} : ModuleEnv a -> Module -> option a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_ModuleEnv e, m => Data.Map.Internal.lookup (Mk_NDModule m) e
    end.

Definition lookupWithDefaultModuleEnv {a} : ModuleEnv a -> a -> Module -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_ModuleEnv e, x, m => Data.Map.Internal.findWithDefault x (Mk_NDModule m) e
    end.

Definition mapModuleEnv {a} {b} : (a -> b) -> ModuleEnv a -> ModuleEnv b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, Mk_ModuleEnv e =>
        Mk_ModuleEnv (Data.Map.Internal.mapWithKey (fun arg_2__ arg_3__ =>
                                                      match arg_2__, arg_3__ with
                                                      | _, v => f v
                                                      end) e)
    end.

Definition minusModuleSet : ModuleSet -> ModuleSet -> ModuleSet :=
  GHC.Prim.coerce Data.Set.Internal.difference.

Definition mkModule : UnitId -> ModuleName -> Module :=
  Mk_Module.

Definition indefModuleToModule : DynFlags.DynFlags -> IndefModule -> Module :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | dflags, IndefModule iuid mod_name =>
        mkModule (indefUnitIdToUnitId dflags iuid) mod_name
    end.

Definition mkHoleModule : ModuleName -> Module :=
  mkModule holeUnitId.

Definition mkModuleEnv {a} : list (Module * a)%type -> ModuleEnv a :=
  fun xs =>
    Mk_ModuleEnv (Data.Map.Internal.fromList (let cont_0__ arg_1__ :=
                                                let 'pair k v := arg_1__ in
                                                cons (pair (Mk_NDModule k) v) nil in
                                              Coq.Lists.List.flat_map cont_0__ xs)).

Definition mkModuleNameFS : FastString.FastString -> ModuleName :=
  fun s => Mk_ModuleName s.

Definition mkModuleSet : list Module -> ModuleSet :=
  Data.Set.Internal.fromList GHC.Base.∘ GHC.Prim.coerce.

Definition moduleEnvKeys {a} : ModuleEnv a -> list Module :=
  fun arg_0__ =>
    let 'Mk_ModuleEnv e := arg_0__ in
    Data.OldList.sort (GHC.Base.map unNDModule (Data.Map.Internal.keys e)).

Definition moduleEnvToList {a} : ModuleEnv a -> list (Module * a)%type :=
  fun arg_0__ =>
    let 'Mk_ModuleEnv e := arg_0__ in
    Data.OldList.sortBy (Data.Ord.comparing Data.Tuple.fst) (let cont_1__ arg_2__ :=
                                                               let 'pair (Mk_NDModule m) v := arg_2__ in
                                                               cons (pair m v) nil in
                                                             Coq.Lists.List.flat_map cont_1__ (Data.Map.Internal.toList
                                                                                      e)).

Definition moduleEnvElts {a} : ModuleEnv a -> list a :=
  fun e => GHC.Base.map Data.Tuple.snd (moduleEnvToList e).

Definition moduleNameFS : ModuleName -> FastString.FastString :=
  fun arg_0__ => let 'Mk_ModuleName mod_ := arg_0__ in mod_.

Definition stableModuleNameCmp : ModuleName -> ModuleName -> comparison :=
  fun n1 n2 => GHC.Base.compare (moduleNameFS n1) (moduleNameFS n2).

Definition moduleNameString : ModuleName -> GHC.Base.String :=
  fun arg_0__ => let 'Mk_ModuleName mod_ := arg_0__ in FastString.unpackFS mod_.

Definition moduleNameColons : ModuleName -> GHC.Base.String :=
  let dots_to_colons :=
    GHC.Base.map (fun c =>
                    if c GHC.Base.== GHC.Char.hs_char__ "." : bool
                    then GHC.Char.hs_char__ ":"
                    else c) in
  dots_to_colons GHC.Base.∘ moduleNameString.

Definition moduleSetElts : ModuleSet -> list Module :=
  Data.OldList.sort GHC.Base.∘
  (GHC.Prim.coerce GHC.Base.∘ Data.Set.Internal.toList).

Definition parseComponentId : Text.ParserCombinators.ReadP.ReadP ComponentId :=
  let abi_char :=
    fun c =>
      orb (GHC.Unicode.isAlphaNum c) (Data.Foldable.elem c (GHC.Base.hs_string__
                                                          "-_.")) in
  GHC.Base.fmap (ComponentId GHC.Base.∘ FastString.mkFastString)
                (Text.ParserCombinators.ReadP.munch1 abi_char).

Definition parseModuleName : Text.ParserCombinators.ReadP.ReadP ModuleName :=
  GHC.Base.fmap mkModuleName (Text.ParserCombinators.ReadP.munch1 (fun c =>
                                                                     orb (GHC.Unicode.isAlphaNum c) (Data.Foldable.elem
                                                                          c (GHC.Base.hs_string__ "_.")))).

Definition plusModuleEnv {a} : ModuleEnv a -> ModuleEnv a -> ModuleEnv a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_ModuleEnv e1, Mk_ModuleEnv e2 =>
        Mk_ModuleEnv (Data.Map.Internal.union e1 e2)
    end.

Definition plusModuleEnv_C {a}
   : (a -> a -> a) -> ModuleEnv a -> ModuleEnv a -> ModuleEnv a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, Mk_ModuleEnv e1, Mk_ModuleEnv e2 =>
        Mk_ModuleEnv (Data.Map.Internal.unionWith f e1 e2)
    end.

Definition pprUnitId : UnitId -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | DefiniteUnitId uid => Panic.noString uid
    | IndefiniteUnitId uid => Panic.noString uid
    end.

Definition unionModuleSet : ModuleSet -> ModuleSet -> ModuleSet :=
  GHC.Prim.coerce Data.Set.Internal.union.

Definition unitIdFS : UnitId -> FastString.FastString :=
  fun arg_0__ =>
    match arg_0__ with
    | IndefiniteUnitId x => indefUnitIdFS x
    | DefiniteUnitId (DefUnitId x) => installedUnitIdFS x
    end.

Definition unitIdString : UnitId -> GHC.Base.String :=
  FastString.unpackFS GHC.Base.∘ unitIdFS.

Definition moduleStableString : Module -> GHC.Base.String :=
  fun arg_0__ =>
    let 'Mk_Module moduleUnitId moduleName := arg_0__ in
    Coq.Init.Datatypes.app (GHC.Base.hs_string__ "$") (Coq.Init.Datatypes.app
                            (unitIdString moduleUnitId) (Coq.Init.Datatypes.app (GHC.Base.hs_string__ "$")
                                                                                (moduleNameString moduleName))).

Definition stableUnitIdCmp : UnitId -> UnitId -> comparison :=
  fun p1 p2 => GHC.Base.compare (unitIdFS p1) (unitIdFS p2).

Definition stableModuleCmp : Module -> Module -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Module p1 n1, Mk_Module p2 n2 =>
        Util.thenCmp (stableUnitIdCmp p1 p2) (stableModuleNameCmp n1 n2)
    end.

Definition rawHashUnitId
   : list (ModuleName * Module)%type -> GHC.Fingerprint.Type.Fingerprint :=
  fun sorted_holes =>
    (fingerprintByteString GHC.Base.∘ Data.ByteString.concat)
    (let cont_0__ arg_1__ :=
       let 'pair m b := arg_1__ in
       cons (GHC.PackageDb.toStringRep m) (cons (Data.ByteString.Char8.singleton
                                                 (GHC.Char.hs_char__ " ")) (cons (FastString.fastStringToByteString
                                                                                  (unitIdFS (moduleUnitId b))) (cons
                                                                                  (Data.ByteString.Char8.singleton
                                                                                   (GHC.Char.hs_char__ ":")) (cons
                                                                                   (GHC.PackageDb.toStringRep
                                                                                    (moduleName b)) (cons
                                                                                    (Data.ByteString.Char8.singleton
                                                                                     (GHC.Char.hs_char__ ""))
                                                                                    nil))))) in
     sorted_holes GHC.Base.>>= cont_0__).

Definition hashUnitId
   : ComponentId -> list (ModuleName * Module)%type -> FastString.FastString :=
  fun cid sorted_holes =>
    (FastString.mkFastStringByteString GHC.Base.∘
     fingerprintUnitId (GHC.PackageDb.toStringRep cid)) (rawHashUnitId sorted_holes).

Definition unitIdFreeHoles : UnitId -> UniqDSet.UniqDSet ModuleName :=
  fun arg_0__ =>
    match arg_0__ with
    | IndefiniteUnitId x => indefUnitIdFreeHoles x
    | DefiniteUnitId _ => UniqDSet.emptyUniqDSet
    end.

Definition unitIdIsDefinite : UnitId -> bool :=
  UniqDSet.isEmptyUniqDSet GHC.Base.∘ unitIdFreeHoles.

Definition moduleFreeHoles : Module -> UniqDSet.UniqDSet ModuleName :=
  fun m =>
    if isHoleModule m : bool then UniqDSet.unitUniqDSet (moduleName m) else
    unitIdFreeHoles (moduleUnitId m).

Definition moduleIsDefinite : Module -> bool :=
  UniqDSet.isEmptyUniqDSet GHC.Base.∘ moduleFreeHoles.

Definition newIndefUnitId
   : ComponentId -> list (ModuleName * Module)%type -> IndefUnitId :=
  fun cid insts =>
    let sorted_insts :=
      Data.OldList.sortBy (Data.Function.on stableModuleNameCmp Data.Tuple.fst)
      insts in
    let fs := hashUnitId cid sorted_insts in
    IndefUnitId fs (Unique.getUnique fs) cid sorted_insts
                (UniqDSet.unionManyUniqDSets (GHC.Base.map (moduleFreeHoles GHC.Base.∘
                                                            Data.Tuple.snd) insts)).

Definition generalizeIndefUnitId : IndefUnitId -> IndefUnitId :=
  fun arg_0__ =>
    let 'IndefUnitId _ _ cid insts _ := arg_0__ in
    newIndefUnitId cid (GHC.Base.map (fun arg_1__ =>
                                        let 'pair m _ := arg_1__ in
                                        pair m (mkHoleModule m)) insts).

Definition generalizeIndefModule : IndefModule -> IndefModule :=
  fun arg_0__ =>
    let 'IndefModule uid n := arg_0__ in
    IndefModule (generalizeIndefUnitId uid) n.

Definition newUnitId
   : ComponentId -> list (ModuleName * Module)%type -> UnitId :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | cid, nil => newSimpleUnitId cid
    | cid, insts => IndefiniteUnitId (newIndefUnitId cid insts)
    end.

Definition parseUnitId : Text.ParserCombinators.ReadP.ReadP UnitId :=
  let parseSimpleUnitId :=
    parseComponentId GHC.Base.>>=
    (fun cid => GHC.Base.return_ (newSimpleUnitId cid)) in
  let parseDefiniteUnitId :=
    Text.ParserCombinators.ReadP.munch1 (fun c =>
                                           orb (GHC.Unicode.isAlphaNum c) (Data.Foldable.elem c (GHC.Base.hs_string__
                                                                                               "-_.+"))) GHC.Base.>>=
    (fun s => GHC.Base.return_ (stringToUnitId s)) in
  let parseFullUnitId :=
    parseComponentId GHC.Base.>>=
    (fun cid =>
       parseModSubst GHC.Base.>>=
       (fun insts => GHC.Base.return_ (newUnitId cid insts))) in
  parseFullUnitId Text.ParserCombinators.ReadP.<++
  (parseDefiniteUnitId Text.ParserCombinators.ReadP.<++ parseSimpleUnitId).

Definition parseModSubst
   : Text.ParserCombinators.ReadP.ReadP (list (ModuleName * Module)%type) :=
  (Text.ParserCombinators.ReadP.between (Text.ParserCombinators.ReadP.char
                                         (GHC.Char.hs_char__ "[")) (Text.ParserCombinators.ReadP.char
                                                                    (GHC.Char.hs_char__ "]")) GHC.Base.∘
   GHC.Base.flip Text.ParserCombinators.ReadP.sepBy
   (Text.ParserCombinators.ReadP.char (GHC.Char.hs_char__ ","))) (parseModuleName
                                                                  GHC.Base.>>=
                                                                  (fun k =>
                                                                     Text.ParserCombinators.ReadP.char
                                                                     (GHC.Char.hs_char__ "=") GHC.Base.>>=
                                                                     (fun _ =>
                                                                        parseModuleId GHC.Base.>>=
                                                                        (fun v => GHC.Base.return_ (pair k v))))).

Definition parseModuleId : Text.ParserCombinators.ReadP.ReadP Module :=
  let parseModule :=
    parseUnitId GHC.Base.>>=
    (fun uid =>
       Text.ParserCombinators.ReadP.char (GHC.Char.hs_char__ ":") GHC.Base.>>=
       (fun _ =>
          parseModuleName GHC.Base.>>=
          (fun modname => GHC.Base.return_ (mkModule uid modname)))) in
  let parseModuleVar :=
    Text.ParserCombinators.ReadP.char (GHC.Char.hs_char__ "<") GHC.Base.>>=
    (fun _ =>
       parseModuleName GHC.Base.>>=
       (fun modname =>
          Text.ParserCombinators.ReadP.char (GHC.Char.hs_char__ ">") GHC.Base.>>=
          (fun _ => GHC.Base.return_ (mkHoleModule modname)))) in
  parseModuleVar Text.ParserCombinators.ReadP.<++ parseModule.

Definition renameHoleUnitId'
   : Packages.PackageConfigMap -> ShHoleSubst -> UnitId -> UnitId :=
  fun pkg_map env uid =>
    match uid with
    | IndefiniteUnitId (IndefUnitId _ _ cid insts fh) =>
        if UniqFM.isNullUFM (UniqFM.intersectUFM_C GHC.Base.const (UniqDFM.udfmToUfm fh)
                             env) : bool
        then uid
        else Packages.improveUnitId pkg_map (newUnitId cid (GHC.Base.map (fun arg_0__ =>
                                                                            let 'pair k v := arg_0__ in
                                                                            pair k (renameHoleModule' pkg_map env v))
                                                        insts))
    | _ => uid
    end.

Definition renameHoleModule'
   : Packages.PackageConfigMap -> ShHoleSubst -> Module -> Module :=
  fun pkg_map env m =>
    if negb (isHoleModule m) : bool
    then let uid := renameHoleUnitId' pkg_map env (moduleUnitId m) in
         mkModule uid (moduleName m) else
    match UniqFM.lookupUFM env (moduleName m) with
    | Some m' => m'
    | _ => m
    end.

Definition renameHoleModule
   : DynFlags.DynFlags -> ShHoleSubst -> Module -> Module :=
  fun dflags => renameHoleModule' (Packages.getPackageConfigMap dflags).

Definition renameHoleUnitId
   : DynFlags.DynFlags -> ShHoleSubst -> UnitId -> UnitId :=
  fun dflags => renameHoleUnitId' (Packages.getPackageConfigMap dflags).

Definition unitModuleEnv {a} : Module -> a -> ModuleEnv a :=
  fun m x => Mk_ModuleEnv (Data.Map.Internal.singleton (Mk_NDModule m) x).

Definition unitModuleSet : Module -> ModuleSet :=
  GHC.Prim.coerce Data.Set.Internal.singleton.

(* Unbound variables:
     Eq Gt Lt None Some andb bool comparison cons default false list mkModuleName
     negb nil op_zt__ option orb pair parseModSubst parseModuleId renameHoleModule'
     true Coq.Init.Datatypes.app Coq.Lists.List.flat_map Data.ByteString.concat
     Data.ByteString.Char8.pack Data.ByteString.Char8.singleton
     Data.ByteString.Unsafe.unsafeUseAsCStringLen Data.Foldable.elem
     Data.Foldable.foldl' Data.Function.on Data.Map.Internal.Map
     Data.Map.Internal.delete Data.Map.Internal.empty Data.Map.Internal.filterWithKey
     Data.Map.Internal.findWithDefault Data.Map.Internal.fromList
     Data.Map.Internal.insert Data.Map.Internal.insertWith Data.Map.Internal.keys
     Data.Map.Internal.lookup Data.Map.Internal.mapWithKey Data.Map.Internal.member
     Data.Map.Internal.null Data.Map.Internal.singleton Data.Map.Internal.toList
     Data.Map.Internal.union Data.Map.Internal.unionWith Data.OldList.sort
     Data.OldList.sortBy Data.Ord.comparing Data.Set.Internal.Set_
     Data.Set.Internal.delete Data.Set.Internal.difference Data.Set.Internal.empty
     Data.Set.Internal.fromList Data.Set.Internal.insert
     Data.Set.Internal.intersection Data.Set.Internal.member
     Data.Set.Internal.singleton Data.Set.Internal.toList Data.Set.Internal.union
     Data.Tuple.fst Data.Tuple.snd DynFlags.DynFlags Encoding.toBase62Padded
     FastString.FastString FastString.fastStringToByteString FastString.fsLit
     FastString.mkFastString FastString.mkFastStringByteString FastString.unpackFS
     FiniteMap.deleteList FiniteMap.insertList FiniteMap.insertListWith GHC.Base.Eq_
     GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.const GHC.Base.flip
     GHC.Base.fmap GHC.Base.map GHC.Base.max GHC.Base.min GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zgzgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.Base.return_
     GHC.Fingerprint.fingerprintData GHC.Fingerprint.Type.Fingerprint
     GHC.IO.Unsafe.unsafePerformIO GHC.PackageDb.toStringRep GHC.Prim.coerce
     GHC.Ptr.castPtr GHC.Unicode.isAlphaNum Packages.PackageConfigMap
     Packages.getPackageConfigMap Packages.improveUnitId Panic.noString
     Text.ParserCombinators.ReadP.ReadP Text.ParserCombinators.ReadP.between
     Text.ParserCombinators.ReadP.char Text.ParserCombinators.ReadP.munch1
     Text.ParserCombinators.ReadP.op_zlzpzp__ Text.ParserCombinators.ReadP.sepBy
     UniqDFM.UniqDFM UniqDFM.udfmToUfm UniqDSet.UniqDSet UniqDSet.emptyUniqDSet
     UniqDSet.isEmptyUniqDSet UniqDSet.unionManyUniqDSets UniqDSet.unitUniqDSet
     UniqFM.UniqFM UniqFM.intersectUFM_C UniqFM.isNullUFM UniqFM.lookupUFM
     Unique.Unique Unique.getUnique Unique.nonDetCmpUnique Util.thenCmp
*)
