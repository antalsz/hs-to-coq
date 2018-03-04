(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Core.

(* Converted imports: *)

Require Core.
Require GHC.Base.
Require IdInfo.
Require Name.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition TypeVar :=
  Core.Var%type.

Definition TKVar :=
  Core.Var%type.

Definition KindVar :=
  Core.Var%type.

Inductive IdScope : Type
  := GlobalId : IdScope
  |  LocalId : Core.ExportFlag -> IdScope.

Definition Id :=
  Core.Var%type.

Definition NcId :=
  Id%type.

Definition TyCoVar :=
  Id%type.

Definition EvId :=
  Id%type.

Definition EvVar :=
  EvId%type.

Definition IpId :=
  EvId%type.

Definition EqVar :=
  EvId%type.

Definition DictId :=
  EvId%type.

Definition DFunId :=
  Id%type.
(* Midamble *)

Instance Unique_Var : Unique.Uniquable Var := {}.
Admitted.

Require Import GHC.Err.
Instance Default_IdScope : Default IdScope := Build_Default _ GlobalId.
Instance Default_Var : Default Var := Build_Default _ (Mk_Id default default default default default default).


Instance Name_NamedThing_TyCoVar : Name.NamedThing TyCoVar.
Admitted.
Instance Name_NamedThing_VarId : Name.NamedThing Var.Id.
Admitted.



Definition varType (arg_8__ : Var) :=
  match arg_8__ with
    | Core.Mk_TyVar _ _ varType => varType
    | Core.Mk_TcTyVar _ _ varType _ => varType
    | Core.Mk_Id _ _ varType _ _ _ => varType
  end.


Definition realUnique (arg_8__ : Var) :=
  match arg_8__ with
    | Core.Mk_TyVar _ u _ => u
    | Core.Mk_TcTyVar _ u _ _ => u
    | Core.Mk_Id _ u _ _ _ _ => u
  end.

Definition varName (arg_8__ : Var) :=
  match arg_8__ with
    | Core.Mk_TyVar n _ _ => n
    | Core.Mk_TcTyVar n _ _ _ => n
    | Core.Mk_Id n _ _ _ _ _ => n
  end.

(* Converted value declarations: *)

(* Translating `instance Outputable.Outputable Core.Var' failed: OOPS! Cannot
   find information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Name.NamedThing Core.Var' failed: OOPS! Cannot find
   information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Unique.Uniquable Core.Var' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition Eq___Var_op_zeze__ : Core.Var -> Core.Var -> bool :=
  fun a b => realUnique a GHC.Base.== realUnique b.

Local Definition Eq___Var_op_zsze__ : Core.Var -> Core.Var -> bool :=
  fun x y => negb (Eq___Var_op_zeze__ x y).

Program Instance Eq___Var : GHC.Base.Eq_ Core.Var :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Var_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Var_op_zsze__ |}.

Local Definition Ord__Var_op_zg__ : Core.Var -> Core.Var -> bool :=
  fun a b => realUnique a GHC.Base.> realUnique b.

Local Definition Ord__Var_op_zgze__ : Core.Var -> Core.Var -> bool :=
  fun a b => realUnique a GHC.Base.>= realUnique b.

Local Definition Ord__Var_op_zl__ : Core.Var -> Core.Var -> bool :=
  fun a b => realUnique a GHC.Base.< realUnique b.

Local Definition Ord__Var_op_zlze__ : Core.Var -> Core.Var -> bool :=
  fun a b => realUnique a GHC.Base.<= realUnique b.

Local Definition Ord__Var_min : Core.Var -> Core.Var -> Core.Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then x else y.

Local Definition Ord__Var_max : Core.Var -> Core.Var -> Core.Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then y else x.

(* Translating `instance Data.Data.Data Core.Var' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

Axiom globaliseId : forall {A : Type}, A.

(* Translating `globaliseId' failed: invalid record upate with non-record-field
   `idScope' unsupported *)

Axiom idDetails : forall {A : Type}, A.

(* Translating `idDetails' failed: using a record pattern for the unknown
   constructor `Id' unsupported *)

Axiom idInfo : forall {A : Type}, A.

(* Translating `idInfo' failed: using a record pattern for the unknown
   constructor `Id' unsupported *)

Axiom isCoVar : forall {A : Type}, A.

(* Translating `isCoVar' failed: using a record pattern for the unknown
   constructor `Id' unsupported *)

Axiom isExportedId : forall {A : Type}, A.

(* Translating `isExportedId' failed: using a record pattern for the unknown
   constructor `Id' unsupported *)

Axiom isGlobalId : forall {A : Type}, A.

Definition isLocalVar : Core.Var -> bool :=
  fun v => negb (isGlobalId v).

Definition mustHaveLocalBinding : Core.Var -> bool :=
  fun var => isLocalVar var.

(* Translating `isGlobalId' failed: using a record pattern for the unknown
   constructor `Id' unsupported *)

Axiom isId : forall {A : Type}, A.

(* Translating `isId' failed: using a record pattern for the unknown constructor
   `Id' unsupported *)

Axiom isLocalId : forall {A : Type}, A.

(* Translating `isLocalId' failed: using a record pattern for the unknown
   constructor `Id' unsupported *)

Axiom isNonCoVarId : forall {A : Type}, A.

(* Translating `isNonCoVarId' failed: using a record pattern for the unknown
   constructor `Id' unsupported *)

Axiom isTKVar : forall {A : Type}, A.

Definition isTyVar : Core.Var -> bool :=
  isTKVar.

Definition isTyCoVar : Core.Var -> bool :=
  fun v => orb (isTyVar v) (isCoVar v).

(* Translating `isTKVar' failed: using a record pattern for the unknown
   constructor `TyVar' unsupported *)

Axiom isTcTyVar : forall {A : Type}, A.

(* Translating `isTcTyVar' failed: using a record pattern for the unknown
   constructor `TcTyVar' unsupported *)

Axiom lazySetIdInfo : forall {A : Type}, A.

(* Translating `lazySetIdInfo' failed: invalid record upate with
   non-record-field `id_info' unsupported *)

Axiom mkTcTyVar : forall {A : Type}, A.

(* Translating `mkTcTyVar' failed: creating a record with the unknown
   constructor `TcTyVar' unsupported *)

Axiom mkTyVar : forall {A : Type}, A.

(* Translating `mkTyVar' failed: creating a record with the unknown constructor
   `TyVar' unsupported *)

Axiom mk_id : forall {A : Type}, A.

Definition mkLocalVar
   : IdInfo.IdDetails -> Name.Name -> Core.Type_ -> IdInfo.IdInfo -> Id :=
  fun details name ty info =>
    mk_id name ty (LocalId Core.NotExported) details info.

Definition mkGlobalVar
   : IdInfo.IdDetails -> Name.Name -> Core.Type_ -> IdInfo.IdInfo -> Id :=
  fun details name ty info => mk_id name ty GlobalId details info.

Definition mkExportedLocalVar
   : IdInfo.IdDetails -> Name.Name -> Core.Type_ -> IdInfo.IdInfo -> Id :=
  fun details name ty info => mk_id name ty (LocalId Core.Exported) details info.

Definition mkCoVar : Name.Name -> Core.Type_ -> CoVar :=
  fun name ty =>
    mk_id name ty (LocalId Core.NotExported) IdInfo.coVarDetails
    IdInfo.vanillaIdInfo.

(* Translating `mk_id' failed: creating a record with the unknown constructor
   `Id' unsupported *)

Axiom setIdDetails : forall {A : Type}, A.

(* Translating `setIdDetails' failed: invalid record upate with non-record-field
   `id_details' unsupported *)

Axiom setIdExported : forall {A : Type}, A.

(* Translating `setIdExported' failed: using a record pattern for the unknown
   constructor `Id' unsupported *)

Axiom setIdNotExported : forall {A : Type}, A.

(* Translating `setIdNotExported' failed: invalid record upate with
   non-record-field `idScope' unsupported *)

Axiom setTcTyVarDetails : forall {A : Type}, A.

(* Translating `setTcTyVarDetails' failed: invalid record upate with
   non-record-field `tc_tv_details' unsupported *)

Axiom setTyVarKind : forall {A : Type}, A.

(* Translating `setTyVarKind' failed: invalid record upate with non-record-field
   `varType' unsupported *)

Axiom setVarName : forall {A : Type}, A.

Definition setTyVarName : TyVar -> Name.Name -> TyVar :=
  setVarName.

(* Translating `setVarName' failed: invalid record upate with non-record-fields
   `realUnique' and `varName' unsupported *)

Axiom setVarType : forall {A : Type}, A.

(* Translating `setVarType' failed: invalid record upate with non-record-field
   `varType' unsupported *)

Axiom setVarUnique : forall {A : Type}, A.

Definition setTyVarUnique : TyVar -> Unique.Unique -> TyVar :=
  setVarUnique.

(* Translating `setVarUnique' failed: invalid record upate with
   non-record-fields `realUnique' and `varName' unsupported *)

Definition tcTyVarDetails : TyVar -> unit :=
  fun x => tt.

Definition tyVarKind : TyVar -> Kind :=
  varType.

Definition tyVarName : TyVar -> Name.Name :=
  varName.

Axiom updateTyVarKind : forall {A : Type}, A.

(* Translating `updateTyVarKind' failed: invalid record upate with
   non-record-field `varType' unsupported *)

Axiom updateTyVarKindM : forall {A : Type}, A.

(* Translating `updateTyVarKindM' failed: invalid record upate with
   non-record-field `varType' unsupported *)

Axiom updateVarType : forall {A : Type}, A.

(* Translating `updateVarType' failed: invalid record upate with
   non-record-field `varType' unsupported *)

Axiom updateVarTypeM : forall {A : Type}, A.

(* Translating `updateVarTypeM' failed: invalid record upate with
   non-record-field `varType' unsupported *)

Definition varUnique : Core.Var -> Unique.Unique :=
  fun var => Unique.mkUniqueGrimily (realUnique var).

Definition nonDetCmpVar : Core.Var -> Core.Var -> comparison :=
  fun a b => Unique.nonDetCmpUnique (varUnique a) (varUnique b).

Local Definition Ord__Var_compare : Core.Var -> Core.Var -> comparison :=
  fun a b => nonDetCmpVar a b.

Program Instance Ord__Var : GHC.Base.Ord Core.Var :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Var_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Var_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Var_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Var_op_zgze__ ;
         GHC.Base.compare__ := Ord__Var_compare ;
         GHC.Base.max__ := Ord__Var_max ;
         GHC.Base.min__ := Ord__Var_min |}.

(* Unbound variables:
     CoVar Kind TyVar bool comparison negb orb realUnique tt unit varName varType
     Core.ExportFlag Core.Exported Core.NotExported Core.Type_ Core.Var GHC.Base.Eq_
     GHC.Base.Ord GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ IdInfo.IdDetails IdInfo.IdInfo
     IdInfo.coVarDetails IdInfo.vanillaIdInfo Name.Name Unique.Unique
     Unique.mkUniqueGrimily Unique.nonDetCmpUnique
*)
