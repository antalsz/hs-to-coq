(* Axiomatized version *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Num.
Require IdInfo.
Require Name.
Require Panic.
(* Require TyCoRep.*)
Require Unique.
Require Util.
Import GHC.Base.Notations.

Require Import Core.

(* Converted type declarations: *)
(*
Inductive ExportFlag : Type := NotExported : ExportFlag
                            |  Exported : ExportFlag.

Inductive IdScope : Type := GlobalId : IdScope
                         |  LocalId : ExportFlag -> IdScope.
*)

Parameter varName : Var -> Name.Name.
Parameter realUnique : Var -> GHC.Num.Int.

(*
 := Mk_TyVar
    : Name.Name -> GHC.Num.Int -> TyCoRep.Kind -> Var
 |  TcTyVar : Name.Name -> GHC.Num.Int -> TyCoRep.Kind -> unit -> Var
 |  Mk_Id
    : Name.Name -> GHC.Num.Int -> TyCoRep.Type_ -> IdScope -> IdInfo.IdDetails -> IdInfo.IdInfo -> Var.
*)

Definition Id :=
  Var%type.

Definition NcId :=
  Id%type.

Definition TyCoVar :=
  Id%type.

Definition KindVar :=
  Var%type.

Definition TKVar :=
  Var%type.

Definition TypeVar :=
  Var%type.

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


Parameter idScope : Var -> IdScope.

Parameter id_details : Var -> IdInfo.IdDetails.

Parameter id_info : Var -> IdInfo.IdInfo.

Parameter tc_tv_details : Var -> unit.  (* TcType.TcTyVarDetails. *)


Parameter tyVarKind       : TyVar -> Kind.
Parameter setTyVarKind    : TyVar -> Kind -> TyVar.
Parameter updateTyVarKind : (Kind -> Kind) -> TyVar -> TyVar.
Parameter mkCoVar         : Name.Name -> Kind -> TyVar.
Parameter mkTyVar         : Name.Name -> Kind -> TyVar.
Parameter setVarTyp       : Var -> Type_ -> Var.

Definition varType (arg_8__ : Var) :=
  match arg_8__ with
    | Core.Mk_TyVar _ _ varType => varType
    | Core.Mk_TcTyVar _ _ varType _ => varType
    | Core.Mk_Id _ _ varType _ _ _ => varType
  end.


Instance Unique_Var : Unique.Uniquable Var := {}.
Admitted.

Require Import Panic.
Instance Default_IdScope : Default IdScope := {}. Admitted.
Instance Default_Var : Default Var := {}. Admitted.


Instance Name_NamedThing_TyCoVar : Name.NamedThing TyCoVar.
Admitted.
Instance Name_NamedThing_VarId : Name.NamedThing Var.Id.
Admitted.


(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)


(* Translating `instance Outputable.Outputable Var.Var' failed: OOPS! Cannot
   find information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Name.NamedThing Var.Var' failed: OOPS! Cannot find
   information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Unique.Uniquable Var.Var' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition Eq___Var_op_zeze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.== realUnique b.

Local Definition Eq___Var_op_zsze__ : Var -> Var -> bool :=
  fun x y => negb (Eq___Var_op_zeze__ x y).

Program Instance Eq___Var : GHC.Base.Eq_ Var := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Var_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Var_op_zsze__ |}.

Local Definition Ord__Var_op_zg__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.> realUnique b.

Local Definition Ord__Var_op_zgze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.>= realUnique b.

Local Definition Ord__Var_op_zl__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.< realUnique b.

Local Definition Ord__Var_op_zlze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.<= realUnique b.

Local Definition Ord__Var_min : Var -> Var -> Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then x else y.

Local Definition Ord__Var_max : Var -> Var -> Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then y else x.

(* Translating `instance Data.Data.Data Var.Var' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)
(*
Definition globaliseId : Id -> Id :=
  fun id =>
    match id with
      | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
              id_info_5__ => Mk_Id varName_0__ realUnique_1__ varType_2__ GlobalId
                                   id_details_4__ id_info_5__
    end.
*)
Parameter idDetails : Id -> IdInfo.IdDetails.

Parameter idInfo : Id -> IdInfo.IdInfo.

Parameter isCoVar : Var -> bool.

Parameter isExportedId : Var -> bool.

Parameter isGlobalId : Var -> bool.

Parameter isLocalVar : Var -> bool.

Parameter mustHaveLocalBinding : Var -> bool.

Parameter isId : Var -> bool.

Parameter isLocalId : Var -> bool.

Parameter setIdNotExported : Id -> Id.

Parameter isNonCoVarId : Var -> bool.

Parameter isTKVar : Var -> bool.

Parameter isTyVar : Var -> bool.

Parameter isTyCoVar : Var -> bool.

Parameter isTcTyVar : Var -> bool.

Parameter lazySetIdInfo : Id -> IdInfo.IdInfo -> Var.


Parameter setIdDetails : Id -> IdInfo.IdDetails -> Id.

Parameter setIdExported : Id -> Id.

Parameter setTcTyVarDetails : TyVar -> unit -> TyVar. (* TvVarDetails. *)

Parameter setVarName : Var -> Name.Name -> Var.

Parameter setTyVarName : TyVar -> Name.Name -> TyVar.


Parameter setVarUnique : Var -> Unique.Unique -> Var.

Parameter setTyVarUnique : TyVar -> Unique.Unique -> TyVar.

Parameter tcTyVarDetails : TyVar -> unit.

Parameter tyVarName : TyVar -> Name.Name.

Definition varUnique : Var -> Unique.Unique :=
  fun var => Unique.mkUniqueGrimily (realUnique var).

Definition nonDetCmpVar : Var -> Var -> comparison :=
  fun a b => Unique.nonDetCmpUnique (varUnique a) (varUnique b).

Local Definition Ord__Var_compare : Var -> Var -> comparison :=
  fun a b => nonDetCmpVar a b.

Program Instance Ord__Var : GHC.Base.Ord Var := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Var_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Var_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Var_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Var_op_zgze__ ;
      GHC.Base.compare__ := Ord__Var_compare ;
      GHC.Base.max__ := Ord__Var_max ;
      GHC.Base.min__ := Ord__Var_min |}.

(* Unbound variables:
     andb bool comparison error false negb orb true tt unit GHC.Base.Eq_
     GHC.Base.Monad GHC.Base.Ord GHC.Base.op_zd__ GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__
     GHC.Base.return_ GHC.Num.Int IdInfo.IdDetails IdInfo.IdInfo IdInfo.coVarDetails
     IdInfo.isCoVarDetails IdInfo.vanillaIdInfo Name.Name Name.setNameUnique
     Panic.assertPanic Panic.noString Panic.panicStr TyCoRep.Kind TyCoRep.Type_
     Unique.Unique Unique.getKey Unique.getUnique Unique.mkUniqueGrimily
     Unique.nonDetCmpUnique Util.debugIsOn
*)
