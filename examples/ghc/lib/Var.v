(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Axiom error : forall {a:Type}, a.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Num.
Require Name.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive ExportFlag : Type := NotExported : ExportFlag
                            |  Exported : ExportFlag.

Inductive IdScope : Type := GlobalId : IdScope
                         |  LocalId : ExportFlag -> IdScope.

Inductive Var : Type := Mk_TyVar : Name.Name -> GHC.Num.Int -> unit -> Var
                     |  TcTyVar : Name.Name -> GHC.Num.Int -> unit -> unit -> Var
                     |  Mk_Id : Name.Name -> GHC.Num.Int -> unit -> IdScope -> unit -> unit -> Var.

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

Definition TyVar :=
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

Definition CoVar :=
  Id%type.

Definition idScope (arg_0__ : Var) :=
  match arg_0__ with
    | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__
                              "Partial record selector: field `idScope' has no match in constructor `Mk_TyVar' of type `Var'")
    | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `idScope' has no match in constructor `TcTyVar' of type `Var'")
    | Mk_Id _ _ _ idScope _ _ => idScope
  end.

Definition id_details (arg_1__ : Var) :=
  match arg_1__ with
    | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__
                              "Partial record selector: field `id_details' has no match in constructor `Mk_TyVar' of type `Var'")
    | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `id_details' has no match in constructor `TcTyVar' of type `Var'")
    | Mk_Id _ _ _ _ id_details _ => id_details
  end.

Definition id_info (arg_2__ : Var) :=
  match arg_2__ with
    | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__
                              "Partial record selector: field `id_info' has no match in constructor `Mk_TyVar' of type `Var'")
    | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `id_info' has no match in constructor `TcTyVar' of type `Var'")
    | Mk_Id _ _ _ _ _ id_info => id_info
  end.

Definition realUnique (arg_3__ : Var) :=
  match arg_3__ with
    | Mk_TyVar _ realUnique _ => realUnique
    | TcTyVar _ realUnique _ _ => realUnique
    | Mk_Id _ realUnique _ _ _ _ => realUnique
  end.

Definition tc_tv_details (arg_4__ : Var) :=
  match arg_4__ with
    | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__
                              "Partial record selector: field `tc_tv_details' has no match in constructor `Mk_TyVar' of type `Var'")
    | TcTyVar _ _ _ tc_tv_details => tc_tv_details
    | Mk_Id _ _ _ _ _ _ => error (GHC.Base.hs_string__
                                 "Partial record selector: field `tc_tv_details' has no match in constructor `Mk_Id' of type `Var'")
  end.

Definition varName (arg_5__ : Var) :=
  match arg_5__ with
    | Mk_TyVar varName _ _ => varName
    | TcTyVar varName _ _ _ => varName
    | Mk_Id varName _ _ _ _ _ => varName
  end.

Definition varType (arg_6__ : Var) :=
  match arg_6__ with
    | Mk_TyVar _ _ varType => varType
    | TcTyVar _ _ varType _ => varType
    | Mk_Id _ _ varType _ _ _ => varType
  end.
(* Midamble *)

Instance Unique_Var : Unique.Uniquable Var.Var := {}.
Admitted.

(* Converted value declarations: *)

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom missingValue : forall {a}, a.

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

Axiom globaliseId : forall {A : Type}, A.

(* Translating `globaliseId' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom lazySetIdInfo : forall {A : Type}, A.

(* Translating `lazySetIdInfo' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom setIdDetails : forall {A : Type}, A.

(* Translating `setIdDetails' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom setIdExported : forall {A : Type}, A.

(* Translating `setIdExported' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom setIdNotExported : forall {A : Type}, A.

(* Translating `setIdNotExported' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom setTcTyVarDetails : forall {A : Type}, A.

(* Translating `setTcTyVarDetails' failed: using a record pattern for the
   unknown constructor `Mk_TyVar' unsupported *)

Axiom setTyVarKind : forall {A : Type}, A.

(* Translating `setTyVarKind' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom setVarName : forall {A : Type}, A.

(* Translating `setVarName' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom setVarType : forall {A : Type}, A.

(* Translating `setVarType' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom setVarUnique : forall {A : Type}, A.

(* Translating `setVarUnique' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom updateTyVarKind : forall {A : Type}, A.

(* Translating `updateTyVarKind' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom updateTyVarKindM : forall {A : Type}, A.

(* Translating `updateTyVarKindM' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom updateVarType : forall {A : Type}, A.

(* Translating `updateVarType' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Axiom updateVarTypeM : forall {A : Type}, A.

(* Translating `updateVarTypeM' failed: using a record pattern for the unknown
   constructor `Mk_TyVar' unsupported *)

Definition isExportedId : Var -> bool :=
  fun arg_7__ =>
    match arg_7__ with
      | Mk_Id _ _ _ GlobalId _ _ => true
      | Mk_Id _ _ _ (LocalId Exported) _ _ => true
      | _ => false
    end.

Definition isGlobalId : Var -> bool :=
  fun arg_9__ =>
    match arg_9__ with
      | Mk_Id _ _ _ GlobalId _ _ => true
      | _ => false
    end.

Definition isLocalVar : Var -> bool :=
  fun v => negb (isGlobalId v).

Definition mustHaveLocalBinding : Var -> bool :=
  fun var => isLocalVar var.

Definition isId : Var -> bool :=
  fun arg_15__ =>
    match arg_15__ with
      | Mk_Id _ _ _ _ _ _ => true
      | _ => false
    end.

Definition isLocalId : Var -> bool :=
  fun arg_13__ =>
    match arg_13__ with
      | Mk_Id _ _ _ (LocalId _) _ _ => true
      | _ => false
    end.

Definition isTKVar : Var -> bool :=
  fun arg_19__ =>
    match arg_19__ with
      | Mk_TyVar _ _ _ => true
      | TcTyVar _ _ _ _ => true
      | _ => false
    end.

Definition isTyVar : Var -> bool :=
  isTKVar.

Definition isTcTyVar : Var -> bool :=
  fun arg_17__ => match arg_17__ with | TcTyVar _ _ _ _ => true | _ => false end.

Definition mkTcTyVar : Name.Name -> unit -> unit -> TyVar :=
  fun name kind details =>
    TcTyVar missingValue missingValue missingValue missingValue.

Definition mkTyVar : Name.Name -> unit -> TyVar :=
  fun name kind => Mk_TyVar missingValue missingValue missingValue.

Definition mk_id : Name.Name -> unit -> IdScope -> unit -> unit -> Id :=
  fun name ty scope details info =>
    Mk_Id missingValue missingValue missingValue missingValue missingValue
          missingValue.

Definition mkLocalVar : unit -> Name.Name -> unit -> unit -> Id :=
  fun details name ty info => mk_id name ty (LocalId NotExported) details info.

Definition mkGlobalVar : unit -> Name.Name -> unit -> unit -> Id :=
  fun details name ty info => mk_id name ty GlobalId details info.

Definition mkExportedLocalVar : unit -> Name.Name -> unit -> unit -> Id :=
  fun details name ty info => mk_id name ty (LocalId Exported) details info.

Definition setTyVarName : TyVar -> Name.Name -> TyVar :=
  setVarName.

Definition setTyVarUnique : TyVar -> Unique.Unique -> TyVar :=
  setVarUnique.

Definition tyVarKind : TyVar -> unit :=
  varType.

Definition tyVarName : TyVar -> Name.Name :=
  varName.

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
     bool comparison error false negb true unit GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zl__
     GHC.Base.op_zlze__ GHC.Num.Int Name.Name Unique.Unique Unique.mkUniqueGrimily
     Unique.nonDetCmpUnique
*)
