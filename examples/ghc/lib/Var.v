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
Require IdInfo.
Require Name.
Require Panic.
Require Unique.
Require Util.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive ExportFlag : Type := NotExported : ExportFlag
                            |  Exported : ExportFlag.

Inductive IdScope : Type := GlobalId : IdScope
                         |  LocalId : ExportFlag -> IdScope.

Inductive Var : Type := Mk_TyVar : Name.Name -> GHC.Num.Int -> unit -> Var
                     |  TcTyVar : Name.Name -> GHC.Num.Int -> unit -> unit -> Var
                     |  Mk_Id
                       : Name.Name -> GHC.Num.Int -> unit -> IdScope -> IdInfo.IdDetails -> IdInfo.IdInfo -> Var.

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

Instance Unique_Var : Unique.Uniquable Var := {}.
Admitted.

Require Import Panic.
Instance Default_IdScope : Default IdScope := Build_Default _ GlobalId.
Instance Default_Var : Default Var := Build_Default _ (Mk_Id default default default default default default).


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

Definition globaliseId : Id -> Id :=
  fun id =>
    match id with
      | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
              id_info_5__ => Mk_Id varName_0__ realUnique_1__ varType_2__ GlobalId
                                   id_details_4__ id_info_5__
    end.

Definition idDetails : Id -> IdInfo.IdDetails :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Id _ _ _ _ details _ => details
      | other => Panic.panicStr (GHC.Base.hs_string__ "idDetails") (Panic.noString
                                                                   other)
    end.

Definition idInfo : Id -> IdInfo.IdInfo :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Id _ _ _ _ _ info => info
      | other => Panic.panicStr (GHC.Base.hs_string__ "idInfo") (Panic.noString other)
    end.

Definition isCoVar : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Id _ _ _ _ details _ => IdInfo.isCoVarDetails details
      | _ => false
    end.

Definition isExportedId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Id _ _ _ GlobalId _ _ => true
      | Mk_Id _ _ _ (LocalId Exported) _ _ => true
      | _ => false
    end.

Definition isGlobalId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Id _ _ _ GlobalId _ _ => true
      | _ => false
    end.

Definition isLocalVar : Var -> bool :=
  fun v => negb (isGlobalId v).

Definition mustHaveLocalBinding : Var -> bool :=
  fun var => isLocalVar var.

Definition isId : Var -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_Id _ _ _ _ _ _ => true | _ => false end.

Definition isLocalId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Id _ _ _ (LocalId _) _ _ => true
      | _ => false
    end.

Definition setIdNotExported : Id -> Id :=
  fun id =>
    if andb Util.debugIsOn (negb (isLocalId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Var.hs")
         (GHC.Num.fromInteger 431))
    else match id with
           | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
           | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
           | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
                   id_info_5__ => Mk_Id varName_0__ realUnique_1__ varType_2__ (LocalId
                                        NotExported) id_details_4__ id_info_5__
         end.

Definition isNonCoVarId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_Id _ _ _ _ details _ => negb (IdInfo.isCoVarDetails details)
      | _ => false
    end.

Definition isTKVar : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_TyVar _ _ _ => true
      | TcTyVar _ _ _ _ => true
      | _ => false
    end.

Definition isTyVar : Var -> bool :=
  isTKVar.

Definition isTyCoVar : Var -> bool :=
  fun v => orb (isTyVar v) (isCoVar v).

Definition isTcTyVar : Var -> bool :=
  fun arg_0__ => match arg_0__ with | TcTyVar _ _ _ _ => true | _ => false end.

Definition lazySetIdInfo : Id -> IdInfo.IdInfo -> Var :=
  fun id info =>
    match id with
      | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
              id_info_5__ => Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__
                                   id_details_4__ info
    end.

Definition mkTcTyVar : Name.Name -> unit -> unit -> TyVar :=
  fun name kind details =>
    TcTyVar missingValue missingValue missingValue missingValue.

Definition mkTyVar : Name.Name -> unit -> TyVar :=
  fun name kind => Mk_TyVar missingValue missingValue missingValue.

Definition mk_id
    : Name.Name -> unit -> IdScope -> IdInfo.IdDetails -> IdInfo.IdInfo -> Id :=
  fun name ty scope details info =>
    Mk_Id missingValue missingValue missingValue missingValue missingValue
          missingValue.

Definition mkLocalVar
    : IdInfo.IdDetails -> Name.Name -> unit -> IdInfo.IdInfo -> Id :=
  fun details name ty info => mk_id name ty (LocalId NotExported) details info.

Definition mkGlobalVar
    : IdInfo.IdDetails -> Name.Name -> unit -> IdInfo.IdInfo -> Id :=
  fun details name ty info => mk_id name ty GlobalId details info.

Definition mkExportedLocalVar
    : IdInfo.IdDetails -> Name.Name -> unit -> IdInfo.IdInfo -> Id :=
  fun details name ty info => mk_id name ty (LocalId Exported) details info.

Definition mkCoVar : Name.Name -> unit -> CoVar :=
  fun name ty =>
    mk_id name ty (LocalId NotExported) IdInfo.coVarDetails IdInfo.vanillaIdInfo.

Definition setIdDetails : Id -> IdInfo.IdDetails -> Id :=
  fun id details =>
    match id with
      | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
              id_info_5__ => Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ details
                                   id_info_5__
    end.

Definition setIdExported : Id -> Id :=
  fun arg_0__ =>
    match arg_0__ with
      | (Mk_Id _ _ _ (LocalId _) _ _ as id) => match id with
                                                 | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__
                                                                           "Partial record update")
                                                 | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__
                                                                            "Partial record update")
                                                 | Mk_Id varName_1__ realUnique_2__ varType_3__ idScope_4__
                                                         id_details_5__ id_info_6__ => Mk_Id varName_1__ realUnique_2__
                                                                                             varType_3__ (LocalId
                                                                                             Exported) id_details_5__
                                                                                             id_info_6__
                                               end
      | (Mk_Id _ _ _ GlobalId _ _ as id) => id
      | tv => Panic.panicStr (GHC.Base.hs_string__ "setIdExported") (Panic.noString
                                                                    tv)
    end.

Definition setTcTyVarDetails : TyVar -> unit -> TyVar :=
  fun tv details =>
    match tv with
      | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | TcTyVar varName_0__ realUnique_1__ varType_2__ tc_tv_details_3__ => TcTyVar
                                                                            varName_0__ realUnique_1__ varType_2__
                                                                            details
      | Mk_Id _ _ _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
    end.

Definition setTyVarKind : TyVar -> unit -> TyVar :=
  fun tv k =>
    match tv with
      | Mk_TyVar varName_0__ realUnique_1__ varType_2__ => Mk_TyVar varName_0__
                                                                    realUnique_1__ k
      | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ => TcTyVar
                                                                            varName_3__ realUnique_4__ k
                                                                            tc_tv_details_6__
      | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
              id_info_12__ => Mk_Id varName_7__ realUnique_8__ k idScope_10__ id_details_11__
                                    id_info_12__
    end.

Definition setVarName : Var -> Name.Name -> Var :=
  fun var new_name =>
    match var with
      | Mk_TyVar varName_0__ realUnique_1__ varType_2__ => Mk_TyVar new_name
                                                                    (Unique.getKey (Unique.getUnique new_name))
                                                                    varType_2__
      | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ => TcTyVar
                                                                            new_name (Unique.getKey (Unique.getUnique
                                                                                                    new_name))
                                                                            varType_5__ tc_tv_details_6__
      | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
              id_info_12__ => Mk_Id new_name (Unique.getKey (Unique.getUnique new_name))
                                    varType_9__ idScope_10__ id_details_11__ id_info_12__
    end.

Definition setTyVarName : TyVar -> Name.Name -> TyVar :=
  setVarName.

Definition setVarType : Id -> unit -> Id :=
  fun id ty =>
    match id with
      | Mk_TyVar varName_0__ realUnique_1__ varType_2__ => Mk_TyVar varName_0__
                                                                    realUnique_1__ ty
      | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ => TcTyVar
                                                                            varName_3__ realUnique_4__ ty
                                                                            tc_tv_details_6__
      | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
              id_info_12__ => Mk_Id varName_7__ realUnique_8__ ty idScope_10__ id_details_11__
                                    id_info_12__
    end.

Definition setVarUnique : Var -> Unique.Unique -> Var :=
  fun var uniq =>
    match var with
      | Mk_TyVar varName_0__ realUnique_1__ varType_2__ => Mk_TyVar
                                                           (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq)
                                                           varType_2__
      | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ => TcTyVar
                                                                            (Name.setNameUnique (varName var) uniq)
                                                                            (Unique.getKey uniq) varType_5__
                                                                            tc_tv_details_6__
      | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
              id_info_12__ => Mk_Id (Name.setNameUnique (varName var) uniq) (Unique.getKey
                                    uniq) varType_9__ idScope_10__ id_details_11__ id_info_12__
    end.

Definition setTyVarUnique : TyVar -> Unique.Unique -> TyVar :=
  setVarUnique.

Definition tcTyVarDetails : TyVar -> unit :=
  fun x => tt.

Definition tyVarKind : TyVar -> unit :=
  varType.

Definition updateTyVarKind : (unit -> unit) -> TyVar -> TyVar :=
  fun update tv =>
    match tv with
      | Mk_TyVar varName_0__ realUnique_1__ varType_2__ => Mk_TyVar varName_0__
                                                                    realUnique_1__ (update (tyVarKind tv))
      | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ => TcTyVar
                                                                            varName_3__ realUnique_4__ (update
                                                                            (tyVarKind tv)) tc_tv_details_6__
      | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
              id_info_12__ => Mk_Id varName_7__ realUnique_8__ (update (tyVarKind tv))
                                    idScope_10__ id_details_11__ id_info_12__
    end.

Definition updateTyVarKindM {m} `{(GHC.Base.Monad m)} : (unit -> m
                                                        unit) -> TyVar -> m TyVar :=
  fun update tv =>
    update (tyVarKind tv) GHC.Base.>>= (fun k' =>
      GHC.Base.return_ GHC.Base.$ (match tv with
        | Mk_TyVar varName_0__ realUnique_1__ varType_2__ => Mk_TyVar varName_0__
                                                                      realUnique_1__ k'
        | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ => TcTyVar
                                                                              varName_3__ realUnique_4__ k'
                                                                              tc_tv_details_6__
        | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
                id_info_12__ => Mk_Id varName_7__ realUnique_8__ k' idScope_10__ id_details_11__
                                      id_info_12__
      end)).

Definition tyVarName : TyVar -> Name.Name :=
  varName.

Definition updateVarType : (unit -> unit) -> Id -> Id :=
  fun f id =>
    match id with
      | Mk_TyVar varName_0__ realUnique_1__ varType_2__ => Mk_TyVar varName_0__
                                                                    realUnique_1__ (f (varType id))
      | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ => TcTyVar
                                                                            varName_3__ realUnique_4__ (f (varType id))
                                                                            tc_tv_details_6__
      | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
              id_info_12__ => Mk_Id varName_7__ realUnique_8__ (f (varType id)) idScope_10__
                                    id_details_11__ id_info_12__
    end.

Definition updateVarTypeM {m} `{GHC.Base.Monad m} : (unit -> m unit) -> Id -> m
                                                    Id :=
  fun f id =>
    f (varType id) GHC.Base.>>= (fun ty' =>
      GHC.Base.return_ (match id with
                         | Mk_TyVar varName_0__ realUnique_1__ varType_2__ => Mk_TyVar varName_0__
                                                                                       realUnique_1__ ty'
                         | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ => TcTyVar
                                                                                               varName_3__
                                                                                               realUnique_4__ ty'
                                                                                               tc_tv_details_6__
                         | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
                                 id_info_12__ => Mk_Id varName_7__ realUnique_8__ ty' idScope_10__
                                                       id_details_11__ id_info_12__
                       end)).

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
     Panic.assertPanic Panic.noString Panic.panicStr Unique.Unique Unique.getKey
     Unique.getUnique Unique.mkUniqueGrimily Unique.nonDetCmpUnique Util.debugIsOn
*)
