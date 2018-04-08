(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

(* Require Import Core.*)

(* Converted imports: *)

Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require IdInfo.
Require Name.
Require Panic.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive TyVarBndr tyvar argf : Type
  := TvBndr : tyvar -> argf -> TyVarBndr tyvar argf.

Inductive ExportFlag : Type
  := NotExported : ExportFlag
  |  Exported : ExportFlag.

Inductive IdScope : Type
  := GlobalId : IdScope
  |  LocalId : ExportFlag -> IdScope.

Inductive Var : Type
  := Mk_TyVar : Name.Name -> GHC.Num.Int -> unit -> Var
  |  Mk_TcTyVar : Name.Name -> GHC.Num.Int -> unit -> unit -> Var
  |  Mk_Id
   : Name.Name ->
     GHC.Num.Int -> unit -> IdScope -> IdInfo.IdDetails -> IdInfo.IdInfo -> Var.

Definition Id :=
  Var%type.

Definition InId :=
  Id%type.

Definition JoinId :=
  Id%type.

Definition NcId :=
  Id%type.

Definition OutId :=
  Id%type.

Definition TyCoVar :=
  Id%type.

Definition InVar :=
  Var%type.

Definition KindVar :=
  Var%type.

Definition OutVar :=
  Var%type.

Definition TKVar :=
  Var%type.

Definition TyVar :=
  Var%type.

Definition InTyVar :=
  TyVar%type.

Definition OutTyVar :=
  TyVar%type.

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

Definition InCoVar :=
  CoVar%type.

Definition OutCoVar :=
  CoVar%type.

Inductive ArgFlag : Type
  := Required : ArgFlag
  |  Specified : ArgFlag
  |  Inferred : ArgFlag.

Definition TyVarBinder :=
  (TyVarBndr TyVar ArgFlag)%type.

Arguments TvBndr {_} {_} _ _.

Instance Default__ExportFlag : GHC.Err.Default ExportFlag :=
  GHC.Err.Build_Default _ NotExported.

Instance Default__IdScope : GHC.Err.Default IdScope :=
  GHC.Err.Build_Default _ GlobalId.

Instance Default__ArgFlag : GHC.Err.Default ArgFlag :=
  GHC.Err.Build_Default _ Required.

Definition idScope (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `idScope' has no match in constructor `Mk_TyVar' of type `Var'")
  | Mk_TcTyVar _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `idScope' has no match in constructor `Mk_TcTyVar' of type `Var'")
  | Mk_Id _ _ _ idScope _ _ => idScope
  end.

Definition id_details (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_details' has no match in constructor `Mk_TyVar' of type `Var'")
  | Mk_TcTyVar _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_details' has no match in constructor `Mk_TcTyVar' of type `Var'")
  | Mk_Id _ _ _ _ id_details _ => id_details
  end.

Definition id_info (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_info' has no match in constructor `Mk_TyVar' of type `Var'")
  | Mk_TcTyVar _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_info' has no match in constructor `Mk_TcTyVar' of type `Var'")
  | Mk_Id _ _ _ _ _ id_info => id_info
  end.

Definition realUnique (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar _ realUnique _ => realUnique
  | Mk_TcTyVar _ realUnique _ _ => realUnique
  | Mk_Id _ realUnique _ _ _ _ => realUnique
  end.

Definition tc_tv_details (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tc_tv_details' has no match in constructor `Mk_TyVar' of type `Var'")
  | Mk_TcTyVar _ _ _ tc_tv_details => tc_tv_details
  | Mk_Id _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tc_tv_details' has no match in constructor `Mk_Id' of type `Var'")
  end.

Definition varName (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar varName _ _ => varName
  | Mk_TcTyVar varName _ _ _ => varName
  | Mk_Id varName _ _ _ _ _ => varName
  end.

Definition varType (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar _ _ varType => varType
  | Mk_TcTyVar _ _ varType _ => varType
  | Mk_Id _ _ varType _ _ _ => varType
  end.
(* Midamble *)

Instance Unique_Var : Unique.Uniquable Var := {}.
Admitted.

Require Import GHC.Err.


(*
Instance Default__IdScope : Default IdScope := Build_Default _ GlobalId. 
*)
Instance Default__Var : Default Var := Build_Default _ (Mk_Id default default default default default default).


Instance Name_NamedThing_TyCoVar : Name.NamedThing TyCoVar.
Admitted.
Instance Name_NamedThing_VarId : Name.NamedThing Id.
Admitted.


(*
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
*)
(* Converted value declarations: *)

(* Translating `instance Outputable__TyVarBndr__ArgFlag__11' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Binary__TyVarBndr' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__ArgFlag' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__ArgFlag' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__Var' failed: OOPS! Cannot find information
   for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance NamedThing__Var' failed: OOPS! Cannot find information
   for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Uniquable__Var' failed: OOPS! Cannot find information
   for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition Eq___Var_op_zeze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.== realUnique b.

Local Definition Eq___Var_op_zsze__ : Var -> Var -> bool :=
  fun x y => negb (Eq___Var_op_zeze__ x y).

Program Instance Eq___Var : GHC.Base.Eq_ Var :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Var_op_zeze__ ;
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

(* Translating `instance Data__Var' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance HasOccName__Var' failed: OOPS! Cannot find information
   for class Qualified "OccName" "HasOccName" unsupported *)

(* Translating `instance Data__TyVarBndr' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__ArgFlag' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___ArgFlag_op_zeze__ : ArgFlag -> ArgFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Required, Required => true
    | Specified, Specified => true
    | Inferred, Inferred => true
    | _, _ => false
    end.

Local Definition Eq___ArgFlag_op_zsze__ : ArgFlag -> ArgFlag -> bool :=
  fun x y => negb (Eq___ArgFlag_op_zeze__ x y).

Program Instance Eq___ArgFlag : GHC.Base.Eq_ ArgFlag :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___ArgFlag_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___ArgFlag_op_zsze__ |}.

Definition binderArgFlag {tv} {argf} : TyVarBndr tv argf -> argf :=
  fun arg_0__ => let 'TvBndr _ argf := arg_0__ in argf.

Definition binderVar {tv} {argf} : TyVarBndr tv argf -> tv :=
  fun arg_0__ => let 'TvBndr v _ := arg_0__ in v.

Definition binderVars {tv} {argf} : list (TyVarBndr tv argf) -> list tv :=
  fun tvbs => GHC.Base.map binderVar tvbs.

Definition globaliseId : Id -> Id :=
  fun id =>
    match id with
    | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_TcTyVar _ _ _ _ =>
        GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
    id_info_5__ =>
        Mk_Id varName_0__ realUnique_1__ varType_2__ GlobalId id_details_4__ id_info_5__
    end.

Definition idDetails : Id -> IdInfo.IdDetails :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ _ details _ => details
    | other =>
        Panic.panicStr (GHC.Base.hs_string__ "idDetails") (Panic.noString other)
    end.

Definition idInfo `{Util.HasDebugCallStack} : Id -> IdInfo.IdInfo :=
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
          #591)
    else match id with
         | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
         | Mk_TcTyVar _ _ _ _ =>
             GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
         | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
         id_info_5__ =>
             Mk_Id varName_0__ realUnique_1__ varType_2__ (LocalId NotExported)
                   id_details_4__ id_info_5__
         end.

Definition isNonCoVarId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ _ details _ => negb (IdInfo.isCoVarDetails details)
    | _ => false
    end.

Definition isTcTyVar : Var -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_TcTyVar _ _ _ _ => true | _ => false end.

Definition isTyVar : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_TyVar _ _ _ => true
    | Mk_TcTyVar _ _ _ _ => true
    | _ => false
    end.

Definition isTyCoVar : Var -> bool :=
  fun v => orb (isTyVar v) (isCoVar v).

Definition isVisibleArgFlag : ArgFlag -> bool :=
  fun arg_0__ => match arg_0__ with | Required => true | _ => false end.

Definition isInvisibleArgFlag : ArgFlag -> bool :=
  negb GHC.Base.∘ isVisibleArgFlag.

Definition lazySetIdInfo : Id -> IdInfo.IdInfo -> Var :=
  fun id info =>
    match id with
    | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_TcTyVar _ _ _ _ =>
        GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
    id_info_5__ =>
        Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__ info
    end.

Definition mkTcTyVar : Name.Name -> unit -> unit -> TyVar :=
  fun name kind details =>
    Mk_TcTyVar name (Unique.getKey (Name.nameUnique name)) kind details.

Definition mkTyVar : Name.Name -> unit -> TyVar :=
  fun name kind => Mk_TyVar name (Unique.getKey (Name.nameUnique name)) kind.

Definition mkTyVarBinder : ArgFlag -> Var -> TyVarBinder :=
  fun vis var => TvBndr var vis.

Definition mkTyVarBinders : ArgFlag -> list TyVar -> list TyVarBinder :=
  fun vis => GHC.Base.map (mkTyVarBinder vis).

Definition mk_id
   : Name.Name -> unit -> IdScope -> IdInfo.IdDetails -> IdInfo.IdInfo -> Id :=
  fun name ty scope details info =>
    Mk_Id name (Unique.getKey (Name.nameUnique name)) ty scope details info.

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

Definition sameVis : ArgFlag -> ArgFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Required, Required => true
    | Required, _ => false
    | _, Required => false
    | _, _ => true
    end.

Definition setIdDetails : Id -> IdInfo.IdDetails -> Id :=
  fun id details =>
    match id with
    | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_TcTyVar _ _ _ _ =>
        GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
    id_info_5__ =>
        Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ details id_info_5__
    end.

Definition setIdExported : Id -> Id :=
  fun arg_0__ =>
    match arg_0__ with
    | (Mk_Id _ _ _ (LocalId _) _ _ as id) =>
        match id with
        | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | Mk_TcTyVar _ _ _ _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | Mk_Id varName_1__ realUnique_2__ varType_3__ idScope_4__ id_details_5__
        id_info_6__ =>
            Mk_Id varName_1__ realUnique_2__ varType_3__ (LocalId Exported) id_details_5__
                  id_info_6__
        end
    | (Mk_Id _ _ _ GlobalId _ _ as id) => id
    | tv =>
        Panic.panicStr (GHC.Base.hs_string__ "setIdExported") (Panic.noString tv)
    end.

Definition setTcTyVarDetails : TyVar -> unit -> TyVar :=
  fun tv details =>
    match tv with
    | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_TcTyVar varName_0__ realUnique_1__ varType_2__ tc_tv_details_3__ =>
        Mk_TcTyVar varName_0__ realUnique_1__ varType_2__ details
    | Mk_Id _ _ _ _ _ _ =>
        GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    end.

Definition setTyVarKind : TyVar -> unit -> TyVar :=
  fun tv k =>
    match tv with
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar varName_0__ realUnique_1__ k
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar varName_3__ realUnique_4__ k tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id varName_7__ realUnique_8__ k idScope_10__ id_details_11__ id_info_12__
    end.

Definition setVarName : Var -> Name.Name -> Var :=
  fun var new_name =>
    match var with
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar new_name (Unique.getKey (Unique.getUnique new_name)) varType_2__
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar new_name (Unique.getKey (Unique.getUnique new_name)) varType_5__
                   tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id new_name (Unique.getKey (Unique.getUnique new_name)) varType_9__
              idScope_10__ id_details_11__ id_info_12__
    end.

Definition setTyVarName : TyVar -> Name.Name -> TyVar :=
  setVarName.

Definition setVarType : Id -> unit -> Id :=
  fun id ty =>
    match id with
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar varName_0__ realUnique_1__ ty
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar varName_3__ realUnique_4__ ty tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id varName_7__ realUnique_8__ ty idScope_10__ id_details_11__ id_info_12__
    end.

Definition setVarUnique : Var -> Unique.Unique -> Var :=
  fun var uniq =>
    match var with
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq)
                 varType_2__
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq)
                   varType_5__ tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq) varType_9__
              idScope_10__ id_details_11__ id_info_12__
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
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar varName_0__ realUnique_1__ (update (tyVarKind tv))
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar varName_3__ realUnique_4__ (update (tyVarKind tv)) tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id varName_7__ realUnique_8__ (update (tyVarKind tv)) idScope_10__
              id_details_11__ id_info_12__
    end.

Definition updateTyVarKindM {m} `{(GHC.Base.Monad m)}
   : (unit -> m unit) -> TyVar -> m TyVar :=
  fun update tv =>
    update (tyVarKind tv) GHC.Base.>>=
    (fun k' =>
       GHC.Base.return_ (match tv with
                         | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
                             Mk_TyVar varName_0__ realUnique_1__ k'
                         | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
                             Mk_TcTyVar varName_3__ realUnique_4__ k' tc_tv_details_6__
                         | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
                         id_info_12__ =>
                             Mk_Id varName_7__ realUnique_8__ k' idScope_10__ id_details_11__ id_info_12__
                         end)).

Definition binderKind {argf} : TyVarBndr TyVar argf -> unit :=
  fun arg_0__ => let 'TvBndr tv _ := arg_0__ in tyVarKind tv.

Definition tyVarName : TyVar -> Name.Name :=
  varName.

Definition updateVarType : (unit -> unit) -> Id -> Id :=
  fun f id =>
    match id with
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar varName_0__ realUnique_1__ (f (varType id))
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar varName_3__ realUnique_4__ (f (varType id)) tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id varName_7__ realUnique_8__ (f (varType id)) idScope_10__ id_details_11__
              id_info_12__
    end.

Definition updateVarTypeM {m} `{GHC.Base.Monad m}
   : (unit -> m unit) -> Id -> m Id :=
  fun f id =>
    f (varType id) GHC.Base.>>=
    (fun ty' =>
       GHC.Base.return_ (match id with
                         | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
                             Mk_TyVar varName_0__ realUnique_1__ ty'
                         | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
                             Mk_TcTyVar varName_3__ realUnique_4__ ty' tc_tv_details_6__
                         | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
                         id_info_12__ =>
                             Mk_Id varName_7__ realUnique_8__ ty' idScope_10__ id_details_11__ id_info_12__
                         end)).

Definition varUnique : Var -> Unique.Unique :=
  fun var => Unique.mkUniqueGrimily (realUnique var).

Definition nonDetCmpVar : Var -> Var -> comparison :=
  fun a b => Unique.nonDetCmpUnique (varUnique a) (varUnique b).

Local Definition Ord__Var_compare : Var -> Var -> comparison :=
  fun a b => nonDetCmpVar a b.

Program Instance Ord__Var : GHC.Base.Ord Var :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Var_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Var_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Var_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Var_op_zgze__ ;
         GHC.Base.compare__ := Ord__Var_compare ;
         GHC.Base.max__ := Ord__Var_max ;
         GHC.Base.min__ := Ord__Var_min |}.

(* External variables:
     andb bool comparison false list negb orb true tt unit GHC.Base.Eq_
     GHC.Base.Monad GHC.Base.Ord GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zgzgze__ GHC.Base.op_zl__
     GHC.Base.op_zlze__ GHC.Base.return_ GHC.Err.Build_Default GHC.Err.Default
     GHC.Err.error GHC.Num.Int GHC.Num.fromInteger IdInfo.IdDetails IdInfo.IdInfo
     IdInfo.coVarDetails IdInfo.isCoVarDetails IdInfo.vanillaIdInfo Name.Name
     Name.nameUnique Name.setNameUnique Panic.assertPanic Panic.noString
     Panic.panicStr Unique.Unique Unique.getKey Unique.getUnique
     Unique.mkUniqueGrimily Unique.nonDetCmpUnique Util.HasDebugCallStack
     Util.debugIsOn
*)
