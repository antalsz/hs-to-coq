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
      | Mk_Id varName_46__ realUnique_47__ varType_48__ idScope_49__ id_details_50__
              id_info_51__ => Mk_Id varName_46__ realUnique_47__ varType_48__ GlobalId
                                    id_details_50__ id_info_51__
    end.

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

Definition setIdNotExported : Id -> Id :=
  fun id =>
    if andb Util.debugIsOn (negb (isLocalId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Var.hs")
         (GHC.Num.fromInteger 431))
    else match id with
           | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
           | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
           | Mk_Id varName_21__ realUnique_22__ varType_23__ idScope_24__ id_details_25__
                   id_info_26__ => Mk_Id varName_21__ realUnique_22__ varType_23__ (LocalId
                                         NotExported) id_details_25__ id_info_26__
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

Definition lazySetIdInfo : Id -> unit -> Var :=
  fun id info =>
    match id with
      | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | Mk_Id varName_68__ realUnique_69__ varType_70__ idScope_71__ id_details_72__
              id_info_73__ => Mk_Id varName_68__ realUnique_69__ varType_70__ idScope_71__
                                    id_details_72__ info
    end.

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

Definition setIdDetails : Id -> unit -> Id :=
  fun id details =>
    match id with
      | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | Mk_Id varName_57__ realUnique_58__ varType_59__ idScope_60__ id_details_61__
              id_info_62__ => Mk_Id varName_57__ realUnique_58__ varType_59__ idScope_60__
                                    details id_info_62__
    end.

Definition setIdExported : Id -> Id :=
  fun arg_32__ =>
    match arg_32__ with
      | (Mk_Id _ _ _ (LocalId _) _ _ as id) => match id with
                                                 | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__
                                                                           "Partial record update")
                                                 | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__
                                                                            "Partial record update")
                                                 | Mk_Id varName_33__ realUnique_34__ varType_35__ idScope_36__
                                                         id_details_37__ id_info_38__ => Mk_Id varName_33__
                                                                                               realUnique_34__
                                                                                               varType_35__ (LocalId
                                                                                               Exported) id_details_37__
                                                                                               id_info_38__
                                               end
      | (Mk_Id _ _ _ GlobalId _ _ as id) => id
      | tv => Panic.panicStr (GHC.Base.hs_string__ "setIdExported") (Panic.noString
                                                                    tv)
    end.

Definition setTcTyVarDetails : TyVar -> unit -> TyVar :=
  fun tv details =>
    match tv with
      | Mk_TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
      | TcTyVar varName_83__ realUnique_84__ varType_85__ tc_tv_details_86__ =>
        TcTyVar varName_83__ realUnique_84__ varType_85__ details
      | Mk_Id _ _ _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
    end.

Definition setTyVarKind : TyVar -> unit -> TyVar :=
  fun tv k =>
    match tv with
      | Mk_TyVar varName_94__ realUnique_95__ varType_96__ => Mk_TyVar varName_94__
                                                                       realUnique_95__ k
      | TcTyVar varName_97__ realUnique_98__ varType_99__ tc_tv_details_100__ =>
        TcTyVar varName_97__ realUnique_98__ k tc_tv_details_100__
      | Mk_Id varName_101__ realUnique_102__ varType_103__ idScope_104__
              id_details_105__ id_info_106__ => Mk_Id varName_101__ realUnique_102__ k
                                                      idScope_104__ id_details_105__ id_info_106__
    end.

Definition setVarName : Var -> Name.Name -> Var :=
  fun var new_name =>
    match var with
      | Mk_TyVar varName_202__ realUnique_203__ varType_204__ => Mk_TyVar new_name
                                                                          (Unique.getKey (Unique.getUnique new_name))
                                                                          varType_204__
      | TcTyVar varName_205__ realUnique_206__ varType_207__ tc_tv_details_208__ =>
        TcTyVar new_name (Unique.getKey (Unique.getUnique new_name)) varType_207__
                tc_tv_details_208__
      | Mk_Id varName_209__ realUnique_210__ varType_211__ idScope_212__
              id_details_213__ id_info_214__ => Mk_Id new_name (Unique.getKey
                                                      (Unique.getUnique new_name)) varType_211__ idScope_212__
                                                      id_details_213__ id_info_214__
    end.

Definition setTyVarName : TyVar -> Name.Name -> TyVar :=
  setVarName.

Definition setVarType : Id -> unit -> Id :=
  fun id ty =>
    match id with
      | Mk_TyVar varName_184__ realUnique_185__ varType_186__ => Mk_TyVar
                                                                 varName_184__ realUnique_185__ ty
      | TcTyVar varName_187__ realUnique_188__ varType_189__ tc_tv_details_190__ =>
        TcTyVar varName_187__ realUnique_188__ ty tc_tv_details_190__
      | Mk_Id varName_191__ realUnique_192__ varType_193__ idScope_194__
              id_details_195__ id_info_196__ => Mk_Id varName_191__ realUnique_192__ ty
                                                      idScope_194__ id_details_195__ id_info_196__
    end.

Definition setVarUnique : Var -> Unique.Unique -> Var :=
  fun var uniq =>
    match var with
      | Mk_TyVar varName_220__ realUnique_221__ varType_222__ => Mk_TyVar
                                                                 (Name.setNameUnique (varName var) uniq) (Unique.getKey
                                                                 uniq) varType_222__
      | TcTyVar varName_223__ realUnique_224__ varType_225__ tc_tv_details_226__ =>
        TcTyVar (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq)
                varType_225__ tc_tv_details_226__
      | Mk_Id varName_227__ realUnique_228__ varType_229__ idScope_230__
              id_details_231__ id_info_232__ => Mk_Id (Name.setNameUnique (varName var) uniq)
                                                      (Unique.getKey uniq) varType_229__ idScope_230__ id_details_231__
                                                      id_info_232__
    end.

Definition setTyVarUnique : TyVar -> Unique.Unique -> TyVar :=
  setVarUnique.

Definition tyVarKind : TyVar -> unit :=
  varType.

Definition updateTyVarKind : (unit -> unit) -> TyVar -> TyVar :=
  fun update tv =>
    match tv with
      | Mk_TyVar varName_112__ realUnique_113__ varType_114__ => Mk_TyVar
                                                                 varName_112__ realUnique_113__ (update (tyVarKind tv))
      | TcTyVar varName_115__ realUnique_116__ varType_117__ tc_tv_details_118__ =>
        TcTyVar varName_115__ realUnique_116__ (update (tyVarKind tv))
                tc_tv_details_118__
      | Mk_Id varName_119__ realUnique_120__ varType_121__ idScope_122__
              id_details_123__ id_info_124__ => Mk_Id varName_119__ realUnique_120__ (update
                                                      (tyVarKind tv)) idScope_122__ id_details_123__ id_info_124__
    end.

Definition updateTyVarKindM {m} `{(GHC.Base.Monad m)} : (unit -> m
                                                        unit) -> TyVar -> m TyVar :=
  fun update tv =>
    update (tyVarKind tv) GHC.Base.>>= (fun k' =>
      GHC.Base.return_ GHC.Base.$ (match tv with
        | Mk_TyVar varName_130__ realUnique_131__ varType_132__ => Mk_TyVar
                                                                   varName_130__ realUnique_131__ k'
        | TcTyVar varName_133__ realUnique_134__ varType_135__ tc_tv_details_136__ =>
          TcTyVar varName_133__ realUnique_134__ k' tc_tv_details_136__
        | Mk_Id varName_137__ realUnique_138__ varType_139__ idScope_140__
                id_details_141__ id_info_142__ => Mk_Id varName_137__ realUnique_138__ k'
                                                        idScope_140__ id_details_141__ id_info_142__
      end)).

Definition tyVarName : TyVar -> Name.Name :=
  varName.

Definition updateVarType : (unit -> unit) -> Id -> Id :=
  fun f id =>
    match id with
      | Mk_TyVar varName_166__ realUnique_167__ varType_168__ => Mk_TyVar
                                                                 varName_166__ realUnique_167__ (f (varType id))
      | TcTyVar varName_169__ realUnique_170__ varType_171__ tc_tv_details_172__ =>
        TcTyVar varName_169__ realUnique_170__ (f (varType id)) tc_tv_details_172__
      | Mk_Id varName_173__ realUnique_174__ varType_175__ idScope_176__
              id_details_177__ id_info_178__ => Mk_Id varName_173__ realUnique_174__ (f
                                                      (varType id)) idScope_176__ id_details_177__ id_info_178__
    end.

Definition updateVarTypeM {m} `{GHC.Base.Monad m} : (unit -> m unit) -> Id -> m
                                                    Id :=
  fun f id =>
    f (varType id) GHC.Base.>>= (fun ty' =>
      GHC.Base.return_ (match id with
                         | Mk_TyVar varName_148__ realUnique_149__ varType_150__ => Mk_TyVar
                                                                                    varName_148__ realUnique_149__ ty'
                         | TcTyVar varName_151__ realUnique_152__ varType_153__ tc_tv_details_154__ =>
                           TcTyVar varName_151__ realUnique_152__ ty' tc_tv_details_154__
                         | Mk_Id varName_155__ realUnique_156__ varType_157__ idScope_158__
                                 id_details_159__ id_info_160__ => Mk_Id varName_155__ realUnique_156__ ty'
                                                                         idScope_158__ id_details_159__ id_info_160__
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
     andb bool comparison error false negb true unit GHC.Base.Eq_ GHC.Base.Monad
     GHC.Base.Ord GHC.Base.op_zd__ GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__
     GHC.Base.return_ GHC.Num.Int Name.Name Name.setNameUnique Panic.assertPanic
     Panic.noString Panic.panicStr Unique.Unique Unique.getKey Unique.getUnique
     Unique.mkUniqueGrimily Unique.nonDetCmpUnique Util.debugIsOn
*)
