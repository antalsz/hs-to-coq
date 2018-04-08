(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require Class.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Foldable.
Require Data.Set.Internal.
Require Data.Traversable.
Require Data.Tuple.
Require FastString.
Require FieldLabel.
(* Require ForeignCall. *)
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require ListSetOps.
Require Name.
Require OccName.
Require Panic.
Require PrelNames.
(* Require TysWiredIn. *)
Require UniqSet.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive StrictnessMark : Type
  := MarkedStrict : StrictnessMark
  |  NotMarkedStrict : StrictnessMark.

Inductive SrcUnpackedness : Type
  := SrcUnpack : SrcUnpackedness
  |  SrcNoUnpack : SrcUnpackedness
  |  NoSrcUnpack : SrcUnpackedness.

Inductive SrcStrictness : Type
  := SrcLazy : SrcStrictness
  |  SrcStrict : SrcStrictness
  |  NoSrcStrict : SrcStrictness.

Inductive HsSrcBang : Type
  := Mk_HsSrcBang
   : BasicTypes.SourceText -> SrcUnpackedness -> SrcStrictness -> HsSrcBang.

Inductive HsImplBang : Type
  := HsLazy : HsImplBang
  |  HsStrict : HsImplBang
  |  HsUnpack : (option unit) -> HsImplBang.

Inductive EqSpec : Type := Mk_EqSpec : Var.TyVar -> unit -> EqSpec.

Inductive DataConRep : Type
  := NoDataConRep : DataConRep
  |  DCR
   : Var.Id ->
     unit -> list unit -> list StrictnessMark -> list HsImplBang -> DataConRep.

Inductive DataCon : Type
  := MkData
   : Name.Name ->
     Unique.Unique ->
     BasicTypes.ConTag ->
     bool ->
     list Var.TyVar ->
     list Var.TyVar ->
     list Var.TyVarBinder ->
     list EqSpec ->
     unit ->
     unit ->
     list unit ->
     unit ->
     list HsSrcBang ->
     list FieldLabel.FieldLabel ->
     Var.Id ->
     DataConRep ->
     BasicTypes.Arity -> BasicTypes.Arity -> unit -> unit -> bool -> unit -> DataCon.

Instance Default__StrictnessMark : GHC.Err.Default StrictnessMark :=
  GHC.Err.Build_Default _ MarkedStrict.

Instance Default__SrcUnpackedness : GHC.Err.Default SrcUnpackedness :=
  GHC.Err.Build_Default _ SrcUnpack.

Instance Default__SrcStrictness : GHC.Err.Default SrcStrictness :=
  GHC.Err.Build_Default _ SrcLazy.

Instance Default__HsImplBang : GHC.Err.Default HsImplBang :=
  GHC.Err.Build_Default _ HsLazy.

Instance Default__DataConRep : GHC.Err.Default DataConRep :=
  GHC.Err.Build_Default _ NoDataConRep.

Definition dcr_arg_tys (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_arg_tys' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ dcr_arg_tys _ _ => dcr_arg_tys
  end.

Definition dcr_bangs (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_bangs' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ _ _ dcr_bangs => dcr_bangs
  end.

Definition dcr_boxer (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_boxer' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ dcr_boxer _ _ _ => dcr_boxer
  end.

Definition dcr_stricts (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_stricts' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ _ dcr_stricts _ => dcr_stricts
  end.

Definition dcr_wrap_id (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_wrap_id' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR dcr_wrap_id _ _ _ _ => dcr_wrap_id
  end.

Definition dcEqSpec (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ dcEqSpec _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcEqSpec.

Definition dcExTyVars (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ dcExTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcExTyVars.

Definition dcFields (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ dcFields _ _ _ _ _ _ _ _ := arg_0__ in
  dcFields.

Definition dcInfix (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcInfix _ := arg_0__ in
  dcInfix.

Definition dcName (arg_0__ : DataCon) :=
  let 'MkData dcName _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcName.

Definition dcOrigArgTys (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ dcOrigArgTys _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcOrigArgTys.

Definition dcOrigResTy (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ dcOrigResTy _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcOrigResTy.

Definition dcOtherTheta (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ dcOtherTheta _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcOtherTheta.

Definition dcPromoted (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcPromoted := arg_0__ in
  dcPromoted.

Definition dcRep (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRep _ _ _ _ _ _ := arg_0__ in
  dcRep.

Definition dcRepArity (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepArity _ _ _ _ _ := arg_0__ in
  dcRepArity.

Definition dcRepTyCon (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepTyCon _ _ _ := arg_0__ in
  dcRepTyCon.

Definition dcRepType (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepType _ _ := arg_0__ in
  dcRepType.

Definition dcSourceArity (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcSourceArity _ _ _ _ :=
    arg_0__ in
  dcSourceArity.

Definition dcSrcBangs (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ dcSrcBangs _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcSrcBangs.

Definition dcStupidTheta (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ dcStupidTheta _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcStupidTheta.

Definition dcTag (arg_0__ : DataCon) :=
  let 'MkData _ _ dcTag _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcTag.

Definition dcUnique (arg_0__ : DataCon) :=
  let 'MkData _ dcUnique _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcUnique.

Definition dcUnivTyVars (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ dcUnivTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcUnivTyVars.

Definition dcUserTyVarBinders (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ dcUserTyVarBinders _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcUserTyVarBinders.

Definition dcVanilla (arg_0__ : DataCon) :=
  let 'MkData _ _ _ dcVanilla _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcVanilla.

Definition dcWorkId (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcWorkId _ _ _ _ _ _ _ := arg_0__ in
  dcWorkId.
(* Midamble *)

Import FieldLabel.

Require GHC.Err.
Instance Default__DataCon : GHC.Err.Default DataCon := {}.
Admitted.

Instance Uniqable_DataCon : Unique.Uniquable DataCon := {}.
Admitted.

(* Parameter dataConRepArgTys : DataCon -> list unit. *)

(* Converted value declarations: *)

Local Definition Eq___DataCon_op_zeze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

Local Definition Eq___DataCon_op_zsze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

Program Instance Eq___DataCon : GHC.Base.Eq_ DataCon :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___DataCon_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___DataCon_op_zsze__ |}.

(* Translating `instance Uniquable__DataCon' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance NamedThing__DataCon' failed: OOPS! Cannot find
   information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Outputable__DataCon' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance OutputableBndr__DataCon' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "OutputableBndr" unsupported *)

(* Translating `instance Data__DataCon' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Outputable__EqSpec' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__StrictnessMark' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__HsSrcBang' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__SrcUnpackedness' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__SrcUnpackedness' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__SrcStrictness' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__SrcStrictness' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__HsImplBang' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Data__HsSrcBang' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__SrcUnpackedness' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___SrcUnpackedness_op_zeze__
   : SrcUnpackedness -> SrcUnpackedness -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | SrcUnpack, SrcUnpack => true
    | SrcNoUnpack, SrcNoUnpack => true
    | NoSrcUnpack, NoSrcUnpack => true
    | _, _ => false
    end.

Local Definition Eq___SrcUnpackedness_op_zsze__
   : SrcUnpackedness -> SrcUnpackedness -> bool :=
  fun x y => negb (Eq___SrcUnpackedness_op_zeze__ x y).

Program Instance Eq___SrcUnpackedness : GHC.Base.Eq_ SrcUnpackedness :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___SrcUnpackedness_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___SrcUnpackedness_op_zsze__ |}.

(* Translating `instance Data__SrcStrictness' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___SrcStrictness_op_zeze__
   : SrcStrictness -> SrcStrictness -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | SrcLazy, SrcLazy => true
    | SrcStrict, SrcStrict => true
    | NoSrcStrict, NoSrcStrict => true
    | _, _ => false
    end.

Local Definition Eq___SrcStrictness_op_zsze__
   : SrcStrictness -> SrcStrictness -> bool :=
  fun x y => negb (Eq___SrcStrictness_op_zeze__ x y).

Program Instance Eq___SrcStrictness : GHC.Base.Eq_ SrcStrictness :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___SrcStrictness_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___SrcStrictness_op_zsze__ |}.

(* Translating `instance Data__HsImplBang' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(*
Definition buildAlgTyCon
   : Name.Name ->
     list Var.TyVar ->
     list CoAxiom.Role ->
     option unit ->
     unit -> TyCon.AlgTyConRhs -> bool -> unut -> unit := tt.
  fun tc_name ktvs roles cType stupid_theta rhs gadt_syn parent => tt.
    let binders := Type.mkTyConBindersPreferAnon ktvs TysWiredIn.liftedTypeKind in
    TyCon.mkAlgTyCon tc_name binders TysWiredIn.liftedTypeKind roles cType
    stupid_theta rhs parent gadt_syn. 

Definition buildSynTyCon
   : Name.Name ->
     list TyCon.TyConBinder -> unit -> list CoAxiom.Role -> unit -> unit :=
  fun name binders res_kind roles rhs =>
    let is_fam_free := Type.isFamFreeTy rhs in
    let is_tau := Type.isTauTy rhs in
    TyCon.mkSynonymTyCon name binders res_kind roles rhs is_tau is_fam_free.
*)

Definition classDataCon : Class.Class -> DataCon :=
  fun clas =>
    match TyCon.tyConDataCons (Class.classTyCon clas) with
    | cons dict_constr no_more =>
        if andb Util.debugIsOn (negb (Data.Foldable.null no_more)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/basicTypes/DataCon.hs") #1346)
        else dict_constr
    | nil => Panic.panic (GHC.Base.hs_string__ "classDataCon")
    end.

Definition dataConBoxer : DataCon -> option unit :=
  fun arg_0__ =>
    match arg_0__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (DCR _ boxer _ _ _) _ _ _ _ _ _ =>
        Some boxer
    | _ => None
    end.

Definition dataConExTyVars : DataCon -> list Var.TyVar :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ tvbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
    tvbs.

Definition dataConFieldLabels : DataCon -> list FieldLabel.FieldLabel :=
  dcFields.

Definition dataConFieldType_maybe
   : DataCon ->
     FieldLabel.FieldLabelString -> option (FieldLabel.FieldLabel * unit)%type :=
  fun con label =>
    Data.Foldable.find ((fun arg_0__ => arg_0__ GHC.Base.== label) GHC.Base.∘
                        (FieldLabel.flLabel GHC.Base.∘ Data.Tuple.fst)) (GHC.List.zip (dcFields con)
                                                                                      (dcOrigArgTys con)).

Definition dataConFieldType : DataCon -> FieldLabel.FieldLabelString -> unit :=
  fun con label =>
    match dataConFieldType_maybe con label with
    | Some (pair _ ty) => ty
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "dataConFieldType") (GHC.Base.mappend
                                                                  (Panic.noString con) (Panic.noString label))
    end.

Definition dataConFullSig
   : DataCon ->
     (list Var.TyVar * list Var.TyVar * list EqSpec * unit * list unit *
      unit)%type :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ univ_tvs ex_tvs _ eq_spec theta _ arg_tys res_ty _ _ _ _ _ _
       _ _ _ _ := arg_0__ in
    pair (pair (pair (pair (pair univ_tvs ex_tvs) eq_spec) theta) arg_tys) res_ty.

Definition dataConImplBangs : DataCon -> list HsImplBang :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep => GHC.List.replicate (dcSourceArity dc) HsLazy
    | DCR _ _ _ _ bangs => bangs
    end.

Definition dataConImplicitTyThings : DataCon -> list unit :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ work rep _ _ _ _ _ _ := arg_0__ in
    let wrap_ids :=
      match rep with
      | NoDataConRep => nil
      | DCR wrap _ _ _ _ => cons (TyCoRep.AnId wrap) nil
      end in
    Coq.Init.Datatypes.app (cons (TyCoRep.AnId work) nil) wrap_ids.

Definition dataConInstOrigArgTys : DataCon -> list unit -> list unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (MkData _ _ _ _ univ_tvs ex_tvs _ _ _ _ arg_tys _ _ _ _ _ _ _ _ _ _ _ as dc)
    , inst_tys =>
        let tyvars := Coq.Init.Datatypes.app univ_tvs ex_tvs in
        if andb Util.debugIsOn (negb (Util.equalLength tyvars inst_tys)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/basicTypes/DataCon.hs") #1274 ((GHC.Base.mappend (id
                                                                                                         (GHC.Base.hs_string__
                                                                                                          "dataConInstOrigArgTys"))
                                                                                                        (Panic.noString
                                                                                                         dc)
                                                                                       Outputable.$$
                                                                                       Panic.noString tyvars)
                                                                                      Outputable.$$
                                                                                      Panic.noString inst_tys))
        else GHC.Base.map (TyCoRep.substTyWith tyvars inst_tys) arg_tys
    end.

Definition dataConIsInfix : DataCon -> bool :=
  dcInfix.

Definition dataConName : DataCon -> Name.Name :=
  dcName.

Definition dataConOrigArgTys : DataCon -> list unit :=
  fun dc => dcOrigArgTys dc.

Definition dataConOrigResTy : DataCon -> unit :=
  fun dc => dcOrigResTy dc.

Definition dataConOrigTyCon : DataCon -> unit :=
  fun dc =>
    match TyCon.tyConFamInst_maybe (dcRepTyCon dc) with
    | Some (pair tc _) => tc
    | _ => dcRepTyCon dc
    end.

Definition dataConRepArgTys : DataCon -> list unit :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ eq_spec theta _ orig_arg_tys _ _ _ _ rep _ _ _ _ _
       _ := arg_0__ in
    match rep with
    | NoDataConRep =>
        if andb Util.debugIsOn (negb (Data.Foldable.null eq_spec)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/basicTypes/DataCon.hs") #1293)
        else Coq.Init.Datatypes.app theta orig_arg_tys
    | DCR _ _ arg_tys _ _ => arg_tys
    end.

Definition dataConRepStrictness : DataCon -> list StrictnessMark :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep =>
        Coq.Lists.List.flat_map (fun _ => cons NotMarkedStrict nil) (dataConRepArgTys
                                 dc)
    | DCR _ _ _ strs _ => strs
    end.

Definition dataConInstArgTys : DataCon -> list unit -> list unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (MkData _ _ _ _ univ_tvs ex_tvs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ as dc)
    , inst_tys =>
        if andb Util.debugIsOn (negb (Util.equalLength univ_tvs inst_tys)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/basicTypes/DataCon.hs") #1257 ((GHC.Base.mappend (id
                                                                                                         (GHC.Base.hs_string__
                                                                                                          "dataConInstArgTys"))
                                                                                                        (Panic.noString
                                                                                                         dc)
                                                                                       Outputable.$$
                                                                                       Panic.noString univ_tvs)
                                                                                      Outputable.$$
                                                                                      Panic.noString inst_tys))
        else if andb Util.debugIsOn (negb (Data.Foldable.null ex_tvs)) : bool
             then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                              "ghc/compiler/basicTypes/DataCon.hs") #1258 (Panic.noString dc))
             else GHC.Base.map (TyCoRep.substTyWith univ_tvs inst_tys) (dataConRepArgTys dc)
    end.

Definition splitDataProductType_maybe
   : unit -> option (unit * list unit * DataCon * list unit)%type :=
  fun ty =>
    match Type.splitTyConApp_maybe ty with
    | Some (pair tycon ty_args) =>
        match TyCon.isDataProductTyCon_maybe tycon with
        | Some con =>
            Some (pair (pair (pair tycon ty_args) con) (dataConInstArgTys con ty_args))
        | _ => None
        end
    | _ => None
    end.

Definition dataConRepArity : DataCon -> BasicTypes.Arity :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arity _ _ _ _ _ := arg_0__ in
    arity.

Definition isNullaryRepDataCon : DataCon -> bool :=
  fun dc => dataConRepArity dc GHC.Base.== #0.

Definition dataConRepType : DataCon -> unit :=
  dcRepType.

Definition dataConSourceArity : DataCon -> BasicTypes.Arity :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arity _ _ _ _ := arg_0__ in
    arity.

Definition isNullarySrcDataCon : DataCon -> bool :=
  fun dc => dataConSourceArity dc GHC.Base.== #0.

Definition dataConSrcBangs : DataCon -> list HsSrcBang :=
  dcSrcBangs.

Definition dataConStupidTheta : DataCon -> unit :=
  fun dc => dcStupidTheta dc.

Definition dataConTag : DataCon -> BasicTypes.ConTag :=
  dcTag.

Definition dataConTagZ : DataCon -> BasicTypes.ConTagZ :=
  fun con => dataConTag con GHC.Num.- BasicTypes.fIRST_TAG.

Definition dataConTyCon : DataCon -> unit :=
  dcRepTyCon.

Definition specialPromotedDc : DataCon -> bool :=
  TyCon.isKindTyCon GHC.Base.∘ dataConTyCon.

Definition dataConUnivAndExTyVars : DataCon -> list Var.TyVar :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ univ_tvs ex_tvs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
      arg_0__ in
    Coq.Init.Datatypes.app univ_tvs ex_tvs.

Definition dataConUnivTyVars : DataCon -> list Var.TyVar :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ tvbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
    tvbs.

Definition dataConUserTyVarBinders : DataCon -> list Var.TyVarBinder :=
  dcUserTyVarBinders.

Definition dataConUserTyVars : DataCon -> list Var.TyVar :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ tvbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
    Var.binderVars tvbs.

Definition dataConUserType : DataCon -> unit :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ user_tvbs _ theta _ arg_tys res_ty _ _ _ _ _ _ _ _ _
       _ := arg_0__ in
    TyCoRep.mkForAllTys user_tvbs (TyCoRep.mkFunTys theta (TyCoRep.mkFunTys arg_tys
                                                                            res_ty)).

Definition dataConWorkId : DataCon -> Var.Id :=
  fun dc => dcWorkId dc.

Definition dataConWrapId : DataCon -> Var.Id :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep => dcWorkId dc
    | DCR wrap_id _ _ _ _ => wrap_id
    end.

Definition dataConWrapId_maybe : DataCon -> option Var.Id :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep => None
    | DCR wrap_id _ _ _ _ => Some wrap_id
    end.

Definition eqHsBang : HsImplBang -> HsImplBang -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | HsLazy, HsLazy => true
    | HsStrict, HsStrict => true
    | HsUnpack None, HsUnpack None => true
    | HsUnpack (Some c1), HsUnpack (Some c2) =>
        Type.eqType (Coercion.coercionType c1) (Coercion.coercionType c2)
    | _, _ => false
    end.

Definition eqSpecPair : EqSpec -> (Var.TyVar * unit)%type :=
  fun arg_0__ => let 'Mk_EqSpec tv ty := arg_0__ in pair tv ty.

Definition eqSpecPreds : list EqSpec -> unit :=
  fun spec =>
    let cont_0__ arg_1__ :=
      let 'Mk_EqSpec tv ty := arg_1__ in
      cons (Type.mkPrimEqPred (TyCoRep.mkTyVarTy tv) ty) nil in
    Coq.Lists.List.flat_map cont_0__ spec.

Definition dataConTheta : DataCon -> unit :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ eq_spec theta _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
    Coq.Init.Datatypes.app (eqSpecPreds eq_spec) theta.

Definition dataConSig
   : DataCon -> (list Var.TyVar * unit * list unit * unit)%type :=
  fun arg_0__ =>
    let '(MkData _ _ _ _ _ _ _ _ _ _ arg_tys res_ty _ _ _ _ _ _ _ _ _ _ as con) :=
      arg_0__ in
    pair (pair (pair (dataConUnivAndExTyVars con) (dataConTheta con)) arg_tys)
         res_ty.

Definition dataConInstSig
   : DataCon -> list unit -> (list Var.TyVar * unit * list unit)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkData _ _ _ _ univ_tvs ex_tvs _ eq_spec theta _ arg_tys _ _ _ _ _ _ _ _ _ _ _
    , univ_tys =>
        let univ_subst := TyCoRep.zipTvSubst univ_tvs univ_tys in
        let 'pair subst ex_tvs' := Data.Traversable.mapAccumL TyCoRep.substTyVarBndr
                                     univ_subst ex_tvs in
        pair (pair ex_tvs' (TyCoRep.substTheta subst (Coq.Init.Datatypes.app
                                                      (eqSpecPreds eq_spec) theta))) (TyCoRep.substTys subst arg_tys)
    end.

Definition dataConCannotMatch : list unit -> DataCon -> bool :=
  fun tys con =>
    let predEqs :=
      fun pred =>
        match Type.classifyPredType pred with
        | Type.EqPred Type.NomEq ty1 ty2 => cons (pair ty1 ty2) nil
        | Type.ClassPred eq (cons _ (cons ty1 (cons ty2 nil))) =>
            if Unique.hasKey eq PrelNames.eqTyConKey : bool
            then cons (pair ty1 ty2) nil else
            nil
        end in
    let 'pair (pair _ inst_theta) _ := dataConInstSig con tys in
    if Data.Foldable.null inst_theta : bool then false else
    if Data.Foldable.all Type.isTyVarTy tys : bool then false else
    Unify.typesCantMatch (Data.Foldable.concatMap predEqs inst_theta).

Definition eqSpecTyVar : EqSpec -> Var.TyVar :=
  fun arg_0__ => let 'Mk_EqSpec tv _ := arg_0__ in tv.

Definition filterEqSpec : list EqSpec -> list Var.TyVar -> list Var.TyVar :=
  fun eq_spec =>
    let not_in_eq_spec :=
      fun var =>
        Data.Foldable.all (negb GHC.Base.∘
                           ((fun arg_0__ => arg_0__ GHC.Base.== var) GHC.Base.∘ eqSpecTyVar)) eq_spec in
    GHC.List.filter not_in_eq_spec.

Definition dataConUserTyVarsArePermuted : DataCon -> bool :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ univ_tvs ex_tvs user_tvbs eq_spec _ _ _ _ _ _ _ _ _ _ _ _ _
       _ := arg_0__ in
    (Coq.Init.Datatypes.app (filterEqSpec eq_spec univ_tvs) ex_tvs) GHC.Base./=
    Var.binderVars user_tvbs.

Definition eqSpecType : EqSpec -> unit :=
  fun arg_0__ => let 'Mk_EqSpec _ ty := arg_0__ in ty.

Definition freshNames : list Name.Name -> list Name.Name :=
  fun avoids =>
    let avoid_occs : OccName.OccSet :=
      OccName.mkOccSet (GHC.Base.map Name.getOccName avoids) in
    let avoid_uniqs : UniqSet.UniqSet Unique.Unique :=
      UniqSet.mkUniqSet (GHC.Base.map Unique.getUnique avoids) in
    Coq.Lists.List.flat_map (fun n =>
                               let occ :=
                                 OccName.mkTyVarOccFS (FastString.mkFastString (cons (GHC.Char.hs_char__ "x")
                                                                                     (GHC.Show.show n))) in
                               let uniq := Unique.mkAlphaTyVarUnique n in
                               if negb (UniqSet.elementOfUniqSet uniq avoid_uniqs) : bool
                               then if negb (OccName.elemOccSet occ avoid_occs) : bool
                                    then cons (Name.mkSystemName uniq occ) nil else
                                    nil else
                               nil) (enumFrom #0).

Definition mkCleanAnonTyConBinders
   : list TyCon.TyConBinder -> list unit -> list TyCon.TyConBinder :=
  fun tc_bndrs tys =>
    let fresh_names :=
      freshNames (GHC.Base.map Name.getName (Var.binderVars tc_bndrs)) in
    let cont_1__ arg_2__ :=
      let 'pair name ty := arg_2__ in
      cons (TyCon.mkAnonTyConBinder (Var.mkTyVar name ty)) nil in
    Coq.Lists.List.flat_map cont_1__ (GHC.List.zip fresh_names tys).

Definition mkDataCon
   : Name.Name ->
     bool ->
     TyCon.TyConRepName ->
     list HsSrcBang ->
     list FieldLabel.FieldLabel ->
     list Var.TyVar ->
     list Var.TyVar ->
     list Var.TyVarBinder ->
     list EqSpec ->
     unit ->
     list unit ->
     unit ->
     TyCon.RuntimeRepInfo -> unit -> unit -> Var.Id -> DataConRep -> DataCon :=
  fun name
  declared_infix
  prom_info
  arg_stricts
  fields
  univ_tvs
  ex_tvs
  user_tvbs
  eq_spec
  theta
  orig_arg_tys
  orig_res_ty
  rep_info
  rep_tycon
  stupid_theta
  work_id
  rep =>
    let roles :=
      Coq.Init.Datatypes.app (GHC.Base.map (GHC.Base.const CoAxiom.Nominal)
                              (Coq.Init.Datatypes.app univ_tvs ex_tvs)) (GHC.Base.map (GHC.Base.const
                                                                                       CoAxiom.Representational)
                              orig_arg_tys) in
    let prom_res_kind := orig_res_ty in
    let user_tvbs_invariant :=
      Data.Set.Internal.fromList (Coq.Init.Datatypes.app (filterEqSpec eq_spec
                                                          univ_tvs) ex_tvs) GHC.Base.==
      Data.Set.Internal.fromList (Var.binderVars user_tvbs) in
    let user_tvbs' :=
      if andb Util.debugIsOn (negb (user_tvbs_invariant)) : bool
      then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                       "ghc/compiler/basicTypes/DataCon.hs") #897 ((Panic.noString univ_tvs
                                                                                    Outputable.$$
                                                                                    Panic.noString ex_tvs) Outputable.$$
                                                                                   Panic.noString user_tvbs))
      else user_tvbs in
    let prom_tv_bndrs :=
      let cont_3__ arg_4__ :=
        match arg_4__ with
        | Var.TvBndr tv vis => cons (TyCon.mkNamedTyConBinder vis tv) nil
        | _ => nil
        end in
      Coq.Lists.List.flat_map cont_3__ user_tvbs' in
    let prom_arg_bndrs :=
      mkCleanAnonTyConBinders prom_tv_bndrs (Coq.Init.Datatypes.app theta
                                                                    orig_arg_tys) in
    let is_vanilla :=
      andb (Data.Foldable.null ex_tvs) (andb (Data.Foldable.null eq_spec)
                                             (Data.Foldable.null theta)) in
    let con :=
      MkData name (Name.nameUnique name) tag is_vanilla univ_tvs ex_tvs user_tvbs'
             eq_spec theta stupid_theta orig_arg_tys orig_res_ty arg_stricts fields work_id
             rep (Data.Foldable.length rep_arg_tys) (Data.Foldable.length orig_arg_tys)
             rep_tycon rep_ty declared_infix promoted in
    let tag :=
      ListSetOps.assoc (GHC.Base.hs_string__ "mkDataCon") (GHC.List.zip
                                                           (TyCon.tyConDataCons rep_tycon) (enumFrom
                                                            BasicTypes.fIRST_TAG)) con in
    let rep_arg_tys := dataConRepArgTys con in
    let rep_ty :=
      match rep with
      | NoDataConRep => dataConUserType con
      | DCR _ _ _ _ _ =>
          Type.mkInvForAllTys univ_tvs (Type.mkInvForAllTys ex_tvs (TyCoRep.mkFunTys
                                                             rep_arg_tys (Type.mkTyConApp rep_tycon (TyCoRep.mkTyVarTys
                                                                                           univ_tvs))))
      end in
    let promoted :=
      TyCon.mkPromotedDataCon con name prom_info (Coq.Init.Datatypes.app prom_tv_bndrs
                                                                         prom_arg_bndrs) prom_res_kind roles rep_info in
    con.

Definition isBanged : HsImplBang -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | HsUnpack _ => true
    | HsStrict => true
    | HsLazy => false
    end.

Definition isLegacyPromotableTyCon : unit -> bool :=
  fun tc =>
    orb (TyCon.isVanillaAlgTyCon tc) (orb (TyCon.isFunTyCon tc) (TyCon.isKindTyCon
                                           tc)).

Definition isMarkedStrict : StrictnessMark -> bool :=
  fun arg_0__ => match arg_0__ with | NotMarkedStrict => false | _ => true end.

Definition isSrcStrict : SrcStrictness -> bool :=
  fun arg_0__ => match arg_0__ with | SrcStrict => true | _ => false end.

Definition isSrcUnpacked : SrcUnpackedness -> bool :=
  fun arg_0__ => match arg_0__ with | SrcUnpack => true | _ => false end.

Definition isTupleDataCon : DataCon -> bool :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _ := arg_0__ in
    TyCon.isTupleTyCon tc.

Definition isUnboxedSumCon : DataCon -> bool :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _ := arg_0__ in
    TyCon.isUnboxedSumTyCon tc.

Definition isUnboxedTupleCon : DataCon -> bool :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _ := arg_0__ in
    TyCon.isUnboxedTupleTyCon tc.

Definition isVanillaDataCon : DataCon -> bool :=
  fun dc => dcVanilla dc.

Definition mkEqSpec : Var.TyVar -> unit -> EqSpec :=
  fun tv ty => Mk_EqSpec tv ty.

Definition dataConEqSpec : DataCon -> list EqSpec :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ eq_spec theta _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
    Coq.Init.Datatypes.app eq_spec (Coq.Init.Datatypes.app (let cont_1__ arg_2__ :=
                                                              match arg_2__ with
                                                              | Some (pair tc (cons _k1 (cons _k2 (cons ty1 (cons ty2
                                                                   nil))))) =>
                                                                  if Unique.hasKey tc PrelNames.heqTyConKey : bool
                                                                  then Coq.Lists.List.flat_map (fun spec =>
                                                                                                  cons spec nil)
                                                                                               (match pair
                                                                                                        (Type.getTyVar_maybe
                                                                                                         ty1)
                                                                                                        (Type.getTyVar_maybe
                                                                                                         ty2) with
                                                                                                | pair (Some tv1) _ =>
                                                                                                    cons (mkEqSpec tv1
                                                                                                          ty2) nil
                                                                                                | pair _ (Some tv2) =>
                                                                                                    cons (mkEqSpec tv2
                                                                                                          ty1) nil
                                                                                                | _ => nil
                                                                                                end) else
                                                                  nil
                                                              | _ => nil
                                                              end in
                                                            Coq.Lists.List.flat_map cont_1__ (GHC.Base.map
                                                                                     Type.splitTyConApp_maybe theta))
                                                           (let cont_7__ arg_8__ :=
                                                              match arg_8__ with
                                                              | Some (pair tc (cons _k (cons ty1 (cons ty2 nil)))) =>
                                                                  if Unique.hasKey tc PrelNames.eqTyConKey : bool
                                                                  then Coq.Lists.List.flat_map (fun spec =>
                                                                                                  cons spec nil)
                                                                                               (match pair
                                                                                                        (Type.getTyVar_maybe
                                                                                                         ty1)
                                                                                                        (Type.getTyVar_maybe
                                                                                                         ty2) with
                                                                                                | pair (Some tv1) _ =>
                                                                                                    cons (mkEqSpec tv1
                                                                                                          ty2) nil
                                                                                                | pair _ (Some tv2) =>
                                                                                                    cons (mkEqSpec tv2
                                                                                                          ty1) nil
                                                                                                | _ => nil
                                                                                                end) else
                                                                  nil
                                                              | _ => nil
                                                              end in
                                                            Coq.Lists.List.flat_map cont_7__ (GHC.Base.map
                                                                                     Type.splitTyConApp_maybe theta))).

Definition isLegacyPromotableDataCon : DataCon -> bool :=
  fun dc =>
    andb (Data.Foldable.null (dataConEqSpec dc)) (andb (Data.Foldable.null
                                                        (dataConTheta dc)) (andb (negb (TyCon.isFamInstTyCon
                                                                                        (dataConTyCon dc)))
                                                                                 (UniqSet.uniqSetAll
                                                                                  isLegacyPromotableTyCon
                                                                                  (Type.tyConsOfType (dataConUserType
                                                                                                      dc))))).

Definition promoteDataCon : DataCon -> unit :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc := arg_0__ in
    tc.

Definition substEqSpec : TyCoRep.TCvSubst -> EqSpec -> EqSpec :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | subst, Mk_EqSpec tv ty =>
        let tv' :=
          Type.getTyVar (GHC.Base.hs_string__ "substEqSpec") (TyCoRep.substTyVar subst
                                                              tv) in
        Mk_EqSpec tv' (TyCoRep.substTy subst ty)
    end.

(* External variables:
     None Some andb bool cons enumFrom false id list negb nil op_zt__ option orb pair
     promoted rep_arg_tys rep_ty tag true unit BasicTypes.Arity BasicTypes.ConTag
     BasicTypes.ConTagZ BasicTypes.SourceText BasicTypes.fIRST_TAG Class.Class
     Class.classTyCon CoAxiom.Nominal CoAxiom.Representational CoAxiom.Role
     Coercion.coercionType Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     Data.Foldable.all Data.Foldable.concatMap Data.Foldable.find
     Data.Foldable.length Data.Foldable.null Data.Set.Internal.fromList
     Data.Traversable.mapAccumL Data.Tuple.fst FastString.mkFastString
     FieldLabel.FieldLabel FieldLabel.FieldLabelString FieldLabel.flLabel
     ForeignCall.CType GHC.Base.Eq_ GHC.Base.const GHC.Base.map GHC.Base.mappend
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zsze__ GHC.Err.Build_Default
     GHC.Err.Default GHC.Err.error GHC.List.filter GHC.List.replicate GHC.List.zip
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Show.show ListSetOps.assoc Name.Name
     Name.getName Name.getOccName Name.mkSystemName Name.nameUnique OccName.OccSet
     OccName.elemOccSet OccName.mkOccSet OccName.mkTyVarOccFS
     Outputable.assertPprPanic Outputable.op_zdzd__ Panic.assertPanic Panic.noString
     Panic.panic Panic.panicStr PrelNames.eqTyConKey PrelNames.heqTyConKey
     TyCoRep.AnId TyCoRep.TCvSubst TyCoRep.mkForAllTys TyCoRep.mkFunTys
     TyCoRep.mkTyVarTy TyCoRep.mkTyVarTys TyCoRep.substTheta TyCoRep.substTy
     TyCoRep.substTyVar TyCoRep.substTyVarBndr TyCoRep.substTyWith TyCoRep.substTys
     TyCoRep.zipTvSubst TyCon.AlgTyConFlav TyCon.AlgTyConRhs TyCon.RuntimeRepInfo
     TyCon.TyConBinder TyCon.TyConRepName TyCon.isDataProductTyCon_maybe
     TyCon.isFamInstTyCon TyCon.isFunTyCon TyCon.isKindTyCon TyCon.isTupleTyCon
     TyCon.isUnboxedSumTyCon TyCon.isUnboxedTupleTyCon TyCon.isVanillaAlgTyCon
     TyCon.mkAlgTyCon TyCon.mkAnonTyConBinder TyCon.mkNamedTyConBinder
     TyCon.mkPromotedDataCon TyCon.mkSynonymTyCon TyCon.tyConDataCons
     TyCon.tyConFamInst_maybe Type.ClassPred Type.EqPred Type.NomEq
     Type.classifyPredType Type.eqType Type.getTyVar Type.getTyVar_maybe
     Type.isFamFreeTy Type.isTauTy Type.isTyVarTy Type.mkInvForAllTys
     Type.mkPrimEqPred Type.mkTyConApp Type.mkTyConBindersPreferAnon
     Type.splitTyConApp_maybe Type.tyConsOfType TysWiredIn.liftedTypeKind
     Unify.typesCantMatch UniqSet.UniqSet UniqSet.elementOfUniqSet UniqSet.mkUniqSet
     UniqSet.uniqSetAll Unique.Unique Unique.getUnique Unique.hasKey
     Unique.mkAlphaTyVarUnique Util.debugIsOn Util.equalLength Var.Id Var.TvBndr
     Var.TyVar Var.TyVarBinder Var.binderVars Var.mkTyVar
*)
