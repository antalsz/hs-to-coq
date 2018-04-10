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
Require Coq.Init.Datatypes.
Require Data.Foldable.
Require Data.Tuple.
Require FieldLabel.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Name.
Require OccName.
Require TyCon.
Require Unique.
Require Var.
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
     BasicTypes.Arity ->
     BasicTypes.Arity -> TyCon.TyCon -> unit -> bool -> TyCon.TyCon -> DataCon.

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

Local Definition Uniquable__DataCon_getUnique : DataCon -> Unique.Unique :=
  dcUnique.

Program Instance Uniquable__DataCon : Unique.Uniquable DataCon :=
  fun _ k => k {| Unique.getUnique__ := Uniquable__DataCon_getUnique |}.

Local Definition NamedThing__DataCon_getName : DataCon -> Name.Name :=
  dcName.

Local Definition NamedThing__DataCon_getOccName : DataCon -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__DataCon_getName n).

Program Instance NamedThing__DataCon : Name.NamedThing DataCon :=
  fun _ k =>
    k {| Name.getName__ := NamedThing__DataCon_getName ;
         Name.getOccName__ := NamedThing__DataCon_getOccName |}.

(* Skipping instance Outputable__DataCon of class Outputable *)

(* Skipping instance OutputableBndr__DataCon of class OutputableBndr *)

(* Skipping instance Data__DataCon of class Data *)

(* Skipping instance Outputable__EqSpec of class Outputable *)

(* Skipping instance Outputable__StrictnessMark of class Outputable *)

(* Skipping instance Outputable__HsSrcBang of class Outputable *)

(* Skipping instance Outputable__SrcUnpackedness of class Outputable *)

(* Skipping instance Binary__SrcUnpackedness of class Binary *)

(* Skipping instance Outputable__SrcStrictness of class Outputable *)

(* Skipping instance Binary__SrcStrictness of class Binary *)

(* Skipping instance Outputable__HsImplBang of class Outputable *)

(* Skipping instance Data__HsSrcBang of class Data *)

(* Skipping instance Data__SrcUnpackedness of class Data *)

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

(* Skipping instance Data__SrcStrictness of class Data *)

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

(* Skipping instance Data__HsImplBang of class Data *)

Definition dataConBoxer : DataCon -> option unit :=
  fun arg_0__ =>
    match arg_0__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (DCR _ boxer _ _ _) _ _ _ _ _ _ =>
        Some boxer
    | _ => None
    end.

Definition dataConFieldType_maybe
   : DataCon ->
     FieldLabel.FieldLabelString -> option (FieldLabel.FieldLabel * unit)%type :=
  fun con label =>
    Data.Foldable.find ((fun arg_0__ => arg_0__ GHC.Base.== label) GHC.Base.∘
                        (FieldLabel.flLabel GHC.Base.∘ Data.Tuple.fst)) (GHC.List.zip (dcFields con)
                                                                                      (dcOrigArgTys con)).

Definition dataConFullSig
   : DataCon ->
     (list Var.TyVar * list Var.TyVar * list EqSpec * unit * list unit *
      unit)%type :=
  fun '(MkData _ _ _ _ univ_tvs ex_tvs _ eq_spec theta _ arg_tys res_ty _ _ _ _ _
  _ _ _ _ _) =>
    pair (pair (pair (pair (pair univ_tvs ex_tvs) eq_spec) theta) arg_tys) res_ty.

Definition dataConImplBangs : DataCon -> list HsImplBang :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep => GHC.List.replicate (dcSourceArity dc) HsLazy
    | DCR _ _ _ _ bangs => bangs
    end.

Definition dataConIsInfix : DataCon -> bool :=
  dcInfix.

Definition dataConName : DataCon -> Name.Name :=
  dcName.

Definition dataConRepArity : DataCon -> BasicTypes.Arity :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arity _ _ _ _ _) => arity.

Definition isNullaryRepDataCon : DataCon -> bool :=
  fun dc => dataConRepArity dc GHC.Base.== #0.

Definition dataConRepType : DataCon -> unit :=
  dcRepType.

Definition dataConSourceArity : DataCon -> BasicTypes.Arity :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arity _ _ _ _) => arity.

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

Definition dataConTyCon : DataCon -> TyCon.TyCon :=
  dcRepTyCon.

Definition dataConUnivAndExTyVars : DataCon -> list Var.TyVar :=
  fun '(MkData _ _ _ _ univ_tvs ex_tvs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
    Coq.Init.Datatypes.app univ_tvs ex_tvs.

Definition dataConUnivTyVars : DataCon -> list Var.TyVar :=
  fun '(MkData _ _ _ _ tvbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => tvbs.

Definition dataConUserTyVarBinders : DataCon -> list Var.TyVarBinder :=
  dcUserTyVarBinders.

Definition dataConUserTyVars : DataCon -> list Var.TyVar :=
  fun '(MkData _ _ _ _ _ _ tvbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
    Var.binderVars tvbs.

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

Definition eqSpecPair : EqSpec -> (Var.TyVar * unit)%type :=
  fun '(Mk_EqSpec tv ty) => pair tv ty.

Definition eqSpecTyVar : EqSpec -> Var.TyVar :=
  fun '(Mk_EqSpec tv _) => tv.

Definition filterEqSpec : list EqSpec -> list Var.TyVar -> list Var.TyVar :=
  fun eq_spec =>
    let not_in_eq_spec :=
      fun var =>
        Data.Foldable.all (negb GHC.Base.∘
                           ((fun arg_0__ => arg_0__ GHC.Base.== var) GHC.Base.∘ eqSpecTyVar)) eq_spec in
    GHC.List.filter not_in_eq_spec.

Definition dataConUserTyVarsArePermuted : DataCon -> bool :=
  fun '(MkData _ _ _ _ univ_tvs ex_tvs user_tvbs eq_spec _ _ _ _ _ _ _ _ _ _ _ _ _
  _) =>
    (Coq.Init.Datatypes.app (filterEqSpec eq_spec univ_tvs) ex_tvs) GHC.Base./=
    Var.binderVars user_tvbs.

Definition eqSpecType : EqSpec -> unit :=
  fun '(Mk_EqSpec _ ty) => ty.

Definition isBanged : HsImplBang -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | HsUnpack _ => true
    | HsStrict => true
    | HsLazy => false
    end.

Definition isMarkedStrict : StrictnessMark -> bool :=
  fun arg_0__ => match arg_0__ with | NotMarkedStrict => false | _ => true end.

Definition isSrcStrict : SrcStrictness -> bool :=
  fun arg_0__ => match arg_0__ with | SrcStrict => true | _ => false end.

Definition isSrcUnpacked : SrcUnpackedness -> bool :=
  fun arg_0__ => match arg_0__ with | SrcUnpack => true | _ => false end.

Definition isTupleDataCon : DataCon -> bool :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _) =>
    TyCon.isTupleTyCon tc.

Definition isUnboxedSumCon : DataCon -> bool :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _) =>
    TyCon.isUnboxedSumTyCon tc.

Definition isUnboxedTupleCon : DataCon -> bool :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _) =>
    TyCon.isUnboxedTupleTyCon tc.

Definition isVanillaDataCon : DataCon -> bool :=
  fun dc => dcVanilla dc.

Definition mkEqSpec : Var.TyVar -> unit -> EqSpec :=
  fun tv ty => Mk_EqSpec tv ty.

Definition promoteDataCon : DataCon -> TyCon.TyCon :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc) => tc.

(* External variables:
     None Some bool false list negb op_zt__ option pair true unit BasicTypes.Arity
     BasicTypes.ConTag BasicTypes.ConTagZ BasicTypes.SourceText BasicTypes.fIRST_TAG
     Coq.Init.Datatypes.app Data.Foldable.all Data.Foldable.find Data.Tuple.fst
     FieldLabel.FieldLabel FieldLabel.FieldLabelString FieldLabel.flLabel
     GHC.Base.Eq_ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Err.Build_Default GHC.Err.Default
     GHC.Err.error GHC.List.filter GHC.List.replicate GHC.List.zip
     GHC.Num.fromInteger GHC.Num.op_zm__ Name.Name Name.NamedThing Name.getName__
     Name.getOccName__ Name.nameOccName OccName.OccName TyCon.TyCon
     TyCon.isTupleTyCon TyCon.isUnboxedSumTyCon TyCon.isUnboxedTupleTyCon
     Unique.Uniquable Unique.Unique Unique.getUnique Unique.getUnique__ Var.Id
     Var.TyVar Var.TyVarBinder Var.binderVars
*)
