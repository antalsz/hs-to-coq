(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

(* Temporary fix for partial record selectors *)
Parameter error : forall {a}, a.

(* Converted imports: *)

Require BasicTypes.
Require FieldLabel.
Require GHC.Base.
Require Name.
Require Unique.
Require Var.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive StrictnessMark : Type := MarkedStrict : StrictnessMark
                                |  NotMarkedStrict : StrictnessMark.

Inductive SrcUnpackedness : Type := SrcUnpack : SrcUnpackedness
                                 |  SrcNoUnpack : SrcUnpackedness
                                 |  NoSrcUnpack : SrcUnpackedness.

Inductive SrcStrictness : Type := SrcLazy : SrcStrictness
                               |  SrcStrict : SrcStrictness
                               |  NoSrcStrict : SrcStrictness.

Inductive HsSrcBang : Type := Mk_HsSrcBang : (option
                                             BasicTypes.SourceText) -> SrcUnpackedness -> SrcStrictness -> HsSrcBang.

Inductive HsImplBang : Type := HsLazy : HsImplBang
                            |  HsStrict : HsImplBang
                            |  HsUnpack : (option TyCoRep.Coercion) -> HsImplBang.

Inductive EqSpec : Type := Mk_EqSpec : Var.TyVar -> TyCoRep.Type_ -> EqSpec.

Inductive DataConRep : Type := NoDataConRep : DataConRep
                            |  DCR : Var.Id -> unit -> list TyCoRep.Type_ -> list StrictnessMark -> list
                                     HsImplBang -> DataConRep.

Inductive DataCon : Type := MkData
                           : Name.Name -> Unique.Unique -> BasicTypes.ConTag -> bool -> list
                             Var.TyVar -> list TyCoRep.TyBinder -> list Var.TyVar -> list
                             TyCoRep.TyBinder -> list
                             EqSpec -> TyCoRep.ThetaType -> TyCoRep.ThetaType -> list
                             TyCoRep.Type_ -> TyCoRep.Type_ -> list HsSrcBang -> list
                             FieldLabel.FieldLabel -> Var.Id -> DataConRep -> BasicTypes.Arity -> BasicTypes.Arity -> TyCon.TyCon -> TyCoRep.Type_ -> bool -> TyCon.TyCon -> DataCon.

Definition dcr_arg_tys (arg_0__ : DataConRep) :=
  match arg_0__ with
    | NoDataConRep => error (GHC.Base.hs_string__
                            "Partial record selector: field `dcr_arg_tys' has no match in constructor `NoDataConRep' of type `DataConRep'")
    | DCR _ _ dcr_arg_tys _ _ => dcr_arg_tys
  end.

Definition dcr_bangs (arg_1__ : DataConRep) :=
  match arg_1__ with
    | NoDataConRep => error (GHC.Base.hs_string__
                            "Partial record selector: field `dcr_bangs' has no match in constructor `NoDataConRep' of type `DataConRep'")
    | DCR _ _ _ _ dcr_bangs => dcr_bangs
  end.

Definition dcr_boxer (arg_2__ : DataConRep) :=
  match arg_2__ with
    | NoDataConRep => error (GHC.Base.hs_string__
                            "Partial record selector: field `dcr_boxer' has no match in constructor `NoDataConRep' of type `DataConRep'")
    | DCR _ dcr_boxer _ _ _ => dcr_boxer
  end.

Definition dcr_stricts (arg_3__ : DataConRep) :=
  match arg_3__ with
    | NoDataConRep => error (GHC.Base.hs_string__
                            "Partial record selector: field `dcr_stricts' has no match in constructor `NoDataConRep' of type `DataConRep'")
    | DCR _ _ _ dcr_stricts _ => dcr_stricts
  end.

Definition dcr_wrap_id (arg_4__ : DataConRep) :=
  match arg_4__ with
    | NoDataConRep => error (GHC.Base.hs_string__
                            "Partial record selector: field `dcr_wrap_id' has no match in constructor `NoDataConRep' of type `DataConRep'")
    | DCR dcr_wrap_id _ _ _ _ => dcr_wrap_id
  end.

Definition dcEqSpec (arg_5__ : DataCon) :=
  match arg_5__ with
    | MkData _ _ _ _ _ _ _ _ dcEqSpec _ _ _ _ _ _ _ _ _ _ _ _ _ _ => dcEqSpec
  end.

Definition dcExTyBinders (arg_6__ : DataCon) :=
  match arg_6__ with
    | MkData _ _ _ _ _ _ _ dcExTyBinders _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      dcExTyBinders
  end.

Definition dcExTyVars (arg_7__ : DataCon) :=
  match arg_7__ with
    | MkData _ _ _ _ _ _ dcExTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => dcExTyVars
  end.

Definition dcFields (arg_8__ : DataCon) :=
  match arg_8__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcFields _ _ _ _ _ _ _ _ => dcFields
  end.

Definition dcInfix (arg_9__ : DataCon) :=
  match arg_9__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcInfix _ => dcInfix
  end.

Definition dcName (arg_10__ : DataCon) :=
  match arg_10__ with
    | MkData dcName _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => dcName
  end.

Definition dcOrigArgTys (arg_11__ : DataCon) :=
  match arg_11__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ dcOrigArgTys _ _ _ _ _ _ _ _ _ _ _ =>
      dcOrigArgTys
  end.

Definition dcOrigResTy (arg_12__ : DataCon) :=
  match arg_12__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ dcOrigResTy _ _ _ _ _ _ _ _ _ _ => dcOrigResTy
  end.

Definition dcOtherTheta (arg_13__ : DataCon) :=
  match arg_13__ with
    | MkData _ _ _ _ _ _ _ _ _ dcOtherTheta _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      dcOtherTheta
  end.

Definition dcPromoted (arg_14__ : DataCon) :=
  match arg_14__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcPromoted => dcPromoted
  end.

Definition dcRep (arg_15__ : DataCon) :=
  match arg_15__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRep _ _ _ _ _ _ => dcRep
  end.

Definition dcRepArity (arg_16__ : DataCon) :=
  match arg_16__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepArity _ _ _ _ _ => dcRepArity
  end.

Definition dcRepTyCon (arg_17__ : DataCon) :=
  match arg_17__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepTyCon _ _ _ => dcRepTyCon
  end.

Definition dcRepType (arg_18__ : DataCon) :=
  match arg_18__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepType _ _ => dcRepType
  end.

Definition dcSourceArity (arg_19__ : DataCon) :=
  match arg_19__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcSourceArity _ _ _ _ =>
      dcSourceArity
  end.

Definition dcSrcBangs (arg_20__ : DataCon) :=
  match arg_20__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ dcSrcBangs _ _ _ _ _ _ _ _ _ => dcSrcBangs
  end.

Definition dcStupidTheta (arg_21__ : DataCon) :=
  match arg_21__ with
    | MkData _ _ _ _ _ _ _ _ _ _ dcStupidTheta _ _ _ _ _ _ _ _ _ _ _ _ =>
      dcStupidTheta
  end.

Definition dcTag (arg_22__ : DataCon) :=
  match arg_22__ with
    | MkData _ _ dcTag _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => dcTag
  end.

Definition dcUnique (arg_23__ : DataCon) :=
  match arg_23__ with
    | MkData _ dcUnique _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => dcUnique
  end.

Definition dcUnivTyBinders (arg_24__ : DataCon) :=
  match arg_24__ with
    | MkData _ _ _ _ _ dcUnivTyBinders _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      dcUnivTyBinders
  end.

Definition dcUnivTyVars (arg_25__ : DataCon) :=
  match arg_25__ with
    | MkData _ _ _ _ dcUnivTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      dcUnivTyVars
  end.

Definition dcVanilla (arg_26__ : DataCon) :=
  match arg_26__ with
    | MkData _ _ _ dcVanilla _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => dcVanilla
  end.

Definition dcWorkId (arg_27__ : DataCon) :=
  match arg_27__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcWorkId _ _ _ _ _ _ _ => dcWorkId
  end.
(* Midamble *)

Import FieldLabel.

Instance Uniqable_DataCon : Unique.Uniquable DataCon := {}.
Admitted.

(* Parameter dataConRepArgTys : DataCon -> list unit. *)

(* Converted value declarations: *)

(* Translating `instance Outputable.Outputable DataCon.EqSpec' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

Local Definition Eq___DataCon_op_zeze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

Local Definition Eq___DataCon_op_zsze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

Program Instance Eq___DataCon : GHC.Base.Eq_ DataCon := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___DataCon_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___DataCon_op_zsze__ |}.

Local Definition Ord__DataCon_compare : DataCon -> DataCon -> comparison :=
  fun a b => GHC.Base.compare (Unique.getUnique a) (Unique.getUnique b).

Local Definition Ord__DataCon_op_zg__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.> Unique.getUnique b.

Local Definition Ord__DataCon_op_zgze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.>= Unique.getUnique b.

Local Definition Ord__DataCon_op_zl__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.< Unique.getUnique b.

Local Definition Ord__DataCon_op_zlze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.<= Unique.getUnique b.

Local Definition Ord__DataCon_min : DataCon -> DataCon -> DataCon :=
  fun x y => if Ord__DataCon_op_zlze__ x y : bool then x else y.

Local Definition Ord__DataCon_max : DataCon -> DataCon -> DataCon :=
  fun x y => if Ord__DataCon_op_zlze__ x y : bool then y else x.

Program Instance Ord__DataCon : GHC.Base.Ord DataCon := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__DataCon_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__DataCon_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__DataCon_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__DataCon_op_zgze__ ;
      GHC.Base.compare__ := Ord__DataCon_compare ;
      GHC.Base.max__ := Ord__DataCon_max ;
      GHC.Base.min__ := Ord__DataCon_min |}.

(* Translating `instance Unique.Uniquable DataCon.DataCon' failed: OOPS! Cannot
   find information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Name.NamedThing DataCon.DataCon' failed: OOPS! Cannot
   find information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Outputable.Outputable DataCon.DataCon' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.OutputableBndr DataCon.DataCon' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "OutputableBndr"
   unsupported *)

(* Translating `instance Data.Data.Data DataCon.DataCon' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Outputable.Outputable DataCon.HsSrcBang' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable DataCon.HsImplBang' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable DataCon.SrcStrictness' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable DataCon.SrcUnpackedness' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable DataCon.StrictnessMark' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Binary.Binary DataCon.SrcStrictness' failed: OOPS!
   Cannot find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary.Binary DataCon.SrcUnpackedness' failed: OOPS!
   Cannot find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Data.Data.Data DataCon.HsSrcBang' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data DataCon.SrcUnpackedness' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___SrcUnpackedness_op_zeze__
    : SrcUnpackedness -> SrcUnpackedness -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | SrcUnpack , SrcUnpack => true
      | SrcNoUnpack , SrcNoUnpack => true
      | NoSrcUnpack , NoSrcUnpack => true
      | _ , _ => false
    end.

Local Definition Eq___SrcUnpackedness_op_zsze__
    : SrcUnpackedness -> SrcUnpackedness -> bool :=
  fun a b => negb (Eq___SrcUnpackedness_op_zeze__ a b).

Program Instance Eq___SrcUnpackedness : GHC.Base.Eq_ SrcUnpackedness := fun _
                                                                            k =>
    k {|GHC.Base.op_zeze____ := Eq___SrcUnpackedness_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___SrcUnpackedness_op_zsze__ |}.

(* Translating `instance Data.Data.Data DataCon.SrcStrictness' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___SrcStrictness_op_zeze__
    : SrcStrictness -> SrcStrictness -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | SrcLazy , SrcLazy => true
      | SrcStrict , SrcStrict => true
      | NoSrcStrict , NoSrcStrict => true
      | _ , _ => false
    end.

Local Definition Eq___SrcStrictness_op_zsze__
    : SrcStrictness -> SrcStrictness -> bool :=
  fun a b => negb (Eq___SrcStrictness_op_zeze__ a b).

Program Instance Eq___SrcStrictness : GHC.Base.Eq_ SrcStrictness := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___SrcStrictness_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___SrcStrictness_op_zsze__ |}.

(* Translating `instance Data.Data.Data DataCon.HsImplBang' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

Axiom isLegacyPromotableDataCon : forall {A : Type}, A.

Axiom dataConEqSpec : forall {A : Type}, A.

Axiom mkEqSpec : forall {A : Type}, A.

Axiom dataConUserType : forall {A : Type}, A.

Axiom mkDataCon : forall {A : Type}, A.

Axiom filterEqSpec : forall {A : Type}, A.

Axiom eqSpecTyVar : forall {A : Type}, A.

Axiom eqSpecType : forall {A : Type}, A.

Axiom eqSpecPair : forall {A : Type}, A.

Axiom dataConCannotMatch : forall {A : Type}, A.

Axiom dataConInstSig : forall {A : Type}, A.

Axiom dataConSig : forall {A : Type}, A.

Axiom dataConTheta : forall {A : Type}, A.

Axiom eqSpecPreds : forall {A : Type}, A.

Axiom substEqSpec : forall {A : Type}, A.

Axiom eqHsBang : forall {A : Type}, A.

Axiom isBanged : forall {A : Type}, A.

Axiom isSrcStrict : forall {A : Type}, A.

Axiom isSrcUnpacked : forall {A : Type}, A.

Axiom isMarkedStrict : forall {A : Type}, A.

Axiom dataConIdentity : forall {A : Type}, A.

Axiom dataConName : forall {A : Type}, A.

Axiom dataConTag : forall {A : Type}, A.

Axiom specialPromotedDc : forall {A : Type}, A.

Axiom dataConTyCon : forall {A : Type}, A.

Axiom dataConOrigTyCon : forall {A : Type}, A.

Axiom dataConRepRepArity : forall {A : Type}, A.

Axiom dataConRepType : forall {A : Type}, A.

Axiom dataConIsInfix : forall {A : Type}, A.

Axiom dataConUnivTyVars : forall {A : Type}, A.

Axiom dataConUnivTyBinders : forall {A : Type}, A.

Axiom dataConExTyVars : forall {A : Type}, A.

Axiom dataConExTyBinders : forall {A : Type}, A.

Axiom dataConAllTyVars : forall {A : Type}, A.

Axiom dataConWorkId : forall {A : Type}, A.

Axiom dataConWrapId_maybe : forall {A : Type}, A.

Axiom dataConWrapId : forall {A : Type}, A.

Axiom dataConImplicitTyThings : forall {A : Type}, A.

Axiom dataConFieldLabels : forall {A : Type}, A.

Axiom dataConFieldType : forall {A : Type}, A.

Axiom dataConSrcBangs : forall {A : Type}, A.

Axiom dataConSourceArity : forall {A : Type}, A.

Axiom isNullaryRepDataCon : forall {A : Type}, A.

Axiom dataConRepArity : forall {A : Type}, A.

Axiom isNullarySrcDataCon : forall {A : Type}, A.

Axiom dataConRepStrictness : forall {A : Type}, A.

Axiom dataConImplBangs : forall {A : Type}, A.

Axiom dataConBoxer : forall {A : Type}, A.

Axiom dataConFullSig : forall {A : Type}, A.

Axiom dataConOrigResTy : forall {A : Type}, A.

Axiom dataConStupidTheta : forall {A : Type}, A.

Axiom splitDataProductType_maybe : forall {A : Type}, A.

Axiom dataConInstArgTys : forall {A : Type}, A.

Axiom dataConInstOrigArgTys : forall {A : Type}, A.

Axiom dataConOrigArgTys : forall {A : Type}, A.

Axiom dataConRepArgTys : forall {A : Type}, A.

Axiom isTupleDataCon : forall {A : Type}, A.

Axiom isUnboxedTupleCon : forall {A : Type}, A.

Axiom isVanillaDataCon : forall {A : Type}, A.

Axiom isLegacyPromotableTyCon : forall {A : Type}, A.

Axiom classDataCon : forall {A : Type}, A.

Axiom promoteDataCon : forall {A : Type}, A.

Axiom buildAlgTyCon : forall {A : Type}, A.

(* Unbound variables:
     bool comparison error false list negb option true unit BasicTypes.Arity
     BasicTypes.ConTag BasicTypes.SourceText FieldLabel.FieldLabel GHC.Base.Eq_
     GHC.Base.Ord GHC.Base.compare GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__
     Name.Name TyCoRep.Coercion TyCoRep.ThetaType TyCoRep.TyBinder TyCoRep.Type_
     TyCon.TyCon Unique.Unique Unique.getUnique Var.Id Var.TyVar
*)
