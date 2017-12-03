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
Require Data.Foldable.
Require Data.Function.
Require DataCon.
Require FieldLabel.
Require GHC.Base.
Require GHC.List.
Require Name.
Require PatSyn.
Require Unique.
Require Var.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive ConLike : Type := RealDataCon : DataCon.DataCon -> ConLike
                         |  PatSynCon : PatSyn.PatSyn -> ConLike.
(* Midamble *)

(* nonqualified record selectors*)
Import FieldLabel.

Instance Unique_ConLike : Unique.Uniquable ConLike := {}. Admitted.

(* Converted value declarations: *)

Local Definition Eq___ConLike_op_zeze__ : ConLike -> ConLike -> bool :=
  Data.Function.on _GHC.Base.==_ Unique.getUnique.

Local Definition Eq___ConLike_op_zsze__ : ConLike -> ConLike -> bool :=
  Data.Function.on _GHC.Base./=_ Unique.getUnique.

Program Instance Eq___ConLike : GHC.Base.Eq_ ConLike := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___ConLike_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___ConLike_op_zsze__ |}.

Local Definition Ord__ConLike_compare : ConLike -> ConLike -> comparison :=
  Data.Function.on GHC.Base.compare Unique.getUnique.

Local Definition Ord__ConLike_op_zg__ : ConLike -> ConLike -> bool :=
  Data.Function.on _GHC.Base.>_ Unique.getUnique.

Local Definition Ord__ConLike_op_zgze__ : ConLike -> ConLike -> bool :=
  Data.Function.on _GHC.Base.>=_ Unique.getUnique.

Local Definition Ord__ConLike_op_zl__ : ConLike -> ConLike -> bool :=
  Data.Function.on _GHC.Base.<_ Unique.getUnique.

Local Definition Ord__ConLike_op_zlze__ : ConLike -> ConLike -> bool :=
  Data.Function.on _GHC.Base.<=_ Unique.getUnique.

Local Definition Ord__ConLike_min : ConLike -> ConLike -> ConLike :=
  fun x y => if Ord__ConLike_op_zlze__ x y : bool then x else y.

Local Definition Ord__ConLike_max : ConLike -> ConLike -> ConLike :=
  fun x y => if Ord__ConLike_op_zlze__ x y : bool then y else x.

Program Instance Ord__ConLike : GHC.Base.Ord ConLike := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__ConLike_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__ConLike_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__ConLike_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__ConLike_op_zgze__ ;
      GHC.Base.compare__ := Ord__ConLike_compare ;
      GHC.Base.max__ := Ord__ConLike_max ;
      GHC.Base.min__ := Ord__ConLike_min |}.

(* Translating `instance Unique.Uniquable ConLike.ConLike' failed: OOPS! Cannot
   find information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Name.NamedThing ConLike.ConLike' failed: OOPS! Cannot
   find information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Outputable.Outputable ConLike.ConLike' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.OutputableBndr ConLike.ConLike' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "OutputableBndr"
   unsupported *)

(* Translating `instance Data.Data.Data ConLike.ConLike' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

Definition conLikeArity : ConLike -> BasicTypes.Arity :=
  fun arg_20__ =>
    match arg_20__ with
      | RealDataCon data_con => DataCon.dataConSourceArity data_con
      | PatSynCon pat_syn => PatSyn.patSynArity pat_syn
    end.

Definition conLikeExTyVars : ConLike -> list Var.TyVar :=
  fun arg_8__ =>
    match arg_8__ with
      | RealDataCon dcon1 => DataCon.dataConExTyVars dcon1
      | PatSynCon psyn1 => PatSyn.patSynExTyVars psyn1
    end.

Definition conLikeFieldLabels : ConLike -> list FieldLabel.FieldLabel :=
  fun arg_12__ =>
    match arg_12__ with
      | RealDataCon data_con => DataCon.dataConFieldLabels data_con
      | PatSynCon pat_syn => PatSyn.patSynFieldLabels pat_syn
    end.

Definition conLikesWithFields : list ConLike -> list
                                FieldLabel.FieldLabelString -> list ConLike :=
  fun con_likes lbls =>
    let has_fld :=
      fun dc lbl =>
        Data.Foldable.any (fun fl => flLabel fl GHC.Base.== lbl) (conLikeFieldLabels
                                                                 dc) in
    let has_flds := fun dc => Data.Foldable.all (has_fld dc) lbls in
    GHC.List.filter has_flds con_likes.

Definition conLikeImplBangs : ConLike -> list DataCon.HsImplBang :=
  fun arg_0__ =>
    match arg_0__ with
      | RealDataCon data_con => DataCon.dataConImplBangs data_con
      | PatSynCon pat_syn => GHC.List.replicate (PatSyn.patSynArity pat_syn)
                             DataCon.HsLazy
    end.

Definition conLikeName : ConLike -> Name.Name :=
  fun arg_4__ =>
    match arg_4__ with
      | RealDataCon data_con => DataCon.dataConName data_con
      | PatSynCon pat_syn => PatSyn.patSynName pat_syn
    end.

(* Unbound variables:
     bool comparison flLabel list BasicTypes.Arity Data.Foldable.all
     Data.Foldable.any Data.Function.on DataCon.DataCon DataCon.HsImplBang
     DataCon.HsLazy DataCon.dataConExTyVars DataCon.dataConFieldLabels
     DataCon.dataConImplBangs DataCon.dataConName DataCon.dataConSourceArity
     FieldLabel.FieldLabel FieldLabel.FieldLabelString GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.compare GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__ GHC.List.filter
     GHC.List.replicate Name.Name PatSyn.PatSyn PatSyn.patSynArity
     PatSyn.patSynExTyVars PatSyn.patSynFieldLabels PatSyn.patSynName
     Unique.getUnique Var.TyVar
*)
