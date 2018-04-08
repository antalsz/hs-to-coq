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
Require DataCon.
Require FieldLabel.
Require GHC.Base.
Require GHC.List.
Require Name.
Require PatSyn.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive ConLike : Type
  := RealDataCon : DataCon.DataCon -> ConLike
  |  PatSynCon : PatSyn.PatSyn -> ConLike.
(* Midamble *)

(* nonqualified record selectors*)
Import FieldLabel.

Instance Unique_ConLike : Unique.Uniquable ConLike := {}. Admitted.

(* Converted value declarations: *)

Local Definition Uniquable__ConLike_getUnique : ConLike -> Unique.Unique :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon dc => Unique.getUnique dc
    | PatSynCon ps => Unique.getUnique ps
    end.

Program Instance Uniquable__ConLike : Unique.Uniquable ConLike :=
  fun _ k => k {| Unique.getUnique__ := Uniquable__ConLike_getUnique |}.

(* Skipping instance NamedThing__ConLike *)

(* Skipping instance Outputable__ConLike of class Outputable *)

(* Skipping instance OutputableBndr__ConLike of class OutputableBndr *)

(* Skipping instance Data__ConLike of class Data *)

Definition conLikeArity : ConLike -> BasicTypes.Arity :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon data_con => DataCon.dataConSourceArity data_con
    | PatSynCon pat_syn => PatSyn.patSynArity pat_syn
    end.

Definition conLikeFieldLabels : ConLike -> list FieldLabel.FieldLabel :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon data_con => DataCon.dataConFieldLabels data_con
    | PatSynCon pat_syn => PatSyn.patSynFieldLabels pat_syn
    end.

Definition conLikesWithFields
   : list ConLike -> list FieldLabel.FieldLabelString -> list ConLike :=
  fun con_likes lbls =>
    let has_fld :=
      fun dc lbl =>
        Data.Foldable.any (fun fl => FieldLabel.flLabel fl GHC.Base.== lbl)
        (conLikeFieldLabels dc) in
    let has_flds := fun dc => Data.Foldable.all (has_fld dc) lbls in
    GHC.List.filter has_flds con_likes.

Definition conLikeName : ConLike -> Name.Name :=
  fun arg_0__ =>
    match arg_0__ with
    | RealDataCon data_con => DataCon.dataConName data_con
    | PatSynCon pat_syn => PatSyn.patSynName pat_syn
    end.

Definition eqConLike : ConLike -> ConLike -> bool :=
  fun x y => Unique.getUnique x GHC.Base.== Unique.getUnique y.

Local Definition Eq___ConLike_op_zeze__ : ConLike -> ConLike -> bool :=
  eqConLike.

Local Definition Eq___ConLike_op_zsze__ : ConLike -> ConLike -> bool :=
  fun x y => negb (Eq___ConLike_op_zeze__ x y).

Program Instance Eq___ConLike : GHC.Base.Eq_ ConLike :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___ConLike_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___ConLike_op_zsze__ |}.

(* External variables:
     bool list negb BasicTypes.Arity Data.Foldable.all Data.Foldable.any
     DataCon.DataCon DataCon.dataConFieldLabels DataCon.dataConName
     DataCon.dataConSourceArity FieldLabel.FieldLabel FieldLabel.FieldLabelString
     FieldLabel.flLabel GHC.Base.Eq_ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zsze____ GHC.List.filter Name.Name PatSyn.PatSyn PatSyn.patSynArity
     PatSyn.patSynFieldLabels PatSyn.patSynName Unique.Uniquable Unique.Unique
     Unique.getUnique Unique.getUnique__
*)
