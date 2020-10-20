(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require Core.
Require FieldLabel.
Require GHC.Base.
Require Name.
Require Unique.

(* Converted type declarations: *)

Inductive ConLike : Type
  := | RealDataCon : Core.DataCon -> ConLike
  |  PatSynCon : Core.PatSyn -> ConLike.

(* Converted value declarations: *)

Instance Eq___ConLike : GHC.Base.Eq_ ConLike.
Proof.
Admitted.

Instance Uniquable__ConLike : Unique.Uniquable ConLike.
Proof.
Admitted.

Instance NamedThing__ConLike : Name.NamedThing ConLike.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `ConLike.Outputable__ConLike' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `ConLike.OutputableBndr__ConLike' *)

(* Skipping all instances of class `Data.Data.Data', including
   `ConLike.Data__ConLike' *)

Axiom eqConLike : ConLike -> ConLike -> bool.

Axiom conLikeArity : ConLike -> BasicTypes.Arity.

Axiom conLikeFieldLabels : ConLike -> list FieldLabel.FieldLabel.

Axiom conLikeInstOrigArgTys : ConLike ->
                              list AxiomatizedTypes.Type_ -> list AxiomatizedTypes.Type_.

Axiom conLikeExTyVars : ConLike -> list Core.TyVar.

Axiom conLikeName : ConLike -> Name.Name.

Axiom conLikeStupidTheta : ConLike -> AxiomatizedTypes.ThetaType.

Axiom conLikeWrapId_maybe : ConLike -> option Core.Id.

Axiom conLikeImplBangs : ConLike -> list Core.HsImplBang.

Axiom conLikeResTy : ConLike ->
                     list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom conLikeFullSig : ConLike ->
                       (list Core.TyVar * list Core.TyVar * list Core.EqSpec *
                        AxiomatizedTypes.ThetaType *
                        AxiomatizedTypes.ThetaType *
                        list AxiomatizedTypes.Type_ *
                        AxiomatizedTypes.Type_)%type.

Axiom conLikeFieldType : ConLike ->
                         FieldLabel.FieldLabelString -> AxiomatizedTypes.Type_.

Axiom conLikesWithFields : list ConLike ->
                           list FieldLabel.FieldLabelString -> list ConLike.

Axiom conLikeIsInfix : ConLike -> bool.

(* External variables:
     bool list op_zt__ option AxiomatizedTypes.ThetaType AxiomatizedTypes.Type_
     BasicTypes.Arity Core.DataCon Core.EqSpec Core.HsImplBang Core.Id Core.PatSyn
     Core.TyVar FieldLabel.FieldLabel FieldLabel.FieldLabelString GHC.Base.Eq_
     Name.Name Name.NamedThing Unique.Uniquable
*)
