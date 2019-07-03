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

Instance Uniquable__ConLike : Unique.Uniquable ConLike := {}.
Proof.
Admitted.

Axiom eqConLike : ConLike -> ConLike -> bool.

Axiom conLikesWithFields : list ConLike ->
                           list FieldLabel.FieldLabelString -> list ConLike.

Axiom conLikeWrapId_maybe : ConLike -> option Core.Id.

Axiom conLikeStupidTheta : ConLike -> AxiomatizedTypes.ThetaType.

Axiom conLikeResTy : ConLike ->
                     list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom conLikeName : ConLike -> Name.Name.

Axiom conLikeIsInfix : ConLike -> bool.

Axiom conLikeInstOrigArgTys : ConLike ->
                              list AxiomatizedTypes.Type_ -> list AxiomatizedTypes.Type_.

Axiom conLikeImplBangs : ConLike -> list Core.HsImplBang.

Axiom conLikeFullSig : ConLike ->
                       (list Core.TyVar * list Core.TyVar * list Core.EqSpec *
                        AxiomatizedTypes.ThetaType *
                        AxiomatizedTypes.ThetaType *
                        list AxiomatizedTypes.Type_ *
                        AxiomatizedTypes.Type_)%type.

Axiom conLikeFieldType : ConLike ->
                         FieldLabel.FieldLabelString -> AxiomatizedTypes.Type_.

Axiom conLikeFieldLabels : ConLike -> list FieldLabel.FieldLabel.

Axiom conLikeExTyVars : ConLike -> list Core.TyVar.

Axiom conLikeArity : ConLike -> BasicTypes.Arity.

(* Skipping all instances of class `Data.Data.Data', including
   `ConLike.Data__ConLike' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `ConLike.OutputableBndr__ConLike' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `ConLike.Outputable__ConLike' *)

Instance NamedThing__ConLike : Name.NamedThing ConLike := {}.
Proof.
Admitted.

Instance Eq___ConLike : GHC.Base.Eq_ ConLike := {}.
Proof.
Admitted.

(* External variables:
     bool list op_zt__ option AxiomatizedTypes.ThetaType AxiomatizedTypes.Type_
     BasicTypes.Arity Core.DataCon Core.EqSpec Core.HsImplBang Core.Id Core.PatSyn
     Core.TyVar FieldLabel.FieldLabel FieldLabel.FieldLabelString GHC.Base.Eq_
     Name.Name Name.NamedThing Unique.Uniquable
*)
