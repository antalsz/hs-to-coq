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
Require Data.Function.
Require FieldLabel.
Require GHC.Base.
Require Name.
Require Unique.
(* Require Var. *)
Import GHC.Base.Notations.

(* Converted type declarations: *)

Parameter PatSyn : Type.
Import FieldLabel.
Parameter patSynArity        : PatSyn -> BasicTypes.Arity.
Parameter patSynFieldLabels  : PatSyn -> list FieldLabel.FieldLabel.
Parameter patSynName         : PatSyn -> Name.Name.


(* Midamble *)

Instance Unique_PatSyn : Unique.Uniquable PatSyn := {}.
Admitted.

(* Converted value declarations: *)

Local Definition Eq___PatSyn_op_zeze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base.==_ Unique.getUnique.

Local Definition Eq___PatSyn_op_zsze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base./=_ Unique.getUnique.

Program Instance Eq___PatSyn : GHC.Base.Eq_ PatSyn := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___PatSyn_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___PatSyn_op_zsze__ |}.

Local Definition Ord__PatSyn_compare : PatSyn -> PatSyn -> comparison :=
  Data.Function.on GHC.Base.compare Unique.getUnique.

Local Definition Ord__PatSyn_op_zg__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base.>_ Unique.getUnique.

Local Definition Ord__PatSyn_op_zgze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base.>=_ Unique.getUnique.

Local Definition Ord__PatSyn_op_zl__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base.<_ Unique.getUnique.

Local Definition Ord__PatSyn_op_zlze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base.<=_ Unique.getUnique.

Local Definition Ord__PatSyn_min : PatSyn -> PatSyn -> PatSyn :=
  fun x y => if Ord__PatSyn_op_zlze__ x y : bool then x else y.

Local Definition Ord__PatSyn_max : PatSyn -> PatSyn -> PatSyn :=
  fun x y => if Ord__PatSyn_op_zlze__ x y : bool then y else x.

Program Instance Ord__PatSyn : GHC.Base.Ord PatSyn := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__PatSyn_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__PatSyn_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__PatSyn_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__PatSyn_op_zgze__ ;
      GHC.Base.compare__ := Ord__PatSyn_compare ;
      GHC.Base.max__ := Ord__PatSyn_max ;
      GHC.Base.min__ := Ord__PatSyn_min |}.

(* Translating `instance Unique.Uniquable PatSyn.PatSyn' failed: OOPS! Cannot
   find information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Name.NamedThing PatSyn.PatSyn' failed: OOPS! Cannot
   find information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Outputable.Outputable PatSyn.PatSyn' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.OutputableBndr PatSyn.PatSyn' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "OutputableBndr"
   unsupported *)

(* Translating `instance Data.Data.Data PatSyn.PatSyn' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(*
Axiom mkPatSyn : forall {A : Type}, A.

Axiom patSynName : forall {A : Type}, A.

Axiom patSynIsInfix : forall {A : Type}, A.

Axiom patSynArity : forall {A : Type}, A.

Axiom patSynArgs : forall {A : Type}, A.

Axiom patSynFieldLabels : forall {A : Type}, A.

Axiom patSynFieldType : forall {A : Type}, A.

Axiom patSynUnivTyBinders : forall {A : Type}, A.

Axiom patSynExTyVars : forall {A : Type}, A.

Axiom patSynExTyBinders : forall {A : Type}, A.

Axiom patSynSig : forall {A : Type}, A.

Axiom patSynMatcher : forall {A : Type}, A.

Axiom patSynBuilder : forall {A : Type}, A.

Axiom tidyPatSynIds : forall {A : Type}, A.

Axiom patSynInstArgTys : forall {A : Type}, A.

Axiom patSynInstResTy : forall {A : Type}, A.

Axiom pprPatSynType : forall {A : Type}, A.
*)

(* Unbound variables:
     bool comparison list op_zt__ option BasicTypes.Arity Data.Function.on
     FieldLabel.FieldLabel GHC.Base.Eq_ GHC.Base.Ord GHC.Base.compare
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zl__
     GHC.Base.op_zlze__ GHC.Base.op_zsze__ Name.Name TyCoRep.ThetaType
     TyCoRep.TyBinder TyCoRep.Type_ Unique.Unique Unique.getUnique Var.Id Var.TyVar
*)
