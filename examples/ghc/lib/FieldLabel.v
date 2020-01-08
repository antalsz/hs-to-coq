(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Foldable.
Require Data.Traversable.
Require FastString.
Require FastStringEnv.
Require GHC.Base.
Require Name.
Require OccName.

(* Converted type declarations: *)

Definition FieldLabelString :=
  FastString.FastString%type.

Inductive FieldLbl a : Type
  := | Mk_FieldLabel (flLabel : FieldLabelString) (flIsOverloaded : bool)
  (flSelector : a)
   : FieldLbl a.

Definition FieldLabel :=
  (FieldLbl Name.Name)%type.

Definition FieldLabelEnv :=
  (FastStringEnv.DFastStringEnv FieldLabel)%type.

Arguments Mk_FieldLabel {_} _ _ _.

Definition flIsOverloaded {a} (arg_0__ : FieldLbl a) :=
  let 'Mk_FieldLabel _ flIsOverloaded _ := arg_0__ in
  flIsOverloaded.

Definition flLabel {a} (arg_0__ : FieldLbl a) :=
  let 'Mk_FieldLabel flLabel _ _ := arg_0__ in
  flLabel.

Definition flSelector {a} (arg_0__ : FieldLbl a) :=
  let 'Mk_FieldLabel _ _ flSelector := arg_0__ in
  flSelector.

(* Converted value declarations: *)

Axiom mkFieldLabelOccs : FieldLabelString ->
                         OccName.OccName -> bool -> FieldLbl OccName.OccName.

(* Skipping all instances of class `Data.Data.Data', including
   `FieldLabel.Data__FieldLbl' *)

Instance Eq___FieldLbl
   : forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_ (FieldLbl a).
Proof.
Admitted.

Instance Functor__FieldLbl : GHC.Base.Functor FieldLbl.
Proof.
Admitted.

Instance Foldable__FieldLbl : Data.Foldable.Foldable FieldLbl.
Proof.
Admitted.

Instance Traversable__FieldLbl : Data.Traversable.Traversable FieldLbl.
Proof.
Admitted.

(* Skipping all instances of class `Binary.Binary', including
   `FieldLabel.Binary__FieldLbl' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `FieldLabel.Outputable__FieldLbl' *)

(* External variables:
     bool Data.Foldable.Foldable Data.Traversable.Traversable FastString.FastString
     FastStringEnv.DFastStringEnv GHC.Base.Eq_ GHC.Base.Functor Name.Name
     OccName.OccName
*)
