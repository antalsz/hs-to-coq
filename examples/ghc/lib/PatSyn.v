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
Require FieldLabel.
Require GHC.Base.
Require Name.
Require Unique.

(* Converted type declarations: *)

Inductive PatSyn : Type
  := MkPatSyn
   : Name.Name ->
     Unique.Unique ->
     list unit ->
     BasicTypes.Arity ->
     bool ->
     list FieldLabel.FieldLabel ->
     list Var.TyVarBinder ->
     unit ->
     list Var.TyVarBinder ->
     unit -> unit -> (Var.Id * bool)%type -> option (Var.Id * bool)%type -> PatSyn.

Definition psArgs (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ psArgs _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psArgs.

Definition psArity (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ psArity _ _ _ _ _ _ _ _ _ := arg_0__ in
  psArity.

Definition psBuilder (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ _ _ psBuilder := arg_0__ in
  psBuilder.

Definition psExTyVars (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ psExTyVars _ _ _ _ := arg_0__ in
  psExTyVars.

Definition psFieldLabels (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ psFieldLabels _ _ _ _ _ _ _ := arg_0__ in
  psFieldLabels.

Definition psInfix (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ psInfix _ _ _ _ _ _ _ _ := arg_0__ in
  psInfix.

Definition psMatcher (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ _ psMatcher _ := arg_0__ in
  psMatcher.

Definition psName (arg_0__ : PatSyn) :=
  let 'MkPatSyn psName _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psName.

Definition psProvTheta (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ psProvTheta _ _ _ := arg_0__ in
  psProvTheta.

Definition psReqTheta (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ psReqTheta _ _ _ _ _ := arg_0__ in
  psReqTheta.

Definition psResultTy (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ psResultTy _ _ := arg_0__ in
  psResultTy.

Definition psUnique (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ psUnique _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psUnique.

Definition psUnivTyVars (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ psUnivTyVars _ _ _ _ _ _ := arg_0__ in
  psUnivTyVars.
(* Midamble *)

Instance Unique_PatSyn : Unique.Uniquable PatSyn := {}.
Admitted.

(* Converted value declarations: *)

Instance Eq___PatSyn : GHC.Base.Eq_ PatSyn := {}.
Proof.
Admitted.

Instance Uniquable__PatSyn : Unique.Uniquable PatSyn := {}.
Proof.
Admitted.

Instance NamedThing__PatSyn : Name.NamedThing PatSyn := {}.
Proof.
Admitted.

(* Skipping instance Outputable__PatSyn of class Outputable *)

(* Skipping instance OutputableBndr__PatSyn of class OutputableBndr *)

(* Skipping instance Data__PatSyn of class Data *)

Axiom mkPatSyn : Name.Name ->
                 bool ->
                 (list Var.TyVarBinder * unit)%type ->
                 (list Var.TyVarBinder * unit)%type ->
                 list unit ->
                 unit ->
                 (Var.Id * bool)%type ->
                 option (Var.Id * bool)%type -> list FieldLabel.FieldLabel -> PatSyn.

Axiom patSynName : PatSyn -> Name.Name.

Axiom patSynIsInfix : PatSyn -> bool.

Axiom patSynArity : PatSyn -> BasicTypes.Arity.

Axiom patSynArgs : PatSyn -> list unit.

Axiom patSynFieldLabels : PatSyn -> list FieldLabel.FieldLabel.

Axiom patSynFieldType : PatSyn -> FieldLabel.FieldLabelString -> unit.

Axiom patSynUnivTyVarBinders : PatSyn -> list Var.TyVarBinder.

Axiom patSynExTyVars : PatSyn -> list Var.TyVar.

Axiom patSynExTyVarBinders : PatSyn -> list Var.TyVarBinder.

Axiom patSynSig : PatSyn ->
                  (list Var.TyVar * unit * list Var.TyVar * unit * list unit * unit)%type.

Axiom patSynMatcher : PatSyn -> (Var.Id * bool)%type.

Axiom patSynBuilder : PatSyn -> option (Var.Id * bool)%type.

Axiom tidyPatSynIds : (Var.Id -> Var.Id) -> PatSyn -> PatSyn.

Axiom patSynInstArgTys : PatSyn -> list unit -> list unit.

Axiom patSynInstResTy : PatSyn -> list unit -> unit.

(* pprPatSynType skipped *)

(* External variables:
     bool list op_zt__ option unit BasicTypes.Arity FieldLabel.FieldLabel
     FieldLabel.FieldLabelString GHC.Base.Eq_ Name.Name Name.NamedThing
     Unique.Uniquable Unique.Unique Var.Id Var.TyVar Var.TyVarBinder
*)
