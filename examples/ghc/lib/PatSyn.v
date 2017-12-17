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
Require Var.

(* Converted type declarations: *)

Inductive PatSyn : Type := MkPatSyn : Name.Name -> Unique.Unique -> list
                                      unit -> BasicTypes.Arity -> bool -> list FieldLabel.FieldLabel -> list
                                      Var.TyVar -> list unit -> unit -> list Var.TyVar -> list
                                      unit -> unit -> unit -> (Var.Id * bool)%type -> option (Var.Id *
                                                                                             bool)%type -> PatSyn.

Definition psArgs (arg_0__ : PatSyn) :=
  match arg_0__ with
    | MkPatSyn _ _ psArgs _ _ _ _ _ _ _ _ _ _ _ _ => psArgs
  end.

Definition psArity (arg_1__ : PatSyn) :=
  match arg_1__ with
    | MkPatSyn _ _ _ psArity _ _ _ _ _ _ _ _ _ _ _ => psArity
  end.

Definition psBuilder (arg_2__ : PatSyn) :=
  match arg_2__ with
    | MkPatSyn _ _ _ _ _ _ _ _ _ _ _ _ _ _ psBuilder => psBuilder
  end.

Definition psExTyBinders (arg_3__ : PatSyn) :=
  match arg_3__ with
    | MkPatSyn _ _ _ _ _ _ _ _ _ _ psExTyBinders _ _ _ _ => psExTyBinders
  end.

Definition psExTyVars (arg_4__ : PatSyn) :=
  match arg_4__ with
    | MkPatSyn _ _ _ _ _ _ _ _ _ psExTyVars _ _ _ _ _ => psExTyVars
  end.

Definition psFieldLabels (arg_5__ : PatSyn) :=
  match arg_5__ with
    | MkPatSyn _ _ _ _ _ psFieldLabels _ _ _ _ _ _ _ _ _ => psFieldLabels
  end.

Definition psInfix (arg_6__ : PatSyn) :=
  match arg_6__ with
    | MkPatSyn _ _ _ _ psInfix _ _ _ _ _ _ _ _ _ _ => psInfix
  end.

Definition psMatcher (arg_7__ : PatSyn) :=
  match arg_7__ with
    | MkPatSyn _ _ _ _ _ _ _ _ _ _ _ _ _ psMatcher _ => psMatcher
  end.

Definition psName (arg_8__ : PatSyn) :=
  match arg_8__ with
    | MkPatSyn psName _ _ _ _ _ _ _ _ _ _ _ _ _ _ => psName
  end.

Definition psOrigResTy (arg_9__ : PatSyn) :=
  match arg_9__ with
    | MkPatSyn _ _ _ _ _ _ _ _ _ _ _ _ psOrigResTy _ _ => psOrigResTy
  end.

Definition psProvTheta (arg_10__ : PatSyn) :=
  match arg_10__ with
    | MkPatSyn _ _ _ _ _ _ _ _ _ _ _ psProvTheta _ _ _ => psProvTheta
  end.

Definition psReqTheta (arg_11__ : PatSyn) :=
  match arg_11__ with
    | MkPatSyn _ _ _ _ _ _ _ _ psReqTheta _ _ _ _ _ _ => psReqTheta
  end.

Definition psUnique (arg_12__ : PatSyn) :=
  match arg_12__ with
    | MkPatSyn _ psUnique _ _ _ _ _ _ _ _ _ _ _ _ _ => psUnique
  end.

Definition psUnivTyBinders (arg_13__ : PatSyn) :=
  match arg_13__ with
    | MkPatSyn _ _ _ _ _ _ _ psUnivTyBinders _ _ _ _ _ _ _ => psUnivTyBinders
  end.

Definition psUnivTyVars (arg_14__ : PatSyn) :=
  match arg_14__ with
    | MkPatSyn _ _ _ _ _ _ psUnivTyVars _ _ _ _ _ _ _ _ => psUnivTyVars
  end.
(* Midamble *)

Instance Unique_PatSyn : Unique.Uniquable PatSyn := {}.
Admitted.

(* Converted value declarations: *)

Instance Eq___PatSyn : GHC.Base.Eq_ PatSyn := {}.
Proof.
Admitted.

Instance Ord__PatSyn : GHC.Base.Ord PatSyn := {}.
Proof.
Admitted.

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

(* Unbound variables:
     bool list op_zt__ option unit BasicTypes.Arity FieldLabel.FieldLabel
     GHC.Base.Eq_ GHC.Base.Ord Name.Name Unique.Unique Var.Id Var.TyVar
*)
