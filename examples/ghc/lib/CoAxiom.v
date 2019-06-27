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
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require Name.
Require Pair.
Require SrcLoc.
Require Unique.

(* Converted type declarations: *)

Definition TypeEqn :=
  (Pair.Pair AxiomatizedTypes.Type_)%type.

Inductive CoAxiomRule : Type
  := | Mk_CoAxiomRule (coaxrName : FastString.FastString) (coaxrAsmpRoles
    : list AxiomatizedTypes.Role) (coaxrRole : AxiomatizedTypes.Role) (coaxrProves
    : list TypeEqn -> option TypeEqn)
   : CoAxiomRule.

Inductive CoAxBranch : Type
  := | Mk_CoAxBranch (cab_loc : SrcLoc.SrcSpan) (cab_tvs : list Core.TyVar)
  (cab_cvs : list Core.CoVar) (cab_roles : list AxiomatizedTypes.Role) (cab_lhs
    : list AxiomatizedTypes.Type_) (cab_rhs : AxiomatizedTypes.Type_) (cab_incomps
    : list CoAxBranch)
   : CoAxBranch.

Axiom Branches : Type -> Type.

Definition BranchIndex :=
  nat%type.

Inductive BranchFlag : Type
  := | Branched : BranchFlag
  |  Unbranched : BranchFlag.

Instance Default__CoAxiomRule : GHC.Err.Default CoAxiomRule :=
  GHC.Err.Build_Default _ (Mk_CoAxiomRule GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default).

Instance Default__CoAxBranch : GHC.Err.Default CoAxBranch :=
  GHC.Err.Build_Default _ (Mk_CoAxBranch GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default).

Instance Default__BranchFlag : GHC.Err.Default BranchFlag :=
  GHC.Err.Build_Default _ Branched.

Definition coaxrAsmpRoles (arg_0__ : CoAxiomRule) :=
  let 'Mk_CoAxiomRule _ coaxrAsmpRoles _ _ := arg_0__ in
  coaxrAsmpRoles.

Definition coaxrName (arg_0__ : CoAxiomRule) :=
  let 'Mk_CoAxiomRule coaxrName _ _ _ := arg_0__ in
  coaxrName.

Definition coaxrProves (arg_0__ : CoAxiomRule) :=
  let 'Mk_CoAxiomRule _ _ _ coaxrProves := arg_0__ in
  coaxrProves.

Definition coaxrRole (arg_0__ : CoAxiomRule) :=
  let 'Mk_CoAxiomRule _ _ coaxrRole _ := arg_0__ in
  coaxrRole.

Definition cab_cvs (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ _ cab_cvs _ _ _ _ := arg_0__ in
  cab_cvs.

Definition cab_incomps (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ _ _ _ _ _ cab_incomps := arg_0__ in
  cab_incomps.

Definition cab_lhs (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ _ _ _ cab_lhs _ _ := arg_0__ in
  cab_lhs.

Definition cab_loc (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch cab_loc _ _ _ _ _ _ := arg_0__ in
  cab_loc.

Definition cab_rhs (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ _ _ _ _ cab_rhs _ := arg_0__ in
  cab_rhs.

Definition cab_roles (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ _ _ cab_roles _ _ _ := arg_0__ in
  cab_roles.

Definition cab_tvs (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ cab_tvs _ _ _ _ _ := arg_0__ in
  cab_tvs.

(* Converted value declarations: *)

Axiom unbranched : CoAxBranch -> Branches AxiomatizedTypes.Unbranched.

Axiom trivialBuiltInFamily : AxiomatizedTypes.BuiltInSynFamily.

Axiom toUnbranchedAxiom : forall {br},
                          AxiomatizedTypes.CoAxiom br ->
                          AxiomatizedTypes.CoAxiom AxiomatizedTypes.Unbranched.

Axiom toUnbranched : forall {br},
                     Branches br -> Branches AxiomatizedTypes.Unbranched.

Axiom toBranchedAxiom : forall {br},
                        AxiomatizedTypes.CoAxiom br ->
                        AxiomatizedTypes.CoAxiom AxiomatizedTypes.Branched.

Axiom toBranched : forall {br},
                   Branches br -> Branches AxiomatizedTypes.Branched.

Axiom placeHolderIncomps : list CoAxBranch.

Axiom numBranches : forall {br}, Branches br -> nat.

Axiom mapAccumBranches : forall {br},
                         (list CoAxBranch -> CoAxBranch -> CoAxBranch) -> Branches br -> Branches br.

Axiom manyBranches : list CoAxBranch -> Branches AxiomatizedTypes.Branched.

Axiom isImplicitCoAxiom : forall {br}, AxiomatizedTypes.CoAxiom br -> bool.

Axiom fsFromRole : AxiomatizedTypes.Role -> FastString.FastString.

Axiom fromBranches : forall {br}, Branches br -> list CoAxBranch.

Axiom coAxiomTyCon : forall {br}, AxiomatizedTypes.CoAxiom br -> Core.TyCon.

Axiom coAxiomSingleBranch_maybe : forall {br},
                                  AxiomatizedTypes.CoAxiom br -> option CoAxBranch.

Axiom coAxiomSingleBranch : AxiomatizedTypes.CoAxiom
                            AxiomatizedTypes.Unbranched ->
                            CoAxBranch.

Axiom coAxiomRole : forall {br},
                    AxiomatizedTypes.CoAxiom br -> AxiomatizedTypes.Role.

Axiom coAxiomNumPats : forall {br}, AxiomatizedTypes.CoAxiom br -> nat.

Axiom coAxiomNthBranch : forall {br},
                         AxiomatizedTypes.CoAxiom br -> BranchIndex -> CoAxBranch.

Axiom coAxiomName : forall {br}, AxiomatizedTypes.CoAxiom br -> Name.Name.

Axiom coAxiomBranches : forall {br}, AxiomatizedTypes.CoAxiom br -> Branches br.

Axiom coAxiomArity : forall {br},
                     AxiomatizedTypes.CoAxiom br -> BranchIndex -> BasicTypes.Arity.

Axiom coAxBranchTyVars : CoAxBranch -> list Core.TyVar.

Axiom coAxBranchSpan : CoAxBranch -> SrcLoc.SrcSpan.

Axiom coAxBranchRoles : CoAxBranch -> list AxiomatizedTypes.Role.

Axiom coAxBranchRHS : CoAxBranch -> AxiomatizedTypes.Type_.

Axiom coAxBranchLHS : CoAxBranch -> list AxiomatizedTypes.Type_.

Axiom coAxBranchIncomps : CoAxBranch -> list CoAxBranch.

Axiom coAxBranchCoVars : CoAxBranch -> list Core.CoVar.

Axiom branchesNth : forall {br}, Branches br -> BranchIndex -> CoAxBranch.

Instance Eq___Role : GHC.Base.Eq_ AxiomatizedTypes.Role := {}.
Proof.
Admitted.

Instance Ord__Role : GHC.Base.Ord AxiomatizedTypes.Role := {}.
Proof.
Admitted.

(* Skipping all instances of class `Data.Data.Data', including
   `CoAxiom.Data__Role' *)

(* Skipping all instances of class `Data.Data.Data', including
   `CoAxiom.Data__CoAxBranch' *)

(* Skipping all instances of class `Binary.Binary', including
   `CoAxiom.Binary__Role' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CoAxiom.Outputable__Role' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CoAxiom.Outputable__CoAxBranch' *)

(* Skipping all instances of class `Data.Data.Data', including
   `CoAxiom.Data__CoAxiom' *)

Instance NamedThing__CoAxiom
   : forall {br}, Name.NamedThing (AxiomatizedTypes.CoAxiom br) :=
  {}.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoAxiom.Outputable__CoAxiom' *)

Instance Uniquable__CoAxiom
   : forall {br}, Unique.Uniquable (AxiomatizedTypes.CoAxiom br) :=
  {}.
Proof.
Admitted.

Instance Eq___CoAxiom
   : forall {br}, GHC.Base.Eq_ (AxiomatizedTypes.CoAxiom br) :=
  {}.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoAxiom.Outputable__CoAxiomRule' *)

Instance Eq___CoAxiomRule : GHC.Base.Eq_ CoAxiomRule := {}.
Proof.
Admitted.

Instance Ord__CoAxiomRule : GHC.Base.Ord CoAxiomRule := {}.
Proof.
Admitted.

Instance Uniquable__CoAxiomRule : Unique.Uniquable CoAxiomRule := {}.
Proof.
Admitted.

(* Skipping all instances of class `Data.Data.Data', including
   `CoAxiom.Data__CoAxiomRule' *)

(* External variables:
     Type bool list nat option AxiomatizedTypes.Branched
     AxiomatizedTypes.BuiltInSynFamily AxiomatizedTypes.CoAxiom AxiomatizedTypes.Role
     AxiomatizedTypes.Type_ AxiomatizedTypes.Unbranched BasicTypes.Arity Core.CoVar
     Core.TyCon Core.TyVar FastString.FastString GHC.Base.Eq_ GHC.Base.Ord
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.default Name.Name Name.NamedThing
     Pair.Pair SrcLoc.SrcSpan Unique.Uniquable
*)
