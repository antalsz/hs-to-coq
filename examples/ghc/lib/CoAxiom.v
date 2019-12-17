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

Axiom Branches : Type -> Type.

Inductive BranchFlag : Type
  := | Branched : BranchFlag
  |  Unbranched : BranchFlag.

Instance Default__BranchFlag : GHC.Err.Default BranchFlag :=
  GHC.Err.Build_Default _ Branched.

(* Converted value declarations: *)

Axiom unbranched : AxiomatizedTypes.CoAxBranch ->
                   Branches AxiomatizedTypes.Unbranched.

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

Axiom placeHolderIncomps : list AxiomatizedTypes.CoAxBranch.

Axiom numBranches : forall {br}, Branches br -> nat.

Axiom mapAccumBranches : forall {br},
                         (list AxiomatizedTypes.CoAxBranch ->
                          AxiomatizedTypes.CoAxBranch -> AxiomatizedTypes.CoAxBranch) ->
                         Branches br -> Branches br.

Axiom manyBranches : list AxiomatizedTypes.CoAxBranch ->
                     Branches AxiomatizedTypes.Branched.

Axiom isImplicitCoAxiom : forall {br}, AxiomatizedTypes.CoAxiom br -> bool.

Axiom fsFromRole : AxiomatizedTypes.Role -> FastString.FastString.

Axiom fromBranches : forall {br},
                     Branches br -> list AxiomatizedTypes.CoAxBranch.

Axiom coAxiomTyCon : forall {br}, AxiomatizedTypes.CoAxiom br -> Core.TyCon.

Axiom coAxiomSingleBranch_maybe : forall {br},
                                  AxiomatizedTypes.CoAxiom br -> option AxiomatizedTypes.CoAxBranch.

Axiom coAxiomSingleBranch : AxiomatizedTypes.CoAxiom
                            AxiomatizedTypes.Unbranched ->
                            AxiomatizedTypes.CoAxBranch.

Axiom coAxiomRole : forall {br},
                    AxiomatizedTypes.CoAxiom br -> AxiomatizedTypes.Role.

Axiom coAxiomNumPats : forall {br}, AxiomatizedTypes.CoAxiom br -> nat.

Axiom coAxiomNthBranch : forall {br},
                         AxiomatizedTypes.CoAxiom br ->
                         AxiomatizedTypes.BranchIndex -> AxiomatizedTypes.CoAxBranch.

Axiom coAxiomName : forall {br}, AxiomatizedTypes.CoAxiom br -> Name.Name.

Axiom coAxiomBranches : forall {br}, AxiomatizedTypes.CoAxiom br -> Branches br.

Axiom coAxiomArity : forall {br},
                     AxiomatizedTypes.CoAxiom br -> AxiomatizedTypes.BranchIndex -> BasicTypes.Arity.

Axiom coAxBranchTyVars : AxiomatizedTypes.CoAxBranch -> list Core.TyVar.

Axiom coAxBranchSpan : AxiomatizedTypes.CoAxBranch -> SrcLoc.SrcSpan.

Axiom coAxBranchRoles : AxiomatizedTypes.CoAxBranch ->
                        list AxiomatizedTypes.Role.

Axiom coAxBranchRHS : AxiomatizedTypes.CoAxBranch -> AxiomatizedTypes.Type_.

Axiom coAxBranchLHS : AxiomatizedTypes.CoAxBranch ->
                      list AxiomatizedTypes.Type_.

Axiom coAxBranchIncomps : AxiomatizedTypes.CoAxBranch ->
                          list AxiomatizedTypes.CoAxBranch.

Axiom coAxBranchCoVars : AxiomatizedTypes.CoAxBranch -> list Core.CoVar.

Axiom branchesNth : forall {br},
                    Branches br -> AxiomatizedTypes.BranchIndex -> AxiomatizedTypes.CoAxBranch.

Instance Eq___Role : GHC.Base.Eq_ AxiomatizedTypes.Role.
Proof.
Admitted.

Instance Ord__Role : GHC.Base.Ord AxiomatizedTypes.Role.
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
   : forall {br}, Name.NamedThing (AxiomatizedTypes.CoAxiom br).
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoAxiom.Outputable__CoAxiom' *)

Instance Uniquable__CoAxiom
   : forall {br}, Unique.Uniquable (AxiomatizedTypes.CoAxiom br).
Proof.
Admitted.

Instance Eq___CoAxiom : forall {br}, GHC.Base.Eq_ (AxiomatizedTypes.CoAxiom br).
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoAxiom.Outputable__CoAxiomRule' *)

Instance Ord__CoAxiomRule : GHC.Base.Ord AxiomatizedTypes.CoAxiomRule.
Proof.
Admitted.

Instance Eq___CoAxiomRule : GHC.Base.Eq_ AxiomatizedTypes.CoAxiomRule.
Proof.
Admitted.

Instance Uniquable__CoAxiomRule : Unique.Uniquable AxiomatizedTypes.CoAxiomRule.
Proof.
Admitted.

(* Skipping all instances of class `Data.Data.Data', including
   `CoAxiom.Data__CoAxiomRule' *)

(* External variables:
     Type bool list nat option AxiomatizedTypes.BranchIndex AxiomatizedTypes.Branched
     AxiomatizedTypes.BuiltInSynFamily AxiomatizedTypes.CoAxBranch
     AxiomatizedTypes.CoAxiom AxiomatizedTypes.CoAxiomRule AxiomatizedTypes.Role
     AxiomatizedTypes.Type_ AxiomatizedTypes.Unbranched BasicTypes.Arity Core.CoVar
     Core.TyCon Core.TyVar FastString.FastString GHC.Base.Eq_ GHC.Base.Ord
     GHC.Err.Build_Default GHC.Err.Default Name.Name Name.NamedThing Pair.Pair
     SrcLoc.SrcSpan Unique.Uniquable
*)
