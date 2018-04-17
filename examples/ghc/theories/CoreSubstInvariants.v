Require Import CoreSyn.
Require Import Id.
Require Import IdInfo.
Require Import VarSet.
Require Import BasicTypes.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.

Require Import CoreFVs.
Require Import CoreSubst.

Require Import GHC.Base.
Import GHC.Base.Notations.

Require Proofs.GHC.Base.

Set Bullet Behavior "Strict Subproofs".

Lemma lookup_insert: forall A k1 k2 (v:A) m,
    k1 == k2 = true ->
    IntMap.Internal.lookup k1 (IntMap.Internal.insert k2 v m) = Some v.
Admitted.

Lemma lookup_insertVarEnv: forall A k1 k2 (v:A) m,
    k1 == k2 = true ->
    VarEnv.lookupVarEnv (VarEnv.extendVarEnv m k1 v) k2 = Some v.
Admitted.

Lemma lookup_insertVarEnv_neq: forall A k1 k2 (v:A) m,
    k1 == k2 = false ->
    VarEnv.lookupVarEnv (VarEnv.extendVarEnv m k1 v) k2 = VarEnv.lookupVarEnv m k2.
Admitted.


(* 
Definition IdSubstEnv :=
  (VarEnv.IdEnv CoreSyn.CoreExpr)%type.

Inductive Subst : Type
  := Mk_Subst : VarEnv.InScopeSet -> IdSubstEnv -> unit -> unit -> Subst.
*)

Definition in_scope_invariant (s : Subst) :=
  match s with 
    | Mk_Subst inScopeSet idSubstEnv _ _ => 
      forall v exp, 
        (VarEnv.lookupVarEnv idSubstEnv v = Some exp) -> 
        VarEnv.varSetInScope (FV.fvVarSet (CoreFVs.expr_fvs exp)) inScopeSet = true
  end.
  
Lemma in_scope_invariant_emptySubst : in_scope_invariant emptySubst.
Proof. 
  unfold in_scope_invariant, emptySubst.
  intros x exp. simpl. intros H. inversion H.
Qed.


Lemma in_scope_invariant_extendIdSubst : forall s v e, 
    in_scope_invariant s -> 
    VarEnv.varSetInScope (FV.fvVarSet (expr_fvs e)) (substInScope s) = true ->
    in_scope_invariant (CoreSubst.extendIdSubst s v e).
Proof.
  intros.
  unfold in_scope_invariant, extendIdSubst.
  destruct s. simpl in *.
  intros x exp h0.
  destruct (v == x) eqn:hEq.
  rewrite lookup_insertVarEnv in h0; eauto.  
  inversion h0. subst. clear h0.
  auto.
  rewrite lookup_insertVarEnv_neq in h0; eauto.
Qed.





(*
-- | A substitution environment, containing 'Id', 'TyVar', and 'CoVar'
-- substitutions.
--
-- Some invariants apply to how you use the substitution:
--
-- 1. #in_scope_invariant# The in-scope set contains at least those 'Id's and 'TyVar's that will be in scope /after/
-- applying the substitution to a term. Precisely, the in-scope set must be a superset of the free vars of the
-- substitution range that might possibly clash with locally-bound variables in the thing being substituted in.
--
-- 2. #apply_once# You may apply the substitution only /once/
--
-- There are various ways of setting up the in-scope set such that the first of these invariants hold:
--
-- * Arrange that the in-scope set really is all the things in scope
--
-- * Arrange that it's the free vars of the range of the substitution
--
-- * Make it empty, if you know that all the free vars of the substitution are fresh, and hence can't possibly clash
data Subst
  = Subst InScopeSet  -- Variables in in scope (both Ids and TyVars) /after/
                      -- applying the substitution
          IdSubstEnv  -- Substitution from NcIds to CoreExprs
          TvSubstEnv  -- Substitution from TyVars to Types
          CvSubstEnv  -- Substitution from CoVars to Coercions

        -- INVARIANT 1: See #in_scope_invariant#
        -- This is what lets us deal with name capture properly
        -- It's a hard invariant to check...
        --
        -- INVARIANT 2: The substitution is apply-once; see Note [Apply once] with
        --              Types.TvSubstEnv
        --
        -- INVARIANT 3: See Note [Extending the Subst]

{-
Note [Extending the Subst]
~~~~~~~~~~~~~~~~~~~~~~~~~~
For a core Subst, which binds Ids as well, we make a different choice for Ids
than we do for TyVars.

For TyVars, see Note [Extending the TCvSubst] with Type.TvSubstEnv

For Ids, we have a different invariant
        The IdSubstEnv is extended *only* when the Unique on an Id changes
        Otherwise, we just extend the InScopeSet

In consequence:

* If all subst envs are empty, substExpr would be a
  no-op, so substExprSC ("short cut") does nothing.

  However, substExpr still goes ahead and substitutes.  Reason: we may
  want to replace existing Ids with new ones from the in-scope set, to
  avoid space leaks.

* In substIdBndr, we extend the IdSubstEnv only when the unique changes

* If the CvSubstEnv, TvSubstEnv and IdSubstEnv are all empty,
  substExpr does nothing (Note that the above rule for substIdBndr
  maintains this property.  If the incoming envts are both empty, then
  substituting the type and IdInfo can't change anything.)

* In lookupIdSubst, we *must* look up the Id in the in-scope set, because
  it may contain non-trivial changes.  Example:
        (/\a. \x:a. ...x...) Int
  We extend the TvSubstEnv with [a |-> Int]; but x's unique does not change
  so we only extend the in-scope set.  Then we must look up in the in-scope
  set when we find the occurrence of x.

* The requirement to look up the Id in the in-scope set means that we
  must NOT take no-op short cut when the IdSubst is empty.
  We must still look up every Id in the in-scope set.

* (However, we don't need to do so for expressions found in the IdSubst
  itself, whose range is assumed to be correct wrt the in-scope set.)

Why do we make a different choice for the IdSubstEnv than the
TvSubstEnv and CvSubstEnv?

* For Ids, we change the IdInfo all the time (e.g. deleting the
  unfolding), and adding it back later, so using the TyVar convention
  would entail extending the substitution almost all the time

* The simplifier wants to look up in the in-scope set anyway, in case it
  can see a better unfolding from an enclosing case expression

* For TyVars, only coercion variables can possibly change, and they are
  easy to spot
-}



*)
