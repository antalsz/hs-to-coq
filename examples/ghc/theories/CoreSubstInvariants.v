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

(* Reasoning about FV.v requires funext. *)
Import Coq.Logic.FunctionalExtensionality.

Require Proofs.GHC.Base.
Require CoreInduct.


Set Bullet Behavior "Strict Subproofs".

(* Some of these lemmas should move elsewhere *)

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

Lemma no_elem_empty : forall v, elemVarSet v emptyVarSet = false.
Admitted.


Lemma union_empty : forall fv, FV.unionFV fv FV.emptyFV = fv.
intro fv. unfold FV.unionFV. unfold FV.emptyFV.
  apply functional_extensionality. intro f.
  apply functional_extensionality. intro vs.
  apply functional_extensionality. intro bs.
  reflexivity.
Qed.

Lemma fvVarSet_union : forall s1 s2, 
    FV.fvVarSet (FV.unionFV s1 s2) = VarSet.unionVarSet (FV.fvVarSet s1) (FV.fvVarSet s2).
  intros. unfold FV.fvVarSet.
Admitted.

Lemma varSetInScope_union : forall s1 s2 s,
    (VarEnv.varSetInScope (unionVarSet s1 s2) s = true) <->
    (VarEnv.varSetInScope s1 s = true) /\ (VarEnv.varSetInScope s2 s = true).

Admitted.

Lemma expr_fvs_App : forall e1 e2, 
    expr_fvs (App e1 e2) = FV.unionFV (expr_fvs e1) (expr_fvs e2).
Proof.
  intros.
  reflexivity.
Qed.

Lemma expr_fvs_Case : forall e b u l, 
    expr_fvs (Case e b u l) = 
    FV.unionFV (expr_fvs e)
               (addBndr b
                        (FV.unionsFV
                           (List.map (fun '(_, bndrs, rhs) => 
                                        addBndrs bndrs (expr_fvs rhs)) l))).
Proof.
  intros.
  simpl.
  apply functional_extensionality. intro f.
  apply functional_extensionality. intro vs.
  apply functional_extensionality. intro bs.
  rewrite union_empty. reflexivity.
Qed.

Lemma substExpr_App : forall s str e1 e2, substExpr str s (App e1 e2) = 
                                 App (substExpr str s e1) (substExpr str s e2).
Proof. intros. simpl.
       f_equal.
       unfold substExpr. 
       destruct e1; reflexivity.
       destruct e2; reflexivity.
Qed.

Definition substAlt str subst (alt:AltCon * list Var.Var * CoreExpr) := 
  let '((con,bndrs), rhs) := alt in
  let '(subst', bndrs') := substBndrs subst bndrs in
  (con, bndrs', substExpr str subst' rhs).

Lemma substExpr_Case : forall str s e b u l, 
    substExpr str s (Case e b u l) = 
    let '(subst', bndr') := substBndr s b in 
    Case (substExpr str s e) bndr' tt (map (substAlt str subst') l).
Proof. intros.                                        
unfold substExpr. simpl.
destruct (substBndr s b) as [subst' bndr'].       
f_equal. destruct e; reflexivity.
Qed.

Hint Rewrite expr_fvs_App expr_fvs_Case substExpr_App substExpr_Case
     fvVarSet_union varSetInScope_union : substfv.

(* 
Definition IdSubstEnv :=
  (VarEnv.IdEnv CoreSyn.CoreExpr)%type.

Inductive Subst : Type
  := Mk_Subst : VarEnv.InScopeSet -> IdSubstEnv -> unit -> unit -> Subst.
*)

Definition in_scope fvs s :=
  VarEnv.varSetInScope (FV.fvVarSet fvs) (substInScope s) = true.

Lemma inscope_union : forall fv1 fv2 s,
 in_scope (FV.unionFV fv1 fv2) s <-> in_scope fv1 s /\ in_scope fv2 s.
Admitted.

Hint Rewrite inscope_union : substfv.

Definition expr_in_scope exp s := 
  in_scope (CoreFVs.expr_fvs exp) s.
  


Definition in_scope_invariant (s : Subst) :=
  match s with 
    | Mk_Subst inScopeSet idSubstEnv _ _ => 
      forall v exp, 
        (VarEnv.lookupVarEnv idSubstEnv v = Some exp) -> 
        expr_in_scope exp s
(*        VarEnv.varSetInScope (FV.fvVarSet (CoreFVs.expr_fvs exp)) inScopeSet = true *)
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
  unfold in_scope_invariant, extendIdSubst, expr_in_scope, in_scope in *.
  destruct s. simpl in *.
  intros x exp h0.
  destruct (v == x) eqn:hEq.
  rewrite lookup_insertVarEnv in h0; eauto.  
  inversion h0. subst. clear h0.
  auto.
  rewrite lookup_insertVarEnv_neq in h0; eauto.
Qed.


Lemma in_scope_invariant_subst_expr : forall e str s,
  in_scope_invariant s ->
  expr_in_scope e s -> 
  expr_in_scope (CoreSubst.substExpr str s e) s.
Proof.
  intro e.
  induction e using CoreInduct.core_induct; intros.
  - simpl. unfold expr_in_scope in *.
    simpl in *.
    unfold lookupIdSubst.
    destruct s as [inScopeSet idSubst ? ?].
    destruct (Var.isLocalId v) eqn:local.
    destruct (VarEnv.lookupVarEnv idSubst v) eqn:lkp.
    + simpl.
      simpl in H.
      apply H in lkp.
      unfold expr_in_scope in lkp. simpl in lkp. auto.
    + destruct (VarEnv.lookupInScope inScopeSet v) eqn:ins.
      simpl in H.
      simpl in H0.
      unfold FV.unitFV.
      unfold FV.fvVarSet.
      unfold VarEnv.varSetInScope.
      destruct inScopeSet.
      unfold FV.fvVarListVarSet.
      unfold GHC.Base.op_z2218U__.
      admit.
      admit.
    + admit.
  - auto. 
  - unfold expr_in_scope, in_scope in *. 
    autorewrite with substfv in *.
    destruct H0 as [h0 h1].
    split; eauto.
  - (* Lam *) admit.
  - (* Let *) admit.
  - (* Case *) 
    unfold expr_in_scope in *.
    autorewrite with substfv in *.
    destruct H1 as [h0 h1].
    destruct (substBndr s bndr) as [subst' bndr'] eqn:sb.
    autorewrite with substfv. split. auto.
Admitted.        

Lemma in_scope_Bndr : forall bndr s s' bndr' fvs,
  substBndr s bndr = (s' , bndr' ) ->
  in_scope fvs s' ->
  in_scope (addBndr bndr fvs) s.
Proof.
  intros.
  unfold substBndr, substIdBndr in H.
  unfold addBndr.
  destruct s.
  autorewrite with substfv.
  simpl in H.
  inversion H. clear H. subst.
  unfold varTypeTyCoFVs.
  split. admit.

  unfold in_scope in *.
  simpl in *.
Admitted.

Lemma varSetInScope_delFV : forall bndr fvs i,
  VarEnv.varSetInScope (FV.fvVarSet fvs) (VarEnv.extendInScopeSet i (VarEnv.uniqAway i bndr)) = true ->
  VarEnv.varSetInScope (FV.fvVarSet (FV.delFV bndr fvs)) i = true.
Proof.  
  intros.
  unfold VarEnv.varSetInScope, FV.fvVarSet, FV.delFV, VarEnv.extendInScopeSet in *.
  destruct i.
  unfold subVarSet in *.
  unfold isEmptyVarSet in *.
  unfold minusVarSet in *.
  unfold extendVarSet in *.
  unfold UniqSet.isEmptyUniqSet in *.
Admitted.

Lemma In_ind : forall A (l:list A) (P : list A -> Prop), 
        (P nil) -> 
        (forall x xs, In x l -> P xs -> P (x :: xs)) -> P l.
Proof.
  intros.
  induction l. auto.
  apply H0. apply in_eq.
  apply IHl.
  intros.
  apply H0.
  apply in_cons. auto. auto.
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
