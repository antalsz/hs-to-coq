Require Import Core.
Require Import CoreSubst.

Require Import Coq.Lists.List.

Require Import Proofs.GhcTactics.
Require Import Proofs.Base.
Require Import Proofs.CoreInduct.
Require Import Proofs.Core.

Require Import Proofs.VarSetFSet.
Require Import Proofs.VarSet.
Require Import Proofs.Var.


Require Import Proofs.ScopeInvariant.
Import GHC.Base.ManualNotations.

Opaque Base.hs_string__.
Opaque GHC.Err.default.

Require Import GHC.Base.
Import GHC.Base.Notations.

Set Bullet Behavior "Strict Subproofs".

(* If uniqueAway returns a variable with the same unique, 
   it returns the same variable. *)      
Axiom uniqAway_eq_same : forall v in_scope_set,
    (uniqAway in_scope_set v == v) = true ->
    (uniqAway in_scope_set v = v).

(* The variable returned by uniqAway is fresh. *)
Axiom uniqAway_lookupVarSet_fresh : forall v in_scope_set,
    lookupVarSet (getInScopeVars in_scope_set) 
                 (uniqAway in_scope_set v) = None.

(* If uniqAway returns a fresh variable, then the original was already in scope. *)
Axiom uniqAway_fresh_in_scope : forall v in_scope_set, 
     (uniqAway in_scope_set v == v) = false ->
     exists v', lookupVarSet (getInScopeVars in_scope_set) v = Some v' /\ almostEqual v v'.
    
 
Axiom lookupVarSet_eq :
  forall v1 v2 vs,
    (v1 GHC.Base.== v2) = true ->
    lookupVarSet vs v1 = lookupVarSet vs v2.

Lemma extend_getInScopeVars : forall in_scope_set v, 
      (extendVarSet (getInScopeVars in_scope_set) v) = (getInScopeVars (extendInScopeSet in_scope_set v)).
Proof. 
  intros.
  unfold extendVarSet, getInScopeVars, extendInScopeSet.
  destruct in_scope_set.
  unfold extendVarSet. auto.
Qed.

(*
Definition go_alt s subst := ltac:(  
    let e := eval cbv fix beta delta [subst_expr] in 
            (subst_expr s subst (Type_ tt)) in 
    lazymatch e with | let y := ?def in _ => 
                       pose (y := def); fold subst_expr in y; exact y

    end).

Definition go s subst := ltac:(  
    let e := eval cbv fix beta delta [subst_expr] in 
            (subst_expr s subst (Type_ tt)) in 
    lazymatch e with | let y := ?def in let x := @?dx y in _ => 
                       let ex :=  
                           eval cbv beta delta [go_alt] in 
                       (dx (go_alt s subst)) in                           
                       pose (x := ex) ; 
                         fold subst_expr in x; 
                         exact x

    end).

Lemma subst_expr_go : forall s subst e, 
    subst_expr s subst e = go s subst e.
Proof.
  intros s subst e.
  unfold subst_expr.
  unfold go.
  destruct e; simpl; auto.
Qed.
*)

(* ---------------------------------------------------------------- *)

Lemma subst_expr_App : forall s subst e1 e2, 
    subst_expr s subst (App e1 e2) = 
    App (subst_expr s subst e1) (subst_expr s subst e2).
    Proof. 
      intros. unfold subst_expr. simpl. 
      f_equal.
      destruct e1; simpl; auto.
      destruct e2; simpl; auto.
Qed.

Lemma subst_expr_Tick : forall doc subst tic e, 
        subst_expr doc subst (Tick tic e) = 
        CoreUtils.mkTick (substTickish subst tic) (subst_expr doc subst e).
Proof.
  intros. 
  unfold subst_expr, CoreUtils.mkTick, substTickish. simpl.
  destruct e; simpl; auto.
Qed.

Lemma subst_expr_Lam : forall s subst bndr body,
        subst_expr s subst (Lam bndr body) = 
        let (subst', bndr') := substBndr subst bndr in
        Lam bndr' (subst_expr s subst' body).
Proof.
  intros.
  unfold subst_expr. simpl.
  destruct (substBndr subst bndr) as [subst' bndr']. 
  f_equal.
Qed.

Definition substAlt str subst (alt:AltCon * list Core.Var * CoreExpr) := 
  let '((con,bndrs), rhs) := alt in
  let '(subst', bndrs') := substBndrs subst bndrs in
  (con, bndrs', subst_expr str subst' rhs).

Lemma subst_expr_Case : forall str s e b u l, 
    subst_expr str s (Case e b u l) = 
    let '(subst', bndr') := substBndr s b in 
    Case (subst_expr str s e) bndr' tt (map (substAlt str subst') l).
Proof. intros.  simpl.
destruct (substBndr s b) as [subst' bndr'].       
f_equal. destruct e; reflexivity.
Qed.


Hint Rewrite subst_expr_App subst_expr_Tick subst_expr_Lam subst_expr_Case :
  subst_expr.


(* ---------------------------------------------------------------- *)

(* When calling (subst subst tm) it should be the case that
   the in-scope set in the substitution is a superset of both:

  (SIa) The free vars of the range of the substitution
  (SIb) The free vars of ty minus the domain of the substitution

  We enforce this by requiring

    - the RHS is wellscoped according to the in_scope_set
    - the current scope is a strongSubset of in_scope_set
*)


Definition WellScoped_Subst  (s : Subst) (vs:VarSet) :=
  match s with 
  | Mk_Subst in_scope_set subst_env _ _ => 
    StrongSubset vs (getInScopeVars in_scope_set) /\
    forall var, 
      (match lookupVarEnv subst_env var with
        | Some expr => WellScoped expr (getInScopeVars in_scope_set)
        | None => True
        end)
  end.

Axiom StrongSubset_refl : forall vs, 
    StrongSubset vs vs.

Axiom StrongSubset_trans : forall vs2 vs1 vs3, 
    StrongSubset vs1 vs2 -> StrongSubset vs2 vs3 -> StrongSubset vs1 vs3.

Lemma WellScoped_Subst_StrongSubst : forall vs1 s vs2,
  StrongSubset vs2 vs1 -> 
  WellScoped_Subst s vs1 ->
  WellScoped_Subst s vs2.
Proof.
  intros.
  unfold WellScoped_Subst in *.
  destruct s.
  destruct H0.
  split.
  - eapply (StrongSubset_trans vs1); auto.
  - auto.
Qed.

(* ---------------------------------------- *)

Lemma WellScoped_substBndr : forall vs in_scope_set env v subst' bndr',
    WellScoped_Subst (Mk_Subst in_scope_set env tt tt) vs ->
    (subst', bndr') = substBndr (Mk_Subst in_scope_set env tt tt) v ->
    exists new_env, subst' = Mk_Subst (extendInScopeSet in_scope_set bndr') new_env tt tt /\
    WellScoped_Subst subst' vs.
Proof.
  intros vs in_scope_set env v subst' bndr' WS SB.
  unfold substBndr, substIdBndr in *.
  simpl in *.
  destruct WS as [SS LV].  
  (* v is the Var that is the name of the bound variable. *)
  destruct ((uniqAway in_scope_set v) == v) eqn:EQ.
  + exists (delVarEnv env v). 
    inversion SB; subst; clear SB. split. auto.
    pose (K := uniqAway_eq_same _ _ EQ).  clearbody K. 
    rewrite K.
    unfold WellScoped_Subst.
    split. unfold StrongSubset.
    intro v'.
    destruct (v == v') eqn: EQV.
    ++ erewrite <- lookupVarSet_eq with (v1 := v)(v2:=v'); eauto.
       rewrite <- K.
       assert (L: lookupVarSet vs
                               (uniqAway in_scope_set v) = None).
       admit.
       rewrite L.
       auto.
    ++ destruct (lookupVarSet vs v') eqn:LV1.
       specialize (LV v').
Admitted.


Lemma substExpr : forall s e vs in_scope_set env, 
    WellScoped_Subst (Mk_Subst in_scope_set env tt tt) vs -> 
    WellScoped e vs -> 
    WellScoped (substExpr s (Mk_Subst in_scope_set env tt tt) e) 
               (getInScopeVars in_scope_set).
Proof.
  intros s e.
  apply (core_induct e); unfold substExpr.
  - unfold subst_expr. intros v vs in_scope_set env WSsubst WSvar.
    unfold lookupIdSubst. 
    simpl in WSsubst. destruct WSsubst as [ ss vv] . specialize (vv v).         
    destruct (isLocalId v) eqn:HLocal; simpl.
    -- destruct (lookupVarEnv env v) eqn:HLookup. 
        + auto.
        + destruct (lookupInScope in_scope_set v) eqn:HIS.
          ++ unfold WellScoped, WellScopedVar in *.
             destruct (lookupVarSet vs v) eqn:LVS; try contradiction.
             unfold lookupInScope in HIS. destruct in_scope_set. simpl.
             assert (VV: ValidVarSet v2). admit.
             unfold ValidVarSet in VV.
             specialize (VV _ _ HIS).
             rewrite lookupVarSet_eq with (v2 := v).
             rewrite HIS.
             eapply Var.almostEqual_refl; auto.
             rewrite Base.Eq_sym. auto.
          ++ unfold WellScoped, WellScopedVar in WSvar.
             unfold lookupInScope in HIS. destruct in_scope_set.
             unfold StrongSubset in ss.
             specialize (ss v). simpl in ss.
             rewrite HIS in ss.
             destruct (lookupVarSet vs v); try contradiction.
    -- unfold WellScoped in WSvar. 
       eapply WellScopedVar_StrongSubset; eauto.
  - unfold subst_expr. auto. 
  - intros. 
    rewrite subst_expr_App.
    unfold WellScoped; simpl; fold WellScoped.
    unfold WellScoped in H2; simpl; fold WellScoped in H2. destruct H2.
    split; eauto.
  - intros.
    rewrite subst_expr_Lam.
    set (sb := substBndr (Mk_Subst in_scope_set env tt tt) v).
    destruct sb as [subst' bndr'] eqn:SB. subst sb.
    symmetry in SB.
    pose (k := WellScoped_substBndr _ _ _ _ _ _ ltac:(eauto) SB). clearbody k.
    destruct k as [new_env [EQ WS]].  
    unfold WellScoped; fold WellScoped.
    rewrite extend_getInScopeVars.
    rewrite EQ.
    unfold WellScoped in H1. fold WellScoped in H1.
    eapply H with (vs := extendVarSet vs v); auto.
    eapply WellScoped_Subst_StrongSubst with (vs1 := extendVarSet vs v); eauto.
    eapply StrongSubset_refl.
    unfold substBndr, substIdBndr in SB.
    destruct (uniqAway in_scope_set v == v) eqn:NC.
    + apply uniqAway_eq_same in NC.
      rewrite NC in SB. simpl in SB.
      inversion SB. subst. clear SB. inversion H3. subst. clear H3.
      unfold WellScoped_Subst in *.
      destruct H0 as [SS LVi].
      destruct WS as [SSE LVd].
      split.
      -- unfold StrongSubset in *.
         intro var.
         destruct (v == var) eqn:EQv.
         rewrite lookupVarSet_extendVarSet_eq; auto.
         rewrite <- extend_getInScopeVars.
         rewrite lookupVarSet_extendVarSet_eq.
         apply almostEqual_refl.
         auto.
         rewrite lookupVarSet_extendVarSet_neq; auto.
         apply SSE.
         unfold CoreBndr in *.
         unfold not. intro. rewrite EQv in H0. discriminate.
      -- intro var.
         eapply LVd.
    + simpl in SB.
      inversion SB. subst. clear SB. inversion H3. subst. clear H3.
      unfold WellScoped_Subst in *.
      destruct H0 as [SS LVi].
      destruct WS as [SSE LVd].
      split.
      -- unfold StrongSubset in *.
         intro var.
         destruct (v == var) eqn:EQv.
         rewrite lookupVarSet_extendVarSet_eq; auto.
         rewrite <- extend_getInScopeVars.
         rewrite lookupVarSet_extendVarSet_neq; auto.         
         rewrite lookupVarSet_eq with (v2 := v).
         destruct (uniqAway_fresh_in_scope _ _ NC) as [v' [LVv' AE]]. rewrite LVv'. auto.
         rewrite Base.Eq_sym. auto.
         unfold not. intro h. 
         rewrite Base.Eq_sym in EQv.
         assert (uniqAway in_scope_set v == v = true).
         eapply Base.Eq_trans. eauto. eauto.
         rewrite NC in H0. discriminate.
         rewrite lookupVarSet_extendVarSet_neq.
         eapply SSE.
         unfold CoreBndr in *.
         intro h. rewrite EQv in h. discriminate.
      -- intro var.
         eapply LVd.
  - 