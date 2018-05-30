Require Import Core.
Require Import CoreFVs.
Require Import CoreUtils.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Proofs.Base.
Require Import Proofs.GhcTactics.
Require Import Proofs.Forall.
Require Import Proofs.CoreFVs.
Require Import Proofs.VarSet.
Require Import Proofs.CoreInduct.
Require Import Proofs.Var.

Import GHC.Base.ManualNotations.



Set Bullet Behavior "Strict Subproofs".

(*
This file describes an invariant of Core files that
 * all variables must be in scope
 * and be structurally equal to their binder
*)

Definition WellScopedVar (v : Var) (in_scope : VarSet) : Prop :=
   match lookupVarSet in_scope v with
    | None => False
    | Some v' => almostEqual v v'
    end.

Fixpoint WellScoped (e : CoreExpr) (in_scope : VarSet) {struct e} : Prop :=
  match e with
  | Mk_Var v => WellScopedVar v in_scope
  | Lit l => True
  | App e1 e2 => WellScoped e1 in_scope /\  WellScoped e2 in_scope
  | Lam v e => WellScoped e (extendVarSet in_scope v)
  | Let bind body =>
      WellScopedBind bind in_scope /\
      WellScoped body (extendVarSetList in_scope (bindersOf bind))
  | Case scrut bndr ty alts  => 
    WellScoped scrut in_scope /\
    Forall' (fun alt =>
      let in_scope' := extendVarSetList in_scope (bndr :: snd (fst alt)) in
      WellScoped (snd alt) in_scope') alts
  | Cast e _ =>   WellScoped e in_scope
  | Tick _ e =>   WellScoped e in_scope
  | Type_ _  =>   True
  | Coercion _ => True
  end
with WellScopedBind (bind : CoreBind) (in_scope : VarSet) : Prop :=
  match bind with
  | NonRec v rhs => WellScoped rhs in_scope
  | Rec pairs => 
     NoDup (map varUnique (map fst pairs)) /\
      Forall' (fun p => WellScoped (snd p) (extendVarSetList in_scope (map fst pairs))) pairs
  end.

Definition WellScopedAlt bndr (alt : CoreAlt) in_scope  :=
    let in_scope' := extendVarSetList in_scope (bndr :: snd (fst alt)) in
    WellScoped (snd alt) in_scope'.

Fixpoint WellScopedProgram (pgm : CoreProgram) (in_scope : VarSet) : Prop :=
  match pgm with
  | [] => True
  | bind :: pgm' =>
    WellScopedBind bind in_scope /\
    WellScopedProgram pgm' (extendVarSetList in_scope (bindersOf bind))
  end.

(** ** Lots of lemmas *)

(** *** [almostEqual] *)

Axiom WellScoped_extendVarSet_ae:
  forall e vs v1 v2,
  almostEqual v1 v2 ->
  WellScoped e (extendVarSet vs v1) <-> WellScoped e (extendVarSet vs v2).


(** *** Structural lemmas *)

Lemma WellScoped_Lam:
  forall v e isvs,
  WellScoped (Lam v e) isvs <-> WellScoped e (extendVarSet isvs v).
Proof. intros. reflexivity. Qed.


Lemma WellScoped_mkLams:
  forall vs e isvs,
  WellScoped (mkLams vs e) isvs <-> WellScoped e (extendVarSetList  isvs vs).
Proof.
  induction vs; intros.
  * reflexivity.
  * simpl.
    rewrite extendVarSetList_cons.
    refine (IHvs _ _).
Qed.

Lemma WellScoped_varToCoreExpr:
  forall v isvs,
  WellScopedVar v isvs -> WellScoped (varToCoreExpr v) isvs.
Proof.
  intros.
  destruct v; simpl; try trivial.
  unfold varToCoreExpr; simpl.
  destruct_match; simpl; try trivial.
Qed.

Lemma WellScoped_mkVarApps:
  forall e vs isvs,
  WellScoped e isvs -> 
  Forall (fun v => WellScopedVar v isvs) vs ->
  WellScoped (mkVarApps e vs) isvs.
Proof.
  intros.
  unfold mkVarApps.
  rewrite Foldable.hs_coq_foldl_list.
  revert e H.
  induction H0; intros.
  * simpl. intuition.
  * simpl.
    apply IHForall; clear IHForall.
    simpl.
    split; try assumption.
    apply WellScoped_varToCoreExpr; assumption.
Qed.

Lemma WellScopedVar_extendVarSet:
  forall v vs,
  WellScopedVar v (extendVarSet vs v).
Proof.
  intros.
  unfold WellScopedVar.
  rewrite lookupVarSet_extendVarSet_self.
  apply almostEqual_refl.
Qed.

Lemma WellScoped_MkLetRec: forall pairs body isvs,
  WellScoped (mkLetRec pairs body) isvs <-> WellScoped (Let (Rec pairs) body) isvs .
Proof.
  intros.
  unfold mkLetRec.
  destruct pairs; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

Lemma WellScoped_MkLet: forall bind body isvs,
  WellScoped (mkLet bind body) isvs <-> WellScoped (Let bind body) isvs .
Proof.
  intros.
  unfold mkLet.
  destruct bind; try reflexivity.
  destruct l; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

(** *** StrongSubset *)

Lemma WellScopedVar_StrongSubset : forall e vs1 vs2, 
    WellScopedVar e vs1 -> StrongSubset vs1 vs2 -> WellScopedVar e vs2.
Proof.
  intros v vs1 vs2 WS SS.
  unfold WellScopedVar, StrongSubset in *.
  specialize (SS v).
  destruct (lookupVarSet vs1 v); try contradiction.
  destruct (lookupVarSet vs2 v) eqn:LV2; try contradiction.
  eapply almostEqual_trans with (v2 := v0); auto.
Qed.

Lemma WellScoped_StrongSubset : forall e vs1 vs2, 
    WellScoped e vs1 -> StrongSubset vs1 vs2 -> WellScoped e vs2.
Proof.
  intro e.
  apply (core_induct e); intros; try (destruct binds);
    unfold WellScoped in *; fold WellScoped in *; eauto.
  - eapply WellScopedVar_StrongSubset; eauto.
  - destruct H1. split; eauto.
  - eapply H; eauto.
    unfold StrongSubset in *.
    intro var.
    specialize (H1 var).
    unfold CoreBndr in v. (* make sure that the type class looks right.*)
    destruct (v GHC.Base.== var) eqn:Eq.
    + rewrite lookupVarSet_extendVarSet_eq; auto.
      rewrite lookupVarSet_extendVarSet_eq; auto.
      eapply almostEqual_refl.
    + rewrite lookupVarSet_extendVarSet_neq.
      destruct (lookupVarSet vs1 var) eqn:IN; auto.
      rewrite lookupVarSet_extendVarSet_neq.
      auto.
      intro h;
      rewrite h in Eq; discriminate.
      intro h;
      rewrite h in Eq; discriminate.
   - destruct H1 as [WE Wb].
      split; eauto.
      eapply H0; eauto.
      eapply StrongSubset_extendVarSetList.
      auto.
  - destruct H1 as [[WE1 WE2] Wb].
     repeat split; auto.
     rewrite Forall'_Forall in *.
     rewrite Forall_forall in *.
     intros h IN. destruct h as [v rhs].
     specialize (WE2 (v,rhs)).
     simpl in *.
     eauto using StrongSubset_extendVarSetList.
     eauto using StrongSubset_extendVarSetList.
  - destruct H1 as [W1 W2].
    split; eauto.
     rewrite Forall'_Forall in *.
     rewrite Forall_forall in *.
     intros h IN. destruct h as [[dc pats] rhs].
     specialize (H0 dc pats rhs IN).
     specialize (W2 (dc,pats,rhs) IN).
     simpl in *.
     eauto using StrongSubset_extendVarSetList.
Qed.

(** *** Relation to [exprFreeVars] *)

Lemma WellScoped_subset:
  forall e vs,
    WellScoped e vs -> subVarSet (exprFreeVars e) vs = true.
Proof.
  intro e.
  apply (core_induct e); intros.
  - unfold WellScoped, WellScopedVar, exprFreeVars in *.
    unfold Base.op_z2218U__.
    unfold exprFVs.
    unfold Base.op_z2218U__.
    destruct (lookupVarSet vs v) eqn:Hl.
    unfold FV.fvVarSet, Base.op_z2218U__,
    FV.fvVarListVarSet, FV.filterFV, expr_fvs,
    FV.unitFV.
Admitted.


(** *** Freshness *)

Axiom WellScopedVar_extendVarSetList_l:
  forall v vs1 vs2,
  WellScopedVar v vs1 ->
  elemVarSet v (mkVarSet vs2) = false ->
  WellScopedVar v (extendVarSetList vs1 vs2).
  

Axiom WellScopedVar_extendVarSetList_r:
  forall v vs1 vs2,
  In v vs2 ->
  NoDup (map varUnique vs2) ->
  WellScopedVar v (extendVarSetList vs1 vs2).


Lemma WellScoped_extendVarSet_fresh:
  forall v e vs,
  elemVarSet v (exprFreeVars e) = false ->
  WellScoped e (extendVarSet vs v) <-> WellScoped e vs.
Proof.
  intros.
  split.
  intro h.
  pose (K := WellScoped_subset e _ h). clearbody K.
  set (fve := exprFreeVars e) in *.
  
  unfold_VarSet.

  set (key := Unique.getWordKey (Unique.getUnique v)) in *.
Admitted.  

Axiom WellScoped_extendVarSetList_fresh:
  forall vs e vs1,
  disjointVarSet (exprFreeVars e) (mkVarSet vs) = true ->
  WellScoped e (extendVarSetList vs1 vs) <-> WellScoped e vs1.


Axiom WellScoped_extendVarSetList:
  forall vs e vs1,
  disjointVarSet vs1 (mkVarSet vs) = true ->
  WellScoped e vs1 -> WellScoped e (extendVarSetList vs1 vs).


Lemma WellScoped_extendVarSetList_fresh_under:
  forall vs1 vs2 e vs,
  disjointVarSet (exprFreeVars e) (mkVarSet vs1)  = true ->
  WellScoped e (extendVarSetList (extendVarSetList vs vs1) vs2) <-> WellScoped e (extendVarSetList vs vs2).
Proof.
  intros.
  rewrite <- WellScoped_mkLams.
  rewrite WellScoped_extendVarSetList_fresh.
  rewrite -> WellScoped_mkLams.
  reflexivity.
  rewrite exprFreeVars_mkLams.
  eapply disjointVarSet_subVarSet_l; only 1: eassumption.
  apply subVarSet_delVarSetList.
Qed.

