Require Import Core.
Require Import FV.
Require Import Proofs.ContainerAxioms.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetFSet.
Require Import Proofs.Var.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Require Import GHC.Base.
Import GHC.Base.ManualNotations.

Set Bullet Behavior "Strict Subproofs".

Reserved Notation "A ⊢ B" (at level 70, no associativity).
Inductive Denotes : VarSet -> FV -> Prop :=
| DenotesVarSet : forall vs fv,
    (forall f in_scope vs' l,
        extendVarSetList emptyVarSet l = vs' ->
        extendVarSetList emptyVarSet (fst (fv f in_scope (l, vs'))) =
        snd (fv f in_scope (l, vs')) /\
        snd (fv f in_scope (l, vs')) =
        unionVarSet (minusVarSet (filterVarSet f vs) in_scope) vs') ->
    vs ⊢ fv
where "A ⊢ B" := (Denotes A B).

Ltac unfold_uniqSet :=
  match goal with
  | |- context[match ?a with UniqSet.Mk_UniqSet _ => _ end] =>
    destruct a
  end.

Ltac unfold_UFM :=
  match goal with
  | |- context[match ?a with UniqFM.UFM _ => _ end] =>
    destruct a
  end.

Ltac unfold_fv := simpl; unfold_uniqSet; unfold_UFM.

Ltac destruct_match :=
  match goal with
  | |- context[match ?a with _ => _ end] =>
    let H := fresh "Hmatch" in
    destruct a eqn:H
  end.

Theorem Denotes_fvVarSet : forall m fv f in_scope l vs,
    m ⊢ fv ->
    extendVarSetList emptyVarSet l = vs ->
    snd (fv f in_scope (l, vs)) =
    unionVarSet (minusVarSet (filterVarSet f m) in_scope) vs.
Proof.
  intros. inversion H.
  specialize (H1 f in_scope vs l ); subst.
  apply H1; reflexivity.
Qed.

Definition WF_fv (fv : FV) : Prop := exists vs, vs ⊢ fv.

Lemma elemVarSet_neq :
  forall x y vs,
    elemVarSet x vs = true ->
    elemVarSet y vs = false ->
    x == y = false.
Proof.
  intros. apply not_true_is_false. intro. revert H. revert H0.
  unfold elemVarSet, UniqSet.elementOfUniqSet; destruct vs.
  unfold UniqFM.elemUFM; destruct u. intro H.
  rewrite member_eq with (k':=(Unique.getWordKey (Unique.getUnique x))) in H.
  - rewrite H. discriminate.
  - simpl. rewrite <- realUnique_eq in H1. cbn in H1.
    apply Nat.eqb_eq in H1. rewrite H1. cbn. apply N.eqb_refl.
Qed.

Lemma elemVarSet_extendVarSet :
  forall x y vs,
    x == y = false ->
    elemVarSet x vs = false ->
    elemVarSet x (extendVarSet vs y) = false.
Proof.
  intros. unfold extendVarSet, UniqSet.addOneToUniqSet. revert H0.
  destruct vs. unfold elemVarSet, UniqSet.elementOfUniqSet.
  unfold UniqFM.addToUFM, UniqFM.elemUFM. destruct u. intros Hmem.
  rewrite member_insert. apply orb_false_iff; split; [ | assumption].
  apply not_true_is_false. intro.
  cbn in H0. cbn in H. apply N.eqb_eq in H0. apply Nat2N.inj in H0.
  rewrite <- Nat.eqb_eq in H0. rewrite H in H0. discriminate.
Qed.

Lemma empty_FV_WF :
  WF_fv emptyFV.
Proof.
  unfold WF_fv. exists emptyVarSet. constructor; intros; subst.
  unfold_fv. rewrite difference_nil_l, <- mkVarSet_extendVarSetList.
  unfold_fv. intuition. do 2 f_equal. symmetry. apply union_nil_r.
Qed.

Lemma unit_FV_WF :
  forall x, WF_fv (unitFV x).
Proof.
  intros. unfold WF_fv.
  exists (unitVarSet x).
  constructor; intros; subst. simpl.
  destruct_match; simpl.
  - unfold_fv. rewrite <- mkVarSet_extendVarSetList.
    destruct_match; unfold_fv; repeat f_equal.
    + admit. (* should be true *)
    + rewrite difference_nil_l, union_nil_r. intuition.
  - destruct_match; simpl.
    + unfold_fv. rewrite <- mkVarSet_extendVarSetList.
      destruct_match; unfold_fv; repeat f_equal.
      * admit.
      * rewrite difference_nil_l, union_nil_r. intuition.
    + destruct_match.
      * unfold_fv. rewrite <- mkVarSet_extendVarSetList.
        unfold_fv. simpl. repeat f_equal. admit.
      * unfold_fv. rewrite <- mkVarSet_extendVarSetList.
        unfold_fv. repeat f_equal.
        rewrite difference_nil_l, union_nil_r. intuition.
Admitted.

Ltac unfold_WF :=
  repeat match goal with
  | [ H : WF_fv ?fv |- _] =>
    let vs := fresh "vs" in
    let Hd := fresh "Hdenotes" in
    inversion H as [vs Hd]; inversion Hd; subst; clear H
  | [ |- WF_fv ?fv ] =>
    unfold WF_fv
  end.

Lemma filter_FV_WF : forall f x,
    WF_fv x -> WF_fv (filterFV f x).
Proof.
  intros. unfold_WF.
  exists (filterVarSet f vs). constructor; intros.
  unfold filterFV.
  specialize (H0 (fun v : Var => f0 v && f v) in_scope vs' l H).
  destruct H0. intuition.
  rewrite H1. rewrite <- filterVarSet_comp. reflexivity.
Qed.

Lemma del_FV_WF : forall fv v,
    WF_fv fv -> WF_fv (delFV v fv).
Proof.
  intros. unfold_WF.
  exists (delVarSet vs v). constructor; intros. unfold delFV.
  specialize (H0 f (extendVarSet in_scope v) vs' l H).
  destruct H0. intuition. rewrite H1.
  (* Seems true. Need theorems from [VarSet]. *)
Admitted.

Lemma union_FV_WF : forall fv fv',
    WF_fv fv -> WF_fv fv' -> WF_fv (unionFV fv fv').
Proof.
  intros. unfold_WF.
  exists (unionVarSet vs vs0). constructor; intros.
  unfold unionFV.
  specialize (H1 f in_scope vs' l H). destruct H1.
  remember (fv' f in_scope (l, vs')) as vs_mid.
  specialize (H0 f in_scope (snd vs_mid) (fst vs_mid) H1); destruct H0.
  replace vs_mid with (fst vs_mid, snd vs_mid); [| destruct vs_mid; reflexivity].
  intuition. rewrite H3. rewrite H2.
Admitted.
  
Lemma union_empty_l : forall fv, FV.unionFV FV.emptyFV fv = fv.
Proof. reflexivity. Qed.

Lemma union_empty_r : forall fv, FV.unionFV fv FV.emptyFV = fv.
Proof. reflexivity. Qed.
