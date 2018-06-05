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

(** * Well-formedness of [FV]s. *)

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

(** Many well-formedness theorems remain unproven. However, because
    the [WF] is definined based on [Denotes], which relates [FV]s to
    [VarSet]s, most of these theorems should be easily provable once
    we have some good theorems or tactics for [VarSet]s. *)

Lemma empty_FV_WF :
  WF_fv emptyFV.
Proof.
  unfold WF_fv. exists emptyVarSet. constructor; intros; subst.
  unfold_fv. rewrite difference_nil_l, <- mkVarSet_extendVarSetList.
  unfold_fv. intuition. do 2 f_equal. symmetry. apply union_nil_r.
Qed.

Lemma extendVarSetList_extendVarSet_iff: forall l x l',
  extendVarSetList (extendVarSet l' x) l =
  extendVarSet (extendVarSetList l' l) x.
Proof.
  induction l; intros x [l'].
  - reflexivity.
  - simpl.
    repeat rewrite extendVarSetList_cons.
    repeat rewrite IHl.
    clear IHl.
    unfold extendVarSetList,
         UniqSet.addListToUniqSet,
         UniqFM.addToUFM,
         UniqSet.addOneToUniqSet, Foldable.foldl',
         Foldable.Foldable__list, extendVarSet,
         UniqSet.addOneToUniqSet, Foldable.foldl',
         UniqFM.addToUFM.
    simpl.
    repeat destruct_match.
    simpl.
    unfold_VarSet.
    subst.
    admit.
Admitted.

Lemma unit_FV_WF :
  forall x, WF_fv (unitFV x).
Proof.
  intros. unfold WF_fv.
  exists (unitVarSet x).
  constructor; intros; subst. simpl.
  destruct_match; simpl; intuition;
    rewrite <- mkVarSet_extendVarSetList.
  - unfold_fv.
    destruct_match; unfold_fv.
    + do 2 f_equal.
      rewrite <-union_nil_r with (i:=i0).
      f_equal.
      * rewrite union_nil_r. reflexivity.
      * symmetry.
        simpl in Hmatch.
        rewrite difference_Tip_member; auto.
    + rewrite difference_nil_l, union_nil_r. intuition.
  - destruct_match; simpl; [auto|].
    destruct_match; simpl; [|auto].
    rewrite mkVarSet_extendVarSetList.
    rewrite extendVarSetList_cons.
    apply extendVarSetList_extendVarSet_iff.
  - unfold_fv.
    destruct_match; unfold_fv.
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

Lemma map_union_FV_WF : forall A f (ls : list A),
    (forall e, In e ls -> WF_fv (f e)) ->
    WF_fv (mapUnionFV f ls).
Proof.
  induction ls.
  - intros; unfold_WF. exists emptyVarSet. constructor; intros. simpl.
    intuition. unfold_fv. unfold_VarSet_to_IntMap.
    rewrite difference_nil_l, union_nil_r; reflexivity.
  - intros. simpl in H.
    assert (forall e : A, In e ls -> WF_fv (f e)). { intros. apply H. tauto. }
    apply IHls in H0.
    assert (WF_fv (f a)). { apply H; tauto. }
    unfold_WF. simpl. exists (unionVarSet vs vs0). constructor; intros.
    specialize (H2 f0 in_scope vs' l H0); destruct H2.
    remember (f a f0 in_scope (l, vs')) as vs_mid.
    specialize (H1 f0 in_scope (snd vs_mid) (fst vs_mid) H2). destruct H1.
    replace vs_mid with (fst vs_mid, snd vs_mid); [| destruct vs_mid; reflexivity].
    intuition. rewrite H4. rewrite H3.
Admitted.

Lemma unions_FV_WF : forall fvs,
    (forall fv, In fv fvs -> WF_fv fv) ->
    WF_fv (unionsFV fvs).
Proof.
  apply map_union_FV_WF.
Qed.

Lemma mkFVs_FV_WF : forall vs,
    WF_fv (mkFVs vs).
Proof.
  intros. apply map_union_FV_WF; intros. apply unit_FV_WF.
Qed.

Hint Resolve unit_FV_WF.
Hint Resolve empty_FV_WF.
Hint Resolve union_FV_WF.
Hint Resolve unions_FV_WF.
Hint Resolve del_FV_WF.
Hint Resolve mkFVs_FV_WF.

(** * Some other theroems about [FV]s. *)

Lemma union_empty_l : forall fv, FV.unionFV FV.emptyFV fv = fv.
Proof. reflexivity. Qed.

Lemma union_empty_r : forall fv, FV.unionFV fv FV.emptyFV = fv.
Proof. reflexivity. Qed.
