Require Import Core.
Require Import FV.
Require Import Proofs.ContainerAxioms.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Require Import GHC.Base.
Import GHC.Base.ManualNotations.

Set Bullet Behavior "Strict Subproofs".

Axiom realUnique_eq : forall x y,
    (x == y) = (realUnique x == realUnique y).

(** For simplicity, only consider deletion for now. *)
Definition WF_fv (fv : FV) : Prop :=
  forall f bs l vs,
    (forall x, elemVarSet x vs && elemVarSet x bs = false) ->
    let '(l', vs') := fv f bs (l, vs) in
    (forall x, elemVarSet x bs = true -> elemVarSet x vs' = false) /\
    (bs = emptyVarSet -> vs = vs').

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
  - simpl. rewrite realUnique_eq in H1. cbn in H1.
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
  cbn in H0. apply N.eqb_eq in H0. apply Nat2N.inj in H0.
  rewrite <- Nat.eqb_eq, <- realUnique_eq in H0. rewrite H in H0. discriminate.
Qed.  

Lemma unit_FV_WF :
  forall x, WF_fv (unitFV x).
Proof.
  unfold WF_fv; intros.
  destruct (unitFV x f bs (l, vs)) eqn:Hfv; intros.
  unfold unitFV in Hfv.
  destruct (elemVarSet x bs) eqn:Hin.
  - inversion Hfv; subst. split; [| reflexivity].
    intros x0 H'. specialize (H x0).
    apply andb_false_elim in H; destruct H; [assumption | congruence].
  - destruct (elemVarSet x vs) eqn:Hin'.
    + inversion Hfv; subst. split; [| reflexivity].
      intros. specialize (H x0).
      apply andb_false_elim in H; destruct H; [assumption | congruence].
    + destruct (f x) eqn:Hf.
      * inversion Hfv; subst. split.
        -- intros. specialize (H x0); apply andb_false_elim in H.
           destruct H; try congruence.
           apply (elemVarSet_neq _ _ _ H0) in Hin.
           apply elemVarSet_extendVarSet; try assumption.
        -- inversion Hfv; subst; assumption.
Qed.

Lemma union_empty_l : forall fv, FV.unionFV FV.emptyFV fv = fv.
Proof. reflexivity. Qed.

Lemma union_empty_r : forall fv, FV.unionFV fv FV.emptyFV = fv.
Proof. reflexivity. Qed.
