
(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From Coq Require Import ssreflect ssrbool ssrfun.

Require Import GHC.Base.
Require Import GHC.Nat.
Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.
Require Import Proofs.Data.Foldable.
Require Import Proofs.GhcTactics.

Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import SetoidList.

Import ListNotations.

Open Scope Z_scope.


Set Bullet Behavior "Strict Subproofs".




(**
Some of this can migrate to [base-thy] at some point, but maybe some lemmas or
tactics are rather specific.
*)

Lemma eqlist_Foldable_elem : forall a (s s' : list a) `{EqLaws a}, 
      eqlistA (fun x y => x == y) s s' ->
      (forall a, Foldable.elem a s = Foldable.elem a s').
Proof.
  intros a s s' EQ EQL. intro H. induction H.
  intro x.
  rewrite elem_nil. auto.
  intro y. 
  repeat rewrite -> elem_cons.
  rewrite IHeqlistA.
  erewrite eq_replace_r; eauto.
Qed.


Lemma elem_exists_in {a}`{Eq_ a} (x:a) (xs : list a) :  Foldable.elem x xs -> exists y, List.In y xs /\ (x == y).
Proof. 
   elim: xs => [|y ys IH].
   hs_simpl. done.
   hs_simpl.
   move => /orP.
   move => [h1| h2].
   exists y. unfold List.In. split; auto. 
   move: (IH h2) => [z [Inz eqz]].
   exists z. unfold List.In. split; auto. 
Qed.

Lemma list_in_elem {a} `{Base.EqLaws a} (x:a) xs: List.In x xs -> Foldable.elem x xs.
Proof. elim: xs => [|y ys IH]. hs_simpl. auto.
hs_simpl. simpl. intuition. subst. apply /orP. left. eapply Eq_refl.
Qed.



Lemma forallb_imp:
  forall a P Q (xs : list a),
  forallb P xs = true ->
  (forall x, P x = true -> Q x = true) ->
  forallb Q xs = true.
Proof.
  induction xs; simpl; intros; auto.
  apply andb_prop in H.
  apply andb_true_intro.
  intuition.
Qed.


Lemma contrapositive : forall (A B:Prop), (A -> B) -> (~ B) -> (~ A).
Proof.
  intros.
  intro h. apply H in h. apply H0. auto.
Qed.

Lemma and_iff_compat_both:
  forall A B C D : Prop,
    A <-> C -> B <-> D ->
    A /\ B <-> C /\ D.
Proof. intros. intuition. Qed.

Lemma unzip_fst {A B} l : forall (l0 : list A) (l1 : list B), List.unzip l = (l0, l1) -> List.map fst l = l0.
Proof. 
  induction l. 
  - simpl. move=> l0 l1 h. inversion h. auto.
  - move=> l0 l1. destruct a; simpl. 
    destruct (List.unzip l) eqn:LL.
    move=> h. inversion h. subst.
    f_equal. eapply IHl. eauto.
Qed.
