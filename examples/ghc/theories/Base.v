
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



