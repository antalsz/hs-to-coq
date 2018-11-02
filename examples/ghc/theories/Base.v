
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

(* I would love to be able to use rewriting instead of this 
   lemma to do this. Why doesn't it work??? *)
Lemma eq_replace_r : forall {a}`{EqLaws a}  (v1 v2 v3 : a),
    (v2 == v3) -> (v1 == v2) = (v1 == v3).
Proof.
  intros.
  rewrite -> H1. (* why does the ssreflect rewriting tactic not work here. *)
  reflexivity.
Qed.

Lemma eq_replace_l : forall {a}`{EqLaws a} (v1 v2 v3 : a),
    (v2 == v3) -> (v2 == v1) = (v3 == v1).
Proof.
  intros.
  eapply Eq_m.
  eauto.
  eapply Eq_refl.
Qed.


(* Some cargo culting here. I'm not sure if we need to do all of this.*)

Local Lemma parametric_eq_trans : forall (a : Type) (H : Eq_ a),
  EqLaws a -> Transitive (fun x y : a => x == y).
Proof.
  intros.
  intros x y z.
  pose (k := Eq_trans).
  eapply k.
Defined. 

Local Lemma parametric_eq_sym : forall (a : Type) (H : Eq_ a),
  EqLaws a -> Symmetric (fun x y : a => x == y).
Proof.
  intros.
  intros x y.
  rewrite Eq_sym.
  auto.
Defined. 


Add Parametric Relation {a}`{H: EqLaws a} : a 
  (fun x y => x == y) 
    reflexivity proved by Eq_refl 
    symmetry proved by (@parametric_eq_sym a _ H)
    transitivity proved by (@parametric_eq_trans a _ H) as parametric_eq.

Instance: RewriteRelation (fun x y => x == y).


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


(**
Some of this can migrate to [base-thy] at some point, but maybe some lemmas or
tactics are rather specific.
*)

Lemma elem_eq : forall {A:Type}`{EqLaws A} (xs : list A) (a b : A),
    a == b -> Foldable.elem a xs = Foldable.elem b xs.
Proof.
  move => A ??.
  elim => // x xs IH.
  move => a b h.
  hs_simpl.
  rewrite (IH _ _ h).
  erewrite eq_replace_l; eauto.
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


Lemma forM_map:
  forall (m : Type -> Type) (a b c : Type) `{Monad m}
  (xs : list a) (act : b -> m c) (f : a -> b),
  Traversable.forM (map f xs) act = Traversable.forM xs (fun x => act (f x)).
Proof.
  intros.
  induction xs.
  * reflexivity.
  * cbv. f_equal. apply IHxs.
Qed.

Lemma forM_cong:
  forall {a m b} `{Monad m} (f g : a -> m b) (xs : list a),
  (forall x, In x xs -> f x = g x) ->
  Traversable.forM xs f = Traversable.forM xs g.
Proof.
  intros.
  rewrite <- forM_map with (act := fun x => x) (f := f).
  rewrite <- forM_map with (act := fun x => x) (f := g).
  f_equal.
  apply map_ext_in.
  assumption.
Qed.


