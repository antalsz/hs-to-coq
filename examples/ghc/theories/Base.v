Require Import GHC.Base.
Require Import GHC.Nat.
Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

Require Import Coq.Lists.List.

Require Import Proofs.GhcTactics.

Import ListNotations.

Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

(**
Some of this can migrate to [base-thy] at some point, but maybe some lemmas or
tactics are rather specific.
*)

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



(*  Theory about foldable for lists *)

Ltac unfold_Foldable_foldr :=
  unfold Foldable.foldr,
  Foldable.foldr__,
  Foldable.Foldable__list,
  Foldable.Foldable__list_foldr.

Ltac unfold_Foldable_foldl' :=
  unfold Foldable.foldl',  Foldable.Foldable__list, 
  Foldable.foldl'__, Foldable.Foldable__list_foldl', foldl'.

Ltac unfold_Foldable_foldl :=
  unfold Foldable.foldl,  Foldable.Foldable__list, 
  Foldable.foldl__, Foldable.Foldable__list_foldl, foldl.


Lemma Foldable_foldr_app : forall a b (f:a -> b -> b) (s:b) 
                              (vs1 : list a) (vs2: list a),
    Foldable.foldr f s (vs1 ++ vs2) =
    Foldable.foldr f (Foldable.foldr f s vs2) vs1.
Proof.
  intros.
  unfold_Foldable_foldr.
  rewrite hs_coq_foldr_base.
  rewrite fold_right_app.
  auto.
Qed.

Lemma Foldable_foldl'_app : forall a b (f:b -> a -> b) (s:b) 
                              (vs1 : list a) (vs2: list a),
    Foldable.foldl' f s (vs1 ++ vs2) =
    Foldable.foldl' f (Foldable.foldl' f s vs1) vs2.
Proof.
  unfold_Foldable_foldl'.
  intros.
  repeat rewrite <- List_foldl_foldr.
  rewrite fold_left_app.
  auto.
Qed.

