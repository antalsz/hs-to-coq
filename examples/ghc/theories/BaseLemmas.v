Require Import GHC.Base.
Require Import GHC.Nat.
Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

Require Import Coq.Lists.List.

Require Import GhcProofs.Tactics.

Import ListNotations.

Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

(**
Some of this can migrate to [base-thy] at some point, but maybe some lemmas or
tactics are rather specific.
*)

Lemma reverse_append : forall A (vs1:list A) (vs0:list A)  a ,
  (List.reverse (a :: vs0) ++ vs1 = List.reverse vs0 ++ (a :: vs1)).
Proof.
  intros A.
  intros.
  rewrite hs_coq_reverse.
  rewrite hs_coq_reverse.
  rewrite <- List.rev_append_rev.
  rewrite <- List.rev_append_rev.
  simpl.
  auto.
Qed.


Lemma List_foldl_foldr:
  forall {a b} f (x : b) (xs : list a),
    fold_left f xs x = List.fold_right (fun x g a => g (f a x)) id xs x.
Proof.
  intros. revert x.
  induction xs; intro.
  * reflexivity.
  * simpl. rewrite IHxs. reflexivity.
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

Lemma snd_unzip:
  forall a b (xs : list (a * b)),
  snd (List.unzip xs) = map snd xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl. f_equal. apply IHxs.
Qed.

Lemma snd_unzip_map:
  forall a b c (f : a -> b) (g : a -> c) xs,
  snd (List.unzip (map (fun x => (f x, g x)) xs)) = map g xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl. f_equal. apply IHxs.
Qed.


Lemma zip_unzip_map:
  forall a b c (f : b -> c) (xs : list (a * b)),
  List.zip (fst (List.unzip xs)) (Base.map f (snd (List.unzip xs)))
  = map (fun '(x,y) => (x, f y)) xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl. f_equal. apply IHxs.
Qed.

Lemma flat_map_unpack_cons_f:
  forall (A B C : Type) (f : A -> B -> C ) (xs : list (A * B)),
   flat_map (fun '(x,y) => [f x y]) xs = map (fun '(x,y) => f x y) xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl. repeat expand_pairs. simpl.
    f_equal. apply IHxs.
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

