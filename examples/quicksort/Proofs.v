Require Import QuickSort.
Require Import Prelude.
Require Import GHC.DeferredFix.

Require Import Coq.Lists.List.
Import ListNotations.

Inductive AlreadySorted {a} `{Ord a} : list a -> Prop :=
 | ASNil: AlreadySorted []
 | ASCons: forall x xs,
     AlreadySorted xs -> 
     Forall (fun y => (op_zl__ y x) = false) xs ->
     AlreadySorted (x::xs).

Axiom unroll_deferred_fix: forall a r `{Default r} (f : (a -> r) -> (a -> r)),
  deferredFix1 f = f (deferredFix1 f).


Lemma Forall_partition:
  forall a p (xs : list a),
  Forall (fun y => (p y) = false) xs ->
  OldList.partition p xs = ([], xs).
Proof.
  intros.
  induction H.
  * reflexivity.
  * unfold OldList.partition in *.
    simpl in *. rewrite IHForall.
    unfold OldList.select.
    rewrite H. reflexivity.
Qed.


Theorem quicksort_already_sorted:
  forall a `(Ord a) (xs : list a),
  AlreadySorted xs -> quicksort xs = xs.
Proof.
  intros.
  induction H1.
  * unfold quicksort.
    rewrite unroll_deferred_fix. reflexivity.
  * change (quicksort (x :: xs) = [] ++ [x] ++ xs).
    unfold quicksort.
    rewrite unroll_deferred_fix.
    rewrite Forall_partition by assumption.
    f_equal;[|f_equal].
    + rewrite unroll_deferred_fix. reflexivity.
    + apply IHAlreadySorted.
Qed.

Require Import Coq.Sorting.Permutation.

Lemma partition_permutation:
  forall a p (xs ys zs : list a),
  OldList.partition p xs = (ys, zs) ->
  Permutation xs (ys ++ zs).
Proof.
  induction xs; intros.
  * simpl in *. inversion_clear H. constructor.
  * simpl in *. unfold OldList.select in *.
    destruct (p a0).
    - destruct (OldList.partition p xs) eqn:?.
      inversion H.
      apply Permutation_cons; [reflexivity|].
      apply IHxs.
      congruence.
    - destruct (OldList.partition p xs) eqn:?.
      inversion H.
      apply Permutation_cons_app.
      apply IHxs.
      congruence.
Qed.


Lemma Forall_partition_l:
  forall a p (xs ys zs : list a),
  OldList.partition p xs = (ys, zs) ->
  Forall (fun y => (p y) = true) ys.
Proof.
  induction xs; intros.
  * simpl in H. inversion H. auto.
  * simpl in *. unfold OldList.select in *.
    destruct (p a0) eqn:?.
    - destruct (OldList.partition p xs) eqn:?.
      inversion H. simpl.
      constructor; try assumption.
      apply (IHxs l zs).
      congruence.
    - destruct (OldList.partition p xs) eqn:?.
      inversion H. simpl.
      destruct zs. try congruence.
      apply (IHxs ys zs).
      congruence.
Qed.


Lemma Forall_partition_r:
  forall a p (xs ys zs : list a),
  OldList.partition p xs = (ys, zs) ->
  Forall (fun y => (p y) = false) zs.
Proof.
  induction xs; intros.
  * simpl in H. inversion H. auto.
  * simpl in *. unfold OldList.select in *.
    destruct (p a0) eqn:?.
    - destruct (OldList.partition p xs) eqn:?.
      inversion H. simpl.
      destruct ys. try congruence.
      apply (IHxs ys zs).
      congruence.
    - destruct (OldList.partition p xs) eqn:?.
      inversion H. simpl.
      constructor; try assumption.
      apply (IHxs ys l0).
      congruence.
Qed.

Lemma partition_length_l:
  forall a p (xs ys zs : list a),
  OldList.partition p xs = (ys, zs) ->
  Peano.le (length ys) (length xs).
Proof.
  induction xs; intros.
  * simpl in *. inversion_clear H. constructor.
  * simpl in *. unfold OldList.select in *.
    destruct (p a0).
    - destruct (OldList.partition p xs) eqn:?.
      inversion H.
      simpl.
      apply le_n_S.
      apply (IHxs l zs).
      congruence.
    - destruct (OldList.partition p xs) eqn:?.
      inversion H.
      destruct zs. try congruence.
      inversion H2.
      simpl.
      rewrite (IHxs ys zs).
      omega.
      congruence.
Qed.


Lemma partition_length_r:
  forall a p (xs ys zs : list a),
  OldList.partition p xs = (ys, zs) ->
  Peano.le (length zs) (length xs).
Proof.
  induction xs; intros.
  * simpl in *. inversion_clear H. constructor.
  * simpl in *. unfold OldList.select in *.
    destruct (p a0).
    - destruct (OldList.partition p xs) eqn:?.
      inversion H.
      destruct ys. try congruence.
      inversion H2.
      simpl.
      rewrite (IHxs ys zs).
      omega.
      congruence.
    - destruct (OldList.partition p xs) eqn:?.
      inversion H.
      simpl.
      apply le_n_S.
      apply (IHxs ys l0).
      congruence.
Qed.


Theorem quicksort_permutation:
  forall a `(Ord a) (xs : list a),
  Permutation  (quicksort xs) xs.
Proof.
  intros.
  remember (length xs) as n.
  generalize dependent xs.
  induction n using lt_wf_ind.
  intros.
  unfold quicksort.
  rewrite unroll_deferred_fix.
  destruct xs.
  * apply perm_nil.
  * destruct (OldList.partition (fun arg_1__ : a => _<_ arg_1__ a0) xs) eqn:?.
    simpl app.
    rewrite <- Permutation_middle.
    apply Permutation_cons; [reflexivity|].
    rewrite (partition_permutation _ _ _ _ _ Heqp).
    apply Permutation_app.
    - apply (H1 (length l)).
      + pose (partition_length_l _ _ _ _ _  Heqp).
        subst n. simpl.
        omega.
      + reflexivity.
    - apply (H1 (length l0)).
      + pose (partition_length_r _ _ _ _ _  Heqp).
        subst n. simpl.
        omega.
      + reflexivity.
Qed.

Require Import Coq.Sorting.Sorted.
Require Import Coq.Sets.Relations_1.
Require Import Coq.Lists.List.

Lemma Forall_app:
  forall a P (xs ys : list a),
  Forall P xs -> Forall P ys ->
  Forall P (xs ++ ys).
Proof.
  intros. induction xs; try assumption. constructor.
  inversion H; assumption.
  apply IHxs. inversion H; assumption.
Qed.

Lemma Forall_Permutation:
  forall a P (xs ys : list a),
  Forall P ys -> Permutation xs ys ->
  Forall P xs.
Proof.
  intros.
  induction H0.
  * auto.
  * constructor.
    + inversion_clear H. assumption.
    + apply IHPermutation. inversion_clear H. assumption.
  * inversion_clear H. inversion_clear H1.
    repeat (constructor; try assumption).
  * auto.
Qed.

Section sorted.
 Variable a : Type.
 Variable eq : Eq_ a.
 Variable ord : Ord a.
 
 Definition R x y := x < y = true.

 Variable trans : Transitive R.
 Variable total : forall a b, R a b \/ R b a.

Lemma StronglySorted_app_cons:
  forall (xs ys : list a) p,
  StronglySorted R xs ->
  StronglySorted R ys ->
  Forall (fun x => R x p) xs ->
  Forall (fun y => R p y) ys ->
  StronglySorted R (xs ++ p :: ys).
Proof.
  intros.
  induction xs.
  * simpl.
    apply SSorted_cons.
    - assumption.
    - assumption.
  * simpl. apply SSorted_cons.
    - apply IHxs.
      + inversion H; assumption.
      + inversion H1; assumption.
    - apply Forall_app.
      inversion_clear H; assumption.
      constructor.
      inversion_clear H1; assumption.
      refine (Forall_impl _ _ H2). intros.
      refine (trans _ _ _ _ H3).
      inversion_clear H1; assumption.
Qed.

Theorem quicksort_sorted:
  forall (xs : list a), StronglySorted R (quicksort xs).
Proof.
  intros.
  remember (length xs) as n.
  generalize dependent xs.
  induction n using lt_wf_ind.
  intros.
  unfold quicksort.
  rewrite unroll_deferred_fix.
  destruct xs.
  * apply SSorted_nil.
  * destruct (OldList.partition (fun arg_1__ : a => _<_ arg_1__ a0) xs) eqn:?.
    simpl app.
    apply StronglySorted_app_cons.
    - apply (H (length l)).
      + pose (partition_length_l _ _ _ _ _  Heqp).
        subst n. simpl.
        omega.
      + reflexivity.
    - apply (H (length l0)).
      + pose (partition_length_r _ _ _ _ _  Heqp).
        subst n. simpl.
        omega.
      + reflexivity.
    - refine (Forall_Permutation _ _ _ _ _ (quicksort_permutation _ _ _)).
      apply (Forall_partition_l _ _ _ _ _  Heqp).
    - refine (Forall_Permutation _ _ _ _ _ (quicksort_permutation _ _ _)).
      specialize (Forall_partition_r _ _ _ _ _  Heqp).
      apply Forall_impl.
      intros.
      destruct (total a0 a1); [assumption|congruence].
Qed.
End sorted.

Print Assumptions quicksort_sorted.