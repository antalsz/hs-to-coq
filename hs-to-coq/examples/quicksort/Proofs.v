Require Import QuickSort.
Require Import Prelude.

Require Import Coq.Lists.List.
Import ListNotations.

Inductive AlreadySorted {a} `{Ord a} : list a -> Prop :=
 | ASNil: AlreadySorted []
 | ASCons: forall x xs,
     AlreadySorted xs -> 
     Forall (fun y => (op_zl__ y x) = false) xs ->
     AlreadySorted (x::xs).

Axiom unroll_unsafe_fix: forall a (f : a -> a),
  unsafeFix f = f (unsafeFix f).


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
  forall xs, AlreadySorted xs -> quicksort xs = xs.
Proof.
  intros.
  induction H.
  * unfold quicksort.
    rewrite unroll_unsafe_fix. reflexivity.
  * change (quicksort (x :: xs) = [] ++ [x] ++ xs).
    unfold quicksort.
    rewrite unroll_unsafe_fix.
    rewrite Forall_partition by assumption.
    f_equal;[|f_equal].
    * rewrite unroll_unsafe_fix. reflexivity.
    * apply IHAlreadySorted.
Qed.
