(** * Verification of [Data.List.sort] *)


Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Lists.List.
Import ListNotations.

(* Basic Haskell libraries *)
Require Import GHC.Base      Proofs.GHC.Base.
Import GHC.Base.Notations.
Require Import Data.OldList  Proofs.Data.OldList.

Require Import Tactics.

(* Working with Haskell *)
Require Import OrdTactic.

Set Bullet Behavior "Strict Subproofs".

(** ** [sort] is a permutation of its input *)

Section Permutation.
Context {a} (cmp : a -> a -> comparison).


Program Fixpoint descending_asscending_permutation
  (ys : list a) { measure (length ys) } :
  (forall x xs, Permutation (List.concat (descending cmp x xs ys))      (xs ++ x :: ys)) /\
  (forall x xs, Permutation (List.concat (ascending cmp x (app xs) ys)) (xs ++ x :: ys)) := _.
Next Obligation.
  rename descending_asscending_permutation into IH.
  destruct ys.
  * split; intros.
    + simpl. rewrite app_nil_r.
      apply Permutation_cons_append.
    + simpl.  rewrite app_nil_r. reflexivity.
  * split; intros.
    + simpl.
      destruct_match.
      - etransitivity; only 1: (apply IH; simpl; omega).
        apply Permutation_middle.
      - simpl.
        etransitivity; only 1: apply Permutation_middle.
        apply Permutation_app_head.
        apply perm_skip.
        destruct_match.
        ** reflexivity.
        ** destruct_match.
           ++ apply IH; simpl; omega.
           ++ replace (fun y : list a => a0 :: y) with (app [a0]) by (simpl; reflexivity).
              apply IH; simpl; omega.
    + simpl.
      destruct_match.
      - replace ((fun arg_54__ : list a => xs ++ x :: arg_54__)) with (app (xs ++ [x]))
          by (extensionality r; rewrite <- app_assoc; reflexivity).
        etransitivity; only 1: (apply IH; simpl; omega).
        rewrite <- app_assoc.
        reflexivity.
      - simpl.
        rewrite <- app_assoc. simpl.
        apply Permutation_app_head.
        apply perm_skip.
        destruct_match.
        ** reflexivity.
        ** destruct_match.
           ++ apply IH; simpl; omega.
           ++ replace (fun y : list a => a0 :: y) with (app [a0]) by (simpl; reflexivity).
              apply IH; simpl; omega.
Qed.

Lemma ascending_permutation:
  forall x xs (ys : list a),
  Permutation (List.concat (ascending cmp x (app xs) ys)) (xs ++ x :: ys).
Proof. intros. apply descending_asscending_permutation. Qed.

Lemma descending_permutation:
  forall x (xs ys : list a),
  Permutation (List.concat (descending cmp x xs ys)) (xs ++ x :: ys).
Proof. intros. apply descending_asscending_permutation. Qed.


Lemma sequences_permutation:
  forall  (xs : list a), Permutation (List.concat (sequences cmp xs)) xs.
Proof.
  intros.
  unfold sequences.
  repeat destruct_match.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * apply descending_permutation.
  * replace (fun y : list a => a0 :: y) with (app [a0]) by (simpl; reflexivity).
    apply ascending_permutation.
Qed.

Lemma mergeAll_eq: forall xs ys zss,
  mergeAll cmp (xs :: ys :: zss) = mergeAll cmp (mergePairs cmp (xs :: ys :: zss)).
Proof.
  intros.
  unfold mergeAll at 1. unfold mergeAll_func.
  lazymatch goal with 
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs => 
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.

Lemma merge_permutation:
  forall xs ys,
  Permutation (merge cmp xs ys) (xs ++ ys).
Proof.
  induction xs.
  * destruct ys; reflexivity.
  * simpl.
    induction ys.
    + simpl. rewrite app_nil_r. reflexivity.
    + simpl.
      destruct_match.
      - replace (a0 :: xs ++ a1 :: ys) with ((a0 :: xs) ++ a1 :: ys) by reflexivity.
        etransitivity; only 2: apply Permutation_middle.
        apply perm_skip.
        simpl.
        apply IHys.
      - replace (a0 :: xs ++ a1 :: ys) with ((a0 :: xs) ++ a1 :: ys) by reflexivity.
        apply perm_skip.
        apply IHxs.
Qed.

Program Fixpoint mergePairs_permutation
  (xss : list (list a)) { measure (length xss) } :
  Permutation (List.concat (mergePairs cmp xss)) (List.concat xss) := _.
Next Obligation.
  intros.
  destruct xss as [|xs[|ys zss]].
  * reflexivity.
  * reflexivity.
  * simpl.
    rewrite app_assoc.
    apply Permutation_app.
    - apply merge_permutation.
    - apply mergePairs_permutation; simpl; omega.
Qed.

Program Fixpoint mergeAll_permutation
  (xss : list (list a)) { measure (length xss) } :
  Permutation (mergeAll cmp xss) (List.concat xss) := _.
Next Obligation.
  destruct xss as [|xs[|ys zss]].
  * reflexivity.
  * simpl. rewrite app_nil_r. reflexivity.
  * rewrite mergeAll_eq.
    etransitivity; only 1: apply mergeAll_permutation. {
      pose proof (mergePairs_length (length zss) _ cmp zss xs ys).
      apply H.
      omega.
    }
    apply mergePairs_permutation.
Qed.


Lemma sortBy_permutation:
  forall  (xs : list a), Permutation (sortBy cmp xs) xs.
Proof.
  intros.
  unfold sortBy.
  etransitivity.
  apply mergeAll_permutation.
  apply sequences_permutation.
Qed.

End Permutation.

Theorem sort_permutation:
  forall a `(Ord a) (xs : list a), Permutation (sort xs) xs.
Proof.
  intros.
  apply sortBy_permutation.
Qed.
