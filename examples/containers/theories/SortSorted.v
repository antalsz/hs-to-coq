(** * Verification of [Data.List.sort] *)


Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.

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

(** ** Unrolling lemmas *)


Lemma mergeAll_singleton: forall a cmp (xs : list a),
  mergeAll cmp [xs] = xs.
Proof.
  intros.
  unfold mergeAll at 1. unfold mergeAll_func.
  lazymatch goal with 
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs => 
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.


Lemma mergeAll_eq: forall a cmp (xs : list a) ys zss,
  mergeAll cmp (xs :: ys :: zss) = mergeAll cmp (mergePairs cmp (xs :: ys :: zss)).
Proof.
  intros.
  unfold mergeAll at 1. unfold mergeAll_func.
  lazymatch goal with 
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs => 
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.


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

Lemma sequences_permutation:
  forall  (xs : list a), Permutation (List.concat (sequences cmp xs)) xs.
Proof.
  intros.
  unfold sequences.
  repeat destruct_match.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * apply descending_asscending_permutation.
  * replace (fun y : list a => a0 :: y) with (app [a0]) by (simpl; reflexivity).
    apply descending_asscending_permutation.
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

(** ** [sort] is sorted *)

Lemma LocallySorted_snoc:
  forall a lt xs x (y : a),
  LocallySorted lt (xs ++ [x]) ->
  lt x y ->
  LocallySorted lt ((xs ++ [x]) ++ [y]).
Proof.
  intros.
  remember (xs ++ [x]) as ys.
  revert xs Heqys.
  induction H; intros xs Heqys.
  * exfalso. eapply app_cons_not_nil. eassumption.
  * 
    assert (xs = []). {
      destruct xs; try reflexivity.
      inversion Heqys.
      exfalso. eapply app_cons_not_nil. eassumption.
    }
    subst.
    simpl in *. inversion Heqys. subst.
    constructor. constructor. assumption.
  * destruct xs; inversion Heqys; subst; clear Heqys.
    specialize (IHLocallySorted _ H4).
    destruct xs; inversion H4; subst; clear H4; simpl in *.
    + repeat (assumption || constructor).
    + repeat (assumption || constructor).
Qed.

Section Sorted.
Context {a} (cmp : a -> a -> comparison).
Context (le : a -> a -> Prop).

Variable cmp_Gt_false : forall a b, (eq_comparison (cmp a b) Gt = false -> le a b).
Variable cmp_Gt_true : forall a b, (eq_comparison (cmp a b) Gt = true -> le b a).

Local Infix "<=" := le.

Ltac destruct_le :=
  lazymatch goal with |- context[eq_comparison (cmp ?x ?y) Gt] =>
    let H := fresh "Hle" in
    destruct (eq_comparison (cmp x y) Gt) eqn:H;
    [ apply cmp_Gt_true in H | apply cmp_Gt_false in H ]
  end.


Program Fixpoint descending_asscending_sorted
  (ys : list a) { measure (length ys) } :
  (forall x xs, LocallySorted le (x :: xs) -> Forall (LocallySorted le) (descending cmp x xs ys)) /\
  (forall x xs, LocallySorted le (xs ++ [x]) -> Forall (LocallySorted le) (ascending cmp x (app xs) ys)) := _.
Next Obligation.
  rename descending_asscending_sorted into IH.
  destruct ys.
  * split; intros.
    + simpl. constructor. assumption. constructor. constructor. constructor.
    + simpl. constructor. assumption. constructor. constructor. constructor.
  * split; intros.
    + simpl.
      destruct_le.
      - apply IH; only 1: (simpl; omega).
        constructor; assumption.
      - constructor. assumption.
        destruct_match.
        ** constructor. constructor. constructor.
        ** destruct_le.
           ++ apply IH; only 1: (simpl; omega).
              constructor. constructor. assumption.
           ++ replace (fun y : list a => a0 :: y) with (app [a0]) by (simpl; reflexivity).
              apply IH; only 1: (simpl; omega).
              constructor. constructor. assumption.
    + simpl.
      rewrite if_negb.
      destruct_le.
      - constructor. assumption.
        destruct_match.
        ** constructor. constructor. constructor.
        ** destruct_le.
           ++ apply IH; only 1: (simpl; omega).
              constructor. constructor. assumption.
           ++ replace (fun y : list a => a0 :: y) with (app [a0]) by (simpl; reflexivity).
              apply IH; only 1: (simpl; omega).
              constructor. constructor. assumption.
      - replace ((fun arg_54__ : list a => xs ++ x :: arg_54__)) with (app (xs ++ [x]))
          by (extensionality r; rewrite <- app_assoc; reflexivity).
        apply IH; only 1: (simpl; omega).
        apply LocallySorted_snoc; assumption.
Qed.

Lemma sequences_sorted:
  forall  (xs : list a), Forall (LocallySorted le) (sequences cmp xs).
Proof.
  intros.
  unfold sequences.
  repeat (destruct_le || destruct_match).
  * simpl. repeat constructor.
  * simpl. repeat constructor.
  * apply descending_asscending_sorted.
    repeat (assumption || constructor).
  * replace (fun y : list a => a0 :: y) with (app [a0]) by (simpl; reflexivity).
    apply descending_asscending_sorted.
    repeat (assumption || constructor).
Qed.

Lemma merge_sorted:
  forall xs ys,
  Sorted le xs ->
  Sorted le ys ->
  Sorted le (merge cmp xs ys).
Proof.
  intros.
  revert ys H0.
  induction H.
  * destruct ys; intros; repeat (assumption || constructor).
  * simpl.
    intros.
    induction H1.
    + repeat (assumption || constructor).
    + simpl.
      destruct_le.
      - constructor.
        apply IHSorted0.
        (* a bit ugly to do this here *)
        clear -H2 Hle le cmp_Gt_false cmp_Gt_true.
        induction H2.
        ++ repeat (assumption || constructor).
        ++ destruct_le.
           ** repeat (assumption || constructor).
           ** constructor. repeat (assumption || constructor). 
      - constructor.
        apply IHSorted.
        constructor.
        assumption.
        assumption.
        destruct l as [| x l]; simpl.
        ++ constructor; assumption.
        ++ destruct (eq_comparison _ _); constructor.
           ** assumption.
           ** inversion H0; assumption.
Qed.

Program Fixpoint mergePairs_sorted
  (xss : list (list a)) { measure (length xss) } :
  Forall (Sorted le) xss -> Forall (Sorted le) (mergePairs cmp xss) := _.
Next Obligation.
  intros.
  destruct xss as [|xs[|ys zss]].
  * repeat (assumption || constructor).
  * repeat (assumption || constructor).
  * inversion_clear H. inversion_clear H1.
    constructor.
    apply merge_sorted; assumption.
    apply mergePairs_sorted; only 1: (simpl; omega).
    assumption.
Qed.

Program Fixpoint mergeAll_sorted
  (xss : list (list a)) { measure (length xss) } :
  Forall (Sorted le) xss -> Sorted le (mergeAll cmp xss) := _.
Next Obligation.
  destruct xss as [|xs[|ys zss]].
  * repeat (assumption || constructor).
  * inversion_clear H. rewrite mergeAll_singleton. assumption.
  * rewrite mergeAll_eq.
    apply mergeAll_sorted. {
      pose proof (mergePairs_length (length zss) _ cmp zss xs ys).
      apply H0.
      omega.
    }
    apply mergePairs_sorted.
    assumption.
Qed.

Lemma Forall_Sorted_LocallySorted_iff:
  forall a lt (xs : list (list a)),
  Forall (Sorted lt) xs <-> Forall (LocallySorted lt) xs.
Proof.
  intros.
  split; intro.
  * rewrite Forall_forall in *.
    intros x Hx. specialize (H x Hx).
    rewrite Sorted_LocallySorted_iff in *.
    assumption.
  * rewrite Forall_forall in *.
    intros x Hx. specialize (H x Hx).
    rewrite Sorted_LocallySorted_iff in *.
    assumption.
Qed.

Lemma sortBy_sorted:
  forall  (xs : list a), Sorted le (sortBy cmp xs).
Proof.
  intros.
  unfold sortBy.
  apply mergeAll_sorted.
  rewrite Forall_Sorted_LocallySorted_iff.
  apply sequences_sorted.
Qed.

End Sorted.


Theorem sort_sorted:
  forall a `(Ord a) `(OrdLaws a) (xs : list a), Sorted (fun x y => x <= y = true) (sort xs).
Proof.
  intros.
  apply sortBy_sorted.
  * intros x y ?. destruct (compare x y) eqn:?; simpl in *; try congruence; try solve [order a].
  * intros x y ?. destruct (compare x y) eqn:?; simpl in *; try congruence; try solve [order a].
Qed.

(** ** [sort] is stable *)

(** Now I am lazy and I only prove it for when [cmp] is a lawful [compare] *)

(** Also, this proof is not the most pretty in the world, but it was late, and it works.*)

Section Stable.
Context {a} `{Hord : OrdLaws a}.

(** We define a sorte stable when it it does not change the all subsequence of 
    equivalent elements, which we can conveniently describe using filter.
 *)
Definition Stable (xs ys : list a) :=
  forall x, filter (fun y => x == y) xs = filter (fun y => x == y) ys.

(** Some lemmas to work with [Stable] without going down to the level of [filter]. *)

Lemma filter_app: forall a p (xs : list a) ys,
  filter p (xs ++ ys) = filter p xs ++ filter p ys.
Proof. intros. induction xs; simpl; try rewrite IHxs; try destruct_match; reflexivity. Qed.

Lemma Stable_app : forall xs ys xs' ys',
  Stable xs xs' -> Stable ys ys' -> Stable (xs ++ ys) (xs' ++ ys').
Proof.
  intros ???????.
  specialize (H x).
  specialize (H0 x).
  rewrite !filter_app.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma Stable_cons : forall x ys ys',
  Stable ys ys' -> Stable (x :: ys) (x :: ys').
Proof.
  intros ?????.
  specialize (H x0).
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma Stable_refl : forall xs, Stable xs xs.
Proof. intros ??. reflexivity. Qed.

Theorem Stable_sym : forall l l' : list a,
 Stable l l' -> Stable l' l.
Proof.
  intros ????.
  symmetry.
  apply H.
Qed.

Theorem Stable_trans : forall l l' l'' : list a,
 Stable l l' -> Stable l' l'' -> Stable l l''.
Proof.
  intros ??????.
  etransitivity.
  apply H.
  apply H0.
Qed.

Instance Stable_Equivalence : Equivalence Stable | 10 := {
  Equivalence_Reflexive := @Stable_refl ;
  Equivalence_Symmetric := @Stable_sym ;
  Equivalence_Transitive := @Stable_trans }.


Definition le: a -> a -> Prop := fun x y => (x <= y = true).
Definition lt : a -> a -> Prop := fun x y => (x < y = true).
Definition gt : a -> a -> Prop := fun x y => (x > y = true).


Lemma Stable_cons_app_lt:
  forall x xs,
  Forall (lt x) xs ->
  Stable (x :: xs) (xs ++ [x]).
Proof.
  intros ??? y.
  simpl.
  rewrite filter_app. simpl.
  destruct (y == x) eqn:?.
  * enough (Htmp : filter (fun y0 : a => _GHC.Base.==_ y y0) xs = []) by (rewrite Htmp; reflexivity).
    induction xs.
    + reflexivity.
    + simpl.
      destruct_match.
      - exfalso.
        inversion H; subst; clear H.
        unfold lt in *.
        order a.
      - apply IHxs.
        inversion H; subst; clear H.
        assumption.
  * rewrite app_nil_r.
    reflexivity.
Qed.


Lemma lt_sorted_stable_cons:
  forall x xs,
  LocallySorted lt (x :: xs) ->
  Stable (x :: xs) (xs ++ [x]).
Proof.
  intros ???.
  apply Stable_cons_app_lt.
  induction xs.
  * constructor.
  * inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    repeat (constructor || assumption).
    repeat (constructor || assumption).
    unfold lt in *; order a.
    lapply IHxs.
    intro. inversion H. assumption.
    repeat (constructor || assumption).
    unfold lt in *; order a.
Qed.


Program Fixpoint descending_ascending_stable
  (ys : list a) { measure (length ys) } :
  (forall x xs, LocallySorted lt (x :: xs) ->
                Stable (List.concat (descending compare x xs ys))      (xs ++ x :: ys)) /\
  (forall x xs, Stable (List.concat (ascending compare x (app xs) ys)) (xs ++ x :: ys)) := _.
Next Obligation.
  rename descending_ascending_stable into IH.
  destruct ys.
  * split; intros.
    + simpl. rewrite app_nil_r. apply lt_sorted_stable_cons. assumption.
    + simpl. rewrite app_nil_r. reflexivity.
  * split; intros.
    + simpl.
      destruct_match.
      - assert (a0 < x = true) by (destruct (compare x a0) eqn:?; simpl in Heq; try congruence; order a).
        clear Heq.
        assert (LocallySorted lt (a0 :: x :: xs)) by (constructor; assumption).
        etransitivity.
        ++ apply IH; only 1: (simpl; omega). assumption.
        ++ replace (xs ++ x :: a0 :: ys) with ((xs ++ [x]) ++ a0 :: ys)
             by (rewrite <- app_assoc; reflexivity).
           apply Stable_app; try reflexivity.
           apply lt_sorted_stable_cons. assumption.
      - replace (xs ++ x :: a0 :: ys) with ((xs ++ [x]) ++ a0 :: ys)
             by (rewrite <- app_assoc; reflexivity).
        change (Stable ((x :: xs) ++ List.concat (match ys with
           | [] => [a0 :: ys]
           | b :: xs0 =>
               if eq_comparison (compare a0 b) Gt
               then descending compare b [a0] xs0
               else ascending compare b (fun y : list a => a0 :: y) xs0
           end)) ((xs ++ [x]) ++ a0 :: ys)).
        apply Stable_app.
        ++ apply lt_sorted_stable_cons. assumption.
        ++ destruct_match.
           ** reflexivity.
           ** destruct_match.
              -- assert (a1 < a0 = true) by (destruct (compare a0 a1) eqn:?; simpl in *; try congruence; order a).
                 apply IH; only 1: (simpl; omega).
                 repeat (assumption||constructor).
              -- replace (fun y : list a => a0 :: y) with (app [a0]) by (simpl; reflexivity).
                 apply IH; only 1: (simpl; omega).
    + simpl.
      destruct_match.
      - replace ((fun arg_54__ : list a => xs ++ x :: arg_54__)) with (app (xs ++ [x]))
          by (extensionality r; rewrite <- app_assoc; reflexivity).
        etransitivity; only 1: (apply IH; simpl; omega).
        rewrite <- app_assoc.
        reflexivity.
      - simpl.
        rewrite <- app_assoc. simpl.
        apply Stable_app; try reflexivity.
        apply Stable_cons; try reflexivity.
        destruct_match.
        ** reflexivity.
        ** destruct_match.
           ++ assert (a1 < a0 = true) by (destruct (compare a0 a1) eqn:?; simpl in *; try congruence; order a).
              apply IH; only 1: (simpl; omega).
              repeat (assumption||constructor).
           ++ replace (fun y : list a => a0 :: y) with (app [a0]) by (simpl; reflexivity).
              apply IH; simpl; omega.
Qed.

Lemma sequences_stable:
  forall  (xs : list a), Stable (List.concat (sequences compare xs)) xs.
Proof.
  intros.
  unfold sequences.
  repeat destruct_match.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * eapply descending_ascending_stable.
    assert (a1 < a0 = true) by (destruct (compare a0 a1) eqn:?; simpl in *; try congruence; order a).
    repeat (assumption||constructor).
  * replace (fun y : list a => a0 :: y) with (app [a0]) by (simpl; reflexivity).
    apply descending_ascending_stable.
Qed.


Lemma merge_stable:
  forall xs ys,
  LocallySorted le xs ->
  Stable (merge compare xs ys) (xs ++ ys).
Proof.
  induction xs.
  * destruct ys; reflexivity.
  * simpl.
    induction ys; intro.
    + simpl. rewrite app_nil_r. reflexivity.
    + simpl.
      destruct_match.
      - assert (a1 < a0 = true) by (destruct (compare a0 a1) eqn:?; simpl in *; try congruence; order a).
        assert (Forall (lt a1) (a0 :: xs)). {
          clear - Hord H H0.
          induction xs.
          * constructor. assumption. constructor.
          * inversion H; subst; clear H.
            repeat (constructor || assumption).
            unfold lt, le in *. order a.
            lapply IHxs.
            intros. inversion H. assumption. clear IHxs.
            destruct xs; constructor;
            inversion H3; subst; clear H3.
            assumption.
            unfold le in *. order a.
        } 
        etransitivity.
        ** apply Stable_cons.
           apply IHys. assumption.
        ** replace (a0 :: xs ++ a1 :: ys) with (((a0 :: xs) ++ [a1]) ++ ys) by (rewrite <- app_assoc; reflexivity).
           replace (a1 :: a0 :: xs ++ ys) with ((a1 :: a0 :: xs) ++ ys) by reflexivity.
           apply Stable_app; try reflexivity.
           apply Stable_cons_app_lt.
           assumption.
      - apply Stable_cons.
        apply IHxs.
        destruct xs. constructor.
        inversion H. assumption.
Qed.

Program Fixpoint mergePairs_stable
  (xss : list (list a)) { measure (length xss) } :
  Forall (LocallySorted le) xss ->
  Stable (List.concat (mergePairs compare xss)) (List.concat xss) := _.
Next Obligation.
  intros.
  destruct xss as [|xs[|ys zss]].
  * reflexivity.
  * reflexivity.
  * simpl.
    rewrite app_assoc.
    apply Stable_app.
    - apply merge_stable.
      inversion H.
      assumption.
    - apply mergePairs_stable; only 1: (simpl; omega).
      inversion H. inversion H3. assumption.
Qed.

Program Fixpoint mergeAll_stable
  (xss : list (list a)) { measure (length xss) } :
  Forall (Sorted le) xss ->
  Stable (mergeAll compare xss) (List.concat xss) := _.
Next Obligation.
  destruct xss as [|xs[|ys zss]].
  * reflexivity.
  * simpl. rewrite app_nil_r. reflexivity.
  * rewrite mergeAll_eq.
    etransitivity; only 1: apply mergeAll_stable. {
      pose proof (mergePairs_length (length zss) _ compare zss xs ys).
      apply H0.
      omega.
    }
    apply mergePairs_sorted.
    + intros x y ?. destruct (compare x y) eqn:?; unfold le in *; simpl in *; try congruence; try solve [order a].
    + intros x y ?. destruct (compare x y) eqn:?; unfold le in *; simpl in *; try congruence; try solve [order a].
    + assumption.
    + apply mergePairs_stable.
      rewrite Forall_Sorted_LocallySorted_iff in *.
      assumption.
Qed.



Lemma sortBy_stable:
  forall  (xs : list a), Stable (sortBy compare xs) xs.
Proof.
  intros.
  unfold sortBy.
  etransitivity.
  apply mergeAll_stable.
  rewrite Forall_Sorted_LocallySorted_iff in *.
  apply sequences_sorted.
  + intros x y ?. destruct (compare x y) eqn:?; unfold le in *; simpl in *; try congruence; try solve [order a].
  + intros x y ?. destruct (compare x y) eqn:?; unfold le in *; simpl in *; try congruence; try solve [order a].
  + apply sequences_stable.
Qed.

End Stable.

Theorem sort_stable:
  forall a `(OrdLaws a) (xs : list a), Stable (sort xs) xs.
Proof.
  intros.
  apply sortBy_stable.
Qed.
