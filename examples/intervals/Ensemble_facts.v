Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Powerset_facts.


Lemma union_reorder:
  forall A s1 s2 s3 s4,
  Union A (Union A s1 s2) (Union A s3 s4) = 
  Union A (Union A s1 s3) (Union A s2 s4).
Proof.
  intros.
  repeat rewrite Union_associative.
  f_equal.
  repeat rewrite <- Union_associative.
  f_equal.
  apply Union_commutative.
Qed.

Lemma Disjoint_Intersection:
  forall A s1 s2, Disjoint A s1 s2 -> Intersection A s1 s2 = Empty_set A.
Proof.
  intros. apply Extensionality_Ensembles. split.
  * destruct H.
    intros x H1. unfold In in *. exfalso. intuition. apply (H _ H1).
  * intuition.
Qed.

Lemma Disjoint_Empty_set_r:
  forall A s1, Intersection A s1 (Empty_set A) = Empty_set A.
Proof.
  intros. apply Extensionality_Ensembles. split.
  * intros x H1. destruct H1. unfold In in *. assumption.
  * intuition.
Qed.

Lemma Empty_set_zero_l:
  forall (U : Type) (X : Ensemble U), Union U X (Empty_set U) = X.
Proof.
  intros.
  rewrite Union_commutative.
  apply Empty_set_zero.
Qed.

Lemma Seminus_Empty_l:
  forall A s, Setminus A (Empty_set A) s = Empty_set A.
Proof.
  intros. apply Extensionality_Ensembles. split.
  * intros x H1. destruct H1. unfold In in *. assumption.
  * intuition.
Qed.


Lemma Seminus_Empty_r:
  forall A s, Setminus A s (Empty_set A) = s.
Proof.
  intros. apply Extensionality_Ensembles. split.
  * intros x H1. destruct H1. unfold In in *. assumption.
  * intuition.
Qed.

Lemma Setminus_Union:
  forall A s1 s2 s3,
  Setminus A (Union A s1 s2) s3 = Union A (Setminus A s1 s3)  (Setminus A s2 s3).
Proof.
  intros. apply Extensionality_Ensembles. split.
  * intros x H. inversion H. inversion H0; intuition.
  * intros x H. constructor; inversion H; inversion H0; intuition.
Qed.

Lemma Setminus_Union_r:
  forall A s1 s2 s3,
  Setminus A s1 (Union A s2 s3) = Setminus A (Setminus A s1 s2) s3.
Proof.
  intros. apply Extensionality_Ensembles. split.
  * intros x H. inversion H. constructor. intuition. contradict H1. intuition.
  * intros x H. inversion H. inversion H0. constructor; intuition. inversion H4; intuition.
Qed.

Lemma Setminus_noop:
  forall A s1 s2,
  Intersection A s1 s2 = Empty_set A -> Setminus A s1 s2 = s1.
Proof.
  intros. apply Extensionality_Ensembles. split.
  * intros x H1. inversion_clear H1. intuition.
  * intros x H1. constructor; intuition. contradict H.
    apply Inhabited_not_empty.
    exists x. intuition.
Qed.
  
Lemma Setminus_empty:
  forall A s1 s2,
  Included A s1 s2 -> Setminus A s1 s2 = Empty_set A.
Proof.
  intros. apply Extensionality_Ensembles. split.
    * intros x H1. inversion_clear H1. contradiction H2. intuition.
    * intuition.
Qed.


Lemma Included_Union_l:
  forall A s1 s2 s3,
    Included A s1 s2 -> Included A s1 (Union A s2 s3).
Proof.
  intros. left. intuition.
Qed.

Lemma Intersection_mono_trans_l:
  forall A s1 s2 s3 s4,
  Included A s1 s2 -> Included A (Intersection A s2 s3) s4 ->
  Included A (Intersection A s1 s3) s4.
Proof.
  intros.
  intros x H1.
  apply H0. clear H0.
  destruct H1. constructor; intuition.
Qed.

Lemma Distributivity_l
     : forall (U : Type) (A B C : Ensemble U),
       Intersection U (Union U A B) C =
       Union U (Intersection U A C) (Intersection U B C).
Proof.
   intros.
   rewrite Intersection_commutative.
   rewrite Distributivity.
   f_equal; apply Intersection_commutative.
Qed.

Lemma union_intersect_reorder:
  forall A s1 s2 s3 s4,
  Disjoint A s1 s4 ->
  Disjoint A s3 s2 ->
  Union A (Intersection A s1 s2) (Intersection A s3 s4) = 
  Intersection A (Union A s1 s3) (Union A s2 s4).
Proof.
  intros.
  repeat (rewrite Distributivity || rewrite Distributivity_l).
  rewrite (Disjoint_Intersection _ _ _ H).
  rewrite (Disjoint_Intersection _ _ _ H0).
  rewrite Empty_set_zero.
  rewrite Union_associative.
  rewrite Empty_set_zero.
  reflexivity.
Qed.


Require Import Coq.Logic.Classical_Prop.

Lemma Setminus_empty_classical:
  forall A s1 s2,
  Setminus A s1 s2 = Empty_set A <-> Included A s1 s2.
Proof.
  intros. split; try apply Setminus_empty; intro.
  intros.
  intros x H1.
  apply Extension in H.
  destruct H. clear H0.
  specialize (H x).
  unfold Setminus, In in *. simpl in *.
  apply Coq.Logic.Classical_Prop.NNPP.
  intro.
  intuition.
Qed.