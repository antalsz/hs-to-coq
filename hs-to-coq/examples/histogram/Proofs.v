Require Import Prelude.
Require Import Histogram.

Lemma group_by_not_nil:
  forall A f (xs : list A),
    ~ In nil (groupBy f xs).
Proof.
  induction xs.
  * simpl. auto.
  * simpl.
    destruct (groupBy f xs) eqn:?.
    - simpl in *.
      intuition congruence.
    - destruct l eqn:?.
      + intuition.
      + destruct (f a a0).
        - contradict IHxs.
          destruct IHxs; try congruence.
          intuition.
        - contradict IHxs.
          destruct IHxs; try congruence.
Qed.


Lemma concat_groupBy:
  forall A f (xs : list A),
    concat (groupBy f xs) = xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl.
    destruct (groupBy f xs) eqn:?.
    - simpl in IHxs. simpl. congruence.
    - destruct l eqn:?.
      - exfalso.
        apply (group_by_not_nil _ f xs).
        rewrite Heql.
        intuition.
      -  destruct (f a a0); simpl in *; congruence.
Qed.

Lemma map_map:
  forall a b c (f : a -> b) (g : b -> c) (x : list a),
  map g (map f x) = map (g ∘ f) x.
Proof.
  intros.
  induction x.
  * auto.
  * simpl. rewrite IHx. auto.
Qed.

Lemma in_map_hd_in_concat:
  forall A (x : A) xs,
  ~ In nil xs -> 
  In x (map hd xs) ->
  In x (concat xs).
Proof.
  intros.
  induction xs.
  * inversion H0.
  * simpl.
    rewrite in_app_iff.
    destruct H0.
    - left.
      subst.
      destruct a.
      * contradict H. intuition.
      * intuition.
    - right.
      apply IHxs.
      * contradict H. right. assumption.
      * assumption.
Qed.

Lemma hist_dom:
  forall X `{Eq_ X} (x : X) xs,
    In x (map fst (hist xs)) -> In x xs.
Proof.
  intros.
  unfold hist in H0.
  rewrite map_map in H0.
  apply in_map_hd_in_concat in H0.
  rewrite concat_groupBy in H0.
  assumption.
  apply group_by_not_nil.
Qed.
