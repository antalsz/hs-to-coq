Require Import Prelude.
Require Import RLE.

Lemma group_by_not_nil:
  forall f (xs : list E),
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
      + destruct (f a e).
        ** contradict IHxs.
           destruct IHxs; try congruence.
           intuition.
        ** contradict IHxs.
           destruct IHxs; try congruence.
Qed.


Lemma concat_groupBy:
  forall f (xs : list E),
    concat (groupBy f xs) = xs.
Proof.
  intros.
  induction xs.
  * reflexivity.
  * simpl.
    destruct (groupBy f xs) eqn:?.
    - simpl in IHxs.  unfold concat in *. simpl in *. congruence.
    - destruct l eqn:?.
      + exfalso.
        apply (group_by_not_nil f xs).
        rewrite Heql.
        intuition.
      + destruct (f a e); unfold concat in *; simpl in *; congruence.
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
  forall (x : E) xs,
  ~ In nil xs -> 
  In x (map hd xs) ->
  In x (concat xs).
Proof.
  intros.
  induction xs.
  * inversion H0.
  * simpl.
    unfold concat. simpl.
    rewrite in_app_iff.
    destruct H0.
    - left.
      subst.
      destruct a.
      + contradict H. intuition.
      + intuition.
    - right.
      apply IHxs.
      + contradict H. right. assumption.
      + assumption.
Qed.

(* For the good rle, we can prove
   properties about it, simply because we
   never look at the axiom. *)
Lemma rle_dom:
  forall `{Eq_ E} (x : E) xs,
    In x (map fst (rle xs)) -> In x xs.
Proof.
  intros.
  unfold rle in H0.
  rewrite map_map in H0.
  apply in_map_hd_in_concat in H0.
  unfold group in H0.
  rewrite concat_groupBy in H0.
  assumption.
  apply group_by_not_nil.
Qed.


(* For the bad rle, at some point we
   would have to prove that [hd nil] is in [xs].
   We would not be able to prove that in general. *)
Lemma int_suc_absurd: forall x : Int,  (#1 + x <> x).
Proof.
  intros.
  change ((1 + x)%Z <> (0 + x)%Z).
  rewrite Z.add_cancel_r.
  destruct (Z.eq_dec 1 0); intuition congruence.
Qed.

Lemma bad_rle_dom:
  exists (x : Int) xs,
    In x (map fst (bad_rle xs)) /\ ~ (In x xs).
Proof.
  remember (hd nil : Int) as x.
  exists x.
  exists (cons (#1 + x) nil).
  split.
  * left. subst. reflexivity.
  * intro.
    destruct H.
    - apply (int_suc_absurd _ H).
    - destruct H.
Qed.


