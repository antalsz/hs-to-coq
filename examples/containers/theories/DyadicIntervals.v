Require Import Omega.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Bool.Bool.

Require Import BitUtils.

Local Open Scope Z_scope.


(** ** Dyadic intervals

A dyadic interval is a set of the form

<<
   [a⋅2^n,…,(a+1)⋅2^n-1)] where a∈Z,n≥0
>>

which can be described by the prefix [p] and the shift width [a].
In the folloing, we just say “range” for a dyadic interval.
*)

Definition range := (Z * N)%type.
Definition rPrefix : range -> Z := fun '(p,b) => Z.shiftl p (Z.of_N b).
Definition rBits : range -> N   := snd.

Lemma rPrefix_rBits_range_eq:
  forall r1 r2, rPrefix r1 = rPrefix r2 -> rBits r1 = rBits r2 -> r1 = r2.
Proof.
  intros.
  destruct r1 as [p1 b1], r2 as [p2 b2].
  simpl in *; subst.
  rewrite Z_shiftl_inj in H by nonneg.
  congruence.
Qed.

(** *** Operation: [inRange]

This operation checks if a value is in the range of the range set.
*)

Definition inRange : Z -> range -> bool :=
  fun n '(p,b) => Z.shiftr n (Z.of_N b) =? p.

Lemma rPrefix_inRange:
  forall r, inRange (rPrefix r) r = true.
Proof.
  intros.
  destruct r as [p b].
  simpl.
  rewrite Z.eqb_eq.
  rewrite -> Z.shiftr_shiftl_l by nonneg.
  replace (_ - _) with 0 by omega.
  reflexivity.
Qed.

Lemma bit_diff_not_in_range:
  forall r j i,
    Z.of_N (rBits r) <= j ->
    Z.testbit (rPrefix r) j <> Z.testbit i j ->
    inRange i r = false.
 Proof.
    intros.
    destruct r as [p b]; simpl in *.
    apply not_true_is_false.
    contradict H0.
    rewrite -> Z.eqb_eq in H0.
    apply Z.bits_inj_iff in H0.
    specialize (H0 (j - Z.of_N b)).
    rewrite -> Z.shiftr_spec in H0 by omega.
    rewrite -> Z.shiftl_spec by (transitivity (Z.of_N b); nonneg).
    replace (j - Z.of_N b + Z.of_N b) with j in H0 by omega.
    rewrite H0. reflexivity.
Qed.

Lemma inRange_bounded:
  forall i r , inRange i r = true -> rPrefix r <= i < rPrefix r + 2^(Z.of_N (rBits r)).
Proof.
  intros.
  destruct r as [p b].
  unfold inRange, rPrefix, rBits, snd in *.
  rewrite Z.eqb_eq in H.
  rewrite !Z.shiftl_mul_pow2 by nonneg.
  rewrite Z.shiftr_div_pow2 in H by nonneg.
  subst.
  assert (0 < 2 ^ Z.of_N b) by (apply Z.pow_pos_nonneg; nonneg).
  enough (0 <= i - i / 2 ^ Z.of_N b * 2 ^ Z.of_N b < 2^(Z.of_N b)) by omega.
  rewrite <- Zmod_eq by omega.
  apply Z_mod_lt; omega.
Qed.

Lemma inRange_false_bounded:
  forall i r , inRange i r = false -> i < rPrefix r \/ rPrefix r + 2^(Z.of_N (rBits r)) <= i.
Proof.
  intros.
  destruct r as [p b].
  unfold inRange, rPrefix, rBits, snd in *.
  rewrite Z.eqb_neq in H.
  rewrite !Z.shiftl_mul_pow2 by nonneg.
  rewrite Z.shiftr_div_pow2 in H by nonneg.
  enough (~ (p * 2 ^ Z.of_N b <= i /\ i <  p * 2 ^ Z.of_N b + 2 ^ Z.of_N b)) by omega.
  contradict H.
  symmetry.
  eapply Z.div_unique_pos with (r := i - 2 ^ Z.of_N b * p); only 2: omega.
  rewrite Z.mul_comm.
  omega. (* WTF, why do I have to commut mult for omega to work? *)
Qed.

Lemma inRange_false_bounded_iff:
  forall i r , inRange i r = false <-> (i < rPrefix r \/ rPrefix r + 2^(Z.of_N (rBits r)) <= i).
Proof.
  intros.
  split; intro.
  * apply inRange_false_bounded; assumption.
  * destruct (inRange i r) eqn:?; try reflexivity; exfalso.
    apply inRange_bounded in Heqb.
    omega.
Qed.

(** *** Operation: [isSubrange] *)

Definition isSubrange : range -> range -> bool :=
  fun r1 r2 => inRange (rPrefix r1) r2 && (rBits r1 <=? rBits r2)%N.

Lemma inRange_isSubrange_true:
  forall i r1 r2,
    isSubrange r1 r2 = true ->
    inRange i r1 = true ->
    inRange i r2 = true.
Proof.
  intros.
  destruct r1 as [p1 b1], r2 as [p2 b2].
  unfold isSubrange in *.
  simpl in *.
  rewrite -> andb_true_iff in H. destruct H.
  rewrite -> N.leb_le in H1.
  rewrite -> Z.eqb_eq in *.
  apply N2Z.inj_le in H1.
  subst.
  apply Z.bits_inj_iff'.
  intros j Hnonneg.
  repeat rewrite -> Z.shiftr_spec by nonneg.
  rewrite -> Z.shiftl_spec by (apply OMEGA2; nonneg).
  repeat rewrite -> Z.shiftr_spec by nonneg.
  f_equal.
  omega.
Qed.

Lemma inRange_isSubrange_false:
  forall i r1 r2,
    isSubrange r1 r2 = true ->
    inRange i r2 = false ->
    inRange i r1 = false.
 Proof.
    intros.
    rewrite <- not_true_iff_false in H0.
    rewrite <- not_true_iff_false.
    contradict H0.
    eapply inRange_isSubrange_true.
    all:eauto.
Qed.

Lemma isSubrange_refl:
  forall r, isSubrange r r = true.
Proof.
  intros r.
  unfold isSubrange.
  destruct r as [p b]; simpl.
  rewrite -> Z.shiftr_shiftl_l by nonneg.
  replace (Z.of_N b - Z.of_N b) with 0 by omega.
  simpl.
  rewrite N.leb_refl.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.

Lemma isSubrange_trans:
  forall r1 r2 r3,
  isSubrange r1 r2 = true ->
  isSubrange r2 r3 = true ->
  isSubrange r1 r3 = true.
Proof.
  intros.
  unfold isSubrange.
  rewrite -> andb_true_iff; split.
  * unfold isSubrange in H.
    rewrite -> andb_true_iff in H; intuition.
    eapply inRange_isSubrange_true; eauto.
  * unfold isSubrange in *.
    rewrite -> andb_true_iff in *; intuition.
    rewrite -> N.leb_le in *.
    Nomega.
Qed.

Lemma isSubrange_antisym:
  forall r1 r2,
  isSubrange r1 r2 = true ->
  isSubrange r2 r1 = true ->
  r1 = r2.
Proof.
  intros.
  destruct r1 as [p1 b1], r2 as [p2 b2]; unfold isSubrange in *; simpl in *.
  apply andb_true_iff in H.
  apply andb_true_iff in H0.
  intuition.
  apply N.leb_le in H2.
  apply N.leb_le in H3.
  assert (b1 = b2) by Nomega; subst.
  rewrite -> Z.shiftr_shiftl_l in H by nonneg.
  rewrite -> Z.shiftr_shiftl_l in H1 by nonneg.
  replace (Z.of_N b2 - Z.of_N b2) with 0 in * by omega.
  simpl in *.
  rewrite -> Z.eqb_eq in *.
  congruence.
Qed.


Lemma inRange_both_smaller_subRange:
  forall i r1 r2,
  inRange i r1 = true ->
  inRange i r2 = true ->
  (rBits r1 <= rBits r2)%N ->
  isSubrange r1 r2 = true.
Proof.
  intros.
  unfold isSubrange.
  rewrite -> andb_true_iff in *.
  rewrite N.leb_le; intuition.
  destruct r1 as [p1 b1], r2 as [p2 b2].
  simpl in *.
  rewrite -> Z.eqb_eq in *.
  apply Z.bits_inj_iff'; intros j ?.
  apply Z.bits_inj_iff in H; specialize (H (j + Z.of_N b2 - Z.of_N b1)).
  apply Z.bits_inj_iff in H0; specialize (H0 j).
  rewrite -> Z.shiftr_spec in * by Nomega.
  rewrite -> Z.shiftl_spec in * by Nomega.
  rewrite <- H.
  rewrite <- H0.
  replace ((j + Z.of_N b2 - Z.of_N b1 + Z.of_N b1)) with (j + Z.of_N b2) by omega.
  reflexivity.
Qed.

Lemma inRange_both_same:
  forall i r1 r2,
  inRange i r1 = true ->
  inRange i r2 = true ->
  (rBits r1 = rBits r2)%N ->
  r1 = r2.
Proof.
  intros.
  apply isSubrange_antisym.
  * apply inRange_both_smaller_subRange with (i := i); try assumption; Nomega.
  * apply inRange_both_smaller_subRange with (i := i); try assumption; Nomega.
Qed.  

Lemma different_prefix_same_bits_not_subrange:
  forall r1 r2,
    rPrefix r1 <> rPrefix r2 -> rBits r1 = rBits r2 -> isSubrange r1 r2 = false.
Proof.
  intros.
  unfold isSubrange.
  destruct r1 as [p1 b1], r2 as [p2 b2]. simpl in *; subst.
  rewrite N.leb_refl.
  rewrite andb_true_r.
  rewrite -> Z_shiftl_inj in H by nonneg.
  rewrite -> Z.shiftr_shiftl_l by nonneg.
  replace (Z.of_N b2 - Z.of_N b2) with 0 by omega. simpl.
  rewrite Z.eqb_neq.
  congruence.
Qed.

Lemma smaller_inRange_iff_subRange:
  forall r1 r2,
    (rBits r1 <= rBits r2)%N ->
    inRange (rPrefix r1) r2 = isSubrange r1 r2.
Proof.
  intros.
  unfold isSubrange.
  enough (Htmp : (rBits r1 <=? rBits r2)%N = true)
    by (rewrite Htmp; rewrite andb_true_r; reflexivity).
  apply N.leb_le.
  auto.
Qed.

Lemma subRange_smaller:
  forall r1 r2, isSubrange r1 r2 = true -> (rBits r1 <= rBits r2)%N.
Proof.
  intros.
  unfold isSubrange in H.
  apply andb_true_iff in H.
  destruct H.
  rewrite -> N.leb_le in H0.
  assumption.
Qed.


(** *** Operation: [rangeDisjoint]

Range sets have the nice property that they are either contained in each other, or
they are completely disjoint.
*)

(* Segments either disjoint or contained in each other *)
Definition rangeDisjoint : range -> range -> bool :=
  fun r1 r2 => negb (isSubrange r1 r2 || isSubrange r2 r1).

Lemma rangeDisjoint_sym: forall r1 r2,
  rangeDisjoint r1 r2 = rangeDisjoint r2 r1.
Proof.
  intros.
  unfold rangeDisjoint.
  rewrite orb_comm.
  reflexivity.
Qed.

Lemma different_prefix_same_bits_disjoint:
  forall r1 r2,
    rPrefix r1 <> rPrefix r2 -> rBits r1 = rBits r2 -> rangeDisjoint r1 r2 = true.
Proof.
  intros.
  unfold rangeDisjoint.
  rewrite -> different_prefix_same_bits_not_subrange; try congruence.
  rewrite -> different_prefix_same_bits_not_subrange; try congruence.
  reflexivity.
Qed.

Lemma inRange_both_not_disj:
  forall i r1 r2,
  inRange i r1 = true ->
  inRange i r2 = true ->
  rangeDisjoint r1 r2 = false.
Proof.
  intros.
  unfold rangeDisjoint.
  rewrite negb_false_iff.
  rewrite orb_true_iff.
  destruct (N.le_ge_cases (rBits r1) (rBits r2));
    [left|right]; eapply inRange_both_smaller_subRange; eauto.
Qed.

Lemma rangeDisjoint_inRange_false:
  forall i r1 r2, rangeDisjoint r1 r2 = true -> inRange i r1 = true -> inRange i r2 = false.
Proof.
  intros.
  destruct (inRange i r2) eqn:?; auto.
  enough (rangeDisjoint r1 r2 = false) by congruence.
  eapply inRange_both_not_disj; eauto.
Qed.

Lemma rangeDisjoint_inRange_false_false:
  forall i r1 r2, rangeDisjoint r1 r2 = true -> inRange i r1 = true -> inRange i r2 = true -> False.
Proof.
  intros.
  pose proof (rangeDisjoint_inRange_false i r1 r2). intuition congruence.
Qed.

Lemma rangeDisjoint_isSubrange_false_false:
  forall r r1 r2, rangeDisjoint r1 r2 = true -> isSubrange r r1 = true -> isSubrange r r2 = true -> False.
Proof.
  intros.
  eapply rangeDisjoint_inRange_false_false with (i := rPrefix r).
  * eassumption.
  * eapply inRange_isSubrange_true; try eassumption; apply rPrefix_inRange.
  * eapply inRange_isSubrange_true; try eassumption; apply rPrefix_inRange.
Qed.


Lemma disjoint_rPrefix_differ:
  forall r1 r2,
    rangeDisjoint r1 r2 = true -> rPrefix r1 <> rPrefix r2.
 Proof.
   intros ????.
   enough (rangeDisjoint r1 r2 = false) by congruence; clear H.
   eapply inRange_both_not_disj.
   apply rPrefix_inRange.
   rewrite H0.
   apply rPrefix_inRange.
Qed.

Lemma disjoint_rPrefix_eqb:
  forall r1 r2,
    rBits r1 = rBits r2 ->
    (rPrefix r1 =? rPrefix r2) = negb (rangeDisjoint r1 r2).
Proof.
  intros.
  rewrite eq_iff_eq_true.
  rewrite negb_true_iff.
  split; intro.
  * rewrite Z.eqb_eq in *.
    apply not_true_iff_false.
    contradict H0.
    apply disjoint_rPrefix_differ.
    assumption.
  * apply not_true_iff_false in H0.
    apply not_false_iff_true.
    contradict H0.
    rewrite Z.eqb_neq in *.
    apply different_prefix_same_bits_disjoint; assumption.
Qed.

Lemma isSubrange_disj_disj_r:
  forall r1 r2 r3,
  isSubrange r2 r3 = true ->
  rangeDisjoint r1 r3 = true ->
  rangeDisjoint r1 r2 = true.
Proof.
  intros.
  unfold rangeDisjoint in *.
  rewrite -> negb_true_iff in *.
  rewrite <- not_true_iff_false in H0.
  rewrite <- not_true_iff_false.
  contradict H0.
  rewrite -> orb_true_iff in *.
  destruct H0; [left|].
  eapply isSubrange_trans; eauto.
  unfold isSubrange in H, H0.
  rewrite -> andb_true_iff in *.
  intuition. clear H2 H3.
  enough (rangeDisjoint r1 r3 = false).
    unfold rangeDisjoint in *.
    rewrite -> negb_false_iff in *.
    rewrite -> orb_true_iff in *.
    assumption.
  eapply inRange_both_not_disj; eassumption.
Qed.

Lemma isSubrange_disj_disj_l:
  forall r1 r2 r3,
  isSubrange r1 r2 = true ->
  rangeDisjoint r2 r3 = true ->
  rangeDisjoint r1 r3 = true.
Proof.
  intros.
  rewrite -> rangeDisjoint_sym in *.
  eapply isSubrange_disj_disj_r; eauto.
Qed.

Lemma smaller_not_subrange_disjoint:
  forall r1 r2,
  (rBits r1 < rBits r2)%N ->
  isSubrange r1 r2 = false ->
  rangeDisjoint r1 r2 = true.
Proof.
  intros.
  unfold rangeDisjoint.
  rewrite H0. simpl.
  unfold isSubrange.
  replace (rBits r2 <=? rBits r1)%N with false.
  rewrite andb_false_r. reflexivity.
  symmetry.
  apply N.leb_gt.
  assumption.
Qed.

Lemma smaller_not_subrange_disjoint_iff:
  forall r1 r2,
  (rBits r1 < rBits r2)%N ->
  isSubrange r1 r2 = false <-> rangeDisjoint r1 r2 = true.
Proof.
  intros. split; intro.
  * apply smaller_not_subrange_disjoint; auto.
  * unfold rangeDisjoint in *.
    rewrite negb_true_iff in H0.
    rewrite orb_false_iff in H0.
    intuition.
Qed.

(** *** Operation: [halfRange]

Non-singelton sets can be partitioned into two halfs.
*)

Definition halfRange : range -> bool -> range :=
  fun '(p,b) h =>
    let b' := N.pred b in
    let p' := Z.shiftl p 1 in
    (if h then Z.lor p' 1 else p', b').

Lemma isSubrange_halfRange:
  forall r h,
    (0 < rBits r)%N ->
    isSubrange (halfRange r h) r = true.
 Proof.
    intros.
    destruct r as [p b].
    unfold isSubrange, inRange, halfRange, rPrefix, rBits, snd in *.
    rewrite andb_true_iff; split.
    * rewrite Z.eqb_eq.
      destruct h.
      - rewrite Z.shiftl_lor.
        rewrite -> Z.shiftl_shiftl by omega.
        replace (1 + Z.of_N (N.pred b)) with (Z.of_N b) by Nomega.
        rewrite Z.shiftr_lor.
        rewrite -> Z.shiftr_shiftl_l by nonneg.
        replace (Z.of_N b - Z.of_N b) with 0 by omega.
        simpl.
        rewrite -> Z.shiftr_shiftl_r by Nomega.
        replace (Z.of_N b - Z.of_N (N.pred b)) with 1 by Nomega.
        replace (Z.shiftr 1 1) with 0 by reflexivity.
        rewrite Z.lor_0_r.
        reflexivity.
      - rewrite -> Z.shiftl_shiftl by omega.
        replace (1 + Z.of_N (N.pred b)) with (Z.of_N b) by Nomega.
        rewrite -> Z.shiftr_shiftl_l by nonneg.
        replace (Z.of_N b - Z.of_N b) with 0 by omega.
        reflexivity.
    * rewrite N.leb_le.
      apply N.le_pred_l.
Qed.


Lemma testbit_halfRange_false:
 forall r i h,
    (0 < rBits r)%N ->
    inRange i r = true ->
    inRange i (halfRange r h) = false <-> Z.testbit i (Z.pred (Z.of_N (rBits r))) = negb h.
Proof.
  intros.
  destruct r as [p b]. unfold inRange, halfRange, rBits, snd in *.
  rewrite -> N2Z.inj_pred in * by auto.
  destruct h; simpl negb.
  * intuition;
     rewrite -> Z.eqb_neq in *;
     rewrite -> Z.eqb_eq in *.
    - apply not_true_is_false.
      contradict H1.
      apply Z.bits_inj_iff'; intros j?.
      rewrite -> Z.shiftr_spec by nonneg.
      rewrite Z.lor_spec.
      rewrite -> Z.shiftl_spec by nonneg.
      rewrite testbit_1.
      assert (j = 0 \/ 1 <= j) by omega.
      destruct H3.
      + subst.
        simpl Z.add.
        rewrite H1; symmetry.
        replace (0 =? 0) with true by reflexivity.
        rewrite orb_true_r.
        reflexivity.
      + apply Z.bits_inj_iff in H0.
        specialize (H0 (Z.pred j)).
        rewrite -> Z.shiftr_spec in * by nonneg.
        replace (j + Z.pred (Z.of_N b)) with (Z.pred j + Z.of_N b) by omega.
        rewrite H0.
        replace (Z.pred j) with (j - 1) by omega.
        replace (j =? 0) with false by (symmetry; rewrite Z.eqb_neq; omega).
        rewrite orb_false_r. reflexivity.
    - apply not_true_iff_false in H1.
      contradict H1.
      apply Z.bits_inj_iff in H1.
      specialize (H1 0).
      rewrite -> Z.shiftr_spec in * by nonneg.
      simpl (_ + _) in H1.
      rewrite H1.
      rewrite Z.lor_spec.
      rewrite -> Z.shiftl_spec by nonneg.
      rewrite testbit_1.
      replace (0 =? 0) with true by reflexivity.
      rewrite orb_true_r.
      reflexivity.
  * intuition;
     rewrite -> Z.eqb_neq in *;
     rewrite -> Z.eqb_eq in *; subst.
    - rewrite <- not_false_iff_true.
      contradict H1.
      apply Z.bits_inj_iff'; intros j?.
      rewrite -> Z.shiftr_spec by nonneg.
      rewrite -> Z.shiftl_spec by nonneg.
      assert (j = 0 \/ 1 <= j) by omega.
      destruct H2.
      + subst.
        simpl Z.add.
        rewrite H1; symmetry.
        apply Z.testbit_neg_r; omega.
      + rewrite -> Z.shiftr_spec in * by nonneg.
        f_equal.
        omega.
    - rewrite <- not_false_iff_true in H1.
      contradict H1.
      apply Z.bits_inj_iff in H1.
      specialize (H1 0).
      rewrite -> Z.shiftr_spec in * by nonneg.
      simpl (_ + _) in H1.
      rewrite H1.
      rewrite -> Z.shiftl_spec by nonneg.
      apply Z.testbit_neg_r; omega.
Qed.

Lemma testbit_halfRange_true_false:
 forall r i,
    (0 < rBits r)%N ->
    inRange i r = true ->
    inRange i (halfRange r true) = false <-> Z.testbit i (Z.pred (Z.of_N (rBits r))) = false.
 Proof. intros ??. apply testbit_halfRange_false. Qed.

Lemma testbit_halfRange_true:
 forall r i,
    (0 < rBits r)%N ->
    inRange i r = true ->
    inRange i (halfRange r true) = Z.testbit i (Z.pred (Z.of_N (rBits r))).
 Proof. intros.
  pose proof (testbit_halfRange_true_false r i H H0).
  match goal with [ |- ?x = ?y ] =>
    destruct x, y end; intuition.
 Qed.

Lemma halfRange_inRange_testbit:
 forall r i h,
    (0 < rBits r)%N ->
    inRange i r = true ->
    inRange i (halfRange r h) = negb (xorb h (Z.testbit i (Z.pred (Z.of_N (rBits r))))).
Proof.
  intros.
  pose proof (testbit_halfRange_false r i h H H0).
  match goal with [ |- ?x = negb (xorb _ ?y) ] =>
    destruct x, y, h end; intuition.
Qed.


Lemma rBits_halfRange:
  forall r h, rBits (halfRange r h) = N.pred (rBits r).
Proof.
  intros.
  destruct r as [p b]. simpl. reflexivity.
Qed.

Lemma rPrefix_halfRange_otherhalf:
  forall r,
  (0 < rBits r)%N ->
  rPrefix (halfRange r true) = rPrefix (halfRange r false) + 2^(Z.of_N (rBits (halfRange r false))).
Proof.
  intros.
  destruct r as [p b].
  unfold halfRange, rPrefix, rBits, snd in *.
  rewrite <- Z.shiftl_1_l.
  rewrite <- Z_shiftl_add by nonneg.
  f_equal.
  rewrite Z.shiftl_mul_pow2 by omega.
  replace (2 ^ 1) with 2 by reflexivity.
  apply Z.bits_inj_iff'. intros i ?.
  rewrite Z.lor_spec.
  assert (i = 0 \/ 0 < i) by omega.
  rewrite Z.mul_comm.
  rewrite testbit_1.
  destruct H1.
  * subst.
    rewrite Z.testbit_odd_0.
    rewrite Z.eqb_refl.
    rewrite orb_true_r.
    reflexivity.
  * subst.
    replace i with (Z.succ (Z.pred i)) by omega.
    rewrite Z.testbit_odd_succ by omega.
    rewrite Z.testbit_even_succ by omega.
    replace (_ =? _) with false
      by (symmetry; rewrite Z.eqb_neq; omega).
    rewrite orb_false_r.
    reflexivity.
Qed.

Lemma halfRange_isSubrange_testbit:
  forall r1 r2 h,
   (rBits r1 < rBits r2)%N ->
   isSubrange r1 r2 = true ->
   isSubrange r1 (halfRange r2 h) = negb (xorb h (Z.testbit (rPrefix r1) (Z.pred (Z.of_N (rBits r2))))).
Proof.
  intros.
  unfold isSubrange in *.
  apply andb_true_iff in H0; destruct H0.
  replace ((rBits r1 <=? rBits (halfRange r2 h))%N) with true.
  + rewrite andb_true_r.
    rewrite halfRange_inRange_testbit by (assumption || Nomega).
    reflexivity.
  + symmetry.
    rewrite N.leb_le.
    rewrite rBits_halfRange.
    Nomega.
 Qed.

Lemma testbit_halfRange_isSubrange:
  forall r1 r2,
    (rBits r1 < rBits r2)%N ->
    isSubrange r1 r2 = true ->
    isSubrange r1 (halfRange r2 true) = Z.testbit (rPrefix r1) (Z.pred (Z.of_N (rBits r2))).
Proof.
  intros.
  rewrite -> halfRange_isSubrange_testbit by auto.
  rewrite -> xorb_true_l at 1.
  rewrite negb_involutive.
  reflexivity.
Qed.

Lemma testbit_halfRange_false_false:
  forall r i,
    (0 < rBits r)%N ->
    inRange i r = true ->
    inRange i (halfRange r false) = false <-> Z.testbit i (Z.pred (Z.of_N (rBits r))) = true.
Proof. intros ??. apply testbit_halfRange_false. Qed.

Lemma testbit_halfRange:
  forall r h,
  (0 < rBits r)%N ->
  Z.testbit (rPrefix (halfRange r h)) (Z.pred (Z.of_N (rBits r))) = h.
Proof.
  intros.
  destruct r as [p b].
  unfold rPrefix, halfRange, rBits, snd in *.
  rewrite -> Z.shiftl_spec by Nomega.
  replace (Z.pred (Z.of_N b) - Z.of_N (N.pred b)) with 0 by Nomega.
  destruct h;
    try rewrite Z.lor_spec;
    rewrite -> Z.shiftl_spec by omega;
    rewrite -> Z.testbit_neg_r by omega;
    reflexivity.
Qed.

Lemma halves_disj_aux:
  forall r h1 h2,
  (0 < rBits r)%N ->
  h2 = negb h1 ->
  isSubrange (halfRange r h1) (halfRange r h2) = false.
Proof.
  intros. subst.
  assert ((rBits (halfRange r h1) < rBits r)%N)
    by (rewrite -> rBits_halfRange; Nomega).
  rewrite -> halfRange_isSubrange_testbit by (auto; apply isSubrange_halfRange; auto).
  rewrite -> testbit_halfRange by assumption.
  destruct h1; reflexivity.
Qed.

Lemma halves_disj:
  forall r,
  (0 < rBits r)%N ->
  rangeDisjoint (halfRange r false) (halfRange r true) = true.
Proof.
  intros.
  unfold rangeDisjoint.
  erewrite halves_disj_aux by auto.
  erewrite halves_disj_aux by auto.
  reflexivity.
Qed.

Lemma smaller_subRange_other_half :
  forall r1 r2,
    (rBits r1 < rBits r2)%N ->
    isSubrange r1 r2 = true ->
    isSubrange r1 (halfRange r2 true) = negb (isSubrange r1 (halfRange r2 false)).
Proof.
  intros.
  rewrite -> halfRange_isSubrange_testbit by auto.
  rewrite -> halfRange_isSubrange_testbit by auto.
  destruct (Z.testbit _ _); reflexivity.
Qed.

Lemma halfRange_smaller:
  forall r h, (0 < rBits r)%N -> (rBits (halfRange r h) < rBits r)%N.
Proof.
  intros.
  destruct r as [p b].
  unfold halfRange.
  simpl in *.
  Nomega.
Qed.


(** *** Operation: [rNonneg]

This predicate inciates that the range covers non-negative numbers. We 
often have to restrict ourselves to these as negative numbers have
an infinite number of bits set, which means that [msDiffBit] would not work.

If we would switch to a finite signed type, this could be dropped.
*)

Definition rNonneg : range -> Prop :=
  fun '(p,b) =>  0 <= p.

Lemma rNonneg_subrange:
  forall r1 r2,
    isSubrange r1 r2 = true ->
    rNonneg r1 <-> rNonneg r2.
Proof.
  intros.
  destruct r1 as [p1 b1], r2 as [p2 b2].
  unfold isSubrange, inRange, rNonneg, rBits, snd, rPrefix in *.
  rewrite -> andb_true_iff in H. destruct H.
  rewrite -> Z.eqb_eq in *.
  subst.
  rewrite -> Z.shiftr_nonneg.
  rewrite -> Z.shiftl_nonneg.
  intuition.
Qed.

Lemma rNonneg_halfRange:
  forall r h,
    (0 < rBits r)%N ->
    rNonneg (halfRange r h) <-> rNonneg r.
Proof.
  intros.
  apply rNonneg_subrange.
  apply isSubrange_halfRange.
  auto.
Qed.


(** *** Lemmas about [msDiffBit]

These lemmas are phrased in terms of ranges, but that is just (dubious) 
convenience; maybe they should be expressed in plain values and calls to
[Z.shiftl]...
*)

Lemma msDiffBit_lt_tmp:
  forall r1 r2,
    rNonneg r1 -> rNonneg r2 -> 
    rangeDisjoint r1 r2 = true ->
    (rBits r1 <= rBits r2)%N ->
    (msDiffBit (rPrefix r1) (rPrefix r2) <= rBits r2)%N ->
    False.
Proof.
  intros.
  assert (inRange (rPrefix r1) r2 = true).
  { destruct r1 as [p1 b1], r2 as [p2 b2].
    unfold inRange, rPrefix, rBits, rNonneg,  snd in *.
    rewrite -> N2Z.inj_le in H2, H3.
    apply Z.eqb_eq.
    symmetry.
    apply Z.bits_inj_iff'. intros j?.
    replace j with ((j + Z.of_N b2) - Z.of_N b2) by omega.
    rewrite <- Z.shiftl_spec by Nomega.
    rewrite <- msDiffBit_Same with (p1 := (Z.shiftl p1 (Z.of_N b1))) (p2 := (Z.shiftl p2 (Z.of_N b2))); try nonneg.
    rewrite -> !Z.shiftl_spec by Nomega.
    rewrite -> !Z.shiftr_spec by Nomega.
    rewrite -> !Z.shiftl_spec by Nomega.
    f_equal. omega.
  }

  unfold rangeDisjoint in H1.
  apply negb_true_iff in H1.
  rewrite -> orb_false_iff in H1.
  unfold isSubrange in *.
  rewrite -> !andb_false_iff in H1.
  rewrite -> !N.leb_nle in H1.
  destruct H1.
  intuition try congruence.
Qed.

Lemma msDiffBit_lt:
  forall r1 r2,
  rNonneg r1 -> rNonneg r2 -> 
  rangeDisjoint r1 r2 = true ->
  (N.max (rBits r1) (rBits r2) < msDiffBit (rPrefix r1) (rPrefix r2))%N.
Proof.
  intros.
  destruct (N.leb_spec (rBits r2) (rBits r1)).
  * rewrite -> N.max_l by assumption.
    apply N.nle_gt.
    intro.
    rewrite rangeDisjoint_sym in H1.
    rewrite msDiffBit_sym in H3.
    apply (msDiffBit_lt_tmp r2 r1 H0 H H1 H2 H3).
  * apply N.lt_le_incl in H2.
    rewrite -> N.max_r by assumption.
    apply N.nle_gt.
    intro.
    apply (msDiffBit_lt_tmp r1 r2 H H0 H1 H2 H3).
Qed.

Lemma msDiffBit_lt_l:
   forall r1 r2,
    rNonneg r1 -> rNonneg r2 -> 
    rangeDisjoint r1 r2 = true ->
    (rBits r1 < msDiffBit (rPrefix r1) (rPrefix r2))%N.
Proof.
  intros.
  apply N.le_lt_trans with (m := N.max (rBits r1) (rBits r2)); try Nomega.
  apply msDiffBit_lt; auto.
Qed.

Lemma msDiffBit_lt_r:
   forall r1 r2,
    rNonneg r1 -> rNonneg r2 -> 
    rangeDisjoint r1 r2 = true ->
    (rBits r2 < msDiffBit (rPrefix r1) (rPrefix r2))%N.
Proof.
  intros.
  apply N.le_lt_trans with (m := N.max (rBits r1) (rBits r2)); try Nomega.
  apply msDiffBit_lt; auto.
Qed.

Lemma msDiffBit_pos:
   forall r1 r2, (0 < msDiffBit (rPrefix r1) (rPrefix r2))%N.
Proof.
  intros.
  unfold msDiffBit.
  replace 0%N with (Z.to_N 0) by reflexivity.
  apply Z2N.inj_lt; try nonneg.
  apply Zle_lt_succ.
  nonneg.
Qed.


(** *** Operation: [commonRangeDisj]

The join of the semi-lattice, here defined for disjoint arguments, in preparation
for [commonRange].
*)

(* The smallest range that encompasses two (disjoint) ranges *)
Definition commonRangeDisj : range -> range -> range :=
  fun r1 r2 =>
    let b := msDiffBit (rPrefix r1) (rPrefix r2) in
    (Z.shiftr (rPrefix r1) (Z.of_N b) , b).

Lemma commonRangeDisj_sym:
  forall r1 r2,
   rNonneg r1 -> rNonneg r2 ->
   commonRangeDisj r1 r2 = commonRangeDisj r2 r1.
Proof.
  intros.
  unfold commonRangeDisj.
  rewrite msDiffBit_sym.
  rewrite msDiffBit_shiftr_same.
  reflexivity.
  destruct r1, r2. unfold rNonneg, rPrefix in *. nonneg.
  destruct r1, r2. unfold rNonneg, rPrefix in *. nonneg.
Qed.

Lemma commonRangeDisj_rBits_lt_l:
  forall r1 r2,
  rNonneg r1 -> rNonneg r2 ->
  rangeDisjoint r1 r2 = true ->
  (rBits r1 < rBits (commonRangeDisj r1 r2))%N.
Proof.
  intros.
  unfold commonRangeDisj. simpl.
  apply (msDiffBit_lt_l); auto.
Qed.

Lemma commonRangeDisj_rBits_lt_r:
  forall r1 r2,
  rNonneg r1 -> rNonneg r2 ->
  rangeDisjoint r1 r2 = true ->
  (rBits r2 < rBits (commonRangeDisj r1 r2))%N.
Proof.
  intros.
  unfold commonRangeDisj. simpl.
  apply (msDiffBit_lt_r); auto.
Qed.

Lemma commonRangeDisj_rBits_le_l:
  forall r1 r2,
  rNonneg r1 -> rNonneg r2 ->
  rangeDisjoint r1 r2 = true ->
  (rBits r1 <= rBits (commonRangeDisj r1 r2))%N.
Proof.
  intros.
  apply N.lt_le_incl.
  apply commonRangeDisj_rBits_lt_l; auto.
Qed.

Lemma commonRangeDisj_rBits_le_r:
  forall r1 r2,
  rNonneg r1 -> rNonneg r2 ->
  rangeDisjoint r1 r2 = true ->
  (rBits r2 <= rBits (commonRangeDisj r1 r2))%N.
Proof.
  intros.
  apply N.lt_le_incl.
  apply commonRangeDisj_rBits_lt_r; auto.
Qed.


Lemma outside_commonRangeDisj_l:
  forall r1 r2 i,
  rNonneg r1 -> rNonneg r2 ->
  rangeDisjoint r1 r2 = true ->
  inRange i (commonRangeDisj r1 r2) = false ->
  inRange i r1 = false.
Proof.
  intros.
  assert (rBits r1 <= rBits (commonRangeDisj r1 r2))%N
    by (apply commonRangeDisj_rBits_le_l; auto).
  rewrite <- not_true_iff_false in H2.
  rewrite <- not_true_iff_false.
  contradict H2.
  clear H1.

  rewrite -> N2Z.inj_le in H3.

  destruct r1 as [p1 b1], r2 as [p2 b2]. simpl in *.
  set (b := msDiffBit _ _) in *.
  apply Z.eqb_eq in H2.
  apply Z.eqb_eq.

  rewrite -> Z.shiftr_shiftl_r by nonneg.
  replace (Z.of_N b) with (Z.of_N b1 + (Z.of_N b - Z.of_N b1)) at 1 by omega.
  rewrite <- Z.shiftr_shiftr by omega.
  rewrite -> H2 by omega.
  reflexivity.
Qed.

Lemma outside_commonRangeDisj_r:
  forall r1 r2 i,
  rNonneg r1 -> rNonneg r2 ->
  rangeDisjoint r1 r2 = true ->
  inRange i (commonRangeDisj r1 r2) = false ->
  inRange i r2 = false.
Proof.
  intros.
  assert (rBits r2 <= rBits (commonRangeDisj r1 r2))%N
    by (apply commonRangeDisj_rBits_le_r; auto).
  rewrite <- not_true_iff_false in H2.
  rewrite <- not_true_iff_false.
  contradict H2.
  clear H1.

  rewrite -> N2Z.inj_le in H3.

  destruct r1 as [p1 b1], r2 as [p2 b2]. simpl in *.
  set (b := msDiffBit _ _) in *.
  apply Z.eqb_eq in H2.
  apply Z.eqb_eq.

  subst b.
  rewrite -> msDiffBit_shiftr_same by nonneg.
  set (b := msDiffBit _ _) in *.

  rewrite -> Z.shiftr_shiftl_r by nonneg.
  replace (Z.of_N b) with (Z.of_N b2 + (Z.of_N b - Z.of_N b2)) at 1 by omega.
  rewrite <- Z.shiftr_shiftr by omega.
  rewrite -> H2 by omega.
  reflexivity.
Qed.

Lemma commonRangeDisj_rBits_pos:
  forall r1 r2,
    rNonneg r1 -> rNonneg r2 ->
    (0 < rBits (commonRangeDisj r1 r2))%N.
Proof.
  intros.
  destruct r1 as [p1 b1], r2 as [p2 b2].
  apply msDiffBit_pos.
Qed.

Lemma commonRangeDisj_rNonneg:
  forall r1 r2,
    rNonneg r1 -> rNonneg r2 ->
    rNonneg (commonRangeDisj r1 r2).
Proof.
  intros.
  destruct r1 as [p1 b1], r2 as [p2 b2].
  simpl in *.
  rewrite Z.shiftr_nonneg, Z.shiftl_nonneg.
  assumption.
Qed.

Lemma commonRangeDisj_rBits_Different:
  forall r1 r2,
    rNonneg r1 -> rNonneg r2 ->
    rangeDisjoint r1 r2 = true ->
      Z.testbit (rPrefix r1) (Z.pred (Z.of_N (rBits (commonRangeDisj r1 r2))))
   <> Z.testbit (rPrefix r2) (Z.pred (Z.of_N (rBits (commonRangeDisj r1 r2)))).
Proof.
  intros.
  destruct r1 as [p1 b1], r2 as [p2 b2]. simpl in *.
  apply msDiffBit_Different; try nonneg.
  (* From here on might be worth a lemma of its own *)
  unfold rangeDisjoint in H1.
  apply negb_true_iff in H1.
  apply not_true_iff_false in H1.
  contradict H1.
  unfold isSubrange. simpl.
  apply orb_true_iff.
  destruct (N.le_ge_cases b2 b1).
  * right.
    rewrite andb_true_iff.
    rewrite N.leb_le. constructor; auto.
    rewrite Z.eqb_eq.
    rewrite <- H1.
    rewrite -> Z.shiftr_shiftl_l by nonneg.
    replace (Z.of_N b1 - Z.of_N b1) with 0 by omega.
    reflexivity.
  * left.
    rewrite andb_true_iff.
    rewrite N.leb_le. constructor; auto.
    rewrite Z.eqb_eq.
    rewrite -> H1.
    rewrite -> Z.shiftr_shiftl_l by nonneg.
    replace ((Z.of_N b2 - Z.of_N b2)) with 0 by omega.
    reflexivity.
Qed.

Lemma common_of_halves:
  forall r,
  (0 < rBits r)%N ->
  r = commonRangeDisj (halfRange r false) (halfRange r true).
Proof.
  intros.
  destruct r as [p b].
  unfold commonRangeDisj, halfRange, rPrefix, rBits, snd in *.
  assert (0 <= Z.pred (Z.of_N b)) by Nomega.
  replace (msDiffBit _ _) with b.
  * f_equal.
    rewrite -> Z.shiftl_shiftl by omega.
    replace (1 + Z.of_N (N.pred b)) with (Z.of_N b) by Nomega.
    rewrite -> Z.shiftr_shiftl_l by nonneg.
    replace (Z.of_N b - Z.of_N b) with 0 by omega.
    reflexivity.
  * unfold msDiffBit.
    rewrite -> N2Z.inj_pred by assumption.
    replace (Z.lxor _ _) with (2^Z.pred (Z.of_N b)).
    { rewrite -> Z.log2_pow2 by assumption.
      rewrite Z.succ_pred.
      rewrite N2Z.id.
      reflexivity.
    }
    
    rewrite Z.shiftl_lor.
    rewrite -> Z.shiftl_shiftl by omega.
    replace (1 + Z.pred (Z.of_N b)) with (Z.of_N b) by omega.
    rewrite Z.shiftl_1_l.

    apply Z.bits_inj_iff'; intros j ?.
    rewrite Z.lxor_spec.
    rewrite Z.lor_spec.
    rewrite -> Z.pow2_bits_eqb by assumption.
    rewrite -> Z.shiftl_spec by assumption.

    match goal with [ |- context [?x =? ?y]] => destruct (Z.eqb_spec x y) end.
    + subst.
      rewrite -> Z.testbit_neg_r by omega.
      reflexivity.
    + destruct (Z.testbit p (j - Z.of_N b)); simpl; auto.
Qed.

Lemma isSubrange_halfRange_commonRangeDisj:
  forall r1 r2,
    rNonneg r1 ->
    rNonneg r2 ->
    rangeDisjoint r1 r2 = true ->
    isSubrange r1
    (halfRange (commonRangeDisj r1 r2)
       (Z.testbit (rPrefix r1)
          (Z.pred (Z.of_N (rBits (commonRangeDisj r1 r2)))))) = true.
Proof.
  intros.
  assert (Hbitslt: (rBits r1 < rBits (commonRangeDisj r1 r2))%N) by
        (apply msDiffBit_lt_l; auto).
  assert (Hbitspos: (0 < rBits (commonRangeDisj r1 r2))%N) by
        (apply msDiffBit_pos; auto).

  destruct r1 as [p1 b1], r2 as [p2 b2].
  unfold isSubrange, inRange, halfRange, commonRangeDisj, rBits, rPrefix, snd in *.
  apply andb_true_iff; split.
  * rewrite Z.eqb_eq.
    rewrite -> N2Z.inj_pred by auto.
    apply Z.bits_inj_iff'. intros j?.
    rewrite -> Z.shiftr_shiftl_r by nonneg.
    rewrite -> Z.shiftr_shiftl_r by nonneg.
    rewrite -> Z.shiftr_spec by nonneg.
    rewrite -> Z.shiftl_spec by Nomega.
    match goal with [ |- context [if ?c then _ else _] ] => destruct c eqn:Htestbit end.
    + rewrite Z.lor_spec.
      rewrite testbit_1.
      assert (Hj : j = 0 \/ 0 <= j - 1) by omega.
      destruct Hj.
      - subst.
        replace (0 =? 0) with true by reflexivity.
        simpl (0 + _).
        rewrite Htestbit.
        rewrite orb_true_r.
        reflexivity.
      - replace (j =? 0) with false by (symmetry; rewrite Z.eqb_neq; omega).
        rewrite orb_false_r.
        rewrite -> Z.shiftl_spec by nonneg.
        rewrite -> Z.shiftr_spec by assumption.
        f_equal.
        omega.
    + assert (Hj : j = 0 \/ 0 <= j - 1) by omega.
      destruct Hj.
      - subst.
        simpl (0 + _).
        rewrite Htestbit.
        rewrite -> Z.shiftl_spec by nonneg.
        symmetry.
        apply Z.testbit_neg_r; omega.
      - rewrite -> Z.shiftl_spec by nonneg.
        rewrite -> Z.shiftr_spec by assumption.
        f_equal.
        omega. 
  * rewrite N.leb_le. Nomega.
Qed.

(** *** Operation: [commonRange]

The join of the semi-lattice.
*)

Definition commonRange : range -> range -> range :=
  fun r1 r2 =>
    if isSubrange r1 r2 then r2 else
    if isSubrange r2 r1 then r1 else
    commonRangeDisj r1 r2.

Lemma commonRange_idem:
  forall r, commonRange r r = r.
Proof.
  intros r.
  unfold commonRange.
  rewrite isSubrange_refl.
  reflexivity.
Qed.

Lemma disjoint_commonRange:
  forall r1 r2,
  rangeDisjoint r1 r2 = true ->
  commonRange r1 r2 = commonRangeDisj r1 r2.
Proof.
  intros.
  unfold rangeDisjoint in H. unfold commonRange.
  apply negb_true_iff in H.
  rewrite -> orb_false_iff in H.
  destruct H.
  rewrite H, H0.
  reflexivity.
Qed.

Lemma isSubrange_commonRange_r:
  forall r1 r2,
  isSubrange r1 r2 = true->
  commonRange r1 r2 = r2.
Proof.
  intros.
  unfold commonRange.
  rewrite H.
  reflexivity.
Qed.


Lemma isSubrange_commonRange_l:
  forall r1 r2,
  isSubrange r2 r1 = true->
  commonRange r1 r2 = r1.
Proof.
  intros.
  unfold commonRange.
  destruct (isSubrange r1 r2) eqn:?.
  * apply isSubrange_antisym; auto. 
  * rewrite H. reflexivity.
Qed.

Lemma isSubrange_commonRange_l':
  forall r1 r2,
  rNonneg r1 ->
  rNonneg r2 ->
  isSubrange r1 (commonRange r1 r2) = true.
Proof.
  intros.
  unfold commonRange.
  destruct (isSubrange r1 r2) eqn:H12.
  { assumption. }
  destruct (isSubrange r2 r1) eqn:H21.
  { apply isSubrange_refl. }

  assert (rangeDisjoint r1 r2 = true)
    by (unfold rangeDisjoint; rewrite H12, H21; reflexivity).
  clear H12 H21.

  destruct r1 as [p1 b1], r2 as [p2 b2].
  unfold isSubrange, commonRangeDisj, isSubrange, inRange, rPrefix, rBits, snd.

  apply andb_true_iff; split.
  * remember (msDiffBit _ _) as b.
    rewrite Z.eqb_eq.
    reflexivity.
  * rewrite N.leb_le.
    change (rBits (p1, b1) <= msDiffBit (rPrefix (p1, b1)) (rPrefix (p2, b2)))%N.
    apply N.lt_le_incl.
    apply msDiffBit_lt_l; auto.
Qed.

Lemma commonRange_sym:
  forall r1 r2,
  rNonneg r1 ->
  rNonneg r2 ->
  commonRange r1 r2 = commonRange r2 r1.
Proof.
  intros.
  unfold commonRange.
  destruct (isSubrange r1 r2) eqn:H12, (isSubrange r2 r1) eqn:H21; auto.
  * apply isSubrange_antisym; auto.
  * apply commonRangeDisj_sym; auto.
Qed.

Lemma isSubrange_commonRange_r':
  forall r1 r2,
  rNonneg r1 ->
  rNonneg r2 ->
  isSubrange r2 (commonRange r1 r2) = true.
Proof.
  intros.
  rewrite commonRange_sym; auto.
  rewrite isSubrange_commonRange_l'; auto.
Qed.

Lemma isSubrange_commonRange:
  forall r1 r2 r3,
  rNonneg r1 ->
  rNonneg r2 ->
  isSubrange (commonRange r1 r2) r3 = isSubrange r1 r3 && isSubrange r2 r3.
Proof.
  intros ??? Hnn1 Hnn2.
  enough (isSubrange (commonRange r1 r2) r3 = true <-> isSubrange r1 r3 && isSubrange r2 r3 = true)
    by (match goal with [ |- ?x = ?y ] => destruct x, y end; intuition; try congruence; symmetry; intuition).
  split; intro.
  * rewrite -> andb_true_iff.
    split.
    + eapply isSubrange_trans; [apply isSubrange_commonRange_l'|eassumption]; auto.
    + eapply isSubrange_trans; [apply isSubrange_commonRange_r'|eassumption]; auto.
  * rewrite -> andb_true_iff in H. destruct H.
    unfold commonRange.
    destruct (isSubrange r1 r2) eqn:H12.
    { destruct (isSubrange r1 r3) eqn:?, (isSubrange r2 r3) eqn:?; auto. }
    destruct (isSubrange r2 r1) eqn:H21.
    { destruct (isSubrange r1 r3) eqn:?, (isSubrange r2 r3) eqn:?; auto. }

    assert (rangeDisjoint r1 r2 = true)
      by (unfold rangeDisjoint; rewrite H12, H21; reflexivity).

    assert (rBits (commonRangeDisj r1 r2) <= rBits r3)%N.
      destruct r1 as [p1 b1], r2 as [p2 b2], r3 as [p3 b3].
      clear H12 H21.
      unfold commonRangeDisj, isSubrange, rPrefix, rBits, inRange, snd in *.
      rewrite -> andb_true_iff in H, H0.
      destruct H, H0.
      rewrite -> N.leb_le in *.
      rewrite -> Z.eqb_eq in *.
      apply msDiffBit_less; try congruence.
      change (rPrefix (p1, b1) <> rPrefix (p2, b2)).
      apply disjoint_rPrefix_differ.
      assumption.

    unfold isSubrange. rewrite andb_true_iff. split.
    + destruct r1 as [p1 b1], r2 as [p2 b2], r3 as [p3 b3].
      clear H12 H21 H0.
      unfold commonRangeDisj, isSubrange, rPrefix, rBits, inRange, snd in *.
      rewrite -> andb_true_iff in H.
      destruct H.
      rewrite -> Z.eqb_eq in *.
      subst.
      apply Z.bits_inj_iff'; intros j ?.
      rewrite -> Z.shiftr_spec by nonneg.
      rewrite -> Z.shiftl_spec by (apply OMEGA2; nonneg).
      rewrite -> Z.shiftr_spec.
      rewrite -> Z.shiftr_spec by nonneg.
      replace (j + Z.of_N b3 -
           Z.of_N (msDiffBit (Z.shiftl p1 (Z.of_N b1)) (Z.shiftl p2 (Z.of_N b2))) +
           Z.of_N (msDiffBit (Z.shiftl p1 (Z.of_N b1)) (Z.shiftl p2 (Z.of_N b2)))) with (j + Z.of_N b3) by omega.
      reflexivity.
      apply N2Z.inj_le in H2.
      omega.
    + rewrite N.leb_le. assumption.
Qed.

(** *** Range-related tactics *)

(** This heavily backracking tactic solves goals of the form [inRange i r = false],
  by exploring all [isSubrange r r2 = true] assumptions, as well
  as some known lemmas about [isSubrange]. *)

Ltac inRange_true :=
  assumption || 
  multimatch goal with 
    | [ H : isSubrange ?r1 ?r2 = true
        |- inRange ?i ?r2 = true ] =>
        apply (inRange_isSubrange_true i r1 r2 H)
  end; try inRange_true.

Ltac inRange_false :=
  assumption || 
  multimatch goal with 
    | [ H : isSubrange ?r1 ?r2 = true
        |- inRange ?i ?r1 = false ] =>
        apply (inRange_isSubrange_false i r1 r2 H)
    | [ |- inRange ?i (halfRange ?r ?b) = false ] =>
        apply (inRange_isSubrange_false i (halfRange r b) r);
          [apply isSubrange_halfRange; assumption |]
    | [ Hdis : rangeDisjoint ?r1 ?r2 = true , H : inRange ?i ?r1 = true
        |- inRange ?i ?r2 = false ] =>
        apply (rangeDisjoint_inRange_false i r1 r2 Hdis H)
    | [ Hdis : rangeDisjoint ?r2 ?r1 = true , H : inRange ?i ?r1 = true
        |- inRange ?i ?r2 = false ] =>
        rewrite rangeDisjoint_sym in Hdis;
        apply (rangeDisjoint_inRange_false i r1 r2 Hdis H)
    | [ |- inRange ?i (halfRange ?r true) = false ] =>
        eapply rangeDisjoint_inRange_false;
        [apply halves_disj; auto | inRange_true ]
    | [ |- inRange ?i (halfRange ?r false) = false ] =>
        eapply rangeDisjoint_inRange_false;
        [rewrite rangeDisjoint_sym; apply halves_disj; auto | inRange_true ]
  end; try inRange_false.

Ltac isSubrange_true :=
  assumption || 
  multimatch goal with 
    | [ |- isSubrange (commonRange ?r1 ?r2) ?r3 = true ] =>
        rewrite isSubrange_commonRange; [apply andb_true_iff; split|..]
    | [ |- isSubrange ?r1 ?r1 = true ] =>
        apply (isSubrange_refl r1)
    | [ H : isSubrange ?r1 ?r2 = true  |- isSubrange ?r1 ?r3 = true ] =>
        apply (isSubrange_trans r1 r2 r3 H)
    | [ |- isSubrange (halfRange ?r1 ?b) ?r2 = true ] =>
        apply (isSubrange_trans (halfRange r1 b) r1 r2);
          [apply isSubrange_halfRange; assumption |]
  end; try isSubrange_true.

