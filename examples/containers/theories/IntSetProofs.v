(**

* The IntSet formalization

This module contains a formalization of Haskell’s Data.IntSet which implements a set of
integers as a patricia trie.

*)

Require Import Omega.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Local Open Scope Z_scope.

(**

** Utility lemmas about [Z], [N] and bits.

Some of these certainly could live in the standard library.

*)



(**
We very often have to resolve non-negativity constraints, so we build
a tactic library for that.
*)

Lemma pos_nonneg: forall p, (0 <= N.pos p)%N. 
Proof.
  compute; congruence.
Qed.

Lemma pos_pos: forall p, (0 < N.pos p)%N. 
Proof.
  compute; congruence.
Qed.

Lemma succ_nonneg: forall n, 0 <= n -> 0 <= Z.succ n.
Proof. intros. omega. Qed.


Lemma ones_nonneg: forall n, 0 <= n -> 0 <= Z.ones n.
Proof.
  intros.
  unfold Z.ones.
  rewrite -> Z.shiftl_mul_pow2 by assumption.
  rewrite Z.mul_1_l.
  rewrite <- Z.lt_le_pred.
  apply Z.pow_pos_nonneg; auto.
  omega.
Qed.

Lemma log2_ones: forall n, 0 < n -> Z.log2 (Z.ones n) = Z.pred n.
  intros.
  unfold Z.ones.
  rewrite -> Z.shiftl_mul_pow2 by omega.
  rewrite Z.mul_1_l.
  apply Z.log2_pred_pow2.
  assumption.
Qed.

Create HintDb nonneg.
Hint Immediate N2Z.is_nonneg : nonneg.
Hint Immediate pos_nonneg : nonneg.
Hint Resolve N.le_0_l : nonneg.
Hint Resolve Z.log2_nonneg : nonneg.
Hint Resolve ones_nonneg : nonneg.
Hint Resolve succ_nonneg : nonneg.
Hint Resolve <- Z.shiftl_nonneg : nonneg.
Hint Resolve <- Z.shiftr_nonneg : nonneg.
Hint Resolve <- Z.land_nonneg : nonneg.
Hint Extern 1 (0 <= Z.succ (Z.pred (Z.of_N _))) => rewrite Z.succ_pred : nonneg.
Hint Resolve <- Z.lxor_nonneg : nonneg.
Hint Extern 0 => omega : nonneg.

Ltac nonneg := solve [auto with nonneg].



(* exists for Z, but not for N? *)
Lemma N_pow_pos_nonneg: forall a b : N, (0 < a -> 0 < a ^ b)%N.
Proof.
  intros.
  apply N.peano_ind with (n := b); intros.
  * simpl. reflexivity.
  * rewrite N.pow_succ_r; [|apply N.le_0_l].
    eapply N.lt_le_trans. apply H0.
    replace (a ^ n)%N  with (1 * a^n)%N at 1 by (apply N.mul_1_l).
    apply N.mul_le_mono_pos_r; auto.
    rewrite <- N.le_succ_l in H.
    apply H.
Qed.

Lemma ones_spec:
  forall n m : Z, 0 <= n -> Z.testbit (Z.ones n) m = (0 <=? m) && (m <? n).
Proof.
  intros.
  destruct (Z.leb_spec 0 m), (Z.ltb_spec m n);
    simpl; try apply not_true_is_false;
    rewrite Z.ones_spec_iff; omega.
Qed.

Lemma lor_ones_ones: forall b1 b2, 0 <= b1 -> 0 <= b2 ->
  Z.lor (Z.ones b1) (Z.ones b2) = Z.ones (Z.max b1 b2).
Proof.
  intros.
  apply Z.bits_inj'. intros z?.
  rewrite -> Z.lor_spec.
  repeat rewrite -> ones_spec by (try rewrite Z.max_le_iff; auto).
  destruct (Z.leb_spec 0 z), (Z.ltb_spec z b1), (Z.ltb_spec z b2), (Z.ltb_spec z (Z.max b1 b2)),  (Zmax_spec b1 b2); intuition; simpl; try omega.
Qed. 


Lemma to_N_log2: forall i, Z.to_N (Z.log2 i) = N.log2 (Z.to_N i).
Proof.
  intros.
  destruct i; try reflexivity.
  destruct p; try reflexivity.
Qed.

Lemma of_N_log2: forall n, Z.of_N (N.log2 n) = Z.log2 (Z.of_N n).
Proof.
  intros.
  destruct n; try reflexivity.
  destruct p; try reflexivity.
Qed.

(* This is a stronger version than what’s in the standard library *)
Lemma log2_le_lin': forall a : N, (* (0 <= a)%N -> *) (N.log2 a <= a)%N.
Proof. intros.
  destruct a.
  reflexivity.
  apply N.log2_le_lin.
  nonneg.
Qed.

Lemma N_land_pow2_testbit:
  forall n i, negb (N.land (2 ^ i) n =? 0)%N = N.testbit n i.
Proof.
  intros.
  destruct (N.testbit n i) eqn:Htb.
  * rewrite negb_true_iff.
    rewrite N.eqb_neq.
    contradict Htb.
    assert (N.testbit (N.land (2^i)%N n) i = false)
     by (rewrite Htb; apply N.bits_0).
    rewrite N.land_spec in H. rewrite N.pow2_bits_true in H.
    simpl in H. congruence.
  * rewrite negb_false_iff.
    rewrite N.eqb_eq.
    apply N.bits_inj.
    intro j.
    rewrite N.land_spec.
    rewrite N.pow2_bits_eqb.
    destruct (N.eqb_spec i j); subst; intuition.
Qed.

Lemma land_pow2_eq:
  forall i b, 0 <= b -> (Z.land i (2 ^ b) =? 0) = (negb (Z.testbit i b)).
Proof.
  intros ?? Hnonneg.
  destruct (Z.testbit i b) eqn:Htb; simpl.
  * rewrite Z.eqb_neq.
    contradict Htb.
    assert (Z.testbit (Z.land i (2^b)) b = false)
     by (rewrite Htb; apply Z.bits_0).
    rewrite Z.land_spec in H. rewrite Z.pow2_bits_true in H.
    rewrite andb_true_r in H.
    simpl in H. congruence.
    nonneg.
  * rewrite Z.eqb_eq.
    apply Z.bits_inj'.
    intros j ?.
    rewrite  Z.bits_0.
    rewrite Z.land_spec.
    rewrite Z.pow2_bits_eqb.
    destruct (Z.eqb_spec b j).
    + subst. rewrite Htb. reflexivity.
    + rewrite andb_false_r.  reflexivity.
    + nonneg.
Qed.

Lemma shiftr_eq_ldiff :
forall n m b,
    0 <= b ->
    Z.ldiff n (Z.ones b) = Z.ldiff m (Z.ones b) ->
    Z.shiftr n b = Z.shiftr m b.
Proof.
  intros.
    * apply Z.bits_inj'.
      intros i ?.
      rewrite -> !Z.shiftr_spec by assumption.
      apply Z.bits_inj_iff in H0.
      specialize (H0 (i + b)).
      rewrite -> !Z.ldiff_spec in H0.
      rewrite -> !Z.ones_spec_high in H0.
      simpl in *.
      rewrite -> ! andb_true_r in H0.
      assumption.
      omega.
Qed.


Lemma Z_shiftl_inj:
  forall x y n,
    0 <= n ->
    Z.shiftl x n = Z.shiftl y n <-> x = y.
Proof.
  intros; split; intro.
  * apply Z.bits_inj'.
    intros i ?.
    apply Z.bits_inj_iff in H0.
    specialize (H0 (i + n)).
    do 2 rewrite -> Z.shiftl_spec in H0 by omega.
    replace (i + n - n) with i in H0 by omega.
    assumption.
  * apply Z.bits_inj'.
    intros i ?.
    apply Z.bits_inj_iff in H0.
    specialize (H0 (i - n)).
    do 2 rewrite -> Z.shiftl_spec by omega.
    assumption.
 Qed.
 
Lemma Z_shiftl_injb:
  forall x y n, 0 <= n -> (Z.shiftl x n =? Z.shiftl y n) = (x =? y).
Proof.
  intros.
  destruct (Z.eqb_spec (Z.shiftl x n) (Z.shiftl y n)),
           (Z.eqb_spec x y); auto; try congruence; exfalso.
  apply Z_shiftl_inj in e; auto.
Qed.

 Lemma land_shiftl_ones:
   forall i n, 0 <= n -> Z.land (Z.shiftl i n) (Z.ones n) = 0.
 Proof.
   intros.
   apply Z.bits_inj'.
   intros j ?.
   rewrite Z.land_spec.
   rewrite -> Z.shiftl_spec by nonneg.
   rewrite Z.bits_0. rewrite andb_false_iff.
   destruct (Z.ltb_spec j n).
   * left. apply Z.testbit_neg_r. omega.
   * right. apply Z.ones_spec_high. omega.
 Qed.
 
Lemma testbit_1:
  forall i, Z.testbit 1 i = (i =? 0).
Proof.
  intros.
  replace 1 with (2^0) by reflexivity.
  rewrite -> Z.pow2_bits_eqb by reflexivity.
  apply Z.eqb_sym.
Qed.

(** ** Most significant differing bit

Only properly defined if both arguments are non-negative.
*)

Definition msDiffBit : Z -> Z -> N :=
  fun n m => Z.to_N (Z.succ (Z.log2 (Z.lxor n m))).

Lemma msDiffBit_sym: forall p1 p2,
  msDiffBit p1 p2 = msDiffBit p2 p1.
Proof.
  intros.
  unfold msDiffBit.
  rewrite Z.lxor_comm.
  reflexivity.
Qed.


Section msDiffBit.
  Variable p1 p2 : Z.
  Variable (Hnonneg1 : 0 <= p1).
  Variable (Hnonneg2 : 0 <= p2).
  Variable (Hne : p1 <> p2).
  
  Local Lemma lxor_pos: 0 < Z.lxor p1 p2.
  Proof.
    assert (0 <= Z.lxor p1 p2) by nonneg.
    enough (Z.lxor p1 p2 <> 0) by omega.
    rewrite Z.lxor_eq_0_iff.
    assumption.
  Qed.
  
  Lemma msDiffBit_Different:
        Z.testbit p1 (Z.pred (Z.of_N (msDiffBit p1 p2)))
     <> Z.testbit p2 (Z.pred (Z.of_N (msDiffBit p1 p2))).
  Proof.
    match goal with [ |- Z.testbit ?x ?b <> Z.testbit ?y ?b] =>
      enough (xorb (Z.testbit x b) (Z.testbit y b) = true)
      by (destruct (Z.testbit x b), (Z.testbit y b); simpl in *; congruence) end.
    rewrite <- Z.lxor_spec.
    unfold msDiffBit.
    rewrite -> Z2N.id by nonneg.
    rewrite -> Z.pred_succ.
    apply Z.bit_log2.
    apply lxor_pos.
  Qed.

  Lemma msDiffBit_Same:
    forall j,  Z.of_N (msDiffBit p1 p2) <= j ->
    Z.testbit p1 j = Z.testbit p2 j.
  Proof.
    intros.
    match goal with [ |- Z.testbit ?x ?b = Z.testbit ?y ?b] =>
      enough (xorb (Z.testbit x b) (Z.testbit y b) = false)
      by (destruct (Z.testbit x b), (Z.testbit y b); simpl in *; congruence) end.
    rewrite <- Z.lxor_spec.
    unfold msDiffBit in H.
    rewrite -> Z2N.id in H by nonneg.
    apply Z.bits_above_log2; try nonneg.
  Qed.

  Lemma msDiffBit_shiftr_same:
        Z.shiftr p1 (Z.of_N (msDiffBit p1 p2))
     =  Z.shiftr p2 (Z.of_N (msDiffBit p1 p2)).
  Proof.
    apply Z.bits_inj_iff'. intros j ?.
    rewrite -> !Z.shiftr_spec by nonneg.
    apply msDiffBit_Same.
    omega.
  Qed.
End msDiffBit.



(** ** Range sets (TODO: find name!)

A range set is a set of the form

   [a⋅2^n,…,(a+1)⋅2^n−)] where a∈Z,n≥0

which can be described by the prefix a and the shift width a.
*)

Definition range := (Z * N)%type.
Definition rPrefix : range -> Z := fun '(p,b) => Z.shiftl p (Z.of_N b).
Definition rBits : range -> N   := snd.

(** *** Operation: [inRange]

This operation checks if a value is in the range of the range set.
*)

Definition inRange : Z -> range -> bool :=
  fun n '(p,b) => Z.shiftr n (Z.of_N b) =? p.

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
    replace ((j - Z.of_N b + Z.of_N b)) with j in H0 by omega.
    rewrite H0. reflexivity.
Qed.

(** *** Operation: [isSubrange] *)

Definition isSubrange : range -> range -> bool :=
  fun r1 r2 => inRange (rPrefix r1) r2 && (rBits r1 <=? rBits r2)%N.

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
    * rewrite -> N2Z.inj_pred by assumption.
      rewrite Z.eqb_eq.
      destruct h.
      - rewrite Z.shiftl_lor.
        rewrite -> Z.shiftl_shiftl by omega.
        replace ((1 + Z.pred (Z.of_N b))) with (Z.of_N b) by omega.
        rewrite Z.shiftr_lor.
        rewrite -> Z.shiftr_shiftl_l by nonneg.
        replace (Z.of_N b - Z.of_N b) with 0 by omega.
        simpl.
        rewrite -> Z.shiftr_shiftl_r
         by (apply Z.lt_le_pred; replace 0 with (Z.of_N  0%N) by reflexivity;  apply N2Z.inj_lt; assumption).
        replace ((Z.of_N b - Z.pred (Z.of_N b))) with 1 by omega.
        replace (Z.shiftr 1 1) with 0 by reflexivity.
        rewrite Z.lor_0_r.
        reflexivity.
      - rewrite -> Z.shiftl_shiftl by omega.
        replace ((1 + Z.pred (Z.of_N b))) with (Z.of_N b) by omega.
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

Lemma halfRange_isSubrange_testbit:
  forall r1 r2 h,
   (rBits r1 < rBits r2)%N ->
   isSubrange r1 r2 = true ->
   isSubrange r1 (halfRange r2 h) = negb (xorb h (Z.testbit (rPrefix r1) (Z.pred (Z.of_N (rBits r2))))).
Proof.
  intros.
  unfold isSubrange in *.
  apply andb_true_iff in H0; destruct H0.
  assert ((0 < rBits r2)%N) by  (eapply N.le_lt_trans; try nonneg; eassumption).
  replace ((rBits r1 <=? rBits (halfRange r2 h))%N) with true.
  + rewrite andb_true_r.
    apply halfRange_inRange_testbit; auto.
  + symmetry.
    rewrite N.leb_le.
    rewrite rBits_halfRange.
    apply N.lt_le_pred; auto.
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


(** *** Operation: [rNoneg]

This predicate inciates that the range covers non-negative numbers. We 
often have to restrict ourselves to these as negative numbers have
an infinite number of bits set, which means that [msDiffBit] would not work.

If we would switch to a finite signed type, this could be dropped.
*)

Definition rNonneg : range -> Prop :=
  fun '(p,b) =>  0 <= p.

(** *** Lemmas about [msDiffBit]

These lemmas are phrased in terms of ranges, but that is just (dubious) 
convenience; maybe they should be expressed in plain values and calls to
[Z.shiftl]...
*)

Lemma msDiffBit_larger_tmp:
  forall r1 r2,
    rNonneg r1 -> rNonneg r2 -> 
    rangeDisjoint r1 r2 = true ->
    (rBits r1 <= rBits r2)%N ->
    (msDiffBit (rPrefix r1) (rPrefix r2) <= rBits r2)%N ->
    False.
Proof.
  intros.
  * assert (inRange (rPrefix r1) r2 = true).
      destruct r1 as [p1 b1], r2 as [p2 b2].
      unfold inRange, rPrefix, rBits, rNonneg,  snd in *.
      rewrite -> N2Z.inj_le in H2, H3.
      apply Z.eqb_eq.
      symmetry.
      apply Z.bits_inj_iff'. intros j?.
      replace j with ((j + Z.of_N b2) - Z.of_N b2) by omega.
      rewrite <- Z.shiftl_spec by (apply OMEGA2; nonneg).
      rewrite <- msDiffBit_Same with (p1 := (Z.shiftl p1 (Z.of_N b1))) (p2 := (Z.shiftl p2 (Z.of_N b2))); try nonneg.
      rewrite -> !Z.shiftl_spec by (apply OMEGA2; nonneg).
      rewrite -> !Z.shiftr_spec by nonneg.
      rewrite -> !Z.shiftl_spec by (apply OMEGA2; nonneg).
      f_equal. omega.

    unfold rangeDisjoint in H1.
    apply negb_true_iff in H1.
    rewrite -> orb_false_iff in H1.
    unfold isSubrange in *.
    rewrite -> !andb_false_iff in H1.
    rewrite -> !N.leb_nle in H1.
    destruct H1.
    intuition try congruence.
Qed.

  Lemma msDiffBit_larger:
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
      apply (msDiffBit_larger_tmp r2 r1 H0 H H1 H2 H3).
    * apply N.lt_le_incl in H2.
      rewrite -> N.max_r by assumption.
      apply N.nle_gt.
      intro.
      apply (msDiffBit_larger_tmp r1 r2 H H0 H1 H2 H3).
Qed.

Lemma msDiffBit_larger_l:
   forall r1 r2,
    rNonneg r1 -> rNonneg r2 -> 
    rangeDisjoint r1 r2 = true ->
    (rBits r1 < msDiffBit (rPrefix r1) (rPrefix r2))%N.
Proof.
  intros.
  apply N.le_lt_trans with (m := N.max (rBits r1) (rBits r2)).
  apply N.le_max_l.
  apply msDiffBit_larger; auto.
Qed.

Lemma msDiffBit_larger_r:
   forall r1 r2,
    rNonneg r1 -> rNonneg r2 -> 
    rangeDisjoint r1 r2 = true ->
    (rBits r2 < msDiffBit (rPrefix r1) (rPrefix r2))%N.
Proof.
  intros.
  apply N.le_lt_trans with (m := N.max (rBits r1) (rBits r2)).
  apply N.le_max_r.
  apply msDiffBit_larger; auto.
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

Lemma commonRangeDis_larger_l:
  forall r1 r2,
  rNonneg r1 -> rNonneg r2 ->
  rangeDisjoint r1 r2 = true ->
  (rBits r1 < rBits (commonRangeDisj r1 r2))%N.
Proof.
  intros.
  unfold commonRangeDisj. simpl.
  apply (msDiffBit_larger_l); auto.
Qed.

Lemma commonRangeDis_larger_r:
  forall r1 r2,
  rNonneg r1 -> rNonneg r2 ->
  rangeDisjoint r1 r2 = true ->
  (rBits r2 < rBits (commonRangeDisj r1 r2))%N.
Proof.
  intros.
  unfold commonRangeDisj. simpl.
  apply (msDiffBit_larger_r); auto.
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
    by (apply N.lt_le_incl; apply commonRangeDis_larger_l; auto).
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
    by (apply N.lt_le_incl; apply commonRangeDis_larger_r; auto).
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




(** ** IntMap-specific operations

These definitions and lemmas are used to link some concepts from the IntMap
implementation to the range sets above.
*)

Require Import GHC.Base.
Require Import GHC.Num.
Require Import Data.Bits.
Require Import Data.IntSet.Base.
Local Open Scope Z_scope.

(** We hardcode the width of the leafe bit maps to 64 bits *)

Definition WIDTH := 64%N.

(** *** Lemmas about [prefixOf] *)

Lemma prefixOf_nonneg: forall p,
  0 <= p -> 0 <= prefixOf p.
Proof.
  intros.
  unfold prefixOf, prefixBitMask, suffixBitMask.
  unfold op_zizazi__, Bits.complement, Bits__N, instance_Bits_Int, complement_Int.
  rewrite Z.land_nonneg; intuition.
Qed.
Hint Resolve prefixOf_nonneg : nonneg.

Lemma rPrefix_shiftr:
  forall e,
  rPrefix (Z.shiftr e 6, (N.log2 WIDTH)) = prefixOf e.
Proof.
  intros.
  unfold rPrefix, prefixOf, prefixBitMask, suffixBitMask.
  unfold Bits.complement, instance_Bits_Int, complement_Int.
  unfold op_zizazi__, Bits.complement, Bits__N, instance_Bits_Int, complement_Int.
  rewrite <- Z.ldiff_land.
  rewrite -> Z.ldiff_ones_r by omega.
  replace (Z.of_N (N.log2 WIDTH)) with 6 by reflexivity.

  rewrite -> Z_shiftl_inj by omega.
  reflexivity.
Qed.

Lemma prefixOf_eq_shiftr:
  forall i p, 
    (prefixOf i =? Z.shiftl p (Z.of_N (N.log2 WIDTH))) =
    (Z.shiftr i (Z.of_N (N.log2 WIDTH)) =? p).
 Proof.
   intros.
   unfold prefixOf, prefixBitMask, suffixBitMask.
   unfold Bits.complement, instance_Bits_Int, complement_Int.
   unfold op_zizazi__, Bits.complement, Bits__N, instance_Bits_Int, complement_Int.
   rewrite <- Z.ldiff_land.
   rewrite -> Z.ldiff_ones_r by omega.
   replace (Z.of_N (N.log2 WIDTH)) with 6 by reflexivity.

   rewrite -> Z_shiftl_injb by omega.
   reflexivity.
 Qed.

(** *** Lemmas about [suffixOf] *)

Lemma suffixOf_lt_WIDTH: forall e, suffixOf e < Z.of_N WIDTH.
  intros.
  unfold suffixOf, suffixBitMask.
  unfold op_zizazi__, Bits.complement, Bits__N, instance_Bits_Int, complement_Int.
  rewrite Z.land_ones.
  change (e mod 64 < 64).
  apply Z.mod_pos_bound.
  reflexivity.
  compute. congruence.
Qed.
  
Lemma suffixOf_noneg:  forall e, 0 <= suffixOf e.
  intros.
  unfold suffixOf, suffixBitMask.
  unfold op_zizazi__, Bits.complement, Bits__N, instance_Bits_Int, complement_Int.
  rewrite Z.land_ones.
  apply Z_mod_lt.
  reflexivity.
  compute. congruence.
Qed.


(** *** [rMask]
Calculates a mask in the sense of the IntSet implementation:
A single bit set just to the right of the prefix.
(Somewhat illdefined for singleton ranges).
*)

Definition rMask   : range -> Z :=
   fun '(p,b) => 2^(Z.pred (Z.of_N b)).

(** *** Operation: [bitmapInRange]

Looks up values, which are in the given range, as bits in the given bitmap.
*)

Definition bitmapInRange r bm i :=
  if inRange i r then N.testbit bm (Z.to_N (Z.land i (Z.ones (Z.of_N (rBits r)))))
                 else false.


(** *** Operation: [isTipPrefix]

A Tip prefix is a number with [N.log2 WIDTH] zeros at the end.
*)

Definition isTipPrefix (p : Z) := Z.land p suffixBitMask = 0.

Lemma isTipPrefix_suffixMask: forall p, isTipPrefix p -> Z.land p suffixBitMask = 0.
Proof. intros.  apply H. Qed.

Lemma isTipPrefix_prefixMask: forall p, isTipPrefix p -> Z.land p prefixBitMask = p.
Proof.
  intros.
  unfold isTipPrefix, prefixBitMask, Bits.complement, instance_Bits_Int, complement_Int in *.
  enough (Z.lor (Z.land p suffixBitMask)  (Z.land p (Z.lnot suffixBitMask)) = p).
  + rewrite H, Z.lor_0_l in H0. assumption.
  + rewrite <- Z.land_lor_distr_r.
    rewrite Z.lor_lnot_diag, Z.land_m1_r. reflexivity.
Qed.

Lemma isTipPrefix_prefixOf: forall e, isTipPrefix (prefixOf e).
Proof.
  intros.
  unfold isTipPrefix, prefixOf, prefixBitMask, suffixBitMask.
  unfold op_zizazi__, Bits.complement, Bits__N, instance_Bits_Int, complement_Int.
  rewrite Z.land_ones. rewrite <- Z.ldiff_land.
  rewrite Z.ldiff_ones_r.
  rewrite Z.shiftl_mul_pow2.
  apply Z_mod_mult.
  all: compute; congruence.
Qed.

(** *** Operation: [isBitMask]

A Tip bit mask is a number with [WIDTH] bits.
*)


Definition isBitMask (bm : N) :=
  (0 < bm /\ bm < 2^WIDTH)%N.

Definition isBitMask_testbit:
  forall bm, isBitMask bm -> (exists i, i < WIDTH /\ N.testbit bm i = true)%N.
  intros.
  exists (N.log2 bm); intuition.
  * destruct H.
    destruct (N.lt_decidable 0%N (N.log2 bm)).
    - apply N.log2_lt_pow2; try assumption.
    - assert (N.log2 bm = 0%N) by 
        (destruct (N.log2 bm); auto; contradict H1; reflexivity).
      rewrite H2. reflexivity.
  * apply N.bit_log2.
    unfold isBitMask in *.
    destruct bm; simpl in *; intuition; compute in H1; congruence.
 Qed.
 
 Lemma isBitMask_lor:
   forall bm1 bm2, isBitMask bm1 -> isBitMask bm2 -> isBitMask (N.lor bm1 bm2).
 Proof.
   intros.
   assert (0 < N.lor bm1 bm2)%N.
   * destruct (isBitMask_testbit bm1 H) as [j[??]].
     assert (N.testbit (N.lor bm1 bm2) j = true) by
       (rewrite N.lor_spec, H2; auto).
     enough (0 <> N.lor bm1 bm2)%N by 
       (destruct (N.lor bm1 bm2); auto; try congruence; apply pos_pos).
     contradict H3; rewrite <- H3.
     rewrite N.bits_0. congruence.
   split; try assumption.
   * unfold isBitMask in *; destruct H, H0.
     rewrite N.log2_lt_pow2; auto.
     rewrite N.log2_lor.
     apply N.max_lub_lt; rewrite <- N.log2_lt_pow2; auto.
 Qed.


Lemma isBitMask_suffixOf: forall e, isBitMask (bitmapOf e).
  intros.
  unfold isBitMask, bitmapOf, suffixOf, suffixBitMask, bitmapOfSuffix, shiftLL.
  unfold op_zizazi__, Bits.complement, Bits__N, instance_Bits_Int, complement_Int.
  unfold fromInteger, Num_Word__.
  rewrite N.shiftl_mul_pow2, N.mul_1_l.
  rewrite Z.land_ones; [|compute; congruence].
  constructor.
  * apply N_pow_pos_nonneg. reflexivity.
  * apply N.pow_lt_mono_r. reflexivity.
    change (Z.to_N (e mod 64) < Z.to_N 64)%N.
    apply Z2N.inj_lt.
    apply Z.mod_pos_bound; compute; congruence.
    compute;congruence.
    apply Z.mod_pos_bound; compute; congruence.
Qed.

(** ** Well-formed IntSets.

This section introduces the predicate to describe the well-formedness of
an IntSet. It has parameters that describe the range that this set covers,
and a function that carries it denotation. This way, invariant preserveratin
and functional correctness of an operation can be expressed in one go.
*)

Inductive Desc : IntSet -> range -> (Z -> bool) -> Prop :=
  | DescTip : forall p bm r f,
    0 <= p ->
    p = rPrefix r ->
    rBits r = N.log2 WIDTH ->
    (forall i, f i = bitmapInRange r bm i) ->
    isBitMask bm ->
    Desc (Tip p bm) r f
  | DescBin : forall s1 r1 f1 s2 r2 f2 p msk r f,
    Desc s1 r1 f1 ->
    Desc s2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = rPrefix r ->
    msk = rMask r -> 
    (forall i, f i = f1 i || f2 i) ->
    Desc (Bin p msk s1 s2) r f.

Inductive WF : IntSet -> Prop :=
  | WFEmpty : WF Nil
  | WFNonEmpty : forall s r f (HD : Desc s r f), WF s.

(** *** Specifying [member] *)

(** *** Specifying [singleton] *)

(** *** Specifying [insert] *)


(** *** Instantiationg the [FSetInterface] *)

Require Import Coq.FSets.FSetInterface.
Require Import Coq.Structures.OrderedTypeEx.

Module Foo: WSfun(N_as_OT).
  Module OrdFacts := OrderedTypeFacts(N_as_OT).

  (* We are saying [N] instead of [Z] to force the invariant that
     all elements have a finite number of bits. The code actually
     works with [Z]. *)
  Definition elt := N.

  (* Well-formedness *)
  
  Definition t := {s : IntSet | WF s}.
  Definition pack (s : IntSet) (H : WF s): t := exist _ s H.

  Notation "x <-- f ;; P" :=
    (match f with
     | exist x _ => P
     end) (at level 99, f at next level, right associativity).

  Definition In_set x (s : IntSet) :=
    member x s = true.
  
  Definition In x (s' : t) :=
    s <-- s' ;;
    In_set (Z.of_N x) s.

  Definition Equal_set s s' := forall a : Z, In_set a s <-> In_set a s'.
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Definition empty : t := pack empty WFEmpty.
  Definition is_empty : t -> bool := fun s' => 
    s <-- s' ;; null s.
  
  Lemma empty_1 : Empty empty.
  Proof. unfold Empty; intros a H. inversion H. Qed.



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
    
    Lemma testbit_halfRange:
      forall r h,
      (0 < rBits r)%N ->
      Z.testbit (rPrefix (halfRange r h)) (Z.pred (Z.of_N (rBits r))) = h.
    Proof.
      intros.
      destruct r as [p b].
      unfold rPrefix, halfRange, rBits, snd in *.
      assert (0 <= Z.pred (Z.of_N b)).
      * apply Z.lt_le_pred.
        replace 0 with (Z.of_N 0)%N by reflexivity.
        apply N2Z.inj_lt.
        assumption.
      rewrite -> Z.shiftl_spec by auto.
      rewrite -> N2Z.inj_pred by auto.
      replace ((Z.pred (Z.of_N b) - Z.pred (Z.of_N b))) with 0 by omega.
      destruct h;
        try rewrite Z.lor_spec;
        rewrite -> Z.shiftl_spec by omega;
        rewrite -> Z.testbit_neg_r by omega;
        reflexivity.
    Qed.
    
    Lemma halves_disj_aux_aux:
      forall r h1 h2,
      (0 < rBits r)%N ->
      h2 = negb h1 ->
      isSubrange (halfRange r h1) (halfRange r h2) = false.
    Proof.
      intros. subst.
      assert ((rBits (halfRange r h1) < rBits r)%N)
        by (rewrite -> rBits_halfRange; apply N.lt_pred_l; intro; rewrite H0 in H; eapply N.lt_irrefl; eassumption).
      rewrite -> halfRange_isSubrange_testbit by (auto; apply isSubrange_halfRange; auto).
      rewrite -> testbit_halfRange by assumption.
      destruct h1; reflexivity.
    Qed.

    Lemma halves_disj_aux:
      forall r,
      (0 < rBits r)%N ->
      rangeDisjoint (halfRange r false) (halfRange r true) = true.
    Proof.
      intros.
      unfold rangeDisjoint.
      erewrite halves_disj_aux_aux by auto.
      erewrite halves_disj_aux_aux by auto.
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
        eapply N.le_trans; eauto.
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
      assert (Z.of_N b1 <= Z.of_N b2) by (apply N2Z.inj_le; auto).
      rewrite -> Z.eqb_eq in *.
      apply Z.bits_inj_iff'; intros j ?.
      apply Z.bits_inj_iff in H; specialize (H (j + Z.of_N b2 - Z.of_N b1)).
      apply Z.bits_inj_iff in H0; specialize (H0 j).
      rewrite -> Z.shiftr_spec in * by nonneg.
      rewrite -> Z.shiftl_spec in * by (apply OMEGA2; nonneg).
      rewrite <- H.
      rewrite <- H0.
      replace ((j + Z.of_N b2 - Z.of_N b1 + Z.of_N b1)) with (j + Z.of_N b2) by omega.
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

    Lemma halves_disj:
      forall r1 r2 r,
      (0 < rBits r)%N ->
      isSubrange r1 (halfRange r false) = true ->
      isSubrange r2 (halfRange r true) = true ->
      rangeDisjoint r1 r2 = true.
    Proof.
      intros.
      eapply isSubrange_disj_disj_l; [eassumption|].
      eapply isSubrange_disj_disj_r; [eassumption|].
      apply halves_disj_aux.
      auto.
    Qed.

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


    Lemma common_of_halves:
      forall r,
      (0 < rBits r)%N ->
      r = commonRangeDisj (halfRange r false) (halfRange r true).
    Proof.
      intros.
      destruct r as [p b].
      unfold commonRangeDisj, halfRange, rPrefix, rBits, snd in *.
      assert (0 <= Z.pred (Z.of_N b)).
      * apply Z.lt_le_pred.
        replace 0 with (Z.of_N 0)%N by reflexivity.
        apply N2Z.inj_lt.
        assumption.

      replace (msDiffBit _ _) with b.
      * f_equal.
        rewrite -> Z.shiftl_shiftl by omega.
        rewrite -> N2Z.inj_pred by assumption.
        replace (1 + Z.pred (Z.of_N b)) with (Z.of_N b) by omega.
        rewrite -> Z.shiftr_shiftl_l by nonneg.
        replace ((Z.of_N b - Z.of_N b)) with 0 by omega.
        reflexivity.
      * unfold msDiffBit.
        rewrite -> N2Z.inj_pred by assumption.
        replace (Z.lxor _ _) with (2^Z.pred (Z.of_N b)).
        + rewrite -> Z.log2_pow2 by assumption.
          rewrite Z.succ_pred.
          rewrite N2Z.id.
          reflexivity.

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
        * subst.
          rewrite -> Z.testbit_neg_r by omega.
          reflexivity.
        * destruct (Z.testbit p (j - Z.of_N b)); simpl; auto.
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

  Lemma isTipPrefix_shiftl_shiftr:
     forall p, isTipPrefix p -> p = Z.shiftl (Z.shiftr p 6) 6.
  Proof.
    intros.
    rewrite <- Z.ldiff_ones_r.
    rewrite Z.ldiff_land.
    symmetry.
    apply isTipPrefix_prefixMask. assumption.
    omega.
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
     replace ((Z.of_N b2 - Z.of_N b2)) with 0 by omega. simpl.
     rewrite Z.eqb_neq.
     congruence.
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
    assert (b1 = b2) by (apply N.le_antisymm; auto); subst.
    rewrite -> Z.shiftr_shiftl_l in H by nonneg.
    rewrite -> Z.shiftr_shiftl_l in H1 by nonneg.
    replace (Z.of_N b2 - Z.of_N b2) with 0 in * by omega.
    simpl in *.
    rewrite -> Z.eqb_eq in *.
    congruence.
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

  Lemma smaller_inRange_iff_subRange:
    forall r1 r2,
      (rBits r1 < rBits r2)%N ->
      inRange (rPrefix r1) r2 = isSubrange r1 r2.
  Proof.
    intros.
    unfold isSubrange.
    enough (Htmp : (rBits r1 <=? rBits r2)%N = true)
      by (rewrite Htmp; rewrite andb_true_r; reflexivity).
    apply N.leb_le.
    apply N.lt_le_incl.
    auto.
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
  
  Lemma halfRange_smaller:
    forall r h, (0 < rBits r)%N -> (rBits (halfRange r h) < rBits r)%N.
  Proof.
    intros.
    destruct r as [p b].
    unfold halfRange.
    simpl in *.
    apply N.lt_pred_l.
    intro. subst. inversion H.
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
    * assumption.
    destruct (isSubrange r2 r1) eqn:H21.
    * apply isSubrange_refl.

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
      apply msDiffBit_larger_l; auto.
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
  
  Lemma msDiffBit_less:
    forall z1 z2 b,
      z1 <> z2 ->
      Z.shiftr z1 (Z.of_N b) = Z.shiftr z2 (Z.of_N b) ->
      (msDiffBit z1 z2 <= b)%N.
  Proof.
    intros.
    unfold msDiffBit.
    enough (Z.log2 (Z.lxor z1 z2) < Z.of_N b)
      by (apply N2Z.inj_le; rewrite -> Z2N.id by nonneg; omega).
    rewrite <- Z.lxor_eq_0_iff in H0.
    rewrite <- Z.shiftr_lxor in H0.
    apply Z.shiftr_eq_0_iff in H0.
    rewrite -> Z.lxor_eq_0_iff in H0.
    intuition.
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
      * destruct (isSubrange r1 r3) eqn:?, (isSubrange r2 r3) eqn:?; auto.
      destruct (isSubrange r2 r1) eqn:H21.
      * destruct (isSubrange r1 r3) eqn:?, (isSubrange r2 r3) eqn:?; auto.

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
      * destruct r1 as [p1 b1], r2 as [p2 b2], r3 as [p3 b3].
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
      * rewrite N.leb_le. assumption.
    Qed.

    Lemma Desc_rNonneg:
      forall {s r f}, Desc s r f -> rNonneg r.
    Proof.
      intros ??? HD.
      induction HD; subst.
      * destruct r. simpl in *. apply Z.shiftl_nonneg in H. assumption.
      * erewrite <- rNonneg_subrange.
        erewrite <- rNonneg_subrange.
        apply IHHD1.
        eassumption.
        apply isSubrange_halfRange.
        assumption.
    Qed.

    Lemma Desc_larger_WIDTH:
      forall {s r f}, Desc s r f -> (N.log2 WIDTH <= rBits r)%N.
    Proof.
      intros ??? HD.
      induction HD; subst.
      * destruct r. simpl in *. subst. reflexivity.
      * etransitivity. apply IHHD1.
        etransitivity. eapply subRange_smaller. eassumption.
        eapply subRange_smaller. apply isSubrange_halfRange.
        assumption.
    Qed.

   Lemma Desc_outside:
     forall {s r f i}, Desc s r f -> inRange i r = false -> f i = false.
   Proof.
     intros ???? HD Houtside.
     induction HD;subst.
     * rewrite H2.
       unfold bitmapInRange.
       rewrite Houtside.
       reflexivity.
     * assert (Hdisj : rangeDisjoint r1 r2 = true) by (eapply halves_disj; eauto).
       rewrite H4; clear H4.
       rewrite IHHD1. rewrite IHHD2. reflexivity.
       + eapply inRange_isSubrange_false. eassumption.
         eapply inRange_isSubrange_false. apply isSubrange_halfRange. auto.
         auto.
       + eapply inRange_isSubrange_false. eassumption.
         eapply inRange_isSubrange_false. apply isSubrange_halfRange. auto.
         auto.
   Qed.

    Lemma Desc_neg_false:
     forall {s r f i}, Desc s r f -> ~ (0 <= i) -> f i = false.
    Proof.
      intros.
      assert (rNonneg r) by apply (Desc_rNonneg H).
      apply (Desc_outside H).
      destruct r as [p b]; simpl in *.
      unfold inRange.
      rewrite Z.eqb_neq.
      contradict H0.
      rewrite <- (Z.shiftr_nonneg i (Z.of_N b)).
      rewrite H0.
      nonneg.
    Qed.

   (* This lemma shows that the way the code gets the upper bits above a one-bit-mask
      is correct *)
   Lemma mask_to_upper_bits:
    forall b, 
      0 <= b ->
      (Z.lxor (Z.lnot (Z.pred (2 ^ b))) (2 ^ b)) =
      Z.lnot (Z.ones (Z.succ b)).
   Proof.
    intros.
     rewrite <- Z.ones_equiv.
     rewrite <- Z.lnot_lxor_l.
     apply Z.bits_inj_iff'. intros j?.
     rewrite -> Z.lnot_spec by nonneg.
     rewrite -> Z.lnot_spec by nonneg.
     rewrite -> Z.lxor_spec.
     rewrite -> ones_spec by nonneg.
     rewrite -> ones_spec by nonneg.
     rewrite -> Z.pow2_bits_eqb by nonneg.
     destruct (Z.leb_spec 0 j), (Z.ltb_spec j b), (Z.ltb_spec j (Z.succ b)), (Z.eqb_spec b j);
        simpl; try congruence; omega.
   Qed.

   Lemma nomatch_spec:
      forall i r,
      (0 < rBits r)%N ->
      nomatch i (rPrefix r) (rMask r) =
      negb (inRange i r).
   Proof.
     intros.
     destruct r as [p b]. simpl in *.
     unfold nomatch, zero, inRange.
     unfold op_zsze__, op_zeze__, Eq_Char___, Eq_Integer___, op_zsze____, op_zeze____.
     unfold mask.
     rewrite -> mask_to_upper_bits.
     f_equal.
     rewrite <- Z.ldiff_land.
     rewrite -> Z.ldiff_ones_r by nonneg.
     rewrite Z.succ_pred.
     rewrite -> Z_shiftl_injb by nonneg.
     reflexivity.

     enough (0 < Z.of_N b) by omega.
     replace 0 with (Z.of_N 0%N) by reflexivity.
     apply N2Z.inj_lt. assumption.
   Qed.

   Lemma zero_spec:
     forall i r,
      (0 < rBits r)%N ->
      zero i (rMask r) = negb (Z.testbit i (Z.pred (Z.of_N (rBits r)))).
   Proof.
     intros.
     destruct r as [p b]. simpl in *.
     unfold zero.
     apply land_pow2_eq.
     apply Z.lt_le_pred.
     change (Z.of_N 0%N < Z.of_N b).
     apply N2Z.inj_lt.
     assumption.
   Qed.

   Lemma prefixOf_eqb_spec:
      forall r i,
      (rBits r = N.log2 WIDTH)%N ->
      prefixOf i =? rPrefix r = inRange i r.
   Proof.
    intros.
    destruct r; simpl in *; subst.
    rewrite prefixOf_eq_shiftr.
    reflexivity.
   Qed.

   Lemma member_spec:
     forall {s r f i}, Desc s r f -> member i s = f i.
   Proof.
     intros ???? HD.
     induction HD; subst.
     * simpl.
       change (((prefixOf i == rPrefix r) && ((bitmapOf i .&.bm) /= #0)) = f i).

       unfold op_zsze__, op_zeze__, Eq_Char___, Eq_Integer___, op_zsze____, op_zeze____.
       rewrite -> prefixOf_eqb_spec by assumption.

       rewrite H2.

       unfold bitmapOf, bitmapOfSuffix, suffixOf, suffixBitMask, shiftLL, bitmapInRange.
       unfold op_zizazi__, Bits.complement, Bits__N, instance_Bits_Int, complement_Int.
       unfold fromInteger, Num_Word__.
       rewrite N.shiftl_mul_pow2, N.mul_1_l.
       rewrite N_land_pow2_testbit.

       rewrite H1.
       reflexivity.
     * rewrite H4. clear H4.
       simpl member.
       rewrite -> nomatch_spec by auto.
       rewrite if_negb.

       rewrite IHHD1, IHHD2. clear IHHD1 IHHD2.
       rewrite -> zero_spec by auto.
       rewrite if_negb.

       destruct (inRange i r) eqn:HIR; simpl negb.
       * destruct (Z.testbit i (Z.pred (Z.of_N (rBits r)))) eqn:Hbit.
         + enough (f1 i = false) as Hf1 by (rewrite Hf1, orb_false_l; reflexivity).
           apply (Desc_outside HD1).
           eapply inRange_isSubrange_false; [eassumption|].
           apply testbit_halfRange_false_false; auto.
         + enough (f2 i = false) as Hf2 by (rewrite Hf2, orb_false_r; reflexivity).
           apply (Desc_outside HD2).
           eapply inRange_isSubrange_false; [eassumption|].
           apply testbit_halfRange_true_false; auto.
       * assert (inRange i r2 = false).
         * eapply inRange_isSubrange_false; try eassumption.
           eapply inRange_isSubrange_false; [apply isSubrange_halfRange|]; try assumption.
         assert (inRange i r1 = false).
         * eapply inRange_isSubrange_false; try eassumption.
           eapply inRange_isSubrange_false; [apply isSubrange_halfRange|]; assumption.
         rewrite -> (Desc_outside HD1), -> (Desc_outside HD2) by auto.
         reflexivity.
   Qed.


   Lemma Desc_some_f:
     forall {s r f}, Desc s r f -> exists i, f i = true.
   Proof.
   intros ??? HD.
   induction HD; subst.
   + destruct (isBitMask_testbit _ H3) as [j[??]].
     set (i := (Z.lor (rPrefix r) (Z.of_N j))).
     exists i.

     (* This proof looks like an Isar-proof… *)
     assert (Z.log2 (Z.of_N j) < 6).
     - rewrite <- of_N_log2.
       change (Z.of_N (N.log2 j) < Z.of_N 6%N).
       apply N2Z.inj_lt.
       destruct (N.lt_decidable 0%N j).
       + apply N.log2_lt_pow2; assumption.
       + enough (j = 0)%N by (subst; compute; congruence).
         destruct j; auto; contradict H5. apply pos_pos.

    assert (inRange i r = true).
    - destruct r as [p b]; simpl in *; subst.
      replace (Z.of_N 6%N) with 6 by reflexivity.
      replace (Z.shiftr i 6) with p.
      apply (Z.eqb_refl).
      symmetry.

      subst i.
      rewrite Z.shiftr_lor.
      replace ((Z.shiftr (Z.of_N j) 6)) with 0.
      rewrite Z.lor_0_r.
      rewrite -> Z.shiftr_shiftl_l by nonneg.
      reflexivity.
      symmetry.
      apply Z.shiftr_eq_0; nonneg.

    assert ((Z.land i (Z.ones 6) = Z.of_N j)).
    - subst i.
      destruct r as [p b]; simpl in *; subst.
      rewrite Z.land_lor_distr_l.
      rewrite -> land_shiftl_ones by omega.
      rewrite Z.lor_0_l.
      rewrite Z.land_ones_low. reflexivity.
      nonneg.
      assumption.

    rewrite  H2; clear H2.
    unfold bitmapInRange.
    rewrite H6.
    rewrite H1.
    replace ((Z.of_N (N.log2 WIDTH))) with 6 by reflexivity.
    rewrite H7.
    rewrite N2Z.id.
    assumption.
  + destruct IHHD1  as [j?].
    exists j.
    rewrite H4.
    rewrite H2.
    reflexivity.
  Qed.

   Lemma Desc_has_member: 
     forall {s r f}, Desc s r f -> exists i, 0 <= i /\ member i s = true.
   Proof.
     intros ??? HD.
     destruct (Desc_some_f HD) as [j?].
     exists j.
     rewrite (member_spec HD). intuition.
     destruct (Z.leb_spec 0 j); auto.
     contradict H.
     rewrite  (Desc_neg_false HD); try congruence.
     apply Zlt_not_le. assumption.
   Qed.

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    intros. unfold Empty, In, In_set, is_empty in *. destruct s. simpl.
    induction w.
    * auto.
    * destruct (Desc_has_member  HD).
      specialize (H (Z.to_N x)).
      rewrite Z2N.id in H; try assumption; intuition.
  Qed.
  
  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof.
    intros ????.
    unfold In, In_set in *. destruct s. simpl in *.
    destruct x; try inversion H. inversion H0.
  Qed.

  Lemma of_N_shiftl:
    forall n i, Z.of_N (N.shiftl n i) = Z.shiftl (Z.of_N n) (Z.of_N i).
  Proof.
    intros.
    apply Z.bits_inj_iff'; intros j?.
    replace j with (Z.of_N (Z.to_N j))
      by (rewrite -> Z2N.id by assumption; reflexivity).
    rewrite N2Z.inj_testbit.
    destruct (N.leb_spec i (Z.to_N j)).
    * rewrite -> N.shiftl_spec_high' by assumption.
      rewrite -> Z.shiftl_spec by nonneg.
      rewrite <- N2Z.inj_sub by assumption.
      rewrite N2Z.inj_testbit.
      reflexivity.
    * rewrite -> N.shiftl_spec_low by assumption.
      rewrite -> Z.shiftl_spec_low by (rewrite <- N2Z.inj_lt; assumption).
      reflexivity.
  Qed.

  Lemma Z_eq_shiftr_land_ones:
    forall i1 i2 b,
    (i1 =? i2) = (Z.shiftr i1 b =? Z.shiftr i2 b) && (Z.land i1 (Z.ones b) =? Z.land i2 (Z.ones b)).
  Proof.
    intros.
    match goal with [ |- ?b1 = ?b2 ] => destruct b1 eqn:?, b2 eqn:? end; try congruence.
    * contradict Heqb1.
      rewrite not_false_iff_true.
      rewrite andb_true_iff.
      repeat rewrite -> Z.eqb_eq in *; subst.
      auto.
    * contradict Heqb0.
      rewrite not_false_iff_true.
      rewrite -> andb_true_iff in Heqb1.
      destruct Heqb1.
      repeat rewrite -> Z.eqb_eq in *; subst.
      apply Z.bits_inj_iff'. intros j ?.
      destruct (Z.ltb_spec j b).
      * apply Z.bits_inj_iff in H0.
        specialize (H0 j).
        repeat rewrite -> Z.land_spec in H0.
        rewrite -> Z.ones_spec_low in H0.
        do 2 rewrite andb_true_r in H0.
        assumption.
        omega.
      * apply Z.bits_inj_iff in H.
        specialize (H (j - b)).
        do 2 rewrite -> Z.shiftr_spec in H by omega.
        replace (j - b + b) with j in H by omega.
        assumption.
   Qed.

  Lemma bitmapInRange_bitmapOf:
    forall e i,
    bitmapInRange (Z.shiftr e 6, N.log2 WIDTH) (bitmapOf e) i = (i =? e).
  Proof.
    intros.
    unfold bitmapInRange, inRange. simpl Z.of_N.
    rewrite <- andb_lazy_alt.
    unfold bitmapOf, bitmapOfSuffix, fromInteger, Num_Word__, shiftLL.
    unfold suffixOf, suffixBitMask.
    unfold op_zizazi__, instance_Bits_Int.
    rewrite <- Z.testbit_of_N' by nonneg.
    rewrite of_N_shiftl.
    rewrite -> Z2N.id by nonneg.
    rewrite -> Z2N.id by nonneg.
    rewrite Z.shiftl_1_l.
    rewrite -> Z.pow2_bits_eqb by nonneg.
    rewrite -> Z.eqb_sym.
    rewrite <- Z_eq_shiftr_land_ones.
    apply Z.eqb_sym.
  Qed.
    
  Lemma singleton_spec:
    forall e,
     0 <= e ->
     Desc (singleton e) (Z.shiftr e 6, N.log2 WIDTH) (fun x => x =? e).
  Proof.
    intros.
    apply DescTip; try nonneg; try apply isBitMask_suffixOf.
    symmetry; apply rPrefix_shiftr.
    intro i.
    symmetry; apply bitmapInRange_bitmapOf.
  Qed.
  
  Definition singleton : elt -> t.
    refine (fun e => pack (singleton (Z.of_N e)) _).
    unfold singleton, Prim.seq.
    eapply WFNonEmpty.
    apply singleton_spec; nonneg.
  Defined.
  
  Lemma branchMask_spec:
    forall r1 r2,
    branchMask (rPrefix r1) (rPrefix r2) = rMask (commonRangeDisj r1 r2).
  Proof.
    intros.
    destruct r1 as [p1 b1], r2 as [p2 b2].
    simpl.
    unfold branchMask.
    unfold msDiffBit.
    rewrite -> Z2N.id by nonneg.
    rewrite Z.pred_succ.
    reflexivity.
  Qed.
  
  Lemma branch_spec:
    forall r1 r2,
    mask (rPrefix r1) (rMask (commonRangeDisj r1 r2)) = rPrefix (commonRangeDisj r1 r2).
  Proof.
    intros.
    assert (0 < msDiffBit (rPrefix r1) (rPrefix r2))%N by apply msDiffBit_pos.
    destruct r1 as [p1 b1], r2 as [p2 b2].
    unfold mask.
    simpl.
    rewrite <- Z.ldiff_ones_r by nonneg.
    rewrite -> mask_to_upper_bits.
    rewrite <- Z.ldiff_land.
    rewrite Z.succ_pred.
    reflexivity.
    apply Zlt_0_le_0_pred.
    replace 0 with (Z.of_N 0%N) by reflexivity.
    apply N2Z.inj_lt.
    assumption.
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
          (apply msDiffBit_larger_l; auto).
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
      rewrite -> Z.shiftl_spec
        by (apply Z.lt_le_pred; replace 0 with (Z.of_N 0%N) by reflexivity; apply N2Z.inj_lt; assumption).
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
    * rewrite N.leb_le.
      apply N.lt_le_pred.
      assumption.
  Qed.

  Lemma link_Desc:
      forall p1' s1 r1 f1 p2' s2 r2 f2 r f,
      Desc s1 r1 f1 ->
      Desc s2 r2 f2 ->
      p1' = rPrefix r1 ->
      p2' = rPrefix r2 ->
      rangeDisjoint r1 r2 = true->
      r = commonRangeDisj r1 r2 ->
      (forall i, f i = f1 i || f2 i) ->
    Desc (link p1' s1 p2' s2) r f.
  Proof.
    intros; subst.
    unfold link.
    rewrite branchMask_spec.
    rewrite branch_spec.
    rewrite -> zero_spec by (apply commonRangeDisj_rBits_pos; eapply Desc_rNonneg; eassumption).
    rewrite if_negb.
    match goal with [ |- context [Z.testbit ?i ?b] ]  => destruct (Z.testbit i b) eqn:Hbit end.
    * assert (Hbit2 : Z.testbit (rPrefix r2) (Z.pred (Z.of_N (rBits (commonRangeDisj r1 r2)))) = false).
      + apply not_true_is_false.
        rewrite <- Hbit.
        apply not_eq_sym.
        apply commonRangeDisj_rBits_Different; try (eapply Desc_rNonneg; eassumption); auto.
      rewrite rangeDisjoint_sym in H3.
      rewrite -> commonRangeDisj_sym in * by (eapply Desc_rNonneg; eassumption).
      apply (DescBin _ _ _ _ _ _ _ _ _ f H0 H); auto.
      + apply commonRangeDisj_rBits_pos; (eapply Desc_rNonneg; eassumption).
      + rewrite <- Hbit2.
        apply isSubrange_halfRange_commonRangeDisj;
          try (eapply Desc_rNonneg; eassumption); auto.
      + rewrite <- Hbit at 1.
        rewrite -> commonRangeDisj_sym by (eapply Desc_rNonneg; eassumption).
        rewrite rangeDisjoint_sym in H3.
        apply isSubrange_halfRange_commonRangeDisj;
          try (eapply Desc_rNonneg; eassumption); auto.
      + intro i. specialize (H5 i). rewrite orb_comm. assumption.
    * assert (Hbit2 : Z.testbit (rPrefix r2) (Z.pred (Z.of_N (rBits (commonRangeDisj r1 r2)))) = true).
      + apply not_false_iff_true.
        rewrite <- Hbit.
        apply not_eq_sym.
        apply commonRangeDisj_rBits_Different; try (eapply Desc_rNonneg; eassumption); auto.
      apply (DescBin _ _ _ _ _ _ _ _ _ f H H0); auto.
      + apply commonRangeDisj_rBits_pos; (eapply Desc_rNonneg; eassumption).
      + rewrite <- Hbit.
        apply isSubrange_halfRange_commonRangeDisj;
          try (eapply Desc_rNonneg; eassumption); auto.
      + rewrite <- Hbit2 at 1.
        rewrite -> commonRangeDisj_sym by (eapply Desc_rNonneg; eassumption).
        rewrite rangeDisjoint_sym in H3.
        apply isSubrange_halfRange_commonRangeDisj;
          try (eapply Desc_rNonneg; eassumption); auto.
  Qed.

  Lemma insertBM_Desc:
    forall p' bm r1 f1,
    forall s2 r2 f2,
    forall r f, 
    Desc (Tip p' bm) r1 f1 ->
    Desc s2 r2 f2 ->
    r = commonRange r1 r2 ->
    (forall i, f i = f1 i || f2 i) ->
    Desc (insertBM p' bm s2) r f.
  Proof.
    intros ????????? HDTip HD ??; subst.
    assert (p' = rPrefix r1) by (inversion HDTip; auto); subst.
    assert (rBits r1 = N.log2 WIDTH)  by (inversion HDTip; auto).
    generalize dependent f.
    induction HD as [p2' bm2 r2 f2|s2 r2 f2 s3 r3 f3 p2' r]; subst; intros f' Hf.
    * simpl.
      unfold Prim.seq.
      unfold GHC.Base.op_zeze__, Eq_Integer___, op_zeze____.
      destruct (Z.eqb_spec (rPrefix r2) (rPrefix r1)); subst.
      + assert (r1 = r2) 
          by (inversion HDTip; destruct r1, r2; subst; simpl in *; subst; 
              rewrite -> Z_shiftl_inj in * by nonneg; congruence).
        subst.
        rewrite commonRange_idem.
        apply DescTip; auto.
        - intro j.
            rewrite Hf.
            rewrite H3.
            inversion HDTip.
            rewrite H9.
            unfold bitmapInRange.
            rewrite N.lor_spec.
            destruct (inRange j r2); reflexivity.
        - apply isBitMask_lor; auto; (inversion HDTip; auto).
      + assert (rangeDisjoint r1 r2 = true) by (apply different_prefix_same_bits_disjoint; try congruence).
        eapply link_Desc; try apply HDTip; auto.
        - apply DescTip; auto.
        - apply disjoint_commonRange; auto.
    * simpl. unfold Prim.seq.
      rewrite -> nomatch_spec by assumption.
      rewrite if_negb.
      assert (N.log2 WIDTH <= rBits r2)%N by (eapply Desc_larger_WIDTH; eauto).
      assert (rBits r2 <= rBits (halfRange r0 false))%N by (apply subRange_smaller; auto).
      assert (rBits (halfRange r0 false) < rBits r0)%N by (apply halfRange_smaller; auto).
      assert (rBits r1 < rBits r0)%N by (rewrite H; eapply N.le_lt_trans; eauto; eapply N.le_lt_trans; eauto).
      rewrite -> smaller_inRange_iff_subRange by auto.
      destruct (isSubrange r1 r0) eqn:Hsubrange.
      + rewrite -> zero_spec by assumption.
        rewrite if_negb.
        rewrite -> (isSubrange_commonRange_r _ _ Hsubrange) in *.
        rewrite <- testbit_halfRange_isSubrange; auto.
        destruct (isSubrange r1 (halfRange r0 true)) eqn:Hbit.
        - assert (isSubrange (commonRange r1 r3) (halfRange r0 true) = true)
            by (rewrite -> isSubrange_commonRange; intuition; eapply Desc_rNonneg; eassumption).
          eapply DescBin; try apply HD1; try apply IHHD2 with (f := fun j => f1 j || f3 j); auto.
          intro i. simpl. rewrite Hf. rewrite H5. destruct (f1 i), (f2 i), (f3 i); reflexivity.
        - assert (isSubrange r1 (halfRange r0 false) = true)
            by (rewrite -> smaller_subRange_other_half, -> negb_false_iff in Hbit by auto; assumption).
          assert (isSubrange (commonRange r1 r2) (halfRange r0 false) = true)
            by (rewrite -> isSubrange_commonRange; intuition; eapply Desc_rNonneg; eassumption).
           eapply DescBin; try apply HD2; try apply IHHD1 with (f := fun j => f1 j || f2 j); auto.
          intro i. simpl. rewrite Hf. rewrite H5. destruct (f1 i), (f2 i), (f3 i); reflexivity.
      + assert (rangeDisjoint r1 r0 = true) by (apply smaller_not_subrange_disjoint; auto).
        clear Hsubrange.
        eapply link_Desc; eauto; try (inversion HDTip; auto).
        eapply DescBin; eauto.
        apply disjoint_commonRange; assumption.
  Qed.

  Lemma insert_Desc:
    forall e r1,
    forall s2 r2 f2,
    forall r f, 
    0 <= e ->
    Desc s2 r2 f2 ->
    r1 = (Z.shiftr e 6, N.log2 WIDTH) ->
    r = commonRange r1 r2 ->
    (forall i, f i = (i =? e) || f2 i) ->
    Desc (insert e s2) r f.
  Proof.
    intros.
    eapply insertBM_Desc.
    eapply DescTip; try nonneg.
    symmetry. apply rPrefix_shiftr. reflexivity.
    apply isBitMask_suffixOf.
    eassumption.
    congruence.
    intros j. rewrite H3. f_equal.
    symmetry. apply bitmapInRange_bitmapOf.
  Qed.
  
  Lemma insert_Nil_Desc:
    forall e r f,
    0 <= e ->
    r = (Z.shiftr e 6, N.log2 WIDTH) ->
    (forall i, f i = (i =? e)) ->
    Desc (insert e Nil) r f.
  Proof.
    intros; subst.
    apply DescTip; try nonneg.
    symmetry. apply rPrefix_shiftr.
    intros j. rewrite H1. symmetry. apply bitmapInRange_bitmapOf.
    apply isBitMask_suffixOf.
  Qed.

  Lemma insertBM_WF:
    forall p bm s,
    0 <= p -> isTipPrefix p -> isBitMask bm -> WF s -> WF (insertBM p bm s).
  Proof.
    intros ??? Hnonneg Hp Hbm HWF.
    set (r1 := (Z.shiftr p 6, N.log2 WIDTH)).
    assert (Desc (Tip p bm) r1 (bitmapInRange r1 bm)).
    * apply DescTip; subst r1; auto.
      apply isTipPrefix_shiftl_shiftr; assumption.

    destruct HWF.
    * simpl. unfold Prim.seq.
      eapply WFNonEmpty; eauto.
    * eapply WFNonEmpty. 
      eapply insertBM_Desc; eauto.
      intro i. reflexivity.
  Qed.
  
  Definition add (e: elt) (s': t) : t.
    refine (s <-- s' ;;
            pack (insert (Z.of_N e) s) _).
    unfold insert, Prim.seq.
    apply insertBM_WF.
    nonneg.
    apply isTipPrefix_prefixOf.
    apply isBitMask_suffixOf.
    assumption.
  Defined.

  Definition remove : elt -> t -> t. Admitted.
  Definition union : t -> t -> t. Admitted.
  Definition inter : t -> t -> t. Admitted.
  Definition diff : t -> t -> t. Admitted.
    
  Definition equal : t -> t -> bool :=
    fun ws ws' => s <-- ws ;;
               s' <-- ws' ;;
               s == s'.
  
  Definition subset : t -> t -> bool :=
    fun ws ws' => s <-- ws ;;
               s' <-- ws' ;;
               isSubsetOf s s'.

  Definition eq_set : IntSet -> IntSet -> Prop := Equal_set.
  Definition eq : t -> t -> Prop := Equal.
  Definition eq_dec : forall s s' : t, {eq s s'} + {~ eq s s'}. Admitted.

  Lemma eq_set_refl : forall s, eq_set s s.
  Proof. intros; constructor; auto. Qed.
    
  Lemma eq_refl : forall s : t, eq s s.
  Proof. destruct s. unfold eq. unfold Equal. intro. apply eq_set_refl. Qed.

  Lemma eq_set_sym : forall s s', eq_set s s' -> eq_set s' s.
  Proof. intros. unfold eq_set, Equal_set in *. intro a. specialize (H a). intuition. Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. destruct s; destruct s'; 
    unfold eq, Equal in *. intros. rewrite H. intuition. Qed.

  Lemma eq_set_trans :
    forall s s' s'', eq_set s s' -> eq_set s' s'' -> eq_set s s''.
  Proof.
    intros ??? H1 H2 a.
    apply (iff_trans (H1 a) (H2 a)).
  Qed.
  
  Lemma eq_trans :
    forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
    destruct s; destruct s'; destruct s''; simpl.
    unfold eq, Equal. intros ???. rewrite H, H0. reflexivity.
  Qed.


  Definition fold : forall A : Type, (elt -> A -> A) -> t -> A -> A. Admitted.
  Definition for_all : (elt -> bool) -> t -> bool. Admitted.
  Definition exists_ : (elt -> bool) -> t -> bool. Admitted.
  Definition filter : (elt -> bool) -> t -> t. Admitted.
  Definition partition : (elt -> bool) -> t -> t * t. Admitted.
  Definition cardinal : t -> nat. Admitted.
  Definition elements : t -> list elt. Admitted.
  Definition choose : t -> option elt. Admitted.
  
  Lemma In_1 :
    forall (s : t) (x y : elt), N.eq x y -> In x s -> In y s.
  Proof. intros. destruct H. assumption. Qed.
  
  Definition mem : elt -> t -> bool := fun e s' =>
   s <-- s' ;; member (Z.of_N e) s.


  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
    
  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
  
  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true. Admitted.
  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'. Admitted.
  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true. Admitted.
  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'. Admitted.
  
  Lemma add_1 :
    forall (s : t) (x y : elt), N.eq x y -> In y (add x s).
  Proof.
    intros.
    inversion_clear H; subst.
    unfold In, add, pack, In_set; intros; destruct s as [s].
    destruct w.
    * (* Not nice that we cannot have Desc x f for empty trees. *)
      erewrite member_spec.
      Focus 2.
      apply insert_Nil_Desc; try nonneg.
      intro. reflexivity.
      simpl. rewrite Z.eqb_refl. reflexivity.
    * erewrite member_spec.
      Focus 2.
      eapply insert_Desc; try nonneg; try eassumption.
      intro. reflexivity.
      simpl. rewrite Z.eqb_refl. reflexivity.
  Qed.

  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s).
  Proof.
    intros.
    unfold In, add, pack, In_set in *; intros; destruct s as [s].
    destruct w.
    * inversion H.
    * erewrite member_spec.
      Focus 2.
      eapply insert_Desc; try nonneg; try eassumption.
      intro. reflexivity.
      simpl. rewrite orb_true_iff. right.
      erewrite  <- member_spec. eassumption. eassumption.
  Qed.

  Lemma add_3 :
    forall (s : t) (x y : elt), ~ N.eq x y -> In y (add x s) -> In y s.
  Proof.
    intros.
    unfold In, add, pack, In_set in *; intros; destruct s as [s].
    destruct w.
    * erewrite member_spec in H0.
        Focus 2.
        eapply insert_Nil_Desc; try nonneg.
        intro. reflexivity. simpl in *.
      rewrite -> Z.eqb_eq in H0.
      rewrite -> N2Z.inj_iff in H0.
      congruence.
    * erewrite member_spec in H0.
        Focus 2.
        eapply insert_Desc; try nonneg; try eassumption.
        intro. reflexivity. simpl in *.
      rewrite -> orb_true_iff in H0.
      rewrite -> Z.eqb_eq in H0.
      rewrite -> N2Z.inj_iff in H0.
      destruct H0. congruence.

      erewrite member_spec.
        Focus 2.
        eassumption.
      assumption.
  Qed.
  
  Lemma remove_1 :
    forall (s : t) (x y : elt), N.eq x y -> ~ In y (remove x s). Admitted.
  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ N.eq x y -> In y s -> In y (remove x s). Admitted.
  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s. Admitted.

  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> N.eq x y.
  Proof.
    intros.
    unfold In, In_set, singleton, pack in *.
    erewrite member_spec in H.
    Focus 2. apply singleton_spec; nonneg.
    simpl in H.
    rewrite -> Z.eqb_eq in H.
    apply N2Z.inj.
    symmetry.
    assumption.
  Qed.

  Lemma singleton_2 :
    forall x y : elt, N.eq x y -> In y (singleton x).
  Proof.
    intros.
    unfold In, In_set, singleton, pack in *.
    erewrite member_spec.
    Focus 2. apply singleton_spec; nonneg.
    simpl.
    rewrite -> Z.eqb_eq.
    congruence.
  Qed.

  Lemma union_1 :
    forall (s s' : t) (x : elt), In x (union s s') -> In x s \/ In x s'. Admitted.
  Lemma union_2 :
    forall (s s' : t) (x : elt), In x s -> In x (union s s'). Admitted.
  Lemma union_3 :
    forall (s s' : t) (x : elt), In x s' -> In x (union s s'). Admitted.
  Lemma inter_1 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s. Admitted.
  Lemma inter_2 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s'. Admitted.
  Lemma inter_3 :
    forall (s s' : t) (x : elt), In x s -> In x s' -> In x (inter s s'). Admitted.
  Lemma diff_1 :
    forall (s s' : t) (x : elt), In x (diff s s') -> In x s. Admitted.
  Lemma diff_2 :
    forall (s s' : t) (x : elt), In x (diff s s') -> ~ In x s'. Admitted.
  Lemma diff_3 :
    forall (s s' : t) (x : elt), In x s -> ~ In x s' -> In x (diff s s'). Admitted.
  Lemma fold_1 :
    forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
    fold A f s i =
    fold_left (fun (a : A) (e : elt) => f e a) (elements s) i. Admitted.
  Lemma cardinal_1 : forall s : t, cardinal s = length (elements s). Admitted.
  Lemma filter_1 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool N.eq f -> In x (filter f s) -> In x s. Admitted.
  Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool N.eq f -> In x (filter f s) -> f x = true. Admitted.
  Lemma filter_3 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool N.eq f -> In x s -> f x = true -> In x (filter f s). Admitted.
  Lemma for_all_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    For_all (fun x : elt => f x = true) s -> for_all f s = true. Admitted.
  Lemma for_all_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    for_all f s = true -> For_all (fun x : elt => f x = true) s. Admitted.
  Lemma exists_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    Exists (fun x : elt => f x = true) s -> exists_ f s = true. Admitted.
  Lemma exists_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    exists_ f s = true -> Exists (fun x : elt => f x = true) s. Admitted.
  Lemma partition_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f -> Equal (fst (partition f s)) (filter f s). Admitted.
  Lemma partition_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s). Admitted.
  Lemma elements_1 :
    forall (s : t) (x : elt), In x s -> InA N.eq x (elements s). Admitted.
  Lemma elements_2 :
    forall (s : t) (x : elt), InA N.eq x (elements s) -> In x s. Admitted.
  Lemma elements_3w : forall s : t, NoDupA N.eq (elements s). Admitted.
  Lemma choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s. Admitted.
  Lemma choose_2 : forall s : t, choose s = None -> Empty s. Admitted.

End Foo.
