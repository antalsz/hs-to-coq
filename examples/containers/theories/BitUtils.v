Require Import Omega.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Bool.Bool.
Local Open Scope Z_scope.

(** ** An omega that works for [N]

This is mostly to work around https://github.com/coq/coq/issues/6602.

*)

Ltac Nomega := rewrite ?N.pred_sub in *; zify; omega.


(** ** Utility lemmas about [Z], [N] and bits.

Some of these certainly could live in the standard library.

*)


(** *** The [nonneg] tactic *)


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
Hint Resolve Z.pow_nonneg : nonneg.
Hint Extern 1 (0 <= Z.succ (Z.pred (Z.of_N _))) => rewrite Z.succ_pred : nonneg.
Hint Resolve <- Z.lxor_nonneg : nonneg.
Hint Extern 0 => omega : nonneg.

Ltac nonneg := solve [auto with nonneg].

Lemma N_gt_0_neq:
  forall n, (n <> 0 <-> 0 < n)%N.
Proof.
  intros.
  destruct n; intuition.
  * inversion H.
  * apply pos_pos.
  * inversion H0.
Qed.

(** *** Lemmas about [N] and [Z], especially related to bits *)

Lemma N_lt_pow2_testbits:
  forall n p, (n < 2^p)%N <-> (forall j, (p <= j)%N -> N.testbit n j = false).
Proof.
  intros.
  etransitivity.
  * symmetry. apply N.div_small_iff.
    apply N.pow_nonzero; congruence.
  * rewrite <- N.shiftr_div_pow2.
    rewrite <- N.bits_inj_iff.
    split; intros H j.
    + intro.
      specialize (H (j - p)%N).
      rewrite N.shiftr_spec, N.bits_0 in * by nonneg.
      rewrite N.sub_add in H by assumption.
      assumption.
    + rewrite N.shiftr_spec, N.bits_0 by nonneg.
      apply H.
      change (0 + p <= j + p)%N.
      apply N.add_le_mono_r.
      nonneg.
Qed.

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

Lemma N_shiftl_inj:
  forall x y n,
    N.shiftl x n = N.shiftl y n <-> x = y.
Proof.
  intros; split; intro.
  * apply N.bits_inj.
    intros i.
    apply N.bits_inj_iff in H.
    specialize (H (i + n)%N).
    do 2 rewrite -> N.shiftl_spec_alt in H by omega.
    assumption.
  * subst. reflexivity.
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

Lemma N_shiftl_spec_eq:
  forall n i j,
  N.testbit (N.shiftl n i) j =
    (if j <? i then false else N.testbit n (j - i))%N.
Proof.
  intros.
  destruct (N.ltb_spec j i).
  * apply N.shiftl_spec_low; assumption.
  * apply N.shiftl_spec_high'; assumption.
Qed.

Lemma Z_shiftl_add:
  forall x y i,
  (0 <= i) ->
  Z.shiftl (x + y) i = Z.shiftl x i + Z.shiftl y i.
Proof.
  intros.
  rewrite !Z.shiftl_mul_pow2 by assumption.
  rewrite Z.mul_add_distr_r.
  reflexivity.
Qed.

Lemma N_shiftl_add:
  forall x y i,
  N.shiftl (x + y)%N i = (N.shiftl x i + N.shiftl y i)%N.
Proof.
  intros.
  rewrite !N.shiftl_mul_pow2 by assumption.
  rewrite N.mul_add_distr_r.
  reflexivity.
Qed.

Lemma testbit_1:
  forall i, Z.testbit 1 i = (i =? 0).
Proof.
  intros.
  replace 1 with (2^0) by reflexivity.
  rewrite -> Z.pow2_bits_eqb by reflexivity.
  apply Z.eqb_sym.
Qed.

Lemma N_testbit_1:
  forall i, N.testbit 1 i = (i =? 0)%N.
Proof.
  intros.
  replace 1%N with (2^0)%N by reflexivity.
  rewrite -> N.pow2_bits_eqb by reflexivity.
  apply N.eqb_sym.
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
    rewrite -> Z.shiftl_spec_low by Nomega.
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
    + apply Z.bits_inj_iff in H0.
      specialize (H0 j).
      repeat rewrite -> Z.land_spec in H0.
      rewrite -> Z.ones_spec_low in H0.
      do 2 rewrite andb_true_r in H0.
      assumption.
      omega.
    + apply Z.bits_inj_iff in H.
      specialize (H (j - b)).
      do 2 rewrite -> Z.shiftr_spec in H by omega.
      replace (j - b + b) with j in H by omega.
      assumption.
Qed.

Lemma Pos_1_testbit_succ:
  forall p i,
  Pos.testbit p~1 (N.succ i) = Pos.testbit p i.
Proof.
  induction i.
  * reflexivity.
  * simpl. rewrite Pos.pred_N_succ. reflexivity.
Qed.


Lemma Pos_0_testbit_succ:
  forall p i,
  Pos.testbit p~0 (N.succ i) = Pos.testbit p i.
Proof.
  induction i.
  * reflexivity.
  * simpl. rewrite Pos.pred_N_succ. reflexivity.
Qed.

Lemma N_bits_impl_le:
  forall a b,
  (forall i, N.testbit a i = true -> N.testbit b i = true) ->
  (a <= b)%N.
Proof.
  intros.
  induction a; try apply N.le_0_l.
  destruct b.
  * exfalso.
    refine (Pbit_faithful_0 p _).
    intro j.
    specialize (H (N.of_nat j)).
    rewrite N.bits_0 in H.
    simpl in H; rewrite Ptestbit_Pbit in H. 
    destruct (Pos.testbit_nat p j) eqn:?; intuition.
  * simpl in *.
    change (Pos.le p p0).
    revert p0 H.
    induction p; intros p0 H.
    - destruct p0 eqn:?.
      + change (p <= p1)%positive.
        apply IHp. intro i.
        specialize (H (N.succ i)).
        rewrite !Pos_1_testbit_succ in H.
        assumption.
      + exfalso.
        specialize (H 0%N).
        simpl in H. intuition congruence.
      + exfalso.
        refine (Pbit_faithful_0 p _).
        intro j.
        specialize (H (N.succ (N.of_nat j))).
        rewrite <- Nat2N.inj_succ in H at 2.
        rewrite Pos_1_testbit_succ, Ptestbit_Pbit in H. 
        destruct (Pos.testbit_nat p j) eqn:?; intuition.
    - destruct p0 eqn:?.
      + transitivity (p1~0)%positive.
        ** change (p <= p1)%positive.
          apply IHp. intro i.
          specialize (H (N.succ i)).
          rewrite Pos_0_testbit_succ, Pos_1_testbit_succ in H.
          assumption.
        ** zify. omega.
      + change (p <= p1)%positive.
        apply IHp. intro i.
        specialize (H (N.succ i)).
        rewrite !Pos_0_testbit_succ in H.
        assumption.
      + exfalso.
        refine (Pbit_faithful_0 p _).
        intro j.
        specialize (H (N.succ (N.of_nat j))).
        rewrite <- Nat2N.inj_succ in H at 2.
        rewrite Pos_0_testbit_succ, Ptestbit_Pbit in H. 
        destruct (Pos.testbit_nat p j) eqn:?; intuition.
     - apply Pos.le_1_l.
Qed.


Lemma clearbit_le:
  forall a i,
  (N.clearbit a i <= a)%N.
Proof.
  intros.
  apply N_bits_impl_le; intros j H.
  rewrite N.clearbit_eqb in H.
  rewrite andb_true_iff in *.
  intuition.
Qed.

Lemma clearbit_lt:
  forall a i,
  N.testbit a i = true ->
  (N.clearbit a i < a)%N.
Proof.
  intros.
  apply N.le_neq; split.
  * apply clearbit_le.
  * intro.
    apply N.bits_inj_iff in H0. specialize (H0 i).
    rewrite N.clearbit_eqb in H0.
    rewrite N.eqb_refl in H0.
    simpl negb in H0.
    rewrite andb_false_r in H0.
    congruence.
Qed.

Lemma ldiff_le:
  forall a b,
  (N.ldiff a b <= a)%N.
Proof.
  intros.
  apply N_bits_impl_le; intros i H.
  rewrite N.ldiff_spec in *.
  rewrite andb_true_iff in *.
  intuition.
Qed.

Lemma ldiff_lt:
  forall a b i,
  N.testbit a i = true ->
  N.testbit b i = true ->
  (N.ldiff a b < a)%N.
Proof.
  intros.
  apply N.le_neq; split.
  * apply ldiff_le.
  * intro.
    apply N.bits_inj_iff in H1. specialize (H1 i).
    rewrite N.ldiff_spec in H1.
    rewrite H, H0 in H1.
    inversion H1.
Qed.

Lemma ldiff_pow2_lt:
  forall a i,
  N.testbit a i = true ->
  (N.ldiff a (2^i) < a)%N.
Proof.
  intros.
  apply ldiff_lt with (i := i); auto.
  apply N.pow2_bits_true.
Qed.

Lemma clearbit_log2_mod:
  forall bm,
  (0 < bm)%N ->
  N.clearbit bm (N.log2 bm)%N = (bm mod (2 ^ N.log2 bm))%N.
Proof.
  intros.
  apply N.bits_inj. intro i.
  rewrite N.clearbit_eqb.
  destruct (N.eqb_spec (N.log2 bm) i); simpl negb; [|destruct (N.ltb_spec i (N.log2 bm))].
  * rewrite N.mod_pow2_bits_high by Nomega.
    simpl negb.
    apply andb_false_r.
  * rewrite N.mod_pow2_bits_low by assumption.
    apply andb_true_r.
  * rewrite N.mod_pow2_bits_high by assumption.
    rewrite N.bits_above_log2 by Nomega.
    apply andb_true_r.
Qed.

Lemma clearbit_pow2_0:
  forall n, (N.clearbit (2 ^ n) n = 0)%N.
Proof.
  intros.
  rewrite N.clearbit_spec'.
  apply N.ldiff_diag.
Qed.

Lemma clearbit_clearbit_comm:
  forall a i j, N.clearbit (N.clearbit a i) j =  N.clearbit (N.clearbit a j) i.
Proof.
  intros.
  rewrite !N.clearbit_spec'.
  rewrite !N.ldiff_ldiff_l.
  rewrite N.lor_comm at 1.
  reflexivity.
Qed.

(** ** Most significant differing bit

Only properly defined if both arguments are non-negative.
*)

Definition msDiffBit : N -> N -> N :=
  fun n m => (N.log2 (N.lxor n m) + 1)%N.

Lemma msDiffBit_sym: forall p1 p2,
  msDiffBit p1 p2 = msDiffBit p2 p1.
Proof.
  intros.
  unfold msDiffBit.
  rewrite N.lxor_comm.
  reflexivity.
Qed.


Section msDiffBit.
  Variable p1 p2 : N.
  Variable (Hne : p1 <> p2).
  
  Local Lemma lxor_pos: (0 < N.lxor p1 p2)%N.
  Proof.
    assert (0 <= N.lxor p1 p2)%N by nonneg.
    enough (N.lxor p1 p2 <> 0)%N by Nomega.
    rewrite N.lxor_eq_0_iff.
    assumption.
  Qed.
  
  Lemma msDiffBit_Different:
        N.testbit p1 (msDiffBit p1 p2 - 1)
     <> N.testbit p2 (msDiffBit p1 p2 - 1).
  Proof.
    match goal with [ |- N.testbit ?x ?b <> N.testbit ?y ?b] =>
      enough (xorb (N.testbit x b) (N.testbit y b) = true)
      by (destruct (N.testbit x b), (N.testbit y b); simpl in *; congruence) end.
    rewrite <- N.lxor_spec.
    unfold msDiffBit.
    rewrite N.add_sub.
    apply N.bit_log2.
    rewrite N.lxor_eq_0_iff.
    assumption.
  Qed.

  Lemma msDiffBit_Same:
    forall j, (msDiffBit p1 p2 <= j)%N ->
    N.testbit p1 j = N.testbit p2 j.
  Proof.
    intros.
    match goal with [ |- N.testbit ?x ?b = N.testbit ?y ?b] =>
      enough (xorb (N.testbit x b) (N.testbit y b) = false)
      by (destruct (N.testbit x b), (N.testbit y b); simpl in *; congruence) end.
    rewrite <- N.lxor_spec.
    unfold msDiffBit in H.
    apply N.bits_above_log2.
    Nomega.
  Qed.

  Lemma msDiffBit_shiftr_same:
        N.shiftr p1 (msDiffBit p1 p2)
     =  N.shiftr p2 (msDiffBit p1 p2).
  Proof.
    apply N.bits_inj_iff. intros j.
    rewrite -> !N.shiftr_spec by nonneg.
    apply msDiffBit_Same.
    Nomega.
  Qed.
End msDiffBit.

Lemma msDiffBit_less:
  forall z1 z2 b,
    z1 <> z2 ->
    N.shiftr z1 b = N.shiftr z2 b ->
    (msDiffBit z1 z2 <= b)%N.
Proof.
  intros.
  unfold msDiffBit.
  enough (N.log2 (N.lxor z1 z2) < b)%N
    by (apply N2Z.inj_le; Nomega).
  rewrite <- N.lxor_eq_0_iff in H0.
  rewrite <- N.shiftr_lxor in H0.
  apply N.shiftr_eq_0_iff in H0.
  rewrite -> N.lxor_eq_0_iff in H0.
  intuition.
Qed.
