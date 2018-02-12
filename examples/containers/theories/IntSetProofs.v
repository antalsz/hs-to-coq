(** * The IntSet formalization

This module contains a formalization of Haskell's Data.IntSet which implements a set of
integers as a patricia trie.

** Status

This is the annotated export list of IntSet. The first column says:

 V verified
 F verified according to the FMapInterface specification
 P skipped, because of partiality
 S skipped, for other reasons
 N nothing to be done

    -- * Set type
 V    IntSet(..), Key -- instance Eq,Show
 N  , Prefix, Mask, BitMap

    -- * Operators
 F  , (\\)

    -- * Query
 F  , null
 F  , size
 F  , member
 V  , notMember
    , lookupLT
    , lookupGT
    , lookupLE
    , lookupGE
 F  , isSubsetOf
 V  , isProperSubsetOf
    , disjoint

    -- * Construction
 F  , empty
 F  , singleton
 F  , insert
 F  , delete

    -- * Combine
 F  , union
    , unions
 F  , difference
 F  , intersection

    -- * Filter
 F  , filter
 F  , partition
    , split
    , splitMember
    , splitRoot

    -- * Map
    , map

    -- * Folds
 V  , foldr
 F  , foldl
    -- ** Strict folds
 V  , foldr'
 V  , foldl'
    -- ** Legacy folds
 V  , fold

    -- * Min\/Max
 P  , findMin
 P  , findMax
 P  , deleteMin
 P  , deleteMax
 P  , deleteFindMin
 P  , deleteFindMax
 P  , maxView
 P  , minView

    -- * Conversion

    -- ** List
 F  , elems
 F  , toList
    , fromList

    -- ** Ordered list
 V  , toAscList
 V  , toDescList
    , fromAscList
    , fromDistinctAscList

    -- * Debugging
 S  , showTree
 S  , showTreeWith

    -- * Internals
 V  , match
 V  , suffixBitMask
 V  , prefixBitMask
 V  , bitmapOf
 V  , zero

*)

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

(** ** A backtracking variant of [eassumption] *)

(** Source: http://stackissue.com/coq/coq/backtracking-eassumption-287.html *)

Ltac beassumption := multimatch goal with H :_ |- _ => exact H end.


(** ** Utilities about sorted (specialized to [Z.lt]) *)

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Sorted.

Lemma sorted_append:
  forall l1 l2 x,
  StronglySorted Z.lt l1 ->
  StronglySorted Z.lt l2 ->
  (forall y, In y l1 -> y < x) ->
  (forall y, In y l2 -> x <= y) ->
  StronglySorted Z.lt (l1 ++ l2).
Proof.
  intros ??? Hsorted1 Hsorted2 Hlt Hge.
  induction Hsorted1.
  * apply Hsorted2.
  * simpl. apply SSorted_cons.
    + apply IHHsorted1.
      intros y Hy.
      apply Hlt.
      right.
      assumption.
    + rewrite Forall_forall.
      intros z Hz.
      rewrite in_app_iff in Hz.
      destruct Hz.
      - rewrite Forall_forall in H.
        apply H; auto.
      - apply Z.lt_le_trans with (m := x).
        apply Hlt. left. reflexivity.
        apply Hge. assumption.
Qed.


Lemma StronglySorted_map:
  forall a b (R1 : a -> a -> Prop) (R2 : b -> b -> Prop) (f : a -> b) (l : list a),
    StronglySorted R1 l ->
    (forall (x y : a), In x l -> In y l -> R1 x y -> R2 (f x) (f y)) ->
    StronglySorted R2 (List.map f l).
Proof.
  intros.
  induction H.
  * simpl. constructor.
  * simpl. constructor.
    + apply IHStronglySorted; intuition.
    + clear IHStronglySorted.
      rewrite Forall_forall.
      intros.
      rewrite in_map_iff in H2.
      destruct H2 as [?[[]?]].
      apply H0.
      left. reflexivity.
      right. assumption.
      rewrite Forall_forall in H1.
      apply H1.
      assumption.
Qed.

(** *** Stuff about [option] *)

Definition oro {a} : option a -> option a -> option a :=
  fun x y => match x with
    | Some v => Some v
    | None => y
    end.

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


Lemma testbit_1:
  forall i, Z.testbit 1 i = (i =? 0).
Proof.
  intros.
  replace 1 with (2^0) by reflexivity.
  rewrite -> Z.pow2_bits_eqb by reflexivity.
  apply Z.eqb_sym.
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


(** ** IntMap-specific operations

These definitions and lemmas are used to link some concepts from the IntMap
implementation to the range sets above.
*)

Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import GHC.Num.
Import GHC.Num.Notations.
Require Import Data.Bits.
Import Data.Bits.Notations.
Require Import Data.IntSet.Internal.
Require Import Utils.Containers.Internal.BitUtil.
Require Import CTZ.
Require Import Popcount.
Local Open Scope Z_scope.
Set Bullet Behavior "Strict Subproofs".

(** A tactic to remove all relevant Haskell type class methods, and
exposes the underlying Coq concepts.
*)

Ltac unfoldMethods :=
  unfold op_zsze__, op_zeze__, Eq_Char___, Eq___IntSet, Eq_Integer___, op_zsze____, op_zeze____,
         op_zl__, op_zg__, Ord_Char___, Ord_Integer___, op_zl____,  op_zg____,
         GHC.Real.fromIntegral, GHC.Real.instance__Integral_Int__74__,
         fromInteger, GHC.Real.toInteger,
         Num_Word__,
         op_zm__, op_zp__, Num_Integer__,
         shiftRL, shiftLL,
         Prim.seq,
         op_zdzn__,
         xor, op_zizazi__, op_zizbzi__, Bits.complement,
         Bits__N,  instance_Bits_Int, complement_Int,
         id, op_z2218U__ in *.

(** We hardcode the width of the leaf bit maps to 64 bits *)

Definition WIDTH := 64%N.
Definition tip_width := N.log2 WIDTH.
Definition tip_widthZ := Z.of_N tip_width.

(** *** Lemmas about [prefixOf] *)

Lemma prefixOf_nonneg: forall p,
  0 <= p -> 0 <= prefixOf p.
Proof.
  intros.
  unfold prefixOf, prefixBitMask, suffixBitMask.
  unfoldMethods.
  rewrite Z.land_nonneg; intuition.
Qed.
Hint Resolve prefixOf_nonneg : nonneg.

Lemma rPrefix_shiftr:
  forall e,
  rPrefix (Z.shiftr e tip_widthZ, tip_width) = prefixOf e.
Proof.
  intros.
  unfold rPrefix, prefixOf, prefixBitMask, suffixBitMask.
  unfoldMethods.
  rewrite <- Z.ldiff_land.
  rewrite -> Z.ldiff_ones_r by omega.
  reflexivity.
Qed.

Lemma prefixOf_eq_shiftr:
  forall i p, 
  (prefixOf i =? Z.shiftl p tip_widthZ) = ((Z.shiftr i tip_widthZ) =? p).
Proof.
  intros.
  unfold prefixOf, prefixBitMask, suffixBitMask.
  unfoldMethods.
  rewrite <- Z.ldiff_land.
  rewrite -> Z.ldiff_ones_r by omega.
  replace tip_widthZ with 6 by reflexivity.
  rewrite -> Z_shiftl_injb by omega.
  reflexivity.
Qed.

(** This lemma indicaes that [prefixOf] implements the check of whether
    the number is part of a tip-sized range. *)
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

(** *** Lemmas about [suffixOf] *)

Lemma suffixOf_lt_WIDTH: forall e, suffixOf e < Z.of_N WIDTH.
  intros.
  unfold suffixOf, suffixBitMask.
  unfoldMethods.
  rewrite Z.land_ones.
  change (e mod 64 < 64).
  apply Z.mod_pos_bound.
  reflexivity.
  compute. congruence.
Qed.
  
Lemma suffixOf_noneg:  forall e, 0 <= suffixOf e.
  intros.
  unfold suffixOf, suffixBitMask.
  unfoldMethods.
  rewrite Z.land_ones.
  apply Z_mod_lt.
  reflexivity.
  compute. congruence.
Qed.


(** *** Operation: [rMask]
Calculates a mask in the sense of the IntSet implementation:
A single bit set just to the right of the prefix.
(Somewhat illdefined for singleton ranges).
*)

Definition rMask   : range -> Z :=
   fun '(p,b) => 2^(Z.pred (Z.of_N b)).

Lemma rMask_nonneg:
  forall r, 0 <= rMask r.
Proof.
  intros.
  destruct r as [p b]. simpl in *.
  nonneg.
Qed.
Hint Resolve rMask_nonneg : nonneg.

(** *** Lemmas about [nomatch], [zero] and their combinations *)

Lemma nomatch_spec:
  forall i r,
  (0 < rBits r)%N ->
  nomatch i (rPrefix r) (rMask r) =
  negb (inRange i r).
Proof.
  intros.
  destruct r as [p b]. simpl in *.
  unfold nomatch, zero, inRange.
  unfoldMethods.
  unfold mask.
  rewrite -> mask_to_upper_bits by Nomega.
  f_equal.
  rewrite <- Z.ldiff_land.
  rewrite -> Z.ldiff_ones_r by nonneg.
  rewrite Z.succ_pred.
  rewrite -> Z_shiftl_injb by nonneg.
  reflexivity.
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
  Nomega.
Qed.

(**
The IntSet code has a repeating pattern consisting of calls to [nomatch] and [zero].
The following two lemmas capture that pattern concisely.
*)

Lemma nomatch_zero:
  forall {a} i r (P : a -> Prop) left right otherwise,
  (0 < rBits r)%N ->
  (inRange i r = false -> P otherwise) ->
  (inRange i (halfRange r false) = true -> inRange i (halfRange r true) = false -> P left) ->
  (inRange i (halfRange r false) = false -> inRange i (halfRange r true) = true -> P right) ->
  P (if nomatch i (rPrefix r) (rMask r) then otherwise else 
     if zero i (rMask r) then left else right).
Proof.
  intros.
  rewrite nomatch_spec by auto.
  rewrite if_negb.
  destruct (inRange i r) eqn:?.
  * rewrite zero_spec by auto. 
    rewrite if_negb.
    destruct (Z.testbit i (Z.pred (Z.of_N (rBits r)))) eqn:Hbit.
    + apply H2.
      rewrite halfRange_inRange_testbit by auto. rewrite Hbit. reflexivity.
      rewrite halfRange_inRange_testbit by auto. rewrite Hbit. reflexivity.
    + apply H1.
      rewrite halfRange_inRange_testbit by auto. rewrite Hbit. reflexivity.
      rewrite halfRange_inRange_testbit by auto. rewrite Hbit. reflexivity.
  * apply H0; reflexivity.
Qed.

Lemma nomatch_zero_smaller:
  forall {a} r1 r (P : a -> Prop) left right otherwise,
  (rBits r1 < rBits r)%N ->
  (rangeDisjoint r1 r = true -> P otherwise) ->
  (isSubrange r1 (halfRange r false) = true  -> isSubrange r1 (halfRange r true) = false -> P left) ->
  (isSubrange r1 (halfRange r false) = false -> isSubrange r1 (halfRange r true) = true -> P right) ->
  P (if nomatch (rPrefix r1) (rPrefix r) (rMask r) then otherwise else 
     if zero (rPrefix r1) (rMask r) then left else right).
Proof.
  intros ????????.
  assert (rBits r1 <= rBits r)%N by Nomega.
  assert (forall h, rBits r1 <= rBits (halfRange r h))%N
    by (intros; rewrite rBits_halfRange; Nomega).
  rewrite <- smaller_not_subrange_disjoint_iff; auto.
  repeat rewrite <- smaller_inRange_iff_subRange by auto.
  apply nomatch_zero.
  Nomega.
Qed.

(** Two ranges with the same size, are either the same, or they are disjoint *)
Lemma same_size_compare:
  forall {a} r1 r2 (P : a -> Prop) same different,
  (rBits r1 = rBits r2) ->
  (r1 = r2 -> P same) ->
  (rangeDisjoint r1 r2 = true -> P different) ->
  P (if rPrefix r1 =? rPrefix r2 then same else different).
Proof.
  intros.
  destruct (Z.eqb_spec (rPrefix r1) (rPrefix r2)).
  * apply H0.
    apply rPrefix_rBits_range_eq; auto.
  * apply H1.
    apply different_prefix_same_bits_disjoint; auto.
Qed.


(** *** Lemmas about [branchMask] *)

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

(** *** Lemmas about [mask] *)

Lemma mask_spec:
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

(** *** Lemmas about [shorter] *)

Lemma shorter_spec:
  forall r1 r2,
  (0 < rBits r1)%N ->
  (0 < rBits r2)%N ->
  shorter (rMask r1) (rMask r2) = (rBits r2 <? rBits r1)%N.
Proof.
  intros.
  destruct r1 as [p1 b1], r2 as [p2 b2]. simpl in *.
  change ((Z.to_N (2 ^ Z.pred (Z.of_N b2))%Z <? Z.to_N (2 ^ Z.pred (Z.of_N b1))%Z)%N = (b2 <? b1)%N).
  apply eq_true_iff_eq.
  rewrite !N.ltb_lt.
  rewrite <- Z2N.inj_lt by (apply Z.pow_nonneg; omega).
  rewrite <- Z.pow_lt_mono_r_iff by Nomega.
  Nomega.
Qed.

(** *** Operation: [bitmapInRange]

Looks up values, which are in the given range, as bits in the given bitmap.
*)

Definition bitmapInRange r bm i :=
  if inRange i r then N.testbit bm (Z.to_N (Z.land i (Z.ones (Z.of_N (rBits r)))))
                 else false.

Lemma bitmapInRange_outside:
  forall r bm i, inRange i r = false -> bitmapInRange r bm i = false.
Proof. intros. unfold bitmapInRange. rewrite H. reflexivity. Qed.

Lemma bitmapInRange_inside:
  forall r bm i, bitmapInRange r bm i = true -> inRange i r = true.
Proof. intros. unfold bitmapInRange in *. destruct (inRange i r); auto.  Qed.


Lemma bitmapInRange_0:
  forall r i, bitmapInRange r 0%N i = false.
Proof.
  intros.
  unfold bitmapInRange.
  destruct (inRange i r); auto.
Qed.

Lemma bitmapInRange_lor:
  forall r bm1 bm2 i,
    bitmapInRange r (N.lor bm1 bm2) i =
    orb (bitmapInRange r bm1 i) (bitmapInRange r bm2 i).
Proof.
  intros.
  unfold bitmapInRange.
  destruct (inRange i r); try reflexivity.
  rewrite N.lor_spec; reflexivity.
Qed.

Lemma bitmapInRange_lxor:
  forall r bm1 bm2 i,
    bitmapInRange r (N.lxor bm1 bm2) i =
    xorb (bitmapInRange r bm1 i) (bitmapInRange r bm2 i).
Proof.
  intros.
  unfold bitmapInRange.
  destruct (inRange i r); try reflexivity.
  rewrite N.lxor_spec; reflexivity.
Qed.

Lemma bitmapInRange_land:
  forall r bm1 bm2 i,
    bitmapInRange r (N.land bm1 bm2) i =
    andb (bitmapInRange r bm1 i) (bitmapInRange r bm2 i).
Proof.
  intros.
  unfold bitmapInRange.
  destruct (inRange i r); try reflexivity.
  rewrite N.land_spec; reflexivity.
Qed.

Lemma bitmapInRange_ldiff:
  forall r bm1 bm2 i,
    bitmapInRange r (N.ldiff bm1 bm2) i =
    andb (bitmapInRange r bm1 i) (negb (bitmapInRange r bm2 i)).
Proof.
  intros.
  unfold bitmapInRange.
  destruct (inRange i r); try reflexivity.
  rewrite N.ldiff_spec; reflexivity.
Qed.


Lemma bitmapInRange_bitmapOf:
  forall e i,
  bitmapInRange (Z.shiftr e 6, N.log2 WIDTH) (bitmapOf e) i = (i =? e).
Proof.
  intros.
  unfold bitmapInRange, inRange. simpl Z.of_N.
  rewrite <- andb_lazy_alt.
  unfold bitmapOf, bitmapOfSuffix, suffixOf, suffixBitMask.
  unfoldMethods.
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

Lemma bitmapInRange_pow:
  forall r e i,
  (e < 2^rBits r)%N ->
  bitmapInRange r (2 ^ e)%N i = (rPrefix r + Z.of_N e =? i).
Proof.
  intros.
  destruct r as [p b].
  unfold bitmapInRange.
  simpl in *.
  destruct (Z.eqb_spec (Z.shiftr i (Z.of_N b)) p).
  * rewrite N.pow2_bits_eqb.
    transitivity (Z.of_N e =? Z.land i (Z.ones (Z.of_N b))).
    - rewrite eq_iff_eq_true.
      rewrite N.eqb_eq, Z.eqb_eq.
      intuition.
      subst. rewrite Z2N.id by nonneg. reflexivity.
      rewrite <- H0. rewrite N2Z.id. reflexivity.
    - rewrite eq_iff_eq_true.
      rewrite !Z.eqb_eq.
      rewrite Z.land_ones by nonneg.
      rewrite Z.shiftr_div_pow2 in e0 by nonneg.
      rewrite Z.div_mod with (a := i) (b := 2^Z.of_N b) at 2
        by (apply Z.pow_nonzero; Nomega).
      rewrite Z.shiftl_mul_pow2 by nonneg.
      rewrite Z.mul_comm.
      subst; omega.
  * symmetry.
    rewrite Z.eqb_neq.
    contradict n.
    subst.
    rewrite Z.shiftr_div_pow2 by nonneg.
    rewrite Z.shiftl_mul_pow2 by nonneg.
    rewrite Z_div_plus_full_l by (apply Z.pow_nonzero; Nomega).
    enough (Z.of_N e / 2 ^ Z.of_N b = 0) by omega.
    apply Z.div_small.
    split; try nonneg.
    zify. rewrite -> N2Z.inj_pow in H. apply H.
Qed.

(** *** Operation: [intoRange]

This is the inverse of bitmapInRange, in a way.
*)

Definition intoRange r i := Z.lor (rPrefix r) (Z.of_N i).

Definition inRange_intoRange:
  forall r i,
  (i < 2^(rBits r))%N ->
  inRange (intoRange r i) r = true.
Proof.
  intros.
  destruct r as [p b]; unfold intoRange, inRange, rPrefix, rBits, snd in *; subst.
  rewrite Z.shiftr_lor.
  rewrite Z.shiftr_shiftl_l by nonneg.
  replace (_ - _) with 0 by omega.
  rewrite Z.shiftr_div_pow2 by nonneg.
  rewrite Z.div_small.
  rewrite Z.lor_0_r. apply Z.eqb_refl.
  split; try nonneg.
  change (Z.of_N i < Z.of_N 2%N ^ Z.of_N b).
  rewrite <- N2Z.inj_pow.
  apply N2Z.inj_lt.
  assumption.
Qed.

Definition bitmapInRange_intoRange:
  forall r i bm,
  (i < 2^(rBits r))%N ->
  bitmapInRange r bm (intoRange r i) = N.testbit bm i.
Proof.
  intros.
  unfold bitmapInRange.
  rewrite inRange_intoRange by assumption.
  f_equal.
  destruct r as [p b]; unfold intoRange, inRange, rPrefix, rBits, snd in *; subst.
  rewrite Z.land_lor_distr_l.
  rewrite land_shiftl_ones by nonneg.
  rewrite Z.lor_0_l.
  rewrite !Z.land_ones by nonneg.
  rewrite Z.mod_small.
  rewrite N2Z.id. reflexivity.
  split; try nonneg.
  change (Z.of_N i < Z.of_N 2%N ^ Z.of_N b).
  rewrite <- N2Z.inj_pow.
  apply N2Z.inj_lt.
  assumption.
Qed.

(** *** Operation: [isTipPrefix]

A Tip prefix is a number with [N.log2 WIDTH] zeros at the end.
*)

Definition isTipPrefix (p : Z) := Z.land p suffixBitMask = 0.

Lemma isTipPrefix_suffixMask: forall p, isTipPrefix p -> Z.land p suffixBitMask = 0.
Proof. intros.  apply H. Qed.

Lemma isTipPrefix_prefixMask: forall p, isTipPrefix p -> Z.land p prefixBitMask = p.
Proof.
  intros.
  unfold isTipPrefix, prefixBitMask in *.
  unfoldMethods.
  enough (Z.lor (Z.land p suffixBitMask)  (Z.land p (Z.lnot suffixBitMask)) = p).
  + rewrite H, Z.lor_0_l in H0. assumption.
  + rewrite <- Z.land_lor_distr_r.
    rewrite Z.lor_lnot_diag, Z.land_m1_r. reflexivity.
Qed.

Lemma isTipPrefix_prefixOf: forall e, isTipPrefix (prefixOf e).
Proof.
  intros.
  unfold isTipPrefix, prefixOf, prefixBitMask, suffixBitMask.
  unfoldMethods.
  rewrite Z.land_ones. rewrite <- Z.ldiff_land.
  rewrite Z.ldiff_ones_r.
  rewrite Z.shiftl_mul_pow2.
  apply Z_mod_mult.
  all: compute; congruence.
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



(** *** Operation: [isBitMask]

A Tip bit mask is a non-zero number with [WIDTH] bits.
*)

Definition isBitMask (bm : N) :=
  (0 < bm /\ bm < 2^WIDTH)%N.

(** Sometimes, we need to allow zero. *)

Definition isBitMask0 (bm : N) := (bm < 2^WIDTH)%N.

Create HintDb isBitMask.
Ltac isBitMask := solve [auto with isBitMask].


Lemma isBitMask_isBitMask0:
  forall bm, isBitMask bm -> isBitMask0 bm.
Proof. intros. unfold isBitMask0, isBitMask in *. intuition. Qed.
Hint Resolve isBitMask_isBitMask0 : isBitMask.

Lemma isBitMask0_zero_or_isBitMask:
  forall bm, isBitMask0 bm <-> (bm = 0%N \/ isBitMask bm).
Proof.
  intros.
  unfold isBitMask, isBitMask0.
  assert (0 <= bm)%N by nonneg.
  rewrite N.lt_eq_cases in H.
  intuition; subst; reflexivity.
Qed.

Lemma isBitMask_isBitMask_and_noneg:
  forall bm, isBitMask bm <-> (bm <> 0%N /\ isBitMask0 bm).
Proof.
  intros.
  unfold isBitMask, isBitMask0. Nomega.
Qed.

Lemma isBitMask_testbit:
  forall bm, isBitMask bm -> (exists i, i < WIDTH /\ N.testbit bm i = true)%N.
Proof.
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
  * split; try assumption.
    unfold isBitMask in *; destruct H, H0.
    rewrite N_lt_pow2_testbits in *.
    intros j?.
    rewrite N.lor_spec.
    rewrite H2, H3 by assumption.
    reflexivity.
Qed.
Hint Resolve isBitMask_lor : isBitMask.

Lemma isBitMask0_land:
  forall bm1 bm2, isBitMask0 bm1 -> isBitMask0 bm2 -> isBitMask0 (N.land bm1 bm2).
Proof.
  intros.
  unfold isBitMask0 in *.
  rewrite N_lt_pow2_testbits in *.
  intros j?.
  rewrite N.land_spec.
  rewrite H, H0 by assumption.
  reflexivity.
Qed.
Hint Resolve isBitMask0_land : isBitMask.

Lemma isBitMask0_lxor:
  forall bm1 bm2, isBitMask0 bm1 -> isBitMask0 bm2 -> isBitMask0 (N.lxor bm1 bm2).
Proof.
  intros.
  unfold isBitMask0 in *.
  rewrite N_lt_pow2_testbits in *.
  intros j?.
  rewrite N.lxor_spec.
  rewrite H, H0 by assumption.
  reflexivity.
Qed.
Hint Resolve isBitMask0_lxor : isBitMask.


Lemma isBitMask0_ldiff:
  forall bm1 bm2, isBitMask0 bm1 -> isBitMask0 (N.ldiff bm1 bm2).
Proof.
  intros.
  unfold isBitMask0 in *.
  rewrite N_lt_pow2_testbits in *.
  intros j?.
  rewrite N.ldiff_spec.
  rewrite H by assumption.
  reflexivity.
Qed.
Hint Resolve isBitMask0_ldiff : isBitMask.

Lemma isBitMask0_lor:
  forall bm1 bm2, isBitMask0 bm1 -> isBitMask0 bm2 -> isBitMask0 (N.lor bm1 bm2).
Proof.
  intros.
  unfold isBitMask0 in *.
  rewrite N_lt_pow2_testbits in *.
  intros j?.
  rewrite N.lor_spec.
  rewrite H, H0 by assumption.
  reflexivity.
Qed.
Hint Resolve isBitMask0_lor : isBitMask.


Lemma isBitMask_bitmapOf: forall e, isBitMask (bitmapOf e).
Proof.
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
Hint Resolve isBitMask_bitmapOf : isBitMask.

Lemma isBitMask0_outside:
  forall bm i,
    isBitMask0 bm -> (WIDTH <= i)%N -> N.testbit bm i = false.
Proof.
  intros.
  unfold isBitMask0 in H.
  rewrite N_lt_pow2_testbits in H.
  intuition.
Qed.

Lemma isBitMask_log2_lt_WIDTH:
  forall bm,
  isBitMask bm -> (N.log2 bm < WIDTH)%N.
Proof. intros. apply N.log2_lt_pow2; apply H. Qed.
Hint Resolve isBitMask_log2_lt_WIDTH : isBitMask.

Lemma isBitMask_ctz_lt_WIDTH:
  forall bm,
  isBitMask bm -> (N_ctz bm < WIDTH)%N.
Admitted.
Hint Resolve isBitMask_ctz_lt_WIDTH : isBitMask.


(** *** Lemmas about [revNat] *)

Require RevNatSlowProofs.

Lemma revNat_spec:
  forall n i, (i < WIDTH)%N ->
  N.testbit (revNatSafe n) i = N.testbit n (WIDTH - 1 - i)%N.
Proof.
  exact (RevNatSlowProofs.revNat_spec).
Qed.


Lemma isBitMask0_revNat:
  forall n, isBitMask0 (revNatSafe n).
Proof.
  exact (RevNatSlowProofs.isBitMask0_revNat).
Qed.
Hint Resolve isBitMask0_revNat : isBitMask.



Lemma isBitMask0_clearbit:
  forall n i,
  isBitMask0 n -> isBitMask0 (N.clearbit n i).
Admitted.
Hint Resolve isBitMask0_clearbit : isBitMask.

Lemma clearbit_revNat:
  forall n i, (i < WIDTH)%N ->
  N.clearbit (revNatSafe n) i = revNatSafe (N.clearbit n (WIDTH - 1 - i))%N.
Proof.
  intros.
  apply N.bits_inj. intro j.
  destruct (N.ltb_spec j WIDTH).
  * rewrite !revNat_spec by assumption.
    rewrite !N.clearbit_eqb.
    rewrite !revNat_spec by assumption.
    destruct (N.eqb_spec i j), (N.eqb_spec (WIDTH - 1 - i) (WIDTH - 1 - j))%N; try reflexivity; try Nomega.
  * rewrite !isBitMask0_outside by isBitMask.
    reflexivity.
Qed.

Lemma revNat_eq_0:
  forall bm,
  isBitMask0 bm ->
  (revNatSafe bm = 0)%N <-> (bm = 0)%N.
Proof.
  intros. split; intro.
  * apply N.bits_inj; intro j.
    destruct (N.ltb_spec j WIDTH).
    - apply N.bits_inj_iff in H0. specialize (H0 (WIDTH - 1 - j)%N).
      rewrite N.bits_0 in *.
      rewrite revNat_spec in H0 by (assumption || Nomega).
      replace (WIDTH - 1 - (WIDTH - 1 - j))%N with j in H0 by Nomega.
      assumption.
    - rewrite N.bits_0 in *.
      apply isBitMask0_outside; auto.
  * subst. reflexivity.
Qed.

Lemma revNat_eqb_0:
  forall bm,
  isBitMask0 bm ->
  (revNatSafe bm =? 0)%N = (bm =? 0)%N.
Proof.
  intros.
  rewrite eq_iff_eq_true.
  rewrite !N.eqb_eq.
  apply revNat_eq_0.
  assumption.
Qed.


Lemma isBitMask_revNat:
  forall n, isBitMask n -> isBitMask (revNatSafe n).
Proof.
  intros.
  rewrite isBitMask_isBitMask_and_noneg in *.
  intuition.
  rewrite revNat_eq_0 in H by assumption. intuition.
Qed.
Hint Resolve isBitMask_revNat : isBitMask.

Lemma revNat_revNat:
  forall n, isBitMask0 n -> revNatSafe (revNatSafe n) = n.
Proof.
  intros.
  apply N.bits_inj_iff; intro i.
  destruct (N.ltb_spec i WIDTH).
  * rewrite !revNat_spec; try isBitMask.
    replace (WIDTH - 1 - (WIDTH - 1 - i))%N with i by Nomega.
    reflexivity.
    Nomega.
  * rewrite !isBitMask0_outside; isBitMask.
Qed.

Lemma revNat_lxor:
  forall n m, isBitMask0 n -> isBitMask0 m ->
    revNatSafe (N.lxor n m) = N.lxor (revNatSafe n) (revNatSafe m).
Proof.
  intros.
  apply N.bits_inj_iff; intro i.
  destruct (N.ltb_spec i WIDTH).
  * rewrite !revNat_spec, !N.lxor_spec, !revNat_spec; isBitMask.
  * rewrite N.lxor_spec.
    rewrite !isBitMask0_outside; isBitMask.
Qed.

Lemma revNat_ldiff:
  forall n m, isBitMask0 n -> isBitMask0 m ->
    revNatSafe (N.ldiff n m) = N.ldiff (revNatSafe n) (revNatSafe m).
Proof.
  intros.
  apply N.bits_inj_iff; intro i.
  destruct (N.ltb_spec i WIDTH).
  * rewrite !revNat_spec, !N.ldiff_spec, !revNat_spec; isBitMask.
  * rewrite N.ldiff_spec.
    rewrite !isBitMask0_outside; isBitMask.
Qed.

Lemma pow_isBitMask:
  forall i, (i < WIDTH)%N -> isBitMask (2^i)%N.
Proof.
  intros.
  split.
  * apply N_pow_pos_nonneg; Nomega.
  * apply N.pow_lt_mono_r; Nomega.
Qed.
Hint Resolve pow_isBitMask : isBitMask.

Lemma revNat_pow:
  forall i,
  (i < WIDTH)%N ->
  (revNatSafe (2 ^ i) = 2 ^ (WIDTH - 1 - i))%N.
Proof.
  intros.
  apply N.bits_inj_iff; intro j.
  destruct (N.ltb_spec j WIDTH).
  * rewrite !revNat_spec by assumption.
    rewrite !N.pow2_bits_eqb.
    rewrite eq_iff_eq_true.
    rewrite !N.eqb_eq.
    Nomega.
  * rewrite isBitMask0_outside by isBitMask.
    symmetry.
    apply N.pow2_bits_false.
    Nomega.
Qed.

(** *** Lemmas about [highestBitMask] and [lowestBitMask] *)

(** And the operations they are based on, [N.log2] and [N_ctz]. *)

Lemma N_ctz_log2:
  forall bm, isBitMask bm ->
  N_ctz bm = (WIDTH - 1 - N.log2 (revNatSafe bm))%N.
Proof.
  intros.
  apply N_ctz_bits_unique.
  * apply H.
  * rewrite <- revNat_spec by isBitMask.
    apply N.bit_log2.
    rewrite revNat_eq_0 by isBitMask.
    unfold isBitMask in H; Nomega.
  * intros.
    rewrite <- (revNat_revNat bm) by isBitMask.
    rewrite revNat_spec by Nomega.
    apply N.bits_above_log2.
    Nomega.
Qed.


Lemma N_log2_ctz:
  forall bm, isBitMask bm ->
  N.log2 bm = (WIDTH - 1 - N_ctz (revNatSafe bm))%N.
Proof.
  intros.
  rewrite N_ctz_log2 by isBitMask.
  rewrite revNat_revNat by isBitMask.
  assert (N.log2 bm < WIDTH)%N by isBitMask.
  Nomega.
Qed.

Lemma isBitMask_highestBitMask:
  forall bm, isBitMask bm -> isBitMask (highestBitMask bm).
Proof.
  intros.
  split.
  * change (0 < 2^N.log2 bm)%N.
    apply N_pow_pos_nonneg; Nomega.
  * apply N.pow_lt_mono_r.
    Nomega.
    isBitMask.
Qed.
Hint Resolve isBitMask_highestBitMask : isBitMask.

Lemma lxor_pow2_clearbit:
  forall a i,
  N.testbit a i = true ->
  N.lxor a (2 ^ i)%N = N.clearbit a i.
Proof.
  intros.
  apply N.bits_inj. intro j.
  rewrite N.lxor_spec, N.pow2_bits_eqb, N.clearbit_eqb.
  destruct (N.eqb_spec i j).
  * subst.
    destruct (N.testbit _ _) eqn:?; try reflexivity; congruence.
  * destruct (N.testbit _ _) eqn:?; try reflexivity.
Qed.

Lemma lxor_lowestBitMask:
  forall bm,
  isBitMask bm ->
  N.lxor bm (lowestBitMask bm) = N.clearbit bm (N_ctz bm).
Proof.
  intros.
  apply lxor_pow2_clearbit.
  apply N_bit_ctz.
  unfold isBitMask in *. Nomega.
Qed.

Lemma split_highestBitMask:
  forall bm,
  isBitMask bm ->
  bm = N.lor (N.clearbit bm (N.log2 bm)) (2^(N.log2 bm))%N.
Proof.
  intros.
  apply N.bits_inj; intro j.
  rewrite N.lor_spec, N.clearbit_eqb.
  rewrite !N.pow2_bits_eqb.
  destruct (N.eqb_spec (N.log2 bm) j).
  * subst.
    destruct (N.testbit _ _) eqn:?; try reflexivity; exfalso.
    rewrite N.bit_log2 in Heqb by (unfold isBitMask in *; Nomega).
    congruence.
  * destruct (N.testbit _ _) eqn:?; try reflexivity.
Qed.


(** *** Bitmasks with one bit *)

Lemma clearbit_log2_0:
  forall bm,
  isBitMask bm ->
  N.clearbit bm (N.log2 bm) = 0%N  ->
  bm = (2^N.log2 bm)%N.
Proof.
  intros.
  apply N.bits_inj; intro j.
  rewrite N.pow2_bits_eqb.
  apply N.bits_inj_iff in H0. specialize (H0 j).
  rewrite N.clearbit_eqb in H0.
  rewrite N.bits_0 in H0.
  destruct (N.eqb_spec (N.log2 bm) j).
  * subst.
    apply N.bit_log2.
    destruct H; Nomega.
  * simpl in H0. rewrite andb_true_r in H0.
    assumption.
Qed.

Lemma clearbit_ctz_0:
  forall bm,
  isBitMask bm ->
  N.clearbit bm (N_ctz bm) = 0%N  ->
  bm = (2^N_ctz bm)%N.
Proof.
  intros.
  apply N.bits_inj; intro j.
  rewrite N.pow2_bits_eqb.
  apply N.bits_inj_iff in H0. specialize (H0 j).
  rewrite N.clearbit_eqb in H0.
  rewrite N.bits_0 in H0.
  destruct (N.eqb_spec (N_ctz bm) j).
  * subst.
    apply N_bit_ctz.
    destruct H; Nomega.
  * simpl in H0. rewrite andb_true_r in H0.
    assumption.
Qed.

(** *** Bitmasks with more than one  bit *)

Definition hasTwoBits bm := isBitMask bm /\ N.clearbit bm (N_ctz bm) <> 0%N.

Lemma isBitMask_twoBits:
  forall bm,
  hasTwoBits bm -> isBitMask bm.
Proof. intros. apply H. Qed.
Hint Immediate isBitMask_twoBits : isBitMask.

Lemma hasTwoBits_revNat:
  forall bm,
  hasTwoBits bm ->
  hasTwoBits (revNatSafe bm).
Proof.
  intros.
  unfold hasTwoBits in *. destruct H.
  split; try isBitMask.
  contradict H0.
  rewrite clearbit_revNat in H0 by isBitMask.
  rewrite revNat_eq_0 in H0 by isBitMask.
  rewrite <- N_log2_ctz in H0 by isBitMask.
  apply clearbit_log2_0 in H0; try isBitMask.
  rewrite H0; clear H0.
  rewrite N_ctz_pow2.
  apply clearbit_pow2_0.
Qed.

Lemma log2_clearbit_ctz:
  forall bm,
  hasTwoBits bm ->
  N.log2 (N.clearbit bm (N_ctz bm)) = N.log2 bm.
Proof.
  intros. destruct H.
  apply N.log2_bits_unique.
  * rewrite N.clearbit_eqb.
    rewrite N.bit_log2 by (unfold isBitMask in H; Nomega).
    rewrite andb_true_l.
    rewrite negb_true_iff.
    rewrite N.eqb_neq.
    contradict H0.
    apply N.bits_inj. intro j.
    rewrite N.bits_0.
    rewrite N.clearbit_eqb.
    destruct (N.ltb_spec j WIDTH).
    - destruct (N.eqb_spec (N_ctz bm) j).
      + subst.
        simpl.
        apply andb_false_r.
      + enough (N.testbit bm j = false) by (replace (N.testbit bm j); apply andb_false_l).
        destruct (N.ltb_spec j (N.log2 bm)).
        ** apply N_bits_below_ctz. Nomega.
        ** apply N.bits_above_log2. Nomega.
    - rewrite isBitMask0_outside by isBitMask.
      apply andb_false_l.
  * intros j Hj.
    rewrite N.clearbit_eqb.
    rewrite N.bits_above_log2 by assumption.
    reflexivity.
Qed.

Lemma ctz_clearbit_log2:
  forall bm,
  hasTwoBits bm ->
  N_ctz (N.clearbit bm (N.log2 bm)) = N_ctz bm.
Proof.
  intros. destruct H.
  apply N_ctz_bits_unique.
  * enough (N.clearbit bm (N.log2 bm) <> 0)%N by Nomega.
    contradict H0.
    apply clearbit_log2_0 in H0; try assumption.
    rewrite H0.
    rewrite N_ctz_pow2.
    rewrite clearbit_pow2_0.
    reflexivity.
  * rewrite N.clearbit_eqb.
    rewrite N_bit_ctz by (unfold isBitMask in H; Nomega).
    rewrite andb_true_l.
    rewrite negb_true_iff.
    rewrite N.eqb_neq.
    contradict H0.
    apply N.bits_inj. intro j.
    rewrite N.bits_0.
    rewrite N.clearbit_eqb.
    destruct (N.ltb_spec j WIDTH).
    - destruct (N.eqb_spec (N_ctz bm) j).
      + subst.
        simpl.
        apply andb_false_r.
      + enough (N.testbit bm j = false) by (replace (N.testbit bm j); apply andb_false_l).
        destruct (N.ltb_spec j (N.log2 bm)).
        ** apply N_bits_below_ctz. Nomega.
        ** apply N.bits_above_log2. Nomega.
    - rewrite isBitMask0_outside by isBitMask.
      apply andb_false_l.
  * intros j Hj.
    rewrite N.clearbit_eqb.
    rewrite N_bits_below_ctz by assumption.
    reflexivity.
Qed.

Lemma isBitMask_clearbit_twoBits:
  forall bm,
  hasTwoBits bm ->
  isBitMask (N.clearbit bm (N.log2 bm)).
Proof.
  intros.
  rewrite isBitMask_isBitMask_and_noneg; split.
  * destruct H.
    contradict H0.
    apply clearbit_log2_0 in H0; try isBitMask.
    rewrite H0.
    rewrite N_ctz_pow2.
    apply clearbit_pow2_0.
  * destruct H. isBitMask.
Qed.
Hint Resolve isBitMask_clearbit_twoBits : isBitMask.

(** *** Induction along a bitmask *)

Lemma bits_ind:
  forall bm (P : N -> Prop),
  isBitMask0 bm ->
  P (0%N) ->
  (forall bm, isBitMask bm -> P (N.clearbit bm (N.log2 bm)) -> P bm) ->
  P bm.
Proof.
  intros bm P Hbm HP0 HPstep.
  
  revert Hbm.
  apply well_founded_ind with (R := N.lt) (a := bm); try apply N.lt_wf_0.
  clear bm. intros bm IH Hbm0.

  destruct (N.eqb_spec bm 0%N).
  * subst. apply HP0.
  * assert (0 < bm)%N by Nomega.
    assert (Hbm : isBitMask bm) by (unfold isBitMask in Hbm0; unfold isBitMask; auto).
    clear H Hbm0.
    apply HPstep; auto.
    apply IH.
    - apply clearbit_lt.
      apply N.bit_log2.
      assumption.
    - isBitMask.
Qed.

Lemma bits_ind_up:
  forall bm (P : N -> Prop),
  isBitMask0 bm ->
  P (0%N) ->
  (forall bm, isBitMask bm -> P (N.clearbit bm (N_ctz bm)) -> P bm) ->
  P bm.
Proof.
  intros bm P Hbm HP0 HPstep.
  
  revert Hbm.
  apply well_founded_ind with (R := N.lt) (a := bm); try apply N.lt_wf_0.
  clear bm. intros bm IH Hbm0.

  destruct (N.eqb_spec bm 0%N).
  * subst. apply HP0.
  * assert (0 < bm)%N by Nomega.
    assert (Hbm : isBitMask bm) by (unfold isBitMask in Hbm0; unfold isBitMask; auto).
    clear H Hbm0.
    apply HPstep; auto.
    apply IH.
    - apply clearbit_lt.
      apply N_bit_ctz.
      Nomega.
    - isBitMask.
Qed.

(** *** Lemmas about [popcount] *)

(** Until we switch to [deferredFix], this will have to do. *)
Axiom unsafeFix_eq : forall a (f : a -> a),
  unsafeFix f = f (unsafeFix f).

Lemma popcount_N_0:
  N_popcount 0%N = 0%N.
Proof.
  reflexivity.
Qed.

Lemma popCount_N_bm:
  forall bm,
  (0 < bm)%N ->
  N_popcount bm = N.succ (N_popcount (N.clearbit bm (N.log2 bm)%N)).
Proof.
  intros.
  rewrite N.clearbit_spec'.
  pose proof (N_popcount_diff bm (2^N.log2 bm)%N).
  replace (N.land (2 ^ N.log2 bm) bm)%N with (2 ^ N.log2 bm)%N in *;
  only 1: replace (N.ldiff (2 ^ N.log2 bm) bm)%N with 0%N in *.
  * rewrite N_popcount_pow2 in *.
    simpl N_popcount in *.
    simpl N.double in *.
    Nomega.
  * symmetry.
    apply N.bits_inj; intro j.
    rewrite N.bits_0.
    rewrite N.ldiff_spec.
    rewrite N.pow2_bits_eqb.
    destruct (N.eqb_spec (N.log2 bm) j).
    + subst.
      rewrite N.bit_log2 by Nomega. reflexivity.
    + reflexivity.
  * symmetry.
    apply N.bits_inj; intro j.
    rewrite N.land_spec.
    rewrite N.pow2_bits_eqb.
    destruct (N.eqb_spec (N.log2 bm) j).
    + subst.
      rewrite N.bit_log2 by Nomega. reflexivity.
    + reflexivity.
Qed.


(** ** Well-formed IntSets.

This section introduces the predicate to describe the well-formedness of
an IntSet. It has parameters that describe the range that this set covers,
and a function that carries it denotation. This way, invariant preservation
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


(** A variant that also allows [Nil], or sets that do not
    cover the full given range, but are certainly contained in them.
    This is used to describe operations that may delete elements.
 *)

Inductive Desc0 : IntSet -> range -> (Z -> bool) -> Prop :=
  | Desc0Nil : forall r f, (forall i, f i = false) -> Desc0 Nil r f
  | Desc0NotNil :
      forall s r f r' f',
      forall (HD : Desc s r f),
      forall (Hsubrange: isSubrange r r' = true)
      (Hf : forall i, f' i = f i),
      Desc0 s r' f'.

(** A variant that also allows [Nil] and does not reqiure a range. Used
    for the top-level specification.
 *)

Inductive Sem : IntSet -> (Z -> bool) -> Prop :=
  | SemNil : forall f, (forall i, f i = false) -> Sem Nil f
  | DescSem : forall s r f (HD : Desc s r f), Sem s f.

(** The highest level: Just well-formedness.
 *)

Definition WF (s : IntSet) : Prop := exists f, Sem s f.

(** All of these respect extensionality of [f] *)

Lemma Desc_change_f:
  forall s r f f',
  Desc s r f -> (forall i, f' i = f i) -> Desc s r f'.
Proof.
  intros.
  induction H.
  * eapply DescTip; try eassumption.
    intro i. rewrite H0, H3. reflexivity.
  * eapply DescBin; try eassumption.
    intro i. rewrite H0, H7. reflexivity.
Qed.

Lemma Sem_change_f:
  forall s f f',
  Sem s f -> (forall i, f' i = f i) -> Sem s f'.
Proof.
  intros.
  destruct H.
  * apply SemNil.
    intro i. rewrite H0, H. reflexivity.
  * eapply DescSem. eapply Desc_change_f. eassumption.
    intro i. rewrite H0. reflexivity.
Qed.


Lemma Desc_Desc0:
  forall s r f, Desc s r f -> Desc0 s r f.
Proof. intros.
  eapply Desc0NotNil.
  * eassumption.
  * apply isSubrange_refl.
  * intro. reflexivity.
Qed.

Lemma Desc0_Sem:
  forall s r f, Desc0 s r f -> Sem s f.
Proof.
  intros.
  destruct H.
  * apply SemNil; eassumption.
  * eapply DescSem. eapply Desc_change_f. eassumption. assumption.
Qed.

Lemma Desc0_WF:
  forall s r f, Desc0 s r f -> WF s.
Proof.
  intros. eexists. eapply Desc0_Sem. eassumption.
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
   apply bitmapInRange_outside; auto.
 * rewrite H4; clear H4.
   rewrite IHHD1 by inRange_false.
   rewrite IHHD2 by inRange_false.
   reflexivity.
Qed.

Lemma Desc_inside:
 forall {s r f i}, Desc s r f -> f i = true -> inRange i r = true.
Proof.
 intros ???? HD Hf.
 destruct (inRange i r) eqn:?; intuition.
 rewrite (Desc_outside HD) in Hf by assumption.
 congruence.
Qed.

Lemma Desc0_outside:
  forall {s r f i}, Desc0 s r f -> inRange i r = false -> f i = false.
Proof.
  intros.
  destruct H; auto.
  rewrite Hf.
  rewrite (Desc_outside HD) by inRange_false.
  reflexivity.
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

Lemma Desc_nonneg:
  forall {s r f i}, Desc s r f -> f i = true -> 0 <= i.
Proof.
  intros.
  destruct (Z.leb_spec 0 i); try auto.
  assert (~ (0 <= i)) by omega.
  erewrite Desc_neg_false in H0 by eassumption.
  congruence.
Qed.

Lemma Sem_nonneg:
  forall {s f i}, Sem s f -> f i = true -> 0 <= i.
Proof.
  intros.
  destruct H.
  * rewrite H in H0. congruence.
  * eapply Desc_nonneg; eassumption.
Qed.

Lemma Desc0_neg_false:
 forall {s r f i}, Desc0 s r f -> ~ (0 <= i) -> f i = false.
Proof.
  intros.
  destruct H; auto.
  rewrite Hf.
  eapply Desc_neg_false; eauto.
Qed.

Lemma Sem_neg_false:
 forall {s f i}, Sem s  f -> i < 0 -> f i = false.
Proof.
  intros.
  destruct (f i) eqn:?; try auto; exfalso.
  enough (0 <= i) by omega.
  apply (Sem_nonneg H Heqb).
Qed.

Lemma Desc0_subRange:
  forall {s r r' f}, Desc0 s r f -> isSubrange r r' = true -> Desc0 s r' f.
Proof.
  intros.
  induction H.
  * apply Desc0Nil; assumption.
  * eapply Desc0NotNil; try eassumption.
    isSubrange_true.
Qed.


Lemma isBitMask_bitmapInRange:
  forall r bm, rBits r = Nlog2 WIDTH -> isBitMask bm ->
    exists i, bitmapInRange r bm i = true.
Proof.
  intros.
  destruct (isBitMask_testbit _ H0) as [j[??]].
  exists (intoRange r j).
  rewrite bitmapInRange_intoRange; try assumption.
  replace (rBits r); assumption.
Qed.

(** The [Desc] predicate only holds for non-empty sets. *)
Lemma Desc_some_f:
  forall {s r f}, Desc s r f -> exists i, f i = true.
Proof.
  intros ??? HD.
  induction HD; subst.
  + destruct (isBitMask_bitmapInRange _ _ H1 H3) as [j ?].
    exists j.
    rewrite H2.
    assumption.
  + destruct IHHD1  as [j?].
    exists j.
    rewrite H4.
    rewrite H2.
    reflexivity.
Qed.

(** The [Desc] predicate is right_unique *)
Lemma Desc_unique_f:
  forall {s r1 f1 r2 f2}, Desc s r1 f1 -> Desc s r2 f2 -> (forall i, f1 i = f2 i).
Proof.
  intros ????? HD.
  revert r2 f2.
  induction HD; subst.
  + intros r2 f2 HD2 i.
    inversion_clear HD2.
      assert (r = r2) by (apply rPrefix_rBits_range_eq; congruence); subst.
    rewrite H2, H6.
    reflexivity.
  + intros r3 f3 HD3 i.
    inversion_clear HD3.
    rewrite H10, H4.
    erewrite IHHD1 by eassumption.
    erewrite IHHD2 by eassumption.
    reflexivity.
Qed.

(** A smart constructor that has more convenient requirements about [f] *)

Lemma DescBin' : forall s1 r1 f1 s2 r2 f2 p msk r f,
    Desc s1 r1 f1 ->
    Desc s2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = rPrefix r ->
    msk = rMask r -> 
    (forall i, inRange i (halfRange r false) = true  -> f i = f1 i) ->
    (forall i, inRange i (halfRange r true)  = true  -> f i = f2 i) ->
    (forall i, inRange i r                   = false -> f i = false) ->
    Desc (Bin p msk s1 s2) r f.
Proof.
  intros.
  eapply DescBin; try eassumption.
  intro i.
  destruct (inRange i r) eqn:Hir.
  * destruct (inRange i (halfRange r false)) eqn: Hir1.
    + assert (Hir2 : inRange i (halfRange r true) = false).
      { eapply rangeDisjoint_inRange_false.
        eapply halves_disj; auto.
        assumption.
      }
      rewrite H6 by assumption.
      rewrite (Desc_outside H0) by inRange_false.
      rewrite orb_false_r. reflexivity.
    + assert (Hir2 : inRange i (halfRange r true) = true).
      { rewrite halfRange_inRange_testbit in Hir1 by auto.
        rewrite halfRange_inRange_testbit by auto.
        destruct (Z.testbit _ _); simpl in *; congruence.
      }
      rewrite H7 by assumption.
      rewrite (Desc_outside H) by inRange_false.
      rewrite orb_false_l. reflexivity.
  * rewrite H8 by assumption.
    rewrite (Desc_outside H) by inRange_false.
    rewrite (Desc_outside H0) by inRange_false.
    reflexivity.
Qed.

(** *** Tactics *)

(** This auxillary tactic destructs one boolean atom in the argument *)

Ltac split_bool_go expr :=
  lazymatch expr with 
    | true       => fail
    | false      => fail
    | Some _     => fail
    | None       => fail
    | match ?x with _ => _ end => split_bool_go x || (simpl x; cbv match)
    | negb ?x    => split_bool_go x
    | ?x && ?y   => split_bool_go x || split_bool_go y
    | ?x || ?y   => split_bool_go x || split_bool_go y
    | xorb ?x ?y => split_bool_go x || split_bool_go y
    | oro ?x ?y  => split_bool_go x || split_bool_go y
    | ?bexpr     => destruct bexpr eqn:?
  end.

(** This auxillary tactic destructs one boolean or option atom in the goal *)

Ltac split_bool :=
  match goal with 
    | [ |- ?lhs = ?rhs] => split_bool_go lhs || split_bool_go rhs
  end.

(** This tactic solves goal of the forms
 [ forall i, f1 i = f2 i || f3 i ]
 by introducing [i], rewriting with all premises of the form
 [forall i, f1 i = … ]
 and then destructing on all boolean atoms. It leaves unsolved cases
 as subgoal.
*)

Ltac solve_f_eq :=
  let i := fresh "i" in
  intro i; simpl;
  repeat
    ( rewrite bitmapInRange_lxor
    + rewrite bitmapInRange_land
    + rewrite bitmapInRange_lor
    + match goal with 
      | [ H : forall i : Z, ?f i = _ |- context [?f i] ] => rewrite H
      end);
  repeat split_bool;
  try reflexivity.

Ltac point_to_inRange :=
  lazymatch goal with 
    | [ HD : Desc ?s ?r ?f, Hf : ?f ?i = true |- _ ] 
      => apply (Desc_inside HD) in Hf
    | [ H : bitmapInRange ?r ?bm ?i = true |- _ ]
      => apply bitmapInRange_inside in H
  end.

Ltac pose_new prf :=
  let prop := type of prf in
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => pose proof prf
  end.

Ltac saturate_inRange :=
  match goal with
   | [ Hsr : isSubrange ?r1 ?r2 = true, Hir : inRange ?i ?r1 = true |- _ ]
     => pose_new (inRange_isSubrange_true i r1 r2 Hsr Hir)
   | [ HrBits : (0 < rBits ?r)%N, Hir : inRange ?i (halfRange ?r ?h) = true |- _ ]
     => pose_new (inRange_isSubrange_true i _ r (isSubrange_halfRange r h HrBits) Hir)
  end.

Ltac inRange_disjoint :=
  match goal with
   | [ H1 : inRange ?i (halfRange ?r false) = true,
       H2 : inRange ?i (halfRange ?r true) = true |- _ ]
     => exfalso;
        refine (rangeDisjoint_inRange_false_false i _ _ _ H1 H2);
        apply halves_disj; auto
   | [ H1 : isSubrange ?r (halfRange ?r2 false) = true,
       H2 : isSubrange ?r (halfRange ?r2 true) = true |- _ ]
     => exfalso;
        refine (rangeDisjoint_isSubrange_false_false r _ _ _ H1 H2);
        apply halves_disj; auto
   | [ H  : rangeDisjoint ?r1 ?r2 = true,
       H1 : inRange ?i ?r1 = true,
       H2 : inRange ?i ?r2 = true |- _ ]
     => exfalso;
        apply (rangeDisjoint_inRange_false_false i _ _ H H1 H2)
   end.

(**
 Like [solve_f_eq], but tries to solve the resulting bugus cases
 using reasoning about [inRange]. *)

Ltac solve_f_eq_disjoint :=
  solve_f_eq;
  repeat point_to_inRange;
  repeat saturate_inRange;
  try inRange_disjoint. (* Only try this, so that we see wher we are stuck. *)

(** *** Uniqueness of representation *)

Lemma both_halfs:
  forall i1 i2 r1 r2,
  (0 < rBits r2)%N ->
  inRange i1 r1 = true ->
  inRange i2 r1 = true ->
  inRange i1 (halfRange r2 false) = true ->
  inRange i2 (halfRange r2 true) = true ->
  isSubrange r2 r1 = true.
Proof.
  intros.
  destruct (N.ltb_spec (rBits r1) (rBits r2)).
  * exfalso.
    assert (isSubrange r1 (halfRange r2 false) = true)
      by (apply inRange_both_smaller_subRange with (i := i1);
          try assumption; rewrite rBits_halfRange; Nomega).
    assert (isSubrange r1 (halfRange r2 true) = true)
      by (apply inRange_both_smaller_subRange with (i := i2);
          try assumption; rewrite rBits_halfRange; Nomega).
    assert (isSubrange r1 r2 = true) by isSubrange_true.
    pose proof (smaller_subRange_other_half _ _ H4).
    rewrite H7, H6, H5 in H8. intuition.
  * apply inRange_both_smaller_subRange with (i := i1).
    + eapply inRange_isSubrange_true; [apply isSubrange_halfRange; assumption|eassumption].
    + assumption.
    + assumption.
Qed.

Lemma criss_cross:
  forall i1 i2 i3 i4 r1 r2,
  (0 < rBits r1)%N ->
  (0 < rBits r2)%N ->
  inRange i1 (halfRange r1 false) = true ->
  inRange i2 (halfRange r1 true) = true ->
  inRange i3 (halfRange r2 false) = true ->
  inRange i4 (halfRange r2 true) = true ->
  inRange i1 r2 = true ->
  inRange i2 r2 = true ->
  inRange i3 r1 = true ->
  inRange i4 r1 = true ->
  r1 = r2.
Proof.
  intros.
  apply isSubrange_antisym.
  + eapply both_halfs with (i1 := i1) (i2 := i2); eassumption.
  + eapply both_halfs with (i1 := i3) (i2 := i4); eassumption.  
Qed.

Lemma larger_f_imp:
  forall s1 r1 f1 s2 r2 f2,
  (rBits r2 < rBits r1)%N ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i : Z, f1 i = true -> f2 i = true) ->
  False.
Proof.
  intros ??? ??? Hsmaller HD1 HD2 Hf.
  destruct HD1.
  * pose proof (Desc_larger_WIDTH HD2).
    Nomega.
  * subst.
    assert (isSubrange r2 (halfRange r false) = true).
      { destruct (Desc_some_f HD1_1) as [i Hi].
        pose proof (Desc_inside HD1_1 Hi).
        specialize (H4 i).
        rewrite (Desc_outside HD1_2) in H4 by inRange_false.
        rewrite orb_false_r in H4.
        rewrite <- H4 in Hi; clear H4.
        apply Hf in Hi; clear Hf.
        apply (Desc_inside HD2) in Hi.
        apply inRange_both_smaller_subRange with (i := i).
        * inRange_true.
        * inRange_true.
        * rewrite rBits_halfRange. Nomega.
      }
    assert (isSubrange r2 (halfRange r true) = true).
      { destruct (Desc_some_f HD1_2) as [i Hi].
        pose proof (Desc_inside HD1_2 Hi).
        specialize (H4 i).
        rewrite (Desc_outside HD1_1) in H4 by inRange_false.
        rewrite orb_false_l in H4.
        rewrite <- H4 in Hi; clear H4.
        apply Hf in Hi; clear Hf.
        apply (Desc_inside HD2) in Hi.
        apply inRange_both_smaller_subRange with (i := i).
        * inRange_true.
        * inRange_true.
        * rewrite rBits_halfRange. Nomega.
      }
      inRange_disjoint.
Qed.


Lemma Desc_unique:
  forall s1 r1 f1 s2 r2 f2,
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i, f1 i = f2 i) ->
  s1 = s2.
Proof.
  intros ?????? HD1.
  revert s2 r2 f2.
  induction HD1.
  * intros s2 r2 f2 HD2 Hf.
    destruct HD2.
    + subst.
      assert (r = r0).
      { destruct (isBitMask_bitmapInRange r bm H1 H3) as [i Hbit].
        assert (Hir : inRange i r = true)
          by (eapply bitmapInRange_inside; eassumption).
        specialize (Hf i).
        specialize (H2 i).
        specialize (H7 i).
        rewrite H2 in Hf; clear H2.
        rewrite H7 in Hf; clear H7.
        rewrite Hbit in Hf; symmetry in Hf.
        apply bitmapInRange_inside in Hf.
        apply inRange_both_same with (i := i); try assumption; Nomega.
      }
      subst.
      f_equal.
      apply N.bits_inj; intro j.
      destruct (N.ltb_spec j WIDTH).
      - set (i := intoRange r0 j).
        specialize (H2 i).
        specialize (H7 i).
        specialize (Hf i).
        rewrite Hf in H2 by assumption; clear Hf.
        rewrite H2 in H7; clear H2.
        subst i.
        rewrite !bitmapInRange_intoRange in H7
          by (replace (rBits r0); assumption).
        assumption.
      - rewrite !isBitMask0_outside by isBitMask.
        reflexivity.
    + exfalso. subst.
      eapply larger_f_imp with (r1 := r0) (r2 := r).
      - assert (N.log2 WIDTH <= rBits r1)%N by (eapply Desc_larger_WIDTH; eauto).
        apply subRange_smaller in H5. rewrite rBits_halfRange in H5.
        Nomega.
      - eapply DescBin with (s1 := s1) (s2 := s2); try eassumption; reflexivity.
      - eapply DescTip; try eassumption; reflexivity.
      - intros i Hi. rewrite Hf. assumption.
  * intros s3 r3 f3 HD3 Hf.
    destruct HD3.
    + exfalso. subst.
      eapply larger_f_imp with (r1 := r) (r2 := r0).
      - assert (N.log2 WIDTH <= rBits r1)%N by (eapply Desc_larger_WIDTH; eauto).
        apply subRange_smaller in H0. rewrite rBits_halfRange in H0.
        Nomega.
      - eapply DescBin with (s1 := s1) (s2 := s2); try eassumption; reflexivity.
      - eapply DescTip; try eassumption; reflexivity.
      - intros i Hi. rewrite <- Hf. assumption.
    + subst.
      assert (r4 = r). {
        destruct (Desc_some_f HD3_1) as [i1 Hi1].
        destruct (Desc_some_f HD3_2) as [i2 Hi2].
        destruct (Desc_some_f HD1_1) as [i3 Hi3].
        destruct (Desc_some_f HD1_2) as [i4 Hi4].
        apply criss_cross with i1 i2 i3 i4; try assumption.
        * apply (Desc_inside HD3_1) in Hi1; inRange_true.
        * apply (Desc_inside HD3_2) in Hi2; inRange_true.
        * apply (Desc_inside HD1_1) in Hi3; inRange_true.
        * apply (Desc_inside HD1_2) in Hi4; inRange_true.
        * specialize (H10 i1); rewrite Hi1 in H10.
          rewrite orb_true_l in H10.
          rewrite <- Hf in H10.
          specialize (H4 i1); rewrite H10 in H4; clear H10; symmetry in H4.
          rewrite orb_true_iff in H4; destruct H4.
          + apply (Desc_inside HD1_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
        * specialize (H10 i2); rewrite Hi2 in H10.
          rewrite orb_true_r in H10.
          rewrite <- Hf in H10.
          specialize (H4 i2); rewrite H10 in H4; clear H10; symmetry in H4.
          rewrite orb_true_iff in H4; destruct H4.
          + apply (Desc_inside HD1_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
        * specialize (H4 i3); rewrite Hi3 in H4.
          rewrite orb_true_l in H4.
          rewrite -> Hf in H4.
          specialize (H10 i3); rewrite H4 in H10; clear H4; symmetry in H10.
          rewrite orb_true_iff in H10; destruct H10.
          + apply (Desc_inside HD3_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD3_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
        * specialize (H4 i4); rewrite Hi4 in H4.
          rewrite orb_true_r in H4.
          rewrite -> Hf in H4.
          specialize (H10 i4); rewrite H4 in H10; clear H4; symmetry in H10.
          rewrite orb_true_iff in H10; destruct H10.
          + apply (Desc_inside HD3_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD3_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
      }
      subst.
      assert (IH_prem_1 : (forall i : Z, f1 i = f0 i)). {
        intro i.
        specialize (H4 i). specialize (H10 i). specialize (Hf i).
        destruct (inRange i (halfRange r false)) eqn:?.
        -- rewrite (Desc_outside HD1_2) in H4 by inRange_false.
           rewrite orb_false_r in H4.
           rewrite <- H4; clear H4.

           rewrite (Desc_outside HD3_2) in H10 by inRange_false.
           rewrite orb_false_r in H10.
           rewrite <- H10; clear H10.

           assumption.
        -- rewrite (Desc_outside HD1_1) by inRange_false.
           rewrite (Desc_outside HD3_1) by inRange_false.
           reflexivity.
      }
      assert (IH_prem_2 : (forall i : Z, f2 i = f3 i)). {
        intro i.
        specialize (H4 i). specialize (H10 i). specialize (Hf i).
        destruct (inRange i (halfRange r true)) eqn:?.
        -- rewrite (Desc_outside HD1_1) in H4 by inRange_false.
           rewrite orb_false_l in H4.
           rewrite <- H4; clear H4.
           
           rewrite (Desc_outside HD3_1) in H10 by inRange_false.
           rewrite orb_false_l in H10.
           rewrite <- H10; clear H10.
           
           assumption.
        -- rewrite (Desc_outside HD1_2) by inRange_false.
           rewrite (Desc_outside HD3_2) by inRange_false.
           reflexivity.
      }
      specialize (IHHD1_1 _ _ _ HD3_1 IH_prem_1).
      destruct IHHD1_1; subst.
      specialize (IHHD1_2 _ _ _ HD3_2 IH_prem_2).
      destruct IHHD1_2; subst.
      reflexivity.
Qed.

Lemma Sem_unique:
  forall s1 f1 s2 f2,
  Sem s1 f1 -> Sem s2 f2 ->
  (forall i, f1 i = f2 i) ->
  s1 = s2.
Proof.
  intros.
  destruct H, H0.
  * reflexivity.
  * exfalso.
    destruct (Desc_some_f HD) as [i Hi]. 
    rewrite <- H1 in Hi.
    rewrite H in Hi.
    congruence.
  * exfalso.
    destruct (Desc_some_f HD) as [i Hi]. 
    rewrite -> H1 in Hi.
    rewrite H in Hi.
    congruence.
  * eapply Desc_unique; eassumption.
Qed.

(** *** Specifying [equal] *)

Lemma equal_spec:
  forall s1 s2, equal s1 s2 = true <-> s1 = s2.
Proof.
  induction s1; intro s2; destruct s2;
    try solve [simpl; intuition congruence].
  * simpl. unfoldMethods.
    rewrite !andb_true_iff.
    rewrite !Z.eqb_eq.
    rewrite IHs1_1.
    rewrite IHs1_2.
    intuition congruence.
  * simpl. unfoldMethods.
    rewrite !andb_true_iff.
    rewrite !Z.eqb_eq.
    rewrite !N.eqb_eq.
    intuition congruence.
Qed.


(** *** Specifying [isSubsetOf] *)

Lemma isSubsetOf_disjoint:
  forall s1 r1 f1 s2 r2 f2,
  rangeDisjoint r1 r2 = true ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i : Z, f1 i = true -> f2 i = true) <-> False.
Proof.
  intros ??? ??? Hdis HD1 HD2.
  intuition.
  destruct (Desc_some_f HD1) as [i Hi].
  eapply rangeDisjoint_inRange_false_false with (i := i).
  ** eassumption.
  ** eapply Desc_inside; eassumption.
  ** apply H in Hi.
     apply (Desc_inside HD2) in Hi.
     assumption.
Qed.

Lemma pointwise_iff:
  forall {a} (P Q Z : a -> Prop),
  (forall i, P i -> (Q i <-> Z i)) ->
  (forall i, P i -> Q i) <-> (forall i, P i -> Z i).
Proof. intuition; specialize (H0 i); specialize (H i); intuition. Qed.

Program Fixpoint isSubsetOf_Desc
  s1 r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  isSubsetOf s1 s2 = true <-> (forall i, f1 i = true -> f2 i = true) := _.
Next Obligation.
  revert isSubsetOf_Desc H H0.
  intros IH HD1 HD2.
  destruct HD1, HD2.
  * (* Both are tips *)
    simpl; subst. unfoldMethods.
    rewrite andb_true_iff.
    rewrite N.eqb_eq.
    destruct (Z.eqb_spec (rPrefix r) (rPrefix r0)).
    - replace r0 with r in * by (apply rPrefix_rBits_range_eq; congruence). clear r0.
      intuition.
      ** rewrite H2 in H0.
         rewrite H7.
         unfold bitmapInRange. unfold bitmapInRange in H0.
         destruct (inRange i r); try congruence.
         set (j := Z.to_N _) in *.
         apply N.bits_inj_iff in H9; specialize (H9 j).
         rewrite N.lxor_spec, N.land_spec, N.bits_0 in H9.
         destruct (N.testbit bm j), (N.testbit bm0 j); simpl in *; congruence.
      ** apply N.bits_inj_iff; intro j.
         rewrite N.bits_0.
         destruct (N.ltb_spec j WIDTH).
         ++ rewrite N.lxor_spec, N.land_spec.
            do 2 split_bool; try reflexivity; exfalso.
            apply not_true_iff_false in Heqb0.
            contradict Heqb0.
            set (i := intoRange r j).
            assert (Hbmir : bitmapInRange r bm0 i = N.testbit bm0 j)
              by (apply bitmapInRange_intoRange; replace (rBits r); assumption).
            rewrite <- Hbmir; clear Hbmir.
            rewrite <- H7.
            apply H0.
            rewrite H2.
            assert (Hbmir : bitmapInRange r bm i = N.testbit bm j)
              by (apply bitmapInRange_intoRange; replace (rBits r); assumption).
            rewrite Hbmir.
            assumption.
         ++ apply isBitMask0_outside. isBitMask. assumption.
    - rewrite isSubsetOf_disjoint.
      ** intuition.
      ** apply different_prefix_same_bits_disjoint; try eassumption; congruence.
      ** eapply DescTip with (p := rPrefix r) (r := r) (bm := bm); try eassumption; try congruence.
      ** eapply DescTip with (p := rPrefix r0) (r := r0) (bm := bm0); try eassumption; try congruence.

  * (* Tip left, Bin right *)
    simpl; subst.
    apply nomatch_zero_smaller.
    - assert (N.log2 WIDTH <= rBits r1)%N by (eapply Desc_larger_WIDTH; eauto).
      apply subRange_smaller in H5. rewrite rBits_halfRange in H5.
      Nomega.
    - intros Hdisj.
      rewrite isSubsetOf_disjoint.
      ** intuition.
      ** eassumption.
      ** eapply DescTip; try eassumption; try reflexivity.
      ** eapply (DescBin s1 _ _ s2); try eassumption; try reflexivity.
    - intros.
       etransitivity; [eapply IH with (f2 := f1)|].
       + simpl. omega.
       + eapply DescTip with (p := rPrefix r) (r := r) (bm := bm); try eassumption; try congruence.
       + eassumption.
       + apply pointwise_iff. intros i Hi. 
         assert (inRange i r = true). {
           rewrite H2 in Hi.
           apply bitmapInRange_inside in Hi.
           assumption.
         }
         rewrite H9.
         rewrite (Desc_outside HD2_2) by inRange_false.
         rewrite orb_false_r. reflexivity.
    - intros.
       etransitivity; [eapply IH with (f2 := f2)|].
       + simpl. omega.
       + eapply DescTip with (p := rPrefix r) (r := r) (bm := bm); try eassumption; try congruence.
       + eassumption.
       + apply pointwise_iff. intros i Hi. 
         assert (inRange i r = true). {
           rewrite H2 in Hi.
           apply bitmapInRange_inside in Hi.
           assumption.
         }
         rewrite H9.
         rewrite (Desc_outside HD2_1) by inRange_false.
         rewrite orb_false_l. reflexivity.

  * (* Bin right, Tip left *)
    intuition; exfalso.
    eapply larger_f_imp with (r1 := r) (r2 := r2).
    - assert (N.log2 WIDTH <= rBits r1)%N by (eapply Desc_larger_WIDTH; eauto).
      apply subRange_smaller in H0. rewrite rBits_halfRange in H0.
      Nomega.
    - eapply DescBin with (s1 := s1) (s2 := s0); try eassumption; reflexivity.
    - eapply DescTip; try eassumption; reflexivity.
    - intros i Hi. apply H10. assumption.
  * (* Bin both sides *)
    simpl; subst.
    rewrite shorter_spec by assumption.
    rewrite shorter_spec by assumption.
    destruct (N.ltb_spec (rBits r4) (rBits r)); [|destruct (N.ltb_spec (rBits r) (rBits r4))].
    - (* left is bigger than right *)
      intuition; exfalso.
      eapply larger_f_imp with (r1 := r) (r2 := r4).
      -- assumption.
      -- eapply DescBin with (s1 := s1) (s2 := s0); try eassumption; reflexivity.
      -- eapply DescBin with (s1 := s2) (s2 := s3); try eassumption; reflexivity.
      -- assumption.
    - (* right is bigger than left *)
      match goal with [ |- ((?x && ?y) = true) <-> ?z ] =>
        enough (Htmp : (if x then y else false) = true <-> z)
        by (destruct x; try rewrite andb_true_iff; intuition congruence)
      end.
      match goal with [ |- context [match_ ?x ?y ?z] ] =>
        replace (match_ x y z) with (negb (nomatch x y z))
          by (unfold nomatch, match_; unfoldMethods; rewrite negb_involutive; reflexivity)
      end.
      rewrite if_negb.
      apply nomatch_zero_smaller; try assumption.
      ** intro Hdisj.
         rewrite isSubsetOf_disjoint.
         -- intuition.
         -- eassumption.
         -- eapply DescBin with (s1 := s1) (s2 := s0); try eassumption; reflexivity.
         -- eapply DescBin with (s1 := s2) (s2 := s3); try eassumption; reflexivity.
      ** intros.
         etransitivity; [eapply IH with (f2 := f2)|].
         + simpl. omega.
         + eapply DescBin with (s1 := s1) (s2 := s0) (r := r); try eassumption; reflexivity.
         + eassumption.
         + apply pointwise_iff. intros i Hi. 
           assert (inRange i r = true). {
             rewrite H4 in Hi.
             rewrite orb_true_iff in Hi; destruct Hi as [Hi | Hi];
             (apply (Desc_inside HD1_1) in Hi || apply (Desc_inside HD1_2) in Hi);
             eapply inRange_isSubrange_true; swap 1 2; try eassumption; isSubrange_true.
           }
           rewrite H10.
           rewrite (Desc_outside HD2_2) by inRange_false.
           rewrite orb_false_r. reflexivity.
      ** intros.
         etransitivity; [eapply IH with (f2 := f3)|].
         + simpl. omega.
         + eapply DescBin with (s1 := s1) (s2 := s0) (r := r); try eassumption; reflexivity.
         + eassumption.
         + apply pointwise_iff. intros i Hi. 
           assert (inRange i r = true). {
             rewrite H4 in Hi.
             rewrite orb_true_iff in Hi; destruct Hi as [Hi | Hi];
             (apply (Desc_inside HD1_1) in Hi || apply (Desc_inside HD1_2) in Hi);
             eapply inRange_isSubrange_true; swap 1 2; try eassumption; isSubrange_true.
           }
           rewrite H10.
           rewrite (Desc_outside HD2_1) by inRange_false.
           rewrite orb_false_l. reflexivity.
    - (* same sized bins *)
      unfoldMethods.
      destruct (Z.eqb_spec (rPrefix r) (rPrefix r4)).
      + replace r4 with r in * by (apply rPrefix_rBits_range_eq; Nomega). clear r4.
        simpl.
        rewrite andb_true_iff.
        rewrite (IH s1 r1 f1 s2 r2 f2); try assumption; simpl; try omega.
        rewrite (IH s0 r0 f0 s3 r3 f3); try assumption; simpl; try omega.
        intuition.
        ++ rewrite H10. rewrite H4 in H8.
           rewrite orb_true_iff in H8.
           destruct H8.
           ** apply H9 in H8.
              rewrite H8.
              rewrite orb_true_l.
              reflexivity.
           ** apply H11 in H8.
              rewrite H8.
              rewrite orb_true_r.
              reflexivity.
        ++ specialize (H4 i). specialize (H10 i).
           rewrite H9 in H4.
           apply (Desc_inside HD1_1) in H9.
           rewrite orb_true_l in H4.
           apply H8 in H4. rewrite H10 in H4.
           rewrite (Desc_outside HD2_2) in H4 by inRange_false.
           rewrite orb_false_r in H4.
           assumption.
        ++ specialize (H4 i). specialize (H10 i).
           rewrite H9 in H4. 
           apply (Desc_inside HD1_2) in H9.
           rewrite orb_true_r in H4.
           apply H8 in H4. rewrite H10 in H4.
           rewrite (Desc_outside HD2_1) in H4 by inRange_false.
           rewrite orb_false_l in H4.
           assumption.
      + rewrite isSubsetOf_disjoint.
        ** intuition.
        ** apply different_prefix_same_bits_disjoint; try eassumption; Nomega.
        ** eapply DescBin with (s1 := s1) (s2 := s0); try eassumption; reflexivity.
        ** eapply DescBin with (s1 := s2) (s2 := s3); try eassumption; reflexivity.
Qed.

Lemma isSubsetOf_Sem:
  forall s1 f1 s2 f2,
  Sem s1 f1 -> Sem s2 f2 ->
  isSubsetOf s1 s2 = true <-> (forall i, f1 i = true -> f2 i = true).
Proof.
  intros ???? HSem1 HSem2.
  destruct HSem1.
  * replace (isSubsetOf Nil s2) with true by (destruct s2; reflexivity).
    intuition; exfalso.
    rewrite H in H1; congruence.
  * destruct HSem2.
    + replace (isSubsetOf s Nil) with false by (destruct HD; reflexivity).
      intuition; exfalso.
      destruct (Desc_some_f HD) as [i Hi].
      apply H0 in Hi.
      rewrite H in Hi.
      congruence.
    + eapply isSubsetOf_Desc; eassumption.
Qed.


Lemma isSubsetOf_refl:
  forall s f,
  Sem s f ->
  isSubsetOf s s = true.
Proof.
  intros.
  rewrite isSubsetOf_Sem by eassumption.
  intuition.
Qed.

Lemma isSubsetOf_antisym:
  forall s1 f1 s2 f2,
  Sem s1 f1 -> Sem s2 f2 ->
  isSubsetOf s1 s2 = true ->
  isSubsetOf s2 s1 = true ->
  s1 = s2.
Proof.
  intros.
  rewrite isSubsetOf_Sem in H1 by eassumption.
  rewrite isSubsetOf_Sem in H2 by eassumption.
  eapply Sem_unique; try eassumption.
  intro i. specialize (H1 i). specialize (H2 i).
  apply eq_true_iff_eq.
  intuition.
Qed.


(** *** Specifying [member] *)

Lemma member_Desc:
 forall {s r f i}, Desc s r f -> member i s = f i.
Proof.
 intros ???? HD.
 induction HD; subst.
 * simpl.
   change (((prefixOf i == rPrefix r) && ((bitmapOf i .&.bm) /= #0)) = f i).
   unfoldMethods.
   rewrite -> prefixOf_eqb_spec by assumption.
   rewrite H2.

   unfold bitmapOf, bitmapOfSuffix, suffixOf, suffixBitMask, bitmapInRange.
   unfoldMethods.
   rewrite N.shiftl_mul_pow2, N.mul_1_l.
   rewrite N_land_pow2_testbit.

   rewrite H1.
   reflexivity.
 * rewrite H4. clear H4.
   simpl member.
   rewrite IHHD1, IHHD2. clear IHHD1 IHHD2.

   apply nomatch_zero; [auto|..]; intros.
   + rewrite (Desc_outside HD1) by inRange_false.
     rewrite (Desc_outside HD2) by inRange_false.
     reflexivity.
   + rewrite (Desc_outside HD2) by inRange_false.
     rewrite orb_false_r. reflexivity.
   + rewrite (Desc_outside HD1) by inRange_false.
     rewrite orb_false_l. reflexivity.
Qed.

Lemma member_Desc0:
  forall {s r f i}, Desc0 s r f -> member i s = f i.
Proof.
  intros.
  destruct H; simpl; auto.
  rewrite Hf.
  eapply member_Desc; eauto.
Qed.

Lemma member_Sem:
  forall {s f i}, Sem s f -> member i s = f i.
Proof.
  intros.
  destruct H.
  * rewrite H. reflexivity.
  * erewrite member_Desc; eauto.
Qed.

Lemma Desc_has_member: 
  forall {s r f}, Desc s r f -> exists i, 0 <= i /\ member i s = true.
Proof.
  intros ??? HD.
  destruct (Desc_some_f HD) as [j?].
  exists j.
  rewrite (member_Desc HD). intuition.
  destruct (Z.leb_spec 0 j); auto.
  contradict H.
  rewrite  (Desc_neg_false HD); try congruence.
  apply Zlt_not_le. assumption.
Qed.

(** *** Specifying [notMember] *)

Lemma notMember_Sem:
  forall {s f i}, Sem s f -> notMember i s = negb (f i).
Proof.
  intros.
  change (negb (member i s) = negb (f i)).
  f_equal.
  apply member_Sem.
  assumption.
Qed.


(** *** Specifying [singleton] *)

Lemma singleton_Desc:
  forall e,
   0 <= e ->
   Desc (singleton e) (Z.shiftr e 6, N.log2 WIDTH) (fun x => x =? e).
Proof.
  intros.
  apply DescTip; try nonneg; try isBitMask.
  symmetry; apply rPrefix_shiftr.
  intro i.
  symmetry; apply bitmapInRange_bitmapOf.
Qed.

Lemma singleton_Sem:
  forall e, 0 <= e -> Sem (singleton e) (fun x => x =? e).
Proof.
  intros.
  eapply DescSem.
  apply singleton_Desc; assumption.
Qed.

Lemma singleton_WF:
  forall e, 0 <= e -> WF (singleton e).
Proof. intros. eexists. apply singleton_Sem; auto. Qed.

(** *** Specifying [insert] *)

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
  rewrite mask_spec.
  rewrite -> zero_spec by (apply commonRangeDisj_rBits_pos; eapply Desc_rNonneg; eassumption).
  rewrite if_negb.
  match goal with [ |- context [Z.testbit ?i ?b] ]  => destruct (Z.testbit i b) eqn:Hbit end.
  * assert (Hbit2 : Z.testbit (rPrefix r2) (Z.pred (Z.of_N (rBits (commonRangeDisj r1 r2)))) = false).
    { apply not_true_is_false.
      rewrite <- Hbit.
      apply not_eq_sym.
      apply commonRangeDisj_rBits_Different; try (eapply Desc_rNonneg; eassumption); auto.
    }
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
    + solve_f_eq.
  * assert (Hbit2 : Z.testbit (rPrefix r2) (Z.pred (Z.of_N (rBits (commonRangeDisj r1 r2)))) = true).
    { apply not_false_iff_true.
      rewrite <- Hbit.
      apply not_eq_sym.
      apply commonRangeDisj_rBits_Different; try (eapply Desc_rNonneg; eassumption); auto.
    }
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
    unfoldMethods.
    apply same_size_compare; try Nomega; intros.
    + subst.
      rewrite commonRange_idem.
      inversion_clear HDTip.
      apply DescTip; auto.
      - solve_f_eq.
      - isBitMask.
    + rewrite rangeDisjoint_sym in *.
      eapply link_Desc; try apply HDTip; auto.
      - apply DescTip; auto.
      - apply disjoint_commonRange; auto.
  * simpl. unfoldMethods.

    assert (N.log2 WIDTH <= rBits r2)%N by (eapply Desc_larger_WIDTH; eauto).
    assert (rBits r2 <= rBits (halfRange r0 false))%N by (apply subRange_smaller; auto).
    assert (rBits (halfRange r0 false) < rBits r0)%N by (apply halfRange_smaller; auto).
    assert (rBits r1 < rBits r0)%N by Nomega.

    apply nomatch_zero_smaller; try assumption; intros.
    + eapply link_Desc; eauto; try (inversion HDTip; auto).
      eapply DescBin; eauto.
      apply disjoint_commonRange; assumption.
    + rewrite -> (isSubrange_commonRange_r r1 r0) in * by isSubrange_true.
      eapply DescBin; try apply HD2; try apply IHHD1 with (f := fun j => f1 j || f2 j); auto.
      ** isSubrange_true; eapply Desc_rNonneg; eassumption.
      ** solve_f_eq.
    + rewrite -> (isSubrange_commonRange_r r1 r0) in * by isSubrange_true.
      eapply DescBin; try apply HD1; try apply IHHD2 with (f := fun j => f1 j || f3 j); auto.
      ** isSubrange_true; eapply Desc_rNonneg; eassumption.
      ** solve_f_eq.
Qed.

Lemma insert_Desc:
  forall e r1,
  forall s2 r2 f2,
  forall r f, 
  0 <= e ->
  Desc s2 r2 f2 ->
  r1 = (Z.shiftr e tip_widthZ, tip_width) ->
  r = commonRange r1 r2 ->
  (forall i, f i = (i =? e) || f2 i) ->
  Desc (insert e s2) r f.
Proof.
  intros.
  eapply insertBM_Desc.
  eapply DescTip; try nonneg.
  * symmetry. apply rPrefix_shiftr.
  * reflexivity.
  * isBitMask.
  * eassumption.
  * congruence.
  * intros j. rewrite H3. f_equal.
    symmetry. apply bitmapInRange_bitmapOf.
Qed.

Lemma insert_Nil_Desc:
  forall e r f,
  0 <= e ->
  r = (Z.shiftr e tip_widthZ, tip_width) ->
  (forall i, f i = (i =? e)) ->
  Desc (insert e Nil) r f.
Proof.
  intros; subst.
  apply DescTip; try nonneg.
  * symmetry. apply rPrefix_shiftr.
  * intros j. rewrite H1. symmetry. apply bitmapInRange_bitmapOf.
  * isBitMask.
Qed.

Lemma insert_Sem:
  forall e s2 f2 f,
  0 <= e ->
  Sem s2 f2 ->
  (forall i, f i = (i =? e) || f2 i) ->
  Sem (insert e s2) f.
Proof.
  intros.
  destruct H0.
  * eapply DescSem. apply insert_Nil_Desc; auto.
    solve_f_eq.
  * eapply DescSem. eapply insert_Desc; eauto.
Qed.

Lemma insert_WF:
  forall n s, WF s -> 0 <= n -> WF (insert n s).
Proof.
  intros.
  destruct H.
  eexists.
  eapply insert_Sem; eauto.
  intro i; reflexivity.
Qed.

(** *** Specifying the smart constructors [tip] and [bin] *)

Lemma tip_Desc0:
  forall p bm r f,
    0 <= p ->
    p = rPrefix r ->
    rBits r = N.log2 WIDTH ->
    (forall i, f i = bitmapInRange r bm i) ->
    isBitMask0 bm ->
    Desc0 (tip p bm) r f.
Proof.
  intros.
  unfold tip.
  unfoldMethods.
  simpl (Z.to_N 0).
  rewrite isBitMask0_zero_or_isBitMask in H3.
  destruct H3; subst.
  * rewrite N.eqb_refl.
    apply Desc0Nil.
    intro j. rewrite H2.
    apply bitmapInRange_0.
  * replace (bm =? 0)%N with false
      by (symmetry; apply N.eqb_neq; intro; subst; inversion H3; inversion H0).
    apply Desc_Desc0.
    apply DescTip; auto.
Qed.

Lemma bin_Desc0:
  forall s1 r1 f1 s2 r2 f2 p msk r f,
    Desc0 s1 r1 f1 ->
    Desc0 s2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = rPrefix r ->
    msk = rMask r -> 
    (forall i, f i = f1 i || f2 i) ->
    Desc0 (bin p msk s1 s2) r f.
Proof.
  intros.
  destruct H, H0.
  * apply Desc0Nil.
    intro j. rewrite H6, H, H0. reflexivity.
  * replace (bin _ _ _ _) with s by (destruct s; reflexivity).
    eapply Desc0NotNil; eauto.
    + isSubrange_true.
    + solve_f_eq.
  * replace (bin _ _ _ _) with s by (destruct s; reflexivity).
    eapply Desc0NotNil; try eassumption.
    + isSubrange_true.
    + solve_f_eq.
  * replace (bin p msk s s0) with (Bin p msk s s0)
      by (destruct s, s0; try reflexivity; try inversion HD; try inversion HD0).
    apply Desc_Desc0.
    eapply DescBin; try eassumption.
    + isSubrange_true.
    + isSubrange_true.
    + solve_f_eq.
Qed.

(** *** Specifying [remove] *)

Lemma deleteBM_Desc:
  forall p' bm s2 r1 r2 f1 f2 f,
  Desc (Tip p' bm) r1 f1 ->
  Desc s2 r2 f2 ->
  (forall i, f i = negb (f1 i) && f2 i) ->
  Desc0 (deleteBM p' bm s2) r2 f.
Proof.
  intros ???????? HTip HD Hf.
  revert dependent f.
  induction HD; intros f' Hf'; subst.
  * simpl deleteBM; unfold Prim.seq.
    inversion_clear HTip; subst.
    unfoldMethods.
    apply same_size_compare; try Nomega; intros.
    + subst.
      apply tip_Desc0; auto.
      - solve_f_eq.
      - isBitMask.
    + apply Desc_Desc0.
      apply DescTip; auto.
      solve_f_eq_disjoint.
  * simpl. unfold Prim.seq.
    inversion_clear HTip; subst.

    assert (N.log2 WIDTH <= rBits r2)%N by (eapply Desc_larger_WIDTH; eauto).
    assert (rBits r2 <= rBits (halfRange r true))%N by (apply subRange_smaller; auto).
    assert (rBits (halfRange r true) < rBits r)%N by (apply halfRange_smaller; auto).
    assert (rBits r1 < rBits r)%N by Nomega.

    apply nomatch_zero_smaller; try assumption; intros.
    + rewrite rangeDisjoint_sym in *.
      apply Desc_Desc0.
      eapply DescBin; try eassumption; try reflexivity.
      intro.
        rewrite Hf'. rewrite H4. rewrite H6.
        destruct (inRange i r) eqn:Hir.
        - rewrite bitmapInRange_outside by inRange_false.
          reflexivity.
        - rewrite (Desc_outside HD1) by inRange_false.
          rewrite (Desc_outside HD2) by inRange_false.
          split_bool; reflexivity.
    + eapply bin_Desc0.
      ** apply IHHD1.
         intro. reflexivity.
      ** apply Desc_Desc0; eassumption.
      ** assumption.
      ** assumption.
      ** assumption.
      ** reflexivity.
      ** reflexivity.
      ** solve_f_eq_disjoint.
    + eapply bin_Desc0.
      ** apply Desc_Desc0; eassumption.
      ** apply IHHD2.
         intro. reflexivity.
      ** assumption.
      ** assumption.
      ** assumption.
      ** reflexivity.
      ** reflexivity.
      ** solve_f_eq_disjoint.
Qed.

Lemma delete_Desc:
  forall e s r f f',
  0 <= e ->
  Desc s r f ->
  (forall i, f' i = negb (i =? e) && f i) ->
  Desc0 (delete e s) r f'.
Proof.
  intros.
  unfold delete, Prim.seq.
  eapply deleteBM_Desc.
  * eapply DescTip; try nonneg.
    + symmetry. apply rPrefix_shiftr.
    + reflexivity.
    + isBitMask.
  * eassumption.
  * setoid_rewrite bitmapInRange_bitmapOf. assumption.
Qed.

Lemma delete_Sem:
  forall e s f f',
  0 <= e ->
  Sem s f ->
  (forall i, f' i = negb (i =? e) && f i) ->
  Sem (delete e s) f'.
Proof.
  intros.
  destruct H0.
  * apply SemNil.
    solve_f_eq.
  * eapply Desc0_Sem.
    eapply delete_Desc; try eassumption.
Qed.

Lemma delete_WF:
  forall n s,
  WF s -> 0 <= n ->
  WF (delete n s).
Proof.
  intros.
  destruct H.
  eexists.
  eapply delete_Sem; try eassumption.
  intro i. reflexivity.
Qed.

(** *** Specifing [union] *)

(** The following is copied from the body of [union] *)

Definition union_body s1 s2 := match s1, s2 with
  | (Bin p1 m1 l1 r1 as t1) , (Bin p2 m2 l2 r2 as t2) => 
     let union2 :=
       if nomatch p1 p2 m2 : bool
       then link p1 t1 p2 t2
       else if zero p1 m2 : bool
            then Bin p2 m2 (union t1 l2) r2
            else Bin p2 m2 l2 (union t1 r2) in
     let union1 :=
       if nomatch p2 p1 m1 : bool
       then link p1 t1 p2 t2
       else if zero p2 m1 : bool
            then Bin p1 m1 (union l1 t2) r1
            else Bin p1 m1 l1 (union r1 t2) in
     if shorter m1 m2 : bool
     then union1
     else if shorter m2 m1 : bool
          then union2
          else if p1 == p2 : bool
                   then Bin p1 m1 (union l1 l2) (union r1 r2)
                   else link p1 t1 p2 t2
  | (Bin _ _ _ _ as t) , Tip kx bm => insertBM kx bm t
  | (Bin _ _ _ _ as t) , Nil => t
  | Tip kx bm , t => insertBM kx bm t
  | Nil , t => t
  end.

Lemma union_eq s1 s2 :
  union s1 s2 = union_body s1 s2.
Proof.
  unfold union, union_func.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext.
  unfold projT1, projT2.
  unfold union_body.
  repeat lazymatch goal with
    | [ |- _ = match ?x with _ => _ end ] => destruct x
    | _ => reflexivity
  end.
Qed.

Program Fixpoint union_Desc
  s1 r1 f1 s2 r2 f2 f
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  (forall i, f i = f1 i || f2 i) ->
  Desc (union s1 s2) (commonRange r1 r2) f 
  := fun HD1 HD2 Hf => _.
Next Obligation.
  rewrite union_eq.
  unfold union_body.
  inversion HD1; subst.
  * eapply insertBM_Desc; try eassumption; try reflexivity.
  * set (sl := Bin (rPrefix r1) (rMask r1) s0 s3) in *.
    inversion HD2; subst.
    + rewrite commonRange_sym by (eapply Desc_rNonneg; eassumption).
      eapply insertBM_Desc; try eassumption; try reflexivity.
      solve_f_eq.
    + set (sr := Bin (rPrefix r2) (rMask r2) s1 s4) in *.
      rewrite !shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r1)); [|destruct (N.ltb_spec (rBits r1) (rBits r2))].
      ++ apply nomatch_zero_smaller; try assumption; intros.
        - rewrite rangeDisjoint_sym in *.
          rewrite disjoint_commonRange in * by assumption.
          eapply link_Desc;
            [ eapply DescBin with (r := r1); try eassumption; try reflexivity
            | eapply DescBin with (r := r2); try eassumption; try reflexivity
            |..]; auto.
        - rewrite -> (isSubrange_commonRange_l r1 r2) in * by isSubrange_true.
          eapply DescBin; [eapply union_Desc|eassumption|..]; try eassumption; try reflexivity.
          ** subst sl sr. simpl. omega.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** solve_f_eq.
        - rewrite -> (isSubrange_commonRange_l r1 r2) in *  by isSubrange_true.
          eapply DescBin; [eassumption|eapply union_Desc|..]; try eassumption; try reflexivity.
          ** subst sl sr. simpl. omega.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** solve_f_eq.
      ++ apply nomatch_zero_smaller; try assumption; intros.
        - rewrite disjoint_commonRange in * by assumption.
          eapply link_Desc;
            [ eapply DescBin with (r := r1); try eassumption; try reflexivity
            | eapply DescBin with (r := r2); try eassumption; try reflexivity
            |..]; auto.
        - rewrite -> (isSubrange_commonRange_r r1 r2) in * by isSubrange_true.
          eapply DescBin; [eapply union_Desc|eassumption|..]; try eassumption; try reflexivity.
          ** subst sl sr. simpl. omega.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** solve_f_eq.
        - rewrite -> (isSubrange_commonRange_r r1 r2) in *  by isSubrange_true.
          eapply DescBin; [eassumption|eapply union_Desc|..]; try eassumption; try reflexivity.
          ** subst sl sr. simpl. omega.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** solve_f_eq.
      ++ apply same_size_compare; try Nomega; intros.
        - subst.
          rewrite commonRange_idem in *.
          eapply DescBin; try assumption; try reflexivity.
          ** eapply union_Desc.
             -- subst sl sr. simpl. omega.
             -- eassumption.
             -- eassumption.
             -- intro i. reflexivity.
          ** eapply union_Desc.
             -- subst sl sr. simpl. omega.
             -- eassumption.
             -- eassumption.
             -- intro i. reflexivity.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** solve_f_eq.
      - rewrite disjoint_commonRange in * by assumption.
        eapply link_Desc;
          [ eapply DescBin with (r := r1); try eassumption; try reflexivity
          | eapply DescBin with (r := r2); try eassumption; try reflexivity
          |..]; auto.
Qed.

Lemma union_Sem:
  forall s1 f1 s2 f2,
  Sem s1 f1 ->
  Sem s2 f2 ->
  Sem (union s1 s2) (fun i => f1 i || f2 i).
Proof.
  intros.
  destruct H; [|destruct H0].
  * eapply Sem_change_f. apply H0.
    solve_f_eq.
  * eapply Sem_change_f. eapply DescSem.
    replace (union s Nil) with s by (destruct s; reflexivity).
    eapply HD.
    solve_f_eq.
  * eapply DescSem.
    eapply union_Desc; try eassumption.
    solve_f_eq.
Qed.

Lemma union_WF:
  forall s1 s2, WF s1 ->  WF s2 -> WF (union s1 s2).
Proof.
  intros.
  destruct H, H0.
  eexists. apply union_Sem; eassumption.
Qed.

(** *** Specifing [intersection] *)

(** The following is copied from the body of [intersection] *)

Definition intersection_body s1 s2 := match s1, s2 with
  | (Bin p1 m1 l1 r1 as t1) , (Bin p2 m2 l2 r2 as t2) =>
      let intersection2 :=
         if nomatch p1 p2 m2 : bool
         then Nil
         else if zero p1 m2 : bool
              then intersection t1 l2
              else intersection t1 r2 in
       let intersection1 :=
         if nomatch p2 p1 m1 : bool
         then Nil
         else if zero p2 m1 : bool
              then intersection l1 t2
              else intersection r1 t2 in
       if shorter m1 m2 : bool
       then intersection1
       else if shorter m2 m1 : bool
            then intersection2
            else if p1 GHC.Base.== p2 : bool
                 then bin p1 m1 (intersection l1 l2) (intersection r1
                                                     r2)
                 else Nil
  | (Bin _ _ _ _ as t1) , Tip kx2 bm2 =>
     (fix intersectBM arg_11__
     := match arg_11__ as arg_11__' return (arg_11__' = arg_11__ -> IntSet) with
          | Bin p1 m1 l1 r1 => fun _ =>
                               if nomatch kx2 p1 m1 : bool
                               then Nil
                               else if zero kx2 m1 : bool
                                    then intersectBM l1
                                    else intersectBM r1
          | Tip kx1 bm1 => fun _ =>
                           if kx1 GHC.Base.== kx2 : bool
                           then tip kx1 (bm1 Data.Bits..&.(**) bm2)
                           else Nil
          | Nil => fun _ => Nil
      end eq_refl) t1
  | Bin _ _ _ _ , Nil => Nil
  | Tip kx1 bm1 , t2 =>
      (fix intersectBM arg_18__
          := match arg_18__  as arg_18__' return (arg_18__' = arg_18__ -> IntSet) with
               | Bin p2 m2 l2 r2 => fun _ =>
                                    if nomatch kx1 p2 m2 : bool
                                    then Nil
                                    else if zero kx1 m2 : bool
                                         then intersectBM l2
                                         else intersectBM r2
               | Tip kx2 bm2 => fun _ =>
                                if kx1 GHC.Base.== kx2 : bool
                                then tip kx1 (bm1 Data.Bits..&.(**) bm2)
                                else Nil
               | Nil => fun _ => Nil
             end eq_refl) t2
  | Nil , _ => Nil
  end.

Lemma intersection_eq s1 s2 :
  intersection s1 s2 = intersection_body s1 s2.
Proof.
  unfold intersection, intersection_func.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext.
  unfold projT1, projT2.
  unfold intersection_body.
  repeat match goal with
    | _ => progress replace (Sumbool.sumbool_of_bool false) with (@right (false = true) (false = false) (@eq_refl bool false))
by reflexivity
    | _ => progress replace (Sumbool.sumbool_of_bool true) with (@left (true = true) (true = false) (@eq_refl bool true))
by reflexivity
    | [ |- _ = match ?x with _ => _ end ] => destruct x
    | _ => assumption || reflexivity
    | [ |- _ ?x = _ ?x ] => induction x
  end.
Qed.


Program Fixpoint intersection_Desc
  s1 r1 f1 s2 r2 f2 f
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  (forall i, f i = f1 i && f2 i) ->
  Desc0 (intersection s1 s2) r1 f 
  := fun HD1 HD2 Hf => _.
Next Obligation.
  rewrite intersection_eq.
  unfold intersection_body.
  unfoldMethods.

  inversion HD1.
  * (* s1 is a Tip *)
    subst.
    clear intersection_Desc.
    generalize dependent f.
    induction HD2; intros f' Hf'; subst.
    + apply same_size_compare; try Nomega; intros.
      -- subst.
         apply tip_Desc0; auto.
         ** solve_f_eq.
         ** isBitMask.
      -- apply Desc0Nil.
         solve_f_eq_disjoint.
    + assert (N.log2 WIDTH <= rBits r0)%N by (eapply Desc_larger_WIDTH; eauto).
      assert (rBits r0 <= rBits (halfRange r false))%N by (apply subRange_smaller; auto).
      assert (rBits (halfRange r false) < rBits r)%N by (apply halfRange_smaller; auto).
      assert (rBits r1 < rBits r)%N by Nomega.

      apply nomatch_zero_smaller; try assumption; intros.
      - apply Desc0Nil.
        solve_f_eq_disjoint.
      - eapply Desc0_subRange; [apply IHHD2_1|]. clear IHHD2_1 IHHD2_2.
        ** solve_f_eq_disjoint.
        ** isSubrange_true; eapply Desc_rNonneg; eassumption.
      - eapply Desc0_subRange.
        ** apply IHHD2_2.
           solve_f_eq_disjoint.
        ** isSubrange_true; eapply Desc_rNonneg; eassumption.

  * (* s1 is a Bin *)
    inversion HD2.
    + (* s2 is a Tip *)

      (* Need to undo the split of s1 *)
      change (Desc0 ((fix intersectBM (arg_11__ : IntSet) : IntSet :=
        match arg_11__  as arg_11__' return (arg_11__' = arg_11__ -> IntSet) with
        | Bin p1 m1 l1 r5 =>
            fun _ =>
            if nomatch p0 p1 m1
            then Nil
            else if zero p0 m1 then intersectBM l1 else intersectBM r5
        | Tip kx1 bm1 =>
            fun _ =>
            if _GHC.Base.==_ kx1 p0 then tip kx1 (N.land bm1 bm) else Nil
        | Nil => fun _ => Nil
        end eq_refl) (Bin p msk s0 s3)) r1 f).
      rewrite  H7.
      clear dependent s0. clear dependent s3. clear dependent r0. clear dependent r3. clear dependent f0. clear dependent f3.
      clear H1.
      subst.

      (* Now we are essentially in the same situation as above. *)
      (* Unfortunately, the two implementations of [intersectionBM] are slightly 
         different in irrelevant details that make ist just hard enough to abstract
         over them in a lemma of its own. So let’s just copy’n’paste. *)
      clear intersection_Desc.
      generalize dependent f.
      induction HD1; intros f' Hf'; subst.
      ++ apply same_size_compare; try Nomega; intros.
        subst.
        apply tip_Desc0; auto.
        ** solve_f_eq_disjoint.
        ** isBitMask.
        ** apply Desc0Nil.
           solve_f_eq_disjoint.

    ++ assert (N.log2 WIDTH <= rBits r1)%N by (eapply Desc_larger_WIDTH; eauto).
      assert (rBits r1 <= rBits (halfRange r false))%N by (apply subRange_smaller; auto).
      assert (rBits (halfRange r false) < rBits r)%N by (apply halfRange_smaller; auto).
      assert (rBits r2 < rBits r)%N by Nomega.

      apply nomatch_zero_smaller; try assumption; intros.
      - apply Desc0Nil.
        solve_f_eq_disjoint.

      - eapply Desc0_subRange.
        ** apply IHHD1_1.
           solve_f_eq_disjoint.
        ** isSubrange_true; eapply Desc_rNonneg; eassumption.

      - eapply Desc0_subRange.
        ** apply IHHD1_2.
           solve_f_eq_disjoint.
        ** isSubrange_true; eapply Desc_rNonneg; eassumption.

    + subst.
      set (sl := Bin (rPrefix r1) (rMask r1) s0 s3) in *.
      set (sr := Bin (rPrefix r2) (rMask r2) s4 s5) in *.
      rewrite !shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r1)).
      ++ (* s2 is smaller than s1 *)
        apply nomatch_zero_smaller; try assumption; intros.
        - (* s2 is disjoint of s1 *)
          apply Desc0Nil.
          solve_f_eq_disjoint.

        - (* s2 is part of the left half of s1 *)
          eapply Desc0_subRange.
          eapply intersection_Desc; clear intersection_Desc; try eassumption.
          ** subst sl sr. simpl. omega.
          ** solve_f_eq_disjoint.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
        - (* s2 is part of the right half of s1 *)
          eapply Desc0_subRange.
          eapply intersection_Desc; clear intersection_Desc; try eassumption.
          ** subst sl sr. simpl. omega.
          ** solve_f_eq_disjoint.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.

      ++ (* s2 is not smaller than s1 *)
        destruct (N.ltb_spec (rBits r1) (rBits r2)).
        -- (* s2 is smaller than s1 *)
          apply nomatch_zero_smaller; try assumption; intros.
          - (* s1 is disjoint of s2 *)
            apply Desc0Nil.
            solve_f_eq_disjoint.
          - (* s1 is part of the left half of s2 *)
            eapply Desc0_subRange.
            eapply intersection_Desc; clear intersection_Desc; try eassumption.
            ** subst sl sr. simpl. omega.
            ** solve_f_eq_disjoint.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.

          - (* s1 is part of the right half of s2 *)

            eapply Desc0_subRange.
            eapply intersection_Desc; clear intersection_Desc; try eassumption.
            ** subst sl sr. simpl. omega.
            ** solve_f_eq_disjoint.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.

        -- (* s1 and s2 are the same size *)
          apply same_size_compare; try Nomega; intros.
          - subst.
            eapply bin_Desc0; try assumption; try reflexivity.
            ** eapply intersection_Desc.
               --- subst sl sr. simpl. omega.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ** eapply intersection_Desc.
               --- subst sl sr. simpl. omega.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.
            ** solve_f_eq_disjoint.
          - apply Desc0Nil.
            solve_f_eq_disjoint.
Qed.

Lemma intersection_Sem:
  forall s1 f1 s2 f2,
  Sem s1 f1 ->
  Sem s2 f2 ->
  Sem (intersection s1 s2) (fun i => f1 i && f2 i).
Proof.
  intros.
  destruct H; [|destruct H0].
  * apply SemNil. solve_f_eq.
  * replace (intersection s Nil) with Nil by (destruct s; reflexivity).
    apply SemNil. solve_f_eq.
  * eapply Desc0_Sem. eapply intersection_Desc; try eauto.
Qed.

Lemma intersection_WF:
  forall s1 s2, WF s1 ->  WF s2 -> WF (intersection s1 s2).
Proof.
  intros.
  destruct H, H0.
  eexists. apply intersection_Sem; eassumption.
Qed.

(** *** Specifing [difference] *)

(** The following is copied from the body of [difference] *)

Definition difference_body s1 s2 := match s1, s2 with
  | (Bin p1 m1 l1 r1 as t1) , (Bin p2 m2 l2 r2 as t2) =>
     let difference2 :=
       if nomatch p1 p2 m2 : bool
       then t1
       else if zero p1 m2 : bool
            then difference t1 l2
            else difference t1 r2 in
     let difference1 :=
       if nomatch p2 p1 m1 : bool
       then t1
       else if zero p2 m1 : bool
            then bin p1 m1 (difference l1 t2) r1
            else bin p1 m1 l1 (difference r1 t2) in
     if shorter m1 m2 : bool
     then difference1
     else if shorter m2 m1 : bool
          then difference2
          else if p1 GHC.Base.== p2 : bool
               then bin p1 m1 (difference l1 l2) (difference r1 r2)
               else t1
  | (Bin _ _ _ _ as t) , Tip kx bm => deleteBM kx bm t
  | (Bin _ _ _ _ as t) , Nil => t
  | (Tip kx bm as t1) , t2 =>
     (fix differenceTip arg_12__
        := match arg_12__ as arg_12__' return (arg_12__' = arg_12__ -> IntSet) with 
             | Bin p2 m2 l2 r2 => fun _ =>
                                  if nomatch kx p2 m2 : bool
                                  then t1
                                  else if zero kx m2 : bool
                                       then differenceTip l2
                                       else differenceTip r2
             | Tip kx2 bm2 => fun _ =>
                              if kx GHC.Base.== kx2 : bool
                              then tip kx (Data.Bits.xor bm (bm Data.Bits..&.(**) bm2))
                              else t1
             | Nil => fun _ => t1
           end eq_refl) t2
  | Nil , _ => Nil
  end.

Lemma difference_eq s1 s2 :
  difference s1 s2 = difference_body s1 s2.
Proof.
  unfold difference, difference_func.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext.
  unfold projT1, projT2.
  unfold difference_body.
  repeat match goal with
    | _ => progress replace (Sumbool.sumbool_of_bool false) with (@right (false = true) (false = false) (@eq_refl bool false))
by reflexivity
    | _ => progress replace (Sumbool.sumbool_of_bool true) with (@left (true = true) (true = false) (@eq_refl bool true))
by reflexivity
    | [ |- _ = match ?x with _ => _ end ] => destruct x
    | _ => assumption || reflexivity
    | [ |- _ ?x = _ ?x ] => induction x
  end.
Qed.

Program Fixpoint difference_Desc
  s1 r1 f1 s2 r2 f2 f
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  (forall i, f i = f1 i && negb (f2 i)) ->
  Desc0 (difference s1 s2) r1 f 
  := fun HD1 HD2 Hf => _.
Next Obligation.
  rewrite difference_eq.
  unfold difference_body.
  unfoldMethods.

  inversion HD1.
  * (* s1 is a Tip *)
    subst.
    clear difference_Desc.
    generalize dependent f.
    induction HD2; intros f' Hf'; subst.
    + unfold xor.
      apply same_size_compare; try Nomega; intros.
      -- subst.
         apply tip_Desc0; auto.
         ** solve_f_eq.
         ** isBitMask.
      -- eapply Desc0NotNil; try eassumption.
         ** apply isSubrange_refl.
         ** solve_f_eq_disjoint.
    + assert (N.log2 WIDTH <= rBits r0)%N by (eapply Desc_larger_WIDTH; eauto).
      assert (rBits r0 <= rBits (halfRange r false))%N by (apply subRange_smaller; auto).
      assert (rBits (halfRange r false) < rBits r)%N by (apply halfRange_smaller; auto).
      assert (rBits r1 < rBits r)%N by Nomega.

      apply nomatch_zero_smaller; try assumption; intros.
      - eapply Desc0NotNil; try eassumption.
        ** apply isSubrange_refl.
        ** solve_f_eq_disjoint.
      - eapply Desc0_subRange; [apply IHHD2_1|apply isSubrange_refl]. clear IHHD2_1 IHHD2_2.
        solve_f_eq_disjoint.
      - eapply Desc0_subRange; [apply IHHD2_2|apply isSubrange_refl]. clear IHHD2_1 IHHD2_2.
        solve_f_eq_disjoint.

  * (* s1 is a Bin *)
    inversion HD2.
    + (* s2 is a Tip *)
      subst.
      eapply deleteBM_Desc; try eassumption.
      solve_f_eq.
    + subst.
      set (sl := Bin (rPrefix r1) (rMask r1) s0 s3) in *.
      set (sr := Bin (rPrefix r2) (rMask r2) s4 s5) in *.
      rewrite !shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r1)).
      ** (* s2 is smaller than s1 *)
        apply nomatch_zero_smaller; try assumption; intros.
        - (* s2 is disjoint of s1 *)
          eapply Desc_Desc0; eapply DescBin; try eassumption; try reflexivity.
          solve_f_eq_disjoint.

        - (* s2 is part of the left half of s1 *)
          eapply bin_Desc0.
          ++ eapply difference_Desc; clear difference_Desc; try eassumption.
             subst sl sr. simpl. omega.
             intro i; reflexivity.
          ++ apply Desc_Desc0; eassumption.
          ++ eassumption.
          ++ eassumption.
          ++ eassumption.
          ++ reflexivity.
          ++ reflexivity.
          ++ solve_f_eq_disjoint.
        - (* s2 is part of the right half of s1 *)
          eapply bin_Desc0.
          ++ apply Desc_Desc0; eassumption.
          ++ eapply difference_Desc; clear difference_Desc; try eassumption.
             subst sl sr. simpl. omega.
             intro i; reflexivity.
          ++ eassumption.
          ++ eassumption.
          ++ eassumption.
          ++ reflexivity.
          ++ reflexivity.
          ++ solve_f_eq_disjoint.

      ** (* s2 is not smaller than s1 *)
        destruct (N.ltb_spec (rBits r1) (rBits r2)).
        -- (* s2 is smaller than s1 *)
          apply nomatch_zero_smaller; try assumption; intros.
          - (* s1 is disjoint of s2 *)
            eapply Desc_Desc0; eapply DescBin; try eassumption; try reflexivity.
            solve_f_eq_disjoint.
          - (* s1 is part of the left half of s2 *)
            eapply Desc0_subRange.
            eapply difference_Desc; clear difference_Desc; try eassumption.
            *** subst sl sr. simpl. omega.
            *** solve_f_eq_disjoint.
            *** apply isSubrange_refl.
          - (* s1 is part of the right half of s2 *)
            eapply Desc0_subRange.
            eapply difference_Desc; clear difference_Desc; try eassumption.
            *** subst sl sr. simpl. omega.
            *** solve_f_eq_disjoint.
            *** apply isSubrange_refl.

        -- (* s1 and s2 are the same size *)
          assert (rBits r1 = rBits r2) by Nomega.
          apply same_size_compare; try Nomega; intros.
          - subst.
            eapply bin_Desc0; try assumption; try reflexivity.
            ++ eapply difference_Desc.
               --- subst sl sr. simpl. omega.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ++ eapply difference_Desc.
               --- subst sl sr. simpl. omega.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ++ assumption.
            ++ assumption.
            ++ solve_f_eq_disjoint.
          - eapply Desc_Desc0; eapply DescBin; try eassumption; try reflexivity.
            solve_f_eq_disjoint.
Qed.

Lemma difference_Sem:
  forall s1 f1 s2 f2,
  Sem s1 f1 ->
  Sem s2 f2 ->
  Sem (difference s1 s2) (fun i => f1 i && negb (f2 i)).
Proof.
  intros.
  destruct H; [|destruct H0].
  * apply SemNil. solve_f_eq.
  * replace (difference s Nil) with s by (destruct s; reflexivity).
    eapply DescSem.
    eapply Desc_change_f.
    eassumption.
    solve_f_eq.
  * eapply Desc0_Sem. eapply difference_Desc; try eauto.
Qed.

Lemma difference_WF:
  forall s1 s2, WF s1 ->  WF s2 -> WF (difference s1 s2).
Proof.
  intros.
  destruct H, H0.
  eexists. apply difference_Sem; eassumption.
Qed.


(** *** Specifing [foldr] *)


(* We can extract the argument to [unsafeFix] from the definition of [foldrBits]. *)
Definition foldrBits_go {a} (p : Int) (f : Int -> a -> a)
  : (Nat -> a -> a) -> Nat -> a -> a.
Proof.
  let foldrBits_rhs := eval unfold foldrBits in (foldrBits p f) in
  match foldrBits_rhs with context[ unsafeFix ?f _ ] => exact f end.
Defined.

(** This lemma will encapsulate the termination proof, so that the rest of the proof
 will not have to be modified. *)
Lemma foldrBits_go_eq {a} (p : Int) (f : Int -> a -> a) :
  unsafeFix (foldrBits_go p f) = foldrBits_go p f (unsafeFix (foldrBits_go p f)).
Proof. apply unsafeFix_eq. Qed.

Lemma foldrBits_go_0:
  forall {a} p (f : Int -> a -> a) x,
  unsafeFix (foldrBits_go p f) 0%N x = x.
Proof.
  intros.
  rewrite foldrBits_go_eq.
  reflexivity.
Qed.

Lemma foldrBits_go_bm:
  forall {a} p (f : Int -> a -> a) bm x,
  isBitMask bm ->
  unsafeFix (foldrBits_go p f) bm x =
    unsafeFix (foldrBits_go p f) (N.clearbit bm (N_ctz bm))
             (f (p + (64 - 1) - Z.of_N (N_ctz bm)) x).
Proof.
  intros.
  etransitivity; [rewrite foldrBits_go_eq; reflexivity|].
  unfold foldrBits_go at 1.
  unfoldMethods.

  replace (bm =? Z.to_N 0)%N with false
    by (symmetry; apply N.eqb_neq; unfold isBitMask in *; zify; rewrite Z2N.id; omega).

  rewrite lxor_lowestBitMask by assumption.
  unfold lowestBitMask, indexOfTheOnlyBit.
  rewrite N.log2_pow2 by Nomega.
  reflexivity.
Qed.

Lemma foldrBits_go_revNat_bm:
  forall {a} p (f : Int -> a -> a) bm x,
  isBitMask bm ->
  unsafeFix (foldrBits_go p f) (revNatSafe bm) x =
    unsafeFix (foldrBits_go p f) (revNatSafe (N.clearbit bm (N.log2 bm)))
             (f (p + Z.of_N (N.log2 bm)) x).
Proof.
  intros.
  rewrite foldrBits_go_bm by isBitMask.
  f_equal.
  rewrite clearbit_revNat by isBitMask.
  rewrite <- N_log2_ctz by isBitMask.
  reflexivity.
  rewrite N_log2_ctz by isBitMask.
  rewrite !N2Z.inj_sub.
  rewrite !Z.add_sub_assoc. reflexivity.
  unfold WIDTH; Nomega.
  assert (N_ctz (revNatSafe bm) < WIDTH)%N by isBitMask.
  unfold WIDTH in *; Nomega.
Qed.

Lemma foldrBits_0:
  forall {a} p (f : Int -> a -> a) x,
  foldrBits p f x 0%N = x.
Proof.
  intros.
  unfold foldrBits.
  apply foldrBits_go_0.
Qed.


Lemma foldrBits_bm:
  forall {a} p (f : Int -> a -> a) bm x,
  isBitMask bm ->
  foldrBits p f x bm =
    foldrBits p f (f (p + Z.of_N (N.log2 bm)) x) 
        (N.clearbit bm (N.log2 bm)).
Proof.
  intros.
  apply foldrBits_go_revNat_bm; try isBitMask.
Qed.


Definition foldr_go {a} k :=
   (fix go (arg_0__ : a) (arg_1__ : IntSet) {struct arg_1__} : a :=
     match arg_1__ with
     | Bin _ _ l r0 => go (go arg_0__ r0) l
     | Tip kx bm =>
         foldrBits kx k
           arg_0__ bm
     | Nil => arg_0__
     end).


(** *** Specifing [toList] *)

Lemma In_cons_iff:
  forall {a} (y x : a) xs, In y (x :: xs) <-> x = y \/ In y xs.
Proof. intros. reflexivity. Qed.

Lemma In_foldrBits_cons:
  forall i r bm l,
  isBitMask0 bm ->
  rBits r = N.log2 WIDTH ->
  In i (foldrBits (rPrefix r) cons l bm) <-> (bitmapInRange r bm i = true \/ In i l).
Proof.
  intros.

  revert l.
  apply bits_ind with (bm := bm).
  * assumption.
  * intros.
    rewrite foldrBits_0.
    rewrite bitmapInRange_0. intuition congruence.
  * clear bm H. intros bm Hbm IH l.
    rewrite foldrBits_bm by isBitMask.
    rewrite -> IH.
    rewrite split_highestBitMask with (bm := bm) at 4 by assumption.
    rewrite bitmapInRange_lor.
    rewrite orb_true_iff.
    rewrite In_cons_iff.
    rewrite bitmapInRange_pow by (replace (rBits r); isBitMask).
    rewrite Z.eqb_eq.
    solve [tauto].
Qed.

Definition toList_go := foldr_go cons.

Lemma toList_go_In:
  forall s f, Sem s f ->
  forall l i, (f i = true \/ In i l) <-> In i (toList_go l s).
Proof.
  intros ?? HS.
  destruct HS.
  * intuition. rewrite H in H1. congruence.
  * induction HD; intros; simpl; subst.
    + rewrite In_foldrBits_cons by isBitMask.
      rewrite H2; reflexivity.
    + unfold op_zl__, Ord_Integer___, op_zl____.
      rewrite <- IHHD1.
      rewrite <- IHHD2.
      rewrite H4.
      rewrite orb_true_iff.
      intuition.
Qed.

Lemma toList_go_In_nil:
  forall s f, Sem s f ->
  forall i, f i = true <-> In i (toList_go nil s).
Proof.
  intros.
  rewrite <- toList_go_In by eassumption.
  intuition.
Qed.

Lemma toList_In:
  forall s f, Sem s f ->
  forall i, f i = true <-> In i (toList s).
Proof.
  intros.
  pose proof (toList_go_In_nil s f H i) as Hgo.
  destruct H.
  * apply Hgo.
  * destruct HD.
    + apply Hgo.
    + subst. simpl.
      unfold op_zl__, Ord_Integer___, op_zl____.
      destruct (Z.ltb_spec (rMask r) 0).
      - rewrite <- toList_go_In by (eapply DescSem; eassumption).
        rewrite <- toList_go_In by (eapply DescSem; eassumption).
        rewrite H4.
        rewrite orb_true_iff.
        intuition.
      - rewrite <- toList_go_In by (eapply DescSem; eassumption).
        rewrite <- toList_go_In by (eapply DescSem; eassumption).
        rewrite H4.
        rewrite orb_true_iff.
        intuition.
Qed.

Lemma toList_In_nonneg:
  forall s, WF s ->
  forall i, In i (toList s) ->
  0 <= i.
Proof.
   intros.
   destruct H as [f HSem].
   rewrite <- toList_In in H0 by eassumption.
   eapply Sem_nonneg; eassumption.
Qed.

Lemma toList_Bits_append:
  forall p l bm,
  isBitMask0 bm ->
  foldrBits p cons l bm = foldrBits p cons nil bm  ++ l.
Proof.
  intros.
  revert l.
  apply bits_ind with (bm := bm).
  - isBitMask.
  - intros xs.
    rewrite !foldrBits_0.
    reflexivity.
  - clear bm H. intros bm Hbm IH xs.
    rewrite !foldrBits_bm with (bm0 := bm) by isBitMask.
    rewrite IH.
    rewrite IH with (l := _ :: nil).
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma toList_go_append:
  forall l s r f,
  Desc s r f ->
  toList_go l s = toList_go nil s ++ l.
Proof.
  intros. revert l.
  induction H; intro l.
  * simpl.
    apply toList_Bits_append; isBitMask.
  * simpl.
    rewrite IHDesc2.
    rewrite IHDesc1.
    rewrite IHDesc2 at 2.
    rewrite IHDesc1 with (l := toList_go nil s2 ++ nil).
    rewrite app_nil_r.
    rewrite app_assoc.
    reflexivity.
Qed.

(** *** Sortedness of [toList] *)


Lemma to_List_Bits_below:
  forall p bm,
  isBitMask0 bm ->
  forall y, In y (foldrBits p cons nil bm) ->
  y <= p + Z.of_N (N.log2 bm).
Proof.
  intros p bm H.
  apply bits_ind with (bm := bm).
  * assumption.
  * intros.
    rewrite foldrBits_0 in H0.
    inversion H0.
  * intros.
    rewrite foldrBits_bm in H2 by isBitMask.
    rewrite toList_Bits_append in H2 by isBitMask.
    apply in_app_iff in H2.
    destruct H2.
    + apply H1 in H2.
      transitivity (p + Z.of_N (N.log2 (N.clearbit bm0 (N.log2 bm0)))); try assumption.
      apply Z.add_le_mono; try reflexivity.
      apply N2Z.inj_le.
      apply N.log2_le_mono.
      apply ldiff_le.
    + destruct H2 as [?|[]]. subst.
      reflexivity.
Qed.

Lemma to_List_Bits_sorted:
  forall p bm,
  isBitMask0 bm ->
  StronglySorted Z.lt (foldrBits p cons nil bm).
Proof.
  intros.
  apply bits_ind with (bm := bm).
  * assumption.
  * rewrite foldrBits_0.
    apply SSorted_nil.
  * clear bm H.
    intros.
    rewrite foldrBits_bm by isBitMask.
    rewrite toList_Bits_append by isBitMask.
    apply sorted_append with (x := p + Z.of_N (N.log2 bm)).
    + assumption.
    + apply SSorted_cons; constructor.
    + intros.
      eapply Z.le_lt_trans.
      eapply to_List_Bits_below; try eassumption; try isBitMask.
      enough (N.log2 (N.clearbit bm (N.log2 bm)) < N.log2 bm)%N by Nomega.
      assert (N.clearbit bm (N.log2 bm) <> 0)%N. {
        intro.
        rewrite H2 in H1.
        rewrite foldrBits_0 in H1.
        inversion H1.
      }
      apply N.log2_lt_pow2; try Nomega.
      rewrite clearbit_log2_mod by (unfold isBitMask in H; Nomega).
      apply N.mod_lt.
      apply N.pow_nonzero.
      Nomega.
    + intros y Hy. destruct Hy as [?|[]]. subst. reflexivity.
Qed.

Lemma to_List_go_Desc_sorted:
  forall s r f, Desc s r f -> StronglySorted Z.lt (toList_go nil s).
Proof.
  intros ??? HD.
  induction HD.
  * simpl. apply to_List_Bits_sorted. isBitMask.
  * simpl. subst.
    unfoldMethods.
    erewrite toList_go_append by (apply HD1).
    apply sorted_append with (x := rPrefix (halfRange r true)).
    + eapply IHHD1; eassumption.
    + eapply IHHD2; eassumption.
    + intros i Hi.
      rewrite rPrefix_halfRange_otherhalf by assumption.
      rewrite <- toList_go_In_nil in Hi by (eapply DescSem; eassumption).
      apply (Desc_inside HD1) in Hi.
      eapply inRange_isSubrange_true in Hi; try eassumption.
      apply inRange_bounded.
      assumption.
    + intros i Hi.
      rewrite <- toList_go_In_nil in Hi by (eapply DescSem; eassumption).
      apply (Desc_inside HD2) in Hi.
      eapply inRange_isSubrange_true in Hi; try eassumption.
      apply inRange_bounded.
      assumption.
Qed.

Lemma to_List_Desc_sorted:
  forall s r f, Desc s r f -> StronglySorted Z.lt (toList s).
Proof.
  intros ??? HD.
  destruct HD.
  * simpl. apply to_List_Bits_sorted. isBitMask.
  * simpl. subst.
    unfoldMethods.
    destruct (Z.ltb_spec (rMask r) 0).
    - (* This branch is inaccessible becase we only store non-negative numbers.
         This would chnage if we would switch to bounded numbers. *)
      exfalso.
      contradict H2.
      apply Zle_not_lt.
      destruct r as [p b].
      unfold rMask.
      nonneg.
    - fold (foldr_go (@cons Key)).
      erewrite toList_go_append by (apply HD1).
      change (StronglySorted Z.lt (toList_go nil s1 ++ toList_go nil s2)).
      apply sorted_append with (x := rPrefix (halfRange r true)).
      + eapply to_List_go_Desc_sorted; eassumption.
      + eapply to_List_go_Desc_sorted; eassumption.
      + intros i Hi.
        rewrite rPrefix_halfRange_otherhalf by assumption.
        rewrite <- toList_go_In_nil in Hi by (eapply DescSem; eassumption).
        apply (Desc_inside HD1) in Hi.
        eapply inRange_isSubrange_true in Hi; try eassumption.
        apply inRange_bounded.
        assumption.
      + intros i Hi.
        rewrite <- toList_go_In_nil in Hi by (eapply DescSem; eassumption).
        apply (Desc_inside HD2) in Hi.
        eapply inRange_isSubrange_true in Hi; try eassumption.
        apply inRange_bounded.
        assumption.
Qed.

Lemma to_List_sorted:
  forall s, WF s -> StronglySorted Z.lt (toList s).
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * apply SSorted_nil.
  * eapply to_List_Desc_sorted; eassumption.
Qed.

(** *** Specifying [foldl] *)

Definition foldl_go {a} k :=
  fix go (arg_0__ : a) (arg_1__ : IntSet) {struct arg_1__} : a :=
   match arg_1__ with
   | Bin _ _ l r0 => go (go arg_0__ l) r0
   | Tip kx bm => foldlBits kx k arg_0__ bm
   | Nil => arg_0__
   end.

(** This is a bit ugly, but it get’s the job done. From [foldlBits_0] and
    [foldlBits_bm] on, everything is pretty again.

    Part of the ugliness is that when solving the termination obligation using
    [Program Definition], the resulting prove captures not only the parameters of the
    local [go] function, but also the (unused) parameters of the enclosing [foldlBits]
    function.
*)
Definition foldlBits_go {a} (p : Int) (f : a -> Int -> a) (x : a) (bm : Nat)
  : ((forall x' : N, {_ : a | (N.to_nat x' < N.to_nat bm)%nat} -> a) -> a).
Proof.
  let rhs := eval unfold foldlBits in (foldlBits p f x bm) in
  match rhs with context[ GHC.Wf.wfFix2 _ _ _ ?f ] => exact (f bm x) end.
Defined.

Require Import Logic.FunctionalExtensionality.

Lemma foldlBits_eq:
  forall {a} p (f : a -> Int -> a) x bm,
  foldlBits p f x bm = @foldlBits_go a p f x bm (fun x y => foldlBits p f (proj1_sig y) x).
Proof.
  intros.
  unfold foldlBits.
  unfold foldlBits_go.
  etransitivity; only 1: apply GHC.Wf.wfFix2_eq.
  destruct (Sumbool.sumbool_of_bool _); try reflexivity.
  f_equal.
  extensionality x'.
  extensionality y'.
  extensionality go'.
  destruct (Sumbool.sumbool_of_bool _); try reflexivity.
  f_equal. f_equal.
  apply ProofIrrelevance.proof_irrelevance.
Qed.


Lemma foldlBits_0:
  forall {a} p (f : a -> Int -> a) x,
  foldlBits p f x 0%N = x.
Proof.
  intros.
  apply foldlBits_eq.
Qed.

Lemma foldlBits_bm:
  forall {a} p (f : a -> Int -> a) bm x,
  isBitMask bm ->
  foldlBits p f x bm =
    foldlBits p f 
       (f x (p + Z.of_N (N_ctz bm)))
       (N.clearbit bm (N_ctz bm)).
Proof.
  intros.
  rewrite foldlBits_eq at 1. unfold foldlBits_go, proj1_sig.
  unfoldMethods.
  replace (bm =? Z.to_N 0)%N with false
    by (symmetry; apply N.eqb_neq; unfold isBitMask in *; zify; rewrite Z2N.id; omega).
  (* eek *)
  replace (Sumbool.sumbool_of_bool false) with (@right (false = true) (false = false) (@eq_refl bool false))
    by reflexivity.
  f_equal.
  * unfold lowestBitMask.
    unfold indexOfTheOnlyBit.
    rewrite N.log2_pow2 by Nomega.
    reflexivity.
  * rewrite lxor_lowestBitMask by assumption.
    reflexivity.
Qed.


(**
This used to be the case definitionally until we switched to Program Fixpoint.
Maybe it will be the case again once we do not admit the termination proofs.
Until then, let’s throw axioms (functional extensionality, proof irrelevance) at it. *)
Lemma foldl'Bits_foldlBits : @foldl'Bits = @foldlBits.
Proof.
  unfold foldl'Bits.
  unfold foldlBits.
  intros.
  extensionality a.
  extensionality p.
  extensionality f.
  extensionality z.
  extensionality bm.
  f_equal.
  extensionality x'.
  extensionality y'.
  extensionality go'.
  destruct (Sumbool.sumbool_of_bool _); try reflexivity.
  f_equal. f_equal.
  apply ProofIrrelevance.proof_irrelevance.
Qed.

Lemma foldlBits_high_bm_aux:
  forall {a} p (f : a -> Int -> a) bm,
  isBitMask0 bm ->
  (bm <> 0)%N ->
  (forall x, foldlBits p f x bm =
    f (foldlBits p f x (N.clearbit bm (N.log2 bm))) (p + Z.of_N (N.log2 bm))).
Proof.
  intros.
  pose proof H.
  revert H1 H0 x.
  apply bits_ind_up with (bm := bm).
  - isBitMask.
  - clear bm H. intros Hbm Hpos x.
    Nomega.
  - clear bm H. intros bm Hbm IH _ Hpos x.
    destruct (N.eqb_spec (N.clearbit bm (N_ctz bm)) (0%N)).
    * clear IH.
    
      rewrite foldlBits_bm by isBitMask.
      rewrite e.
      rewrite foldlBits_0.

      apply clearbit_ctz_0 in e; try isBitMask.
      rewrite e.
      rewrite N.log2_pow2 by nonneg.
      rewrite clearbit_pow2_0.
      rewrite foldlBits_0.

      replace bm with (2^N.log2 bm)%N
        by (rewrite e; rewrite N.log2_pow2 by nonneg; reflexivity).
      rewrite N_ctz_pow2.
      reflexivity.
    * assert (hasTwoBits bm) by (split; auto; isBitMask).
      rewrite foldlBits_bm by isBitMask.
      rewrite IH by (isBitMask || assumption).
      rewrite log2_clearbit_ctz by assumption.
      f_equal.
      etransitivity; [|rewrite foldlBits_bm by isBitMask;  reflexivity].
      rewrite ctz_clearbit_log2 by assumption.
      rewrite clearbit_clearbit_comm at 1.
      reflexivity.
Qed.


Lemma foldlBits_high_bm:
  forall {a} p (f : a -> Int -> a) bm x,
  isBitMask bm ->
  foldlBits p f x bm =
    f (foldlBits p f x (N.clearbit bm (N.log2 bm))) (p + Z.of_N (N.log2 bm)).
Proof.
  intros.
  unfold isBitMask in H.
  apply foldlBits_high_bm_aux.
  * apply H.
  * Nomega.
Qed.

Lemma foldlBits_foldrBits:
  forall {a b}  k (x : a) p bm (k' : a -> b), isBitMask0 bm ->
    k' (foldlBits p k x bm) = foldrBits p (fun x g a => g (k a x)) k' bm x.
Proof.
  intros.
  unfold foldrBits.
  fold (@foldrBits_go (a->b) p (fun x g a => g (k a x))).

  revert k'.
  apply bits_ind with (bm := bm).
  - assumption.
  - intros.
    rewrite foldrBits_go_0.
    rewrite foldlBits_0.
    reflexivity.
  - clear bm H. intros bm Hbm IH k'.
    rewrite !@foldrBits_go_revNat_bm with (bm := bm) by isBitMask.
    rewrite !@foldlBits_high_bm with (bm := bm) by isBitMask.
    rewrite <- IH.
    reflexivity.
Qed.

Lemma foldl_go_foldr_go:
  forall {a b}  k (x : a) s r f (k' : a -> b), Desc s r f ->
    k' (foldl_go k x s) = foldr_go (fun x g a => g (k a x)) k' s x.
Proof.
  intros.
  revert x k'; induction H; intros.
  * apply foldlBits_foldrBits; isBitMask.
  * simpl.
    rewrite IHDesc2 with (k' := k').
    rewrite IHDesc1 with (k' := foldr_go _ k' s2).
    reflexivity.
Qed.

Lemma foldl_foldr:
  forall {a} k (x : a) s, WF s ->
    foldl k x s = foldr (fun x g a => g (k a x)) id s x.
Proof.
 intros.
 destruct H as [f HSem].
 destruct HSem.
 * reflexivity.
 * revert x; destruct HD; intros.
   + simpl.
     apply foldlBits_foldrBits with (k' :=  fun x => x); isBitMask.
   + simpl.
     fold (foldl_go k).
     fold (foldr_go (fun (x0 : Key) (g : a -> a) (a0 : a) => g (k a0 x0))).
     unfoldMethods.
     destruct (Z.ltb_spec msk 0).
     - erewrite foldl_go_foldr_go with (k' := fun x => x) by eassumption.
       eapply foldl_go_foldr_go; eassumption.
     - erewrite foldl_go_foldr_go with (k' := fun x => x) by eassumption.
       eapply foldl_go_foldr_go; eassumption.
Qed.

Lemma fold_right_foldrBits_go:
  forall {a} f (x : a) p bm xs, isBitMask0 bm -> 
  fold_right f x (foldrBits p cons xs bm) = foldrBits p f (fold_right f x xs) bm.
Proof.
  intros.
  unfold foldrBits.
  fold (foldrBits_go p cons).
  fold (foldrBits_go p f).

  revert xs.
  apply bits_ind with (bm := bm).
  - assumption.
  - intros xs.
    rewrite !foldrBits_go_0.
    reflexivity.
  - clear bm H. intros bm Hbm IH xs.
    rewrite !@foldrBits_go_revNat_bm with (bm := bm) by isBitMask.
    rewrite IH.
    reflexivity.
Qed.

Lemma fold_right_toList_go:
  forall {a} f (x : a) s r f' xs, Desc s r f' -> 
  fold_right f x (foldr_go cons xs s) = foldr_go f (fold_right f x xs) s.
Proof.
  intros. 
  revert xs; induction H; intros.
  * apply fold_right_foldrBits_go; isBitMask.
  * simpl.
    rewrite IHDesc1.
    rewrite IHDesc2.
    reflexivity.
Qed.

Lemma fold_right_toList:
  forall {a} f (x : a) s xs, WF s-> 
  fold_right f x (foldr cons xs s) = foldr f (fold_right f x xs) s.
Proof.
  intros.
  destruct H as [f' HSem].
  destruct HSem.
  * reflexivity.
  * destruct HD.
    + apply fold_right_foldrBits_go; isBitMask.
    + simpl.
      unfoldMethods.
      fold (foldr_go (@cons Key)). 
      fold (foldr_go f).
      destruct (Z.ltb_spec msk 0).
      - do 2 erewrite fold_right_toList_go by eassumption. reflexivity.
      - do 2 erewrite fold_right_toList_go by eassumption. reflexivity.
Qed.

Lemma List_foldl_foldr:
  forall {a b} f (x : b) (xs : list a),
    fold_left f xs x = List.fold_right (fun x g a => g (f a x)) id xs x.
Proof.
  intros. revert x.
  induction xs; intro.
  * reflexivity.
  * simpl. rewrite IHxs. reflexivity.
Qed.

Lemma foldl_spec:
  forall {a} f (x : a) s, WF s ->
    foldl f x s = fold_left f (toList s) x.
Proof.
  intros.
  unfold toList, toAscList.
  rewrite foldl_foldr by assumption.
  rewrite List_foldl_foldr.
  rewrite fold_right_toList by assumption.
  reflexivity.
Qed.

(** *** Specifying [size] *)

Definition sizeGo : Int -> IntSet -> Int.
Proof.
  let size_rhs := eval unfold size in size in
  match size_rhs with ?f #0 => exact f end.
Defined.

Lemma popCount_N_length_toList_go:
  forall bm p l,
  isBitMask0 bm ->
  Z.of_N (N_popcount bm) + Z.of_nat (length l) = Z.of_nat (length (foldrBits p cons l bm)).
Proof.
  intros.
  unfold foldrBits.
  fold (foldrBits_go p cons).
  revert l.
  apply bits_ind with (bm := bm).
  - isBitMask.
  - intros.
    rewrite foldrBits_go_0.
    reflexivity.
  - clear bm H. intros bm Hbm IH l.
    rewrite !@foldrBits_go_revNat_bm with (bm := bm) by isBitMask.
    rewrite popCount_N_bm by (unfold isBitMask in Hbm; Nomega).
    rewrite <- IH; clear IH.
    simpl.
    Nomega.
Qed.

Lemma sizeGo_spec':
  forall x s r f, Desc s r f ->
  sizeGo x s = x + Z.of_nat (length (toList_go nil s)).
Proof.
  intros.
  intros.
  revert x; induction H; intro x.
  + simpl.
    unfold bitcount.
    rewrite <- popCount_N_length_toList_go by isBitMask.
    simpl.
    rewrite Z.add_0_r.
    reflexivity.
  + simpl.
    erewrite toList_go_append with (s := s1) by eassumption.
    erewrite toList_go_append with (s := s2) by eassumption.
    rewrite IHDesc1.
    rewrite IHDesc2.
    rewrite !app_length.
    simpl length.
    unfold Int in *.
    Nomega.
Qed.

Lemma sizeGo_spec:
  forall x s, WF s ->
  sizeGo x s = x + Z.of_nat (length (toList s)).
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * simpl. rewrite Z.add_0_r. reflexivity.
  * destruct HD.
    + simpl.
      unfold bitcount.
      rewrite <- popCount_N_length_toList_go by isBitMask.
      simpl. rewrite Z.add_0_r.
      reflexivity.
    + subst. simpl.
      unfoldMethods.
      destruct (Z.ltb_spec (rMask r) 0).
      -- erewrite toList_go_append with (s := s1) by eassumption.
         erewrite toList_go_append with (s := s2) by eassumption.
         erewrite sizeGo_spec' by eassumption.
         erewrite sizeGo_spec' by eassumption.
         rewrite !app_length.
         simpl length.
         unfold Int in *.
         Nomega.
      -- erewrite toList_go_append with (s := s1) by eassumption.
         erewrite toList_go_append with (s := s2) by eassumption.
         erewrite sizeGo_spec' by eassumption.
         erewrite sizeGo_spec' by eassumption.
         rewrite !app_length.
         simpl length.
         unfold Int in *.
         Nomega.
Qed.

Lemma size_spec:
  forall s, WF s ->
  size s = Z.of_nat (length (toList s)).
Proof.
  intros.
  unfold size.
  rewrite sizeGo_spec by assumption.
  reflexivity.
Qed.

(** *** Specifing [toDescList] *)

(** The easiest complete specification simply relates this to [toList] *)

Lemma toDescList_spec:
  forall s, WF s -> toDescList s = rev (toList s).
Proof.
  intros.
  unfold toDescList.
  rewrite foldl_spec by assumption.
  rewrite <- fold_left_rev_right.
  generalize (rev (toList s)).
  intro xs.
  induction xs.
  * reflexivity.
  * simpl. rewrite IHxs. reflexivity.
Qed.

(** *** Specifying [filter] *)

Definition filterBits p o bm :=
  (foldlBits 0
     (fun (bm0 : BitMap) (bi : Key) =>
      if p (o + bi) : bool then N.lor bm0 (bitmapOfSuffix bi) else bm0)
      0%N
      bm).

Lemma testbit_filterBits:
  forall p o bm i,
  isBitMask0 bm ->
  N.testbit (filterBits p o bm) i =
  (N.testbit bm i && p (o + Z.of_N i)).
Proof.
  intros.

  unfold filterBits.
  transitivity ((N.testbit bm i && p (o + Z.of_N i)) || N.testbit 0%N i);
    try (rewrite N.bits_0; rewrite orb_false_r; reflexivity).
  generalize (0%N) as a.
  apply bits_ind with (bm := bm).
  * assumption.
  * intros a.
    rewrite foldlBits_0.
    rewrite N.bits_0.
    rewrite andb_false_l.
    rewrite orb_false_l.
    reflexivity.
  * intros.
    unfold filterBits.
    rewrite foldlBits_high_bm by isBitMask.
    lazymatch goal with [|- N.testbit (if ?x then N.lor ?z ?y else ?z) ?i = _]  =>
      transitivity (N.testbit (N.lor z (if x then y else 0%N)) i);
        [destruct x; try rewrite N.lor_0_r; reflexivity|]
    end.
    rewrite N.lor_spec.
    rewrite H1; clear H1.
    rewrite N.clearbit_eqb.

    lazymatch goal with [|- context [N.testbit (if ?x then ?y else 0%N) ?i] ] =>
      replace (N.testbit (if x then y else 0%N) i)
         with (x && N.testbit y i)
           by (destruct x; try rewrite N.bits_0; repeat split_bool; reflexivity)
    end.
    rewrite Z.add_0_l.
    unfold bitmapOfSuffix; unfoldMethods; rewrite N.shiftl_1_l.
    rewrite !N.pow2_bits_eqb.
    rewrite N2Z.id.

    destruct (N.eqb_spec (N.log2 bm0) i).
    + subst; repeat split_bool; try reflexivity; exfalso.
      rewrite N.bit_log2 in Heqb by (unfold isBitMask in *; Nomega).
      congruence.
    + repeat split_bool; try reflexivity; exfalso.
Qed.

Lemma isBitMask_filterBits:
  forall p o bm,
  isBitMask0 bm -> isBitMask0 (filterBits p o bm).
Proof.
  intros.
  unfold isBitMask0.
  rewrite N_lt_pow2_testbits.
  intros j Hj.
  rewrite testbit_filterBits by isBitMask.
  rewrite isBitMask0_outside by assumption.
  rewrite andb_false_l.
  reflexivity.
Qed.
Hint Resolve isBitMask_filterBits : isBitMask.

Lemma filter_Desc:
  forall p s r f f',
  Desc s r f -> 
  (forall i, f' i = f i && p i) ->
  Desc0 (filter p s) r f'.
Proof.
  intros.
  revert f' H0.
  induction H.
  * intros.
    simpl. subst.
    rewrite foldl'Bits_foldlBits.
    fold (filterBits p (rPrefix r) bm).
    eapply tip_Desc0; try assumption; try reflexivity.
    + intro i.
      rewrite H4.
      rewrite H2.
      unfold bitmapInRange.
      destruct (inRange i r) eqn:Hir.
      - rewrite testbit_filterBits by isBitMask.
        f_equal. f_equal.
        clear p H4.
        rewrite Z.div_mod with (a := i) (b := Z.of_N WIDTH) at 1
          by (intro Htmp; inversion Htmp).
        f_equal.
        ** destruct r as [p b]. unfold inRange, rPrefix, rBits, snd in *.
           rewrite Z.eqb_eq in Hir.
           subst.
           rewrite Z.shiftl_mul_pow2 by nonneg.
           rewrite Z.shiftr_div_pow2 by nonneg.
           rewrite Z.mul_comm.
           reflexivity.
        ** rewrite Z2N.id by nonneg.
           rewrite Z.land_ones by nonneg.
           rewrite H1.
           reflexivity.
      - rewrite andb_false_l. reflexivity.
    + isBitMask.
  * intros. subst. simpl.
    eapply bin_Desc0.
    + apply IHDesc1; intro; reflexivity.
    + apply IHDesc2; intro; reflexivity.
    + assumption.
    + assumption.
    + assumption.
    + reflexivity.
    + reflexivity.
    + solve_f_eq.
Qed.

Lemma filter_Sem:
  forall p s f f',
  Sem s f -> 
  (forall i, f' i = f i && p i) ->
  Sem (filter p s) f'.
Proof.
  intros.
  destruct H.
  * apply SemNil.
    solve_f_eq.
  * eapply Desc0_Sem.
    eapply filter_Desc.
    eassumption.
    eassumption.
Qed.

Lemma filter_WF:
  forall p s, WF s -> WF (filter p s).
Proof.
  intros.
  destruct H.
  eexists.
  eapply filter_Sem.
  eassumption.
  intro. reflexivity.
Qed.

(** *** Specifying [partition] *)

(** Conveniently, [partition] uses [filterBits] *)

Lemma partition_fst:
  forall p s,
  fst (partition p s) = filter p s.
Proof.
  intros.
  induction s.
  * simpl.
    rewrite (surjective_pairing (partition p s1)).
    rewrite (surjective_pairing (partition p s2)).
    simpl.
    rewrite IHs1, IHs2.
    reflexivity.
  * reflexivity.
  * reflexivity.
Qed.

Lemma filterBits_neg:
  forall P p bm,
  isBitMask0 bm ->
  N.lxor bm (filterBits P p bm) = filterBits (fun x => negb (P x)) p bm.
Proof.
  intros.
  apply N.bits_inj; intro i.
  rewrite N.lxor_spec.
  rewrite testbit_filterBits by isBitMask.
  rewrite testbit_filterBits by isBitMask.
  repeat split_bool; reflexivity.
Qed.

(* We could do this without the WF requirements if we used bounded Nats;
   as we only need it for the [isBitMask0] requiremenet *)
Lemma partition_snd:
  forall p s,
  WF s ->
  snd (partition p s) = filter (fun x => negb (p x)) s.
Proof.
  intros P s Hwf.
  destruct Hwf as [f HSem].
  destruct HSem.
  * reflexivity.
  * intros.
    induction HD.
    + simpl.
      rewrite foldl'Bits_foldlBits.
      f_equal.
      change (N.lxor bm (filterBits P p bm) = filterBits (fun x => negb (P x)) p bm).
      apply filterBits_neg; isBitMask.
    + simpl.
      rewrite (surjective_pairing (partition P s1)).
      rewrite (surjective_pairing (partition P s2)).
      simpl.
      rewrite IHHD1, IHHD2.
      reflexivity.
Qed.

(** *** Constructiveness of inequality *)

(** I found this easiest to specify once we have [toList]: If two sets are not
equal, we find an element where they differ.*)

Lemma Sem_notSubset_witness:
  forall s1 f1 s2 f2,
    Sem s1 f1 -> Sem s2 f2 ->
    isSubsetOf s1 s2 = false <-> (exists i, f1 i = true /\ f2 i = false).
Proof.
  intros.
  split; intro.
  * assert (~ (Forall (fun i => f2 i = true) (toList s1))).
    { intro.
      rewrite <- not_true_iff_false in H1.
      contradict H1.
      rewrite Forall_forall in H2.
      rewrite isSubsetOf_Sem by eassumption. 
      intros i Hi.
      apply H2.
      rewrite <- toList_In by eassumption.
      assumption.
    }
    rewrite <- Exists_Forall_neg in H2 by (intro i; destruct (f2 i); intuition).
    rewrite Exists_exists in H2.
    destruct H2 as [i [Hin Hf2]].
    rewrite not_true_iff_false in Hf2.
    rewrite <- toList_In in Hin by eassumption.
    exists i; intuition.
  * apply  not_true_iff_false.
    intro.
    rewrite isSubsetOf_Sem in H2 by eassumption.
    destruct H1 as [i [Hin Hf2]].
    specialize (H2 i).
    intuition congruence.
Qed.

Lemma Sem_differ_witness:
  forall s1 f1 s2 f2,
    Sem s1 f1 -> Sem s2 f2 ->
    s1 <> s2 <-> (exists i, f1 i <> f2 i).
Proof.
  intros.
  transitivity (isSubsetOf s1 s2 = false \/ isSubsetOf s2 s1 = false).
  * destruct (isSubsetOf s1 s2) eqn:?, (isSubsetOf s2 s1) eqn:?; intuition try congruence.
    + exfalso. apply H1.
      eapply isSubsetOf_antisym; eassumption.
    + subst. erewrite isSubsetOf_refl in Heqb by eassumption. congruence.
    + subst. erewrite isSubsetOf_refl in Heqb by eassumption. congruence.
  * do 2 rewrite Sem_notSubset_witness by eassumption.
    intuition.
    + destruct H2 as [i?]. exists i. intuition congruence.
    + destruct H2 as [i?]. exists i. intuition congruence.    
    + destruct H1 as [i?].
      destruct (f1 i) eqn:?, (f2 i) eqn:?; try congruence.
      - left. exists i. intuition congruence.
      - right. exists i. intuition congruence.
Qed.


(** *** Specifying [isProperSubsetOf] *)

(** [subsetCmp] is a strange beast, as it returns an [ordering], but does not totally
order the sets. We first relate it to [equal] and [isSubsetOf], and then stich the specification
for [isProperSubsetOf] together using that. We use [difference] in the stiching,
hence the position of this section. *)

Program Fixpoint subsetCmp_equal
  s1 r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  subsetCmp s1 s2 = Eq <-> equal s1 s2 = true := _.
Next Obligation.
  revert subsetCmp_equal H H0.
  intros IH HD1 HD2.
  destruct HD1, HD2.
  * (* Both are tips *)
    simpl; subst. unfoldMethods.
    rewrite if_negb.
    destruct (Z.eqb_spec (rPrefix r) (rPrefix r0)).
    - destruct (N.eqb_spec bm bm0); try intuition congruence.
      destruct (N.lxor bm (N.land bm bm0) =? 0)%N;
      intuition; rewrite ?andb_false_r in *; try congruence.
    - destruct (N.eqb_spec bm bm0); intuition; rewrite ?andb_true_r, ?andb_false_r in *; try congruence.
  * (* Tip left, Bin right *)
    simpl; subst.
    repeat (match goal with [ |- (match ?scrut with _ => _ end) = Eq <-> _ ] => destruct scrut end;
            try intuition congruence).
  * (* Bin right, Tip left *)
    simpl; subst.
    intuition congruence.
  * (* Bin both sides *)
    simpl; subst; unfold shorter, natFromInt; unfoldMethods.
    repeat rewrite andb_true_iff.
    repeat rewrite !N.eqb_eq.
    repeat rewrite !Z.eqb_eq.
    unfold op_zg__, Ord_Char___, op_zg____.
    destruct (N.ltb_spec (Z.to_N (rMask r4)) (Z.to_N (rMask r)));
      only 2: destruct (N.ltb_spec (Z.to_N (rMask r)) (Z.to_N (rMask r4))).
    - (* left is bigger than right *)
      rewrite <- Z2N.inj_lt in H2 by nonneg.
      intuition try (congruence||omega).
    - (* right is bigger than left *)
      rewrite <- Z2N.inj_lt in H3 by nonneg.
      repeat (match goal with [ |- (match ?scrut with _ => _ end) = Eq <-> _ ] => destruct scrut end);
      intuition try (congruence||omega).
    - (* same sized bins *)
      rewrite <- Z2N.inj_le in H2 by nonneg.
      rewrite <- Z2N.inj_le in H3 by nonneg.
      unfoldMethods.
      rewrite <- IH by ((simpl; omega) || eassumption).
      rewrite <- IH by ((simpl; omega) || eassumption).
      destruct (Z.eqb_spec (rPrefix r) (rPrefix r4));
      repeat (match goal with [ |- (match ?scrut with _ => _ end) = Eq <-> _ ] => destruct scrut eqn:? end);
        intuition try (congruence || omega).
Qed.

Program Fixpoint subsetCmp_isSubsetOf
  s1 r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  negb (eq_comparison (subsetCmp s1 s2) Gt) = isSubsetOf s1 s2 := _.
Next Obligation.
  revert subsetCmp_isSubsetOf H H0.
  intros IH HD1 HD2.
  destruct HD1, HD2.
  * (* Both are tips *)
    simpl; subst. unfoldMethods.
    rewrite if_negb.
    destruct (Z.eqb_spec (rPrefix r) (rPrefix r0)).
    - destruct (N.eqb_spec bm bm0); try intuition congruence.
      + subst. rewrite N.land_diag, N.lxor_nilpotent, N.eqb_refl. intuition congruence.
      + destruct (N.lxor bm (N.land bm bm0) =? 0)%N;
        intuition; rewrite ?andb_false_r in *; try congruence.
    - destruct (N.lxor bm (N.land bm bm0) =? 0)%N;
      intuition; rewrite ?andb_false_r in *; try congruence.
  * (* Tip left, Bin right *)
    simpl; subst.
    do 2 erewrite <- IH by (first [ simpl; omega
                                  | apply DescTip; try eassumption; reflexivity
                                  | eassumption ]).
    repeat (match goal with [ |- context [match ?scrut with _ => _ end] ] => destruct scrut end;
            try intuition congruence).
  * (* Bin right, Tip left *)
    simpl; subst.
    intuition congruence.
  * (* Bin both sides *)
    simpl; subst; unfold shorter, natFromInt; unfoldMethods.
    repeat rewrite andb_true_iff.
    repeat rewrite !N.eqb_eq.
    repeat rewrite !Z.eqb_eq.
    destruct (N.ltb_spec (Z.to_N (rMask r4)) (Z.to_N (rMask r)));
      only 2: destruct (N.ltb_spec (Z.to_N (rMask r)) (Z.to_N (rMask r4))).
    - (* left is bigger than right *)
      reflexivity.
    - (* right is bigger than left *)
      unfold match_, nomatch. unfoldMethods.
      rewrite if_negb.
      do 2 erewrite <- IH by (first [ simpl; omega
                                    | eapply DescBin; try beassumption; reflexivity
                                    | eassumption ]).
      destruct (mask _ _ =? _), (zero _ _);
      repeat (match goal with [ |- context [match ?scrut with _ => _ end] ] => destruct scrut eqn:? end); intuition.
    - (* same sized bins *)
      unfoldMethods.
      do 2 erewrite <- IH by (first [ simpl; omega
                                    | eapply DescBin; try beassumption; reflexivity
                                    | eassumption ]).
      destruct (Z.eqb_spec (rPrefix r) (rPrefix r4));
        repeat (match goal with [ |- context [match ?scrut with _ => _ end] ] => destruct scrut eqn:? end); intuition.
Qed.

Lemma isProperSubsetOf_Sem:
  forall s1 f1 s2 f2,
  Sem s1 f1 -> Sem s2 f2 ->
  isProperSubsetOf s1 s2 = true <-> ((forall i, f1 i = true -> f2 i = true) /\ (exists i, f1 i <> f2 i)).
Proof.
  intros ???? HSem1 HSem2.
  rewrite <- Sem_differ_witness by eassumption.
  rewrite <- isSubsetOf_Sem by eassumption.
  destruct HSem1, HSem2.
  * replace (isProperSubsetOf _ _) with false by reflexivity.
    replace (isSubsetOf _ _) with true by reflexivity.
    intuition try congruence.
  * replace (isProperSubsetOf Nil s) with true by (destruct HD; reflexivity).
    replace (isSubsetOf Nil s) with true by (destruct s; reflexivity).
    intuition try congruence.
    subst; inversion HD.
  * replace (isProperSubsetOf s Nil) with false by (destruct s; reflexivity).
    replace (isSubsetOf s Nil) with false by (destruct HD; reflexivity).
    intuition try congruence.
  * pose proof (subsetCmp_isSubsetOf _ _ _ _ _ _ HD HD0).
    rewrite eq_iff_eq_true in H.
    pose proof (subsetCmp_equal _ _ _ _ _ _ HD HD0).
    rewrite equal_spec in H0.
    unfold isProperSubsetOf.
    destruct (subsetCmp s s0) eqn:Hssc; simpl in *;
    intuition try congruence.
Qed.


(** *** Correctness of [valid] *)

(** The [valid] function is used in the test suite to detect whether
   functions return valid trees. It should be equivalent to our [WF].
   
   For now it is not complete (see https://github.com/haskell/containers/issues/522)
   and even with that fixed we might have a problem due to too wide types.
*)

Require Import IntSetValidity.

Definition noNilInSet : IntSet -> bool :=
    (fix noNilInSet (t' : IntSet) : bool :=
        match t' with
        | Bin _ _ l' r' => noNilInSet l' && noNilInSet r'
        | Tip _ _ => true
        | Nil => false
        end).

Lemma valid_noNilInSet: forall s r f, Desc s r f -> noNilInSet s = true.
Proof.
  intros.
  induction H.
  * reflexivity.
  * simpl. rewrite IHDesc1, IHDesc2. reflexivity.
Qed.

Lemma valid_nilNeverChildOfBin: forall s, WF s -> nilNeverChildOfBin s = true.
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * reflexivity.
  * pose proof (valid_noNilInSet _ _ _ HD).
    destruct HD; apply H.
Qed.

Lemma valid_maskPowerOfTwo: forall s, WF s -> maskPowerOfTwo s = true.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * reflexivity.
  * induction HD.
    - reflexivity.
    - simpl. unfold bitcount. unfoldMethods.
      rewrite IHHD1, IHHD2.
      subst. simpl.
      rewrite andb_true_r.
      rewrite Z.eqb_eq.
      destruct r as [p b].
      unfold rMask, rBits, snd in *.
      unfold id.
      rewrite Z2N.inj_pow; try nonneg; try Nomega.
      simpl Z.to_N.
      rewrite Z2N.inj_pred.
      rewrite N2Z.id.
      rewrite N_popcount_pow2.
      reflexivity.
Qed.

Lemma Foldable_all_forallb:
  forall {a} p (l : list a), Foldable.all p l = forallb p l.
Proof.
  intros.
  induction l.
  * reflexivity.
  * simpl. rewrite <- IHl.
    compute.
    match goal with [ |- _ = match ?x with _ => _ end ] => destruct x end.
    match goal with [ |- _ = match ?x with _ => _ end ] => destruct x end.
    reflexivity.
    match goal with [ |- match ?x with _ => _ end = _ ] => destruct x eqn:? end.
    match goal with [ H : match ?x with _ => _ end = _ |- _] => destruct x eqn:? end.
    congruence.
Qed.

Lemma valid_commonPrefix: forall s, WF s -> commonPrefix s = true.
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * reflexivity.
  * destruct HD.
    - reflexivity.
    - unfold commonPrefix.
      unfoldMethods.
      set (s := Bin p msk s1 s2).
      assert (Desc s r f) by (eapply DescBin; eassumption).
      
      replace elems with toList by reflexivity.
      rewrite Foldable_all_forallb.
      rewrite forallb_forall.
      intros i Hi.
      rewrite <- toList_In in Hi by (eapply DescSem; eassumption).
      eapply Desc_inside in Hi; try eassumption.
      rewrite Z.eqb_eq.
      symmetry.
      apply Z.lxor_eq_0_iff.
      subst p.
      clear - Hi.
      destruct r as [p b].
      unfold inRange, rPrefix in *.
      rewrite Z.eqb_eq in Hi.
      subst.
      apply Z.bits_inj_iff'.
      intros j Hi.
      rewrite Z.land_spec.
      rewrite !Z.shiftl_spec by assumption.
      destruct (Z.ltb_spec j (Z.of_N b)).
      + rewrite Z.testbit_neg_r by Nomega.
        rewrite andb_false_l.
        reflexivity.
      + rewrite !Z.shiftr_spec by Nomega.
        replace (j - Z.of_N b + Z.of_N b) with j by Nomega.
        rewrite andb_diag.
        reflexivity.
Qed.

Lemma valid_maskRespected: forall s, WF s -> maskRespected s = true.
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * reflexivity.
  * destruct HD.
    - reflexivity.
    - unfold maskRespected.
      unfoldMethods.
      replace elems with toList by reflexivity.
      rewrite !Foldable_all_forallb.
      rewrite andb_true_iff; split.
      + rewrite forallb_forall.
        intros i Hi.
        rewrite <- toList_In in Hi by (eapply DescSem; eassumption).
        eapply Desc_inside in Hi; try eassumption.
        subst msk.
        rewrite zero_spec by assumption.
        rewrite negb_true_iff.
        apply testbit_halfRange_true_false; try assumption.
        eapply inRange_isSubrange_true; [|eassumption]; isSubrange_true.
        inRange_false; fail.
      + rewrite forallb_forall.
        intros i Hi.
        rewrite <- toList_In in Hi by (eapply DescSem; eassumption).
        eapply Desc_inside in Hi; try eassumption.
        subst msk.
        rewrite zero_spec by assumption.
        rewrite negb_involutive.
        apply testbit_halfRange_false_false; try assumption.
        eapply inRange_isSubrange_true; [|eassumption]; isSubrange_true.
        inRange_false; fail.
Qed.

Lemma valid_tipsValid: forall s, WF s -> tipsValid s = true.
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * reflexivity.
  * induction HD.
    + simpl.
      unfold validTipPrefix.
      unfoldMethods.
      destruct r as [p' b]. unfold rPrefix, rBits, snd in *. subst.
      rewrite Z.eqb_eq.
      apply Z.bits_inj_iff'. intros i?.
      rewrite Z.bits_0.
      rewrite Z.land_spec.
      rewrite Z.shiftl_spec by assumption.
      destruct (Z.ltb_spec i (Z.of_N (N.log2 WIDTH))).
      - rewrite Z.testbit_neg_r with (a := p') by omega.
        apply andb_false_r.
      - rewrite Z.bits_above_log2.
        apply andb_false_l.
        omega.
        unfold WIDTH in *.
        simpl Z.log2 in *.
        simpl Z.of_N in H1.
        omega.
    + simpl.
      rewrite IHHD1, IHHD2.
      reflexivity.
Qed.

Lemma valid_correct: forall s, WF s -> valid s = true.
Proof.
  intros.
  unfold valid.
  rewrite valid_nilNeverChildOfBin by assumption.
  rewrite valid_maskPowerOfTwo by assumption.
  rewrite valid_commonPrefix by assumption.
  rewrite valid_maskRespected by assumption.
  rewrite valid_tipsValid by assumption.
  reflexivity.
Qed.


(** ** Instantiating the [FSetInterface] *)

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

  Definition empty : t.
    eexists. eexists. apply SemNil. intro. reflexivity.
  Defined.
  
  Definition is_empty : t -> bool := fun s' => 
    s <-- s' ;; null s.

  Lemma empty_1 : Empty empty.
  Proof. unfold Empty; intros a H. inversion H. Qed.

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    intros. unfold Empty, In, In_set, is_empty in *. destruct s. simpl.
    destruct w as [s HSem].
    induction HSem.
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

  Definition singleton : elt -> t.
    refine (fun e => pack (singleton (Z.of_N e)) _).
    apply singleton_WF; nonneg.
  Defined.

  Definition add (e: elt) (s': t) : t.
    refine (s <-- s' ;;
            pack (insert (Z.of_N e) s) _).
    apply insert_WF; nonneg.
  Defined.

  Definition remove  (e: elt) (s': t) : t.
    refine (s <-- s' ;;
            pack (delete (Z.of_N e) s) _).
    apply delete_WF; nonneg.
  Defined.

  Definition union (s1' s2' : t) : t.
    refine (s1 <-- s1' ;;
            s2 <-- s2' ;;
            pack (union s1 s2) _).
    apply union_WF; assumption.
  Defined.

  Definition inter (s1' s2' : t) : t.
    refine (s1 <-- s1' ;;
            s2 <-- s2' ;;
            pack (intersection s1 s2) _).
    apply intersection_WF; assumption.
  Defined.

  Definition diff (s1' s2' : t) : t.
    refine (s1 <-- s1' ;;
          s2 <-- s2' ;;
          pack (difference s1 s2) _).
  apply difference_WF; assumption.
  Defined.


  Definition equal : t -> t -> bool :=
    fun ws ws' => s <-- ws ;;
               s' <-- ws' ;;
               s == s'.
  
  Definition subset : t -> t -> bool :=
    fun ws ws' => s <-- ws ;;
               s' <-- ws' ;;
               isSubsetOf s s'.

  Definition eq : t -> t -> Prop := Equal.

  Definition eq_dec : forall s s' : t, {eq s s'} + {~ eq s s'}.
  Proof.
    intros.
    destruct s as [s1 Hwf1].
    destruct s' as [s2 Hwf2].   
    destruct (Internal.equal s1 s2) eqn:?.
    * left.
      rewrite equal_spec in Heqb.
      subst.
      intro. unfold In. reflexivity.
    * right.
      apply not_true_iff_false in Heqb.
      contradict Heqb.
      rewrite equal_spec.
      destruct Hwf1 as [f1 HSem1].
      destruct Hwf2 as [f2 HSem2].
      eapply Sem_unique; try eassumption.
      intro i.
      apply eq_iff_eq_true.
      destruct (Z.leb_spec 0 i).
      + specialize (Heqb (Z.to_N i)).
        unfold eq, In, In_set in Heqb.
        erewrite (member_Sem HSem1) in Heqb.
        erewrite (member_Sem HSem2) in Heqb.
        rewrite Z2N.id in Heqb by assumption.
        assumption.
      + rewrite (Sem_neg_false HSem1) by assumption.
        rewrite (Sem_neg_false HSem2) by assumption.
        intuition.
  Defined.

  Lemma eq_refl : forall s : t, eq s s.
  Proof. destruct s. unfold eq. unfold Equal. intro. reflexivity. Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. destruct s; destruct s'; 
    unfold eq, Equal in *. intros. rewrite H. intuition. Qed.

  Lemma eq_trans :
    forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
    destruct s; destruct s'; destruct s''; simpl.
    unfold eq, Equal. intros ???. rewrite H, H0. reflexivity.
  Qed.

  Definition fold (A : Type) (f : elt -> A -> A) (ws : t) (x : A) : A :=
    s <-- ws;;
    foldl (fun x a => f (Z.to_N a) x) x s.

  Definition filter : (elt -> bool) -> t -> t.
    refine (fun p ws =>
       s <-- ws;;
       pack (filter (fun x => p (Z.to_N x)) s) _).
    apply filter_WF; assumption.
  Defined.
  
  
  Program Definition partition : (elt -> bool) -> t -> t * t :=
     (fun p ws => Data.IntSet.Internal.partition (fun x => p (Z.to_N x)) ws).
  Next Obligation.
    rewrite partition_snd.
    apply filter_WF.
    destruct ws; auto.
    destruct ws; auto.
  Qed.
  Next Obligation.
    rewrite partition_fst.
    apply filter_WF.
    destruct ws; auto.
  Qed.

  Definition cardinal : t -> nat :=
    fun ws => s <-- ws;;
              Z.to_nat (size s).

  Definition elements (ws : t) : list elt :=
    s <-- ws;;
    List.map Z.to_N (toList s).


  Lemma In_1 :
    forall (s : t) (x y : elt), N.eq x y -> In x s -> In y s.
  Proof. intros. destruct H. assumption. Qed.
  
  Definition mem : elt -> t -> bool := fun e s' =>
   s <-- s' ;; member (Z.of_N e) s.


  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
  
  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true.
  Proof.
    intros.
    destruct s as [s1 [f1 HSem1]].
    destruct s' as [s2 [f2 HSem2]].
    apply equal_spec.
    eapply Sem_unique; try eassumption.
    intro i.
    apply eq_iff_eq_true.
    destruct (Z.leb_spec 0 i).
    + specialize (H (Z.to_N i)).
      unfold eq, In, In_set in H.
      erewrite (member_Sem HSem1) in H.
      erewrite (member_Sem HSem2) in H.
      rewrite Z2N.id in H by assumption.
      assumption.
    + rewrite (Sem_neg_false HSem1) by assumption.
      rewrite (Sem_neg_false HSem2) by assumption.
      intuition.
  Qed.

  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
  Proof.
    intros.
    destruct s as [s1 [f1 HSem1]].
    destruct s' as [s2 [f2 HSem2]].
    apply equal_spec in H.
    subst.
    intro i; intuition.
  Qed.

  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true.
  Proof.
    intros.
    destruct s as [s1 [f1 HSem1]].
    destruct s' as [s2 [f2 HSem2]].
    unfold Subset, subset, In, In_set in *.
    rewrite isSubsetOf_Sem by eassumption.
    intro i. specialize (H (Z.to_N i)).
    destruct (Z.ltb_spec i 0).
    * intros.
      erewrite Sem_neg_false in H1 by eassumption.
      congruence.
    * rewrite Z2N.id in H by nonneg.
      do 2 erewrite member_Sem in H by eassumption.
      assumption.
  Qed.

  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
  Proof.
    intros.
    destruct s as [s1 [f1 HSem1]].
    destruct s' as [s2 [f2 HSem2]].
    unfold Subset, subset, In, In_set in *.
    rewrite isSubsetOf_Sem in H by eassumption.
    intro i. specialize (H (Z.of_N i)).
    do 2 erewrite member_Sem by eassumption.
    assumption.
  Qed.

  Lemma add_1 :
    forall (s : t) (x y : elt), N.eq x y -> In y (add x s).
  Proof.
    intros.
    inversion_clear H; subst.
    unfold In, add, pack, In_set; intros; destruct s as [s].
    destruct w as [f HSem].
    erewrite member_Sem.
      Focus 2.
      eapply insert_Sem; try nonneg; try eassumption.
      intro. reflexivity.
    simpl. rewrite Z.eqb_refl. reflexivity.
  Qed.

  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s).
  Proof.
    intros.
    unfold In, add, pack, In_set in *; intros; destruct s as [s].
    destruct w as [f HSem].
    erewrite member_Sem.
      Focus 2.
      eapply insert_Sem; try nonneg; try eassumption.
      intro. reflexivity.
      simpl. rewrite orb_true_iff. right.
    erewrite <- member_Sem. eassumption. eassumption.
  Qed.

  Lemma add_3 :
    forall (s : t) (x y : elt), ~ N.eq x y -> In y (add x s) -> In y s.
  Proof.
    intros.
    unfold In, add, pack, In_set in *; intros; destruct s as [s].
    destruct w as [f HSem].
    erewrite member_Sem in H0.
      Focus 2.
      eapply insert_Sem; try nonneg; try eassumption.
      intro. reflexivity. simpl in *.
    rewrite -> orb_true_iff in H0.
    rewrite -> Z.eqb_eq in H0.
    rewrite -> N2Z.inj_iff in H0.
    destruct H0. congruence.

    erewrite member_Sem.
      Focus 2.
      eassumption.
    assumption.
  Qed.

  Lemma remove_1 :
    forall (s : t) (x y : elt), N.eq x y -> ~ In y (remove x s).
  Proof.
    intros.
    unfold In, remove, pack, In_set in *; intros; destruct s as [s].
    destruct H.
    destruct w as [f HSem].
    erewrite member_Sem.
      Focus 2.
      eapply delete_Sem; try nonneg.
      eassumption.
      intro i. reflexivity.
    simpl.
    rewrite Z.eqb_refl; simpl.
    congruence.
  Qed.

  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ N.eq x y -> In y s -> In y (remove x s).
  Proof.
    intros.
    unfold In, remove, pack, In_set in *; intros; destruct s as [s].
    apply not_false_iff_true.
    contradict H.
    destruct w as [f HSem].
    erewrite member_Sem in H.
        Focus 2.
        eapply delete_Sem; try nonneg.
        eassumption.
      intro i. reflexivity.
    erewrite member_Sem in H0 by eassumption.
    simpl in *.
    destruct (Z.eqb_spec (Z.of_N y) (Z.of_N x)); simpl in *; try congruence.
    apply N2Z.inj in e. subst. reflexivity.
  Qed.

  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s.
  Proof.
    intros.
    unfold In, remove, pack, In_set in *; intros; destruct s as [s].
    destruct w as [f HSem].
    erewrite member_Sem in H.
        Focus 2.
        eapply delete_Sem; try nonneg.
        eassumption.
      intro i. reflexivity.
    erewrite member_Sem by eassumption.
    simpl in *.
    rewrite andb_true_iff in H. intuition.
  Qed.

  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> N.eq x y.
  Proof.
    intros.
    unfold In, In_set, singleton, pack in *.
    erewrite member_Sem in H.
    Focus 2. apply singleton_Sem; nonneg.
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
    erewrite member_Sem.
    Focus 2. apply singleton_Sem; nonneg.
    simpl.
    rewrite -> Z.eqb_eq.
    congruence.
  Qed.

  Lemma union_1 :
    forall (s s' : t) (x : elt), In x (union s s') -> In x s \/ In x s'.
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, union, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem by eassumption.
    erewrite member_Sem in H
     by (eapply union_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite orb_true_iff in H.
    assumption.
  Qed.

  Lemma union_2 :
    forall (s s' : t) (x : elt), In x s -> In x (union s s').
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, union, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem in H by eassumption.
    erewrite member_Sem
     by (eapply union_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite orb_true_iff.
    intuition.
  Qed.

  Lemma union_3 :
    forall (s s' : t) (x : elt), In x s' -> In x (union s s').
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, union, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem in H by eassumption.
    erewrite member_Sem
     by (eapply union_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite orb_true_iff.
    intuition.
  Qed.

  Lemma inter_1 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s.
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, inter, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem by eassumption.
    erewrite member_Sem in H
     by (eapply intersection_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff in H.
    intuition.
  Qed.

  Lemma inter_2 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s'.
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, inter, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem by eassumption.
    erewrite member_Sem in H
     by (eapply intersection_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff in H.
    intuition.
  Qed.
  
  Lemma inter_3 :
    forall (s s' : t) (x : elt), In x s -> In x s' -> In x (inter s s').
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, inter, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem in H by eassumption.
    erewrite !member_Sem in H0 by eassumption.
    erewrite member_Sem
     by (eapply intersection_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff.
    intuition.
  Qed.

  Lemma diff_1 :
    forall (s s' : t) (x : elt), In x (diff s s') -> In x s.
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, diff, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem by eassumption.
    erewrite member_Sem in H
     by (eapply difference_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff in H.
    intuition.
  Qed.

  Lemma diff_2 :
    forall (s s' : t) (x : elt), In x (diff s s') -> ~ In x s'.
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, diff, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem by eassumption.
    erewrite member_Sem in H
     by (eapply difference_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff in H.
    rewrite negb_true_iff in H.
    intuition congruence.
  Qed.

  Lemma diff_3 :
    forall (s s' : t) (x : elt), In x s -> ~ In x s' -> In x (diff s s').
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, diff, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem in H by eassumption.
    erewrite !member_Sem in H0 by eassumption.
    erewrite member_Sem
     by (eapply difference_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff.
    intuition.
  Qed.

  Lemma fold_left_map:
    forall {a b c} f (g : a -> b) (x : c) xs,
    fold_left (fun a e => f a e) (List.map g xs) x
      = fold_left (fun a e => f a (g e)) xs x.
  Proof.
    intros.
    revert x.
    induction xs; intros.
    * reflexivity.
    * simpl. rewrite IHxs. reflexivity.
  Qed.

  Lemma fold_1 :
    forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
    fold A f s i =
    fold_left (fun (a : A) (e : elt) => f e a) (elements s) i.
  Proof.
    intros.
    destruct s as [s Hwf].
    simpl.
    rewrite fold_left_map.
    apply foldl_spec; assumption.
  Qed.

  Lemma cardinal_1 : forall s : t, cardinal s = length (elements s).
  Proof.
    intros.
    destruct s as [s Hwf].
    simpl.
    rewrite map_length.
    rewrite size_spec by assumption.
    apply Nat2Z.id.
  Qed.

  Lemma filter_1 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool N.eq f -> In x (filter f s) -> In x s.
  Proof.
    intros s x P Heq Hin.
    destruct s as [s [f HSem]].
    unfold filter, In, In_set in *.
    simpl in *.
    erewrite member_Sem by eassumption.
    erewrite member_Sem in Hin
      by (eapply filter_Sem; try eassumption; intro i; reflexivity).
    simpl in *.
    rewrite N2Z.id in *.
    rewrite andb_true_iff in Hin.
    intuition.
  Qed.

  Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool N.eq f -> In x (filter f s) -> f x = true.
  Proof.
    intros s x P Heq Hin.
    destruct s as [s [f HSem]].
    unfold filter, In, In_set in *.
    simpl in *.
    erewrite member_Sem in Hin
      by (eapply filter_Sem; try eassumption; intro i; reflexivity).
    simpl in *.
    rewrite N2Z.id in *.
    rewrite andb_true_iff in Hin.
    intuition.
  Qed.

  Lemma filter_3 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool N.eq f -> In x s -> f x = true -> In x (filter f s).
  Proof.
    intros s x P Heq Hin HP.
    destruct s as [s [f HSem]].
    unfold filter, In, In_set in *.
    simpl in *.
    erewrite member_Sem in Hin by eassumption.
    erewrite member_Sem
      by (eapply filter_Sem; try eassumption; intro i; reflexivity).
    simpl in *.
    rewrite N2Z.id in *.
    rewrite andb_true_iff.
    intuition.
  Qed.

  Lemma partition_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f -> Equal (fst (partition f s)) (filter f s).
  Proof.
    intros.
    destruct s.
    unfold Equal, partition; simpl.
    rewrite partition_fst.
    reflexivity.
  Qed.

  Lemma partition_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s).
  Proof.
    intros.
    destruct s.
    unfold Equal, partition; simpl.
    rewrite partition_snd by assumption.
    reflexivity.
  Qed.

  Lemma elements_1 :
    forall (s : t) (x : elt), In x s -> InA N.eq x (elements s).
  Proof.
    intros.
    destruct s as [s Hwf].
    destruct Hwf as [f HSem].
    simpl in *.
    unfold In_set in *.
    erewrite member_Sem in H by eassumption.
    apply OrdFacts.ListIn_In.
    replace x with (Z.to_N (Z.of_N x)) by (rewrite N2Z.id; reflexivity).
    apply in_map.
    rewrite <- toList_In by eassumption.
    assumption.
  Qed.

  Lemma elements_2 :
    forall (s : t) (x : elt), InA N.eq x (elements s) -> In x s.
  Proof.
    intros.
    destruct s as [s Hwf].
    destruct Hwf as [f HSem].
    simpl in *.
    unfold In_set in *.
    erewrite member_Sem by eassumption.
    rewrite InA_alt in H.
    destruct H as [_[[]?]].
    rewrite in_map_iff in H.
    destruct H as [?[[]?]].
    rewrite <- toList_In in H by eassumption.
    rewrite Z2N.id by (eapply Sem_nonneg; eassumption).
    assumption.
  Qed.

  Lemma elements_3w : forall s : t, NoDupA N.eq (elements s).
  Proof.
    intros.
    destruct s as [s Hwf].
    simpl.
    apply OrdFacts.Sort_NoDup.
    apply StronglySorted_Sorted.
    eapply StronglySorted_map.
    * apply to_List_sorted; assumption.
    * intros.
      assert (0 <= x) by (eapply toList_In_nonneg; eassumption).
      assert (0 <= y) by (eapply toList_In_nonneg; eassumption).
      apply Z2N.inj_lt; assumption.
  Qed.

(**
  These portions of the [FMapInterface] have no counterpart in the [IntSet] interface.
  We implement them generically.
  *)

  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Definition for_all : (elt -> bool) -> t -> bool :=
    fun P s => forallb P (elements s).
  Definition exists_ : (elt -> bool) -> t -> bool :=
    fun P s => existsb P (elements s).

  Lemma for_all_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    For_all (fun x : elt => f x = true) s -> for_all f s = true.
  Proof.
    intros.
    unfold For_all, for_all in *.
    rewrite forallb_forall.
    intros. apply H0.
    apply elements_2.
    apply OrdFacts.ListIn_In.
    assumption.
  Qed.

  Lemma for_all_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    for_all f s = true -> For_all (fun x : elt => f x = true) s.
  Proof.
    intros.
    unfold For_all, for_all in *.
    rewrite forallb_forall in H0.
    intros. apply H0.
    apply elements_1 in H1.
    rewrite InA_alt in H1.
    destruct H1 as [?[[]?]].
    assumption.
  Qed.

  Lemma exists_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    Exists (fun x : elt => f x = true) s -> exists_ f s = true.
  Proof.
    intros.
    unfold Exists, exists_ in *.
    rewrite existsb_exists.
    destruct H0 as [x[??]].
    exists x.
    split; auto.
    apply elements_1 in H0.
    rewrite InA_alt in H0.
    destruct H0 as [?[[]?]].
    assumption.
  Qed.

  Lemma exists_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    exists_ f s = true -> Exists (fun x : elt => f x = true) s.
  Proof.
    intros.
    unfold Exists, exists_ in *.
    rewrite existsb_exists in H0.
    destruct H0 as [x[??]].
    exists x.
    split; auto.
    apply elements_2.
    apply OrdFacts.ListIn_In.
    assumption.
  Qed.

  (** One could implement [choose] with [minView]. We currenlty do not
  translate [minView], because of a call to [error] in a branch that is inaccessible
  in well-formed trees. Stretch goal: translate that and use it here.
  *)

  Definition choose : t -> option elt :=
    fun s => match elements s with
                | nil => None
                | x :: _ => Some x
              end.


  Lemma choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s.
  Proof.
    intros.
    unfold choose in *.
    destruct (elements s) eqn:?; try congruence.
    inversion H; subst.
    apply elements_2.
    rewrite Heql.
    left.
    reflexivity.
  Qed.

  Lemma choose_2 : forall s : t, choose s = None -> Empty s.
  Proof.
    intros.
    unfold choose in *.
    destruct (elements s) eqn:?; try congruence.
    intros x ?.
    apply elements_1 in H0.
    rewrite Heql in H0.
    inversion H0.
  Qed.

End Foo.
