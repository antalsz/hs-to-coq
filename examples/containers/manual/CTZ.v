(** * Counting trailing zeroes in [N] *)

(**
The [IntSet] code has two bit-fiddly operations: [lowestBitMask] and [highestBitMask], with
implementations that only work on fixed-width numbers. Since we use arbitrary-width numbers
in our development, we replace them with naive implementations.

[highestBitMask] can nicely be implemented based on [N.log2]; for [lowestBitMask] we need an
equivalent, which is [ctz] (count trailing zeroes).
*)

Require Import Coq.PArith.PArith.
Require Import Coq.NArith.NArith.
Require Import Omega.

(** First for [positive], where the function is nicely total. *)

Fixpoint Pos_ctz (p : positive) : N :=
  match p with
  | 1%positive => 0%N
  | (p~1)%positive => 0%N
  | (p~0)%positive => N.succ (Pos_ctz p)
  end.

Lemma Pos_bits_below_ctz:
  forall p n, (n < Pos_ctz p)%N -> Pos.testbit p n = false.
Proof.
  induction p; intros.
  * simpl in *. destruct n; inversion H.
  * simpl in *.
    destruct n; try reflexivity.
    apply IHp.
    rewrite N.pos_pred_spec.
    apply N.succ_lt_mono.
    rewrite N.succ_pred_pos by reflexivity.
    assumption.
  * simpl in *. destruct n; inversion H.
Qed.

Lemma Pos_bit_ctz:
  forall p, Pos.testbit p (Pos_ctz p) = true.
Proof.
  induction p; intros; try reflexivity.
  simpl.
  destruct (Pos_ctz p) eqn:?.
  * auto.
  * simpl. 
    rewrite Pos.pred_N_succ.
    assumption.
Qed.

Lemma Pos_ctz_bits_unique:
  forall p n,
  Pos.testbit p n = true ->
  (forall m : N, (m < n)%N -> Pos.testbit p m = false) ->
  Pos_ctz p = n.
Proof.
  induction p; intros.
  * destruct (N.eq_0_gt_0_cases n).
    + subst. reflexivity.
    + apply H0 in H1. inversion H1.
  * simpl.
    destruct (N.eq_0_gt_0_cases n).
    + subst. inversion H.
    + rewrite <- (N.lt_succ_pred 0%N n) by assumption.
      f_equal. apply IHp.
      - simpl in H.
        destruct n eqn:?; try congruence.
        rewrite N.pos_pred_spec in H.
        assumption.
      - intros.
        assert (N.succ m < n)%N by (apply N.lt_succ_lt_pred; assumption).
        specialize (H0 _ H3).
        simpl in H0.
        destruct m eqn:?; simpl in H0.
        ** assumption.
        ** rewrite Pos.pred_N_succ in H0.
           assumption.
  * destruct (N.eq_0_gt_0_cases n).
    + subst. reflexivity.
    + apply H0 in H1. inversion H1.
Qed.

Lemma Pos_ctz_pow2:
  forall n, Pos_ctz (Pos.pow 2 n) = N.pos n.
Proof.
  apply Pos.peano_ind; intros.
  * reflexivity.
  * rewrite Pos.pow_succ_r.
    simpl.
    rewrite H.
    reflexivity.
Qed.


(** And now for [N], returning [0] for [0]. *)

Definition N_ctz (a : N) : N :=
  match a with
  | 0%N => 0%N
  | N.pos p => Pos_ctz p
  end.

Lemma N_bits_below_ctz:
  forall a n, (n < N_ctz a)%N -> N.testbit a n = false.
Proof.
  intros.
  destruct a.
  * simpl in *. exfalso. eapply N.nlt_0_r. apply H.
  * apply Pos_bits_below_ctz. 
    apply H.
Qed.

Lemma N_bit_ctz:
  forall a, (0 < a)%N -> N.testbit a (N_ctz a) = true.
Proof.
  intros.
  destruct a.
  * inversion H.
  * apply Pos_bit_ctz. 
Qed.


Lemma N_ctz_bits_unique:
  forall a n,
  (0 < a)%N ->
  N.testbit a n = true ->
  (forall m : N, (m < n)%N -> N.testbit a m = false) ->
  N_ctz a = n.
Proof.
  intros.
  destruct a.
  * inversion H. 
  * apply Pos_ctz_bits_unique; assumption.
Qed.

Lemma N_ctz_pow2:
  forall n, N_ctz (N.pow 2 n) = n.
Proof.
  intros.
  destruct n.
  * reflexivity.
  * simpl. apply Pos_ctz_pow2.
Qed.