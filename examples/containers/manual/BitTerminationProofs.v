(**

This file contains the justification for the bit-wise recursion in [IntSet] and [IntMap].
This needs to be defined before these modules are used, unfortunately.

There is some duplication between the stuff here and the [IntSetTheories], which
of course imports [IntSet].
*)

Require Import Coq.NArith.NArith.
Require Import Coq.Bool.Bool.
Require Import CTZ.
Require Import Omega.


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
  (bm <> 0)%N ->
  N.lxor bm (2^(N_ctz bm))%N = N.clearbit bm (N_ctz bm).
Proof.
  intros.
  apply lxor_pow2_clearbit.
  apply N_bit_ctz.
  zify. omega.
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

Lemma N2nat_inj_lt:
  forall a b : N,
  (N.to_nat a < N.to_nat b) <-> (a < b)%N.
Proof.
  intros.
  zify. omega.
Qed.

(* This lemma is tailored to what we actually have to prove -- up to unfolding. *)
Lemma foldlBits_proof:
  forall a,
  N.eqb a 0 = false ->
  (N.to_nat (N.lxor a (2 ^ CTZ.N_ctz a)) < N.to_nat a).
Proof.
  intros.
  rewrite N.eqb_neq in H.
  apply N2nat_inj_lt.
  rewrite lxor_lowestBitMask by assumption.
  apply clearbit_lt.
  apply CTZ.N_bit_ctz.
  zify; omega.
Qed.

Require Coq.Program.Tactics.

Ltac termination_foldl:=
  Coq.Program.Tactics.program_simpl;
  apply foldlBits_proof;
  assumption.
