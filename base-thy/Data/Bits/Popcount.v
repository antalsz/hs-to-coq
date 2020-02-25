(** * Counting ones in [positive] and [N] *)

Require Import Coq.PArith.PArith.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Omega.

Require Import Data.Bits.

(** Copied from [Coq.ZArith.Zlogarithm]. *)
Fixpoint Is_power (p:positive) : Prop :=
  match p with
    | xH => True
    | xO q => Is_power q
    | xI q => False
  end.

(** Copied from [Coq.ZArith.Zlogarithm]. *)
Lemma Is_power_correct :
  forall p:positive, Is_power p <-> (exists y : nat, p = shift_nat y 1).
Proof.
  split;
    [ elim p;
      [ simpl in |- *; tauto | simpl in |- *; intros; generalize (H H0); intro H1; elim H1; intros y0 Hy0; exists (S y0); rewrite Hy0; reflexivity | intro; exists 0%nat; reflexivity ]
    | intros; elim H; intros; rewrite H0; elim x; intros; simpl in |- *; trivial ].
Qed.

Lemma Pos_popcount_pow2:
  forall n, Pos_popcount (Pos.pow 2 n) = 1%positive.
Proof.
  apply Pos.peano_ind; intros.
  * reflexivity.
  * rewrite Pos.pow_succ_r.
    apply H.
Qed.

Lemma Pos_popcount_1_Is_power (p : positive) :
  Pos_popcount p = 1%positive -> Is_power p.
Proof.
  induction p as [p IH | p IH |]; simpl; auto.
  specialize (Pos.succ_not_1 (Pos_popcount p)); contradiction.
Qed.

(** And now for [N] *)

Lemma N_popcount_double:
  forall n, N_popcount (N.double n) = N_popcount n.
Proof.
  intros.
  destruct n.
  * reflexivity.
  * reflexivity.
Qed.

Lemma N_popcount_Ndouble:
  forall n, N_popcount (Pos.Ndouble n) = N_popcount n.
Proof.
  intros.
  destruct n.
  * reflexivity.
  * reflexivity.
Qed.

Lemma N_popcount_Nsucc_double:
  forall n, N_popcount (Pos.Nsucc_double n) = N.succ (N_popcount n).
Proof.
  intros.
  destruct n.
  * reflexivity.
  * reflexivity.
Qed.


Lemma N_popcount_pow2:
  forall n, N_popcount (N.pow 2 n) = 1%N.
Proof.
  apply N.peano_ind; intros.
  * reflexivity.
  * rewrite N.pow_succ_r by apply N.le_0_l.
    rewrite <- N.double_spec.
    rewrite N_popcount_double.
    assumption.
Qed.

Lemma N_popcount_1_pow2 (n : N) :
  N_popcount n = 1%N -> exists i : N, (2^i = n)%N.
Proof.
  destruct n as [|p]; simpl; [discriminate | intros def_Npcp].
  assert (Pos_popcount p = 1%positive) as def_pcp by (inversion def_Npcp; reflexivity).
  apply Pos_popcount_1_Is_power, Is_power_correct in def_pcp.
  destruct def_pcp as [y def_p]; rewrite def_p.
  specialize (shift_nat_correct y 1); rewrite Z.mul_1_r, Zpower_nat_Z; intros def_power.
  exists (N.of_nat y). 
  rewrite <-N2Z.inj_iff, N2Z.inj_pow; simpl.
  rewrite def_power, nat_N_Z; reflexivity.
Qed.

Lemma N_double_succ:
  forall n,
  N.double (N.succ n) = N.succ (N.succ (N.double n)).
Proof.
  destruct n.
  * reflexivity.
  * reflexivity.
Qed.

Lemma Pop_popcount_diff:
  forall p1 p2,
  (N.pos (Pos_popcount p1) + N.pos (Pos_popcount p2) =
  N_popcount (Pos.ldiff p1 p2) + N_popcount (Pos.ldiff p2 p1) + N.double (N_popcount (Pos.land p2 p1)))%N.
Proof.
  induction p1; intros; destruct p2.
  all: try (
    simpl;
    try specialize (IHp1 p2);
    rewrite ?N_popcount_Ndouble, ?N_popcount_Nsucc_double,
            ?N_double_succ;
    zify; omega
  ).
  * simpl.
    destruct (Pos_popcount p2); simpl in *; try rewrite <- Pplus_one_succ_r; try reflexivity.
Qed.


Lemma N_popcount_diff:
  forall n1 n2,
  (N_popcount n1 + N_popcount n2 =
  N_popcount (N.ldiff n1 n2) + N_popcount (N.ldiff n2 n1) + N.double (N_popcount (N.land n2 n1)))%N.
Proof.
  intros. destruct n1, n2; try reflexivity.
  apply Pop_popcount_diff.
Qed.
