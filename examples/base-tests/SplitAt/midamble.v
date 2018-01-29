Require Import Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Lemma length_drop_le:
  forall {a} n (xs : list a),
  length (GHC.List.drop n xs) <= length xs.
Proof.
  intros.
  revert n. induction xs; intros.
  * simpl. destruct (n <=? 0)%Z; auto.
  * simpl.
    destruct (n <=? 0)%Z.
    + reflexivity.
    + specialize (IHxs (n - 1)%Z). 
      omega.
Qed.

Lemma length_drop_lt:
  forall {a} n (xs : list a), (false = ZArith.BinInt.Z.leb n 0) -> xs <> [] ->
  length (GHC.List.drop n xs) < length xs.
Proof.
  intros.
  destruct xs.
  * congruence.
  * simpl.
    rewrite <- H.
    apply le_lt_n_Sm.
    apply length_drop_le.
Qed.

Ltac solve_splitAt := Coq.Program.Tactics.program_simpl; apply length_drop_lt; intuition.
