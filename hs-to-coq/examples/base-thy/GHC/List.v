Require Import GHC.Num.
Require Import GHC.List.

(* -------------------------------------------------------------------- *)

(* Haskell-Coq equivalence *)

Require Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Lemma hs_coq_lenAcc_add {A} (l : list A) (acc1 acc2 : Z) :
  lenAcc l (acc1 + acc2)%Z = (lenAcc l acc1 + acc2)%Z.
Proof.
  generalize dependent acc1; generalize dependent acc2;
    induction l as [|x l IH]; simpl; auto; intros.
  rewrite <-Z.add_assoc, Z.add_comm, <-Z.add_assoc, Z.add_comm, IH; do 2 f_equal;
    apply Z.add_comm.
Qed.

Lemma hs_coq_lenAcc {A} (l : list A) (acc : Z) :
  lenAcc l acc = (Zlength l + acc)%Z.
Proof.
  generalize dependent acc; induction l as [|x l IH]; simpl; auto; intros.
  rewrite Zlength_cons, Z.add_succ_l, <-IH, hs_coq_lenAcc_add, Z.add_1_r; reflexivity.
Qed.

Theorem hs_coq_list_length {A} (l : list A) :
  length l = Zlength l.
Proof.
  unfold length; rewrite hs_coq_lenAcc, Z.add_0_r; reflexivity.
Qed.

Theorem hs_coq_filter {A} (p : A -> bool) (l : list A) :
  filter p l = Coq.Lists.List.filter p l.
Proof.
  induction l; simpl; auto.
  destruct (p _); f_equal; auto.
Qed.
