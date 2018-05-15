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

Theorem hs_coq_reverse : forall A (xs : list A), 
    List.reverse xs = Coq.Lists.List.rev xs.
Proof.
  intros A.
  unfold List.reverse.
  set (rev := fix rev (arg_0__ arg_1__ : list A) {struct arg_0__} : 
   list A :=
     match arg_0__ with
     | nil => arg_1__
     | cons x xs => rev xs (cons x arg_1__)
     end).
  induction xs.
  simpl.
  auto.
  simpl.
  rewrite <- List.rev_append_rev.
  replace (List.rev_append xs (a :: nil)) with 
      (List.rev_append (a :: xs) nil); auto.
Qed.


(* -------------------------------------------------------------------- *)

(* Make sure by-hand definitions are suitable for reasoning. *)

Lemma take_drop : forall (a:Set) (xs : list a) n,
    xs = Coq.Lists.List.app (take n xs) (drop n xs).
Proof.
  intros a xs.
  induction xs; intro n.
  unfold take. unfold drop.
  destruct (n <=? 0)%Z; auto.
  unfold take. unfold drop.
  destruct (n <=? 0)%Z.
  auto.
  fold (@take a).
  fold (@drop a).
  simpl.
  f_equal.
  auto.
Qed.
