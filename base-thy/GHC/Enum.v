From Coq Require Import ssreflect ssrfun.
Set Bullet Behavior "Strict Subproofs".

Require Import GHC.Base.
Require Import GHC.Enum.

(******************************************************************************)
(** `iterates'` and `iterates` functions -- used for specification **)

Fixpoint iterates' {A} (n : nat) (f : A -> A) (z : A) : list A :=
  match n with
  | O    => nil
  | S n' => z :: iterates' n' f (f z)
  end.

Fixpoint iterates {A} (n : nat) (f : A -> A) (z : A) : list A :=
  z :: match n with
       | O    => nil
       | S n' => iterates n' f (f z)
       end.

Theorem iterates_iterates' {A} (n : nat) (f : A -> A) (z : A) :
  iterates n f z = iterates' (S n) f z.
Proof. by elim: n z => [|n IH] z //=; rewrite IH. Qed.

Theorem iterates'_ext {A} (n : nat) (f1 f2 : A -> A) (z : A) :
  f1 =1 f2 ->
  iterates' n f1 z = iterates' n f2 z.
Proof. by move=> f_eq; elim: n z => [|n IH] z //=; rewrite f_eq IH. Qed.

Theorem iterates_ext {A} (n : nat) (f1 f2 : A -> A) (z : A) :
  f1 =1 f2 ->
  iterates n f1 z = iterates n f2 z.
Proof. rewrite !iterates_iterates'; apply iterates'_ext. Qed.

Theorem iterates'_map {A} (n : nat) (f : A -> A) (z : A) :
  iterates' n f z = Coq.Lists.List.map (fun n => Nat.iter n f z) (seq 0 n).
Proof.
  elim: n z => [|n IH] z //=.
  rewrite -seq_shift map_map IH /=.
  f_equal; apply map_ext => i.
  by elim: i => [|i IH'] //=; rewrite IH'.
Qed.

Theorem iterates_map {A} (n : nat) (f : A -> A) (z : A) :
  iterates n f z = Coq.Lists.List.map (fun n => Nat.iter n f z) (seq 0 (S n)).
Proof. rewrite iterates_iterates'; apply iterates'_map. Qed.

Theorem iterates'_length {A} (n : nat) (f : A -> A) (z : A) :
  length (iterates' n f z) = n.
Proof. by rewrite iterates'_map map_length seq_length. Qed.

Theorem iterates_length {A} (n : nat) (f : A -> A) (z : A) :
  length (iterates n f z) = S n.
Proof. rewrite iterates_iterates'; apply iterates'_length. Qed.

Theorem iterates'_In {A} (n : nat) (f : A -> A) (z : A) (a : A) :
  In a (iterates' n f z) <-> ex2 (fun i => i < n)%nat (fun i => a = Nat.iter i f z).
Proof.
  rewrite iterates'_map in_map_iff.
  split=> [[i [def_a i_in_seq]] | [i LT def_a]]; subst; exists i; try split; try done.
  - move: i_in_seq => /in_seq [] //=.
  - apply in_seq => //=; split => //.
    apply Nat.le_0_l.
Qed.

Theorem iterates_In {A} (n : nat) (f : A -> A) (z : A) (a : A) :
  In a (iterates n f z) <-> ex2 (fun i => i <= n)%nat (fun i => a = Nat.iter i f z).
Proof.
  rewrite iterates_iterates' iterates'_In.
  split=> [[i LT def_a] | [i LE def_a]]; exists i=> //; omega.
Qed.

(******************************************************************************)
(** Lemmas about `Nat.iter` **)

Lemma iter_plus_nat (m n : nat) : Nat.iter m S n = (m + n)%nat.
Proof. by elim: m => [|m IH] //=; rewrite IH. Qed.

Lemma iter_plus_N (m : nat) (n : N) : Nat.iter m N.succ n = (N.of_nat m + n)%N.
Proof. by elim: m => [|m IH] //; rewrite Nat2N.inj_succ N.add_succ_l /= IH. Qed.

Lemma iter_plus_Z (m : nat) (n : Z) : Nat.iter m Z.succ n = (Z.of_nat m + n)%Z.
Proof. by elim: m => [|m IH] //; rewrite Nat2Z.inj_succ Z.add_succ_l /= IH. Qed.

(******************************************************************************)
(** `eftInt`, including `eftInt_aux` and `enumFromTo` **)

(* Unrolling `eftInt_aux` *)

Definition eftInt_aux_rhs (y x : Int) (pf : (x <= y)%Z) : list Int :=
  x :: match Z.eq_dec x y with
       | left  _   => nil
       | right neq => eftInt_aux y (x+1) (eftInt_aux_pf pf neq)
       end%Z.

Lemma eftInt_aux_unroll (to from : Int) (pf : (from <= to)%Z) :
  eftInt_aux to from pf = eftInt_aux_rhs to from pf.
Proof.
  rewrite /eftInt_aux /eftInt_aux_func Wf.WfExtensionality.fix_sub_eq_ext /= /eftInt_aux_rhs.
  by case: (Z.eq_dec from to).
Qed.

(* Specifying `eftInt_aux`, `eftInt`, and `enumFromTo` in terms of
   `iterate`/`iterate'` *)

Theorem eftInt_aux_iterates (to from : Int) (pf : (from <= to)%Z) :
  eftInt_aux to from pf = iterates (Z.to_nat (to - from)) Z.succ from.
Proof.
  remember (Z.to_nat (to - from)) as diff eqn:def_diff.
  elim: diff to from pf def_diff => [|diff IH] to from pf def_diff /=;
    rewrite eftInt_aux_unroll /eftInt_aux_rhs.
  - case: (Z.eq_dec _ _) => [// | NEQ].
    suff LE: (to - from <= 0)%Z by omega.
    move: def_diff; case: (to - from)%Z => //=.
    move=> p ZERO; move: (Pos2Nat.is_pos p) => POS; omega.
  - case: (Z.eq_dec _ _) => [? | NEQ]; first by subst; rewrite Z.sub_diag in def_diff.
    rewrite IH //.
    by rewrite Z.sub_add_distr Z2Nat.inj_sub //= -def_diff /Pos.to_nat /= Nat.sub_0_r.
Qed.

Theorem eftInt_iterates' (from to : Int) :
  eftInt from to = iterates' (Z.to_nat (to - from + 1)) Z.succ from.
Proof.
  rewrite /eftInt; case: (Z_gt_dec _ _) => [GT | LE].
  - have: (to - from < 0)%Z by omega.
    case: (to - from)%Z => //=.
    case=> //=.
  - rewrite eftInt_aux_iterates iterates_iterates'; f_equal.
    rewrite Z.add_1_r Z2Nat.inj_succ //; omega.
Qed.

Theorem enumFromTo_Int_iterates' (from to : Int) :
  enumFromTo from to = iterates' (Z.to_nat (to - from + 1)) Z.succ from.
Proof. apply eftInt_iterates'. Qed.

(* Specifying `eftInt_aux`, `eftInt`, and `enumFromTo` in terms of membership *)

Theorem eftInt_aux_In (to from : Int) (pf : (from <= to)%Z) (a : Int) :
  In a (eftInt_aux to from pf) <-> (from <= a <= to)%Z.
Proof.
  rewrite eftInt_aux_iterates iterates_In.
  split=> [[i LE ->{a}] | [LE_a a_LE]].
  - rewrite iter_plus_Z.
    move: LE => /inj_le; rewrite Z2Nat.id => [|LE]; omega.
  - remember (Z.to_nat (to - from)) as diff eqn:def_diff.
    elim: diff from pf def_diff LE_a => [|diff IH] from pf def_diff LE_a.
    + exists 0 => //=.
      suff LE: (to - from <= 0)%Z by apply Z.le_antisymm; omega.
      move: def_diff; case: (to - from)%Z => //= p.
      move: (Pos2Nat.is_pos p) => *; omega.
    + case: (Z.eq_dec from a) => [? | NEQ]; first by subst a; exists 0 => //=; omega.
      have LE_a': (from < a)%Z by omega.
      case: (IH (Z.succ from)) => [| | | i LE_i def_a]; try omega.
      * by rewrite Z.sub_succ_r Z2Nat.inj_pred -def_diff.
      * exists (S i); first by apply le_n_S.
        by rewrite def_a /Nat.iter nat_rect_succ_r.
Qed.

Theorem eftInt_In (from to : Int) (a : Int) :
  In a (eftInt from to) <-> (from <= a <= to)%Z.
Proof.
  rewrite /eftInt; case: (Z_gt_dec _ _) => ?; [simpl; omega | apply eftInt_aux_In].
Qed.

Theorem enumFromTo_Int_In (from to : Int) (a : Int) :
  In a (enumFromTo from to) <-> (from <= a <= to)%Z.
Proof. apply eftInt_In. Qed.
