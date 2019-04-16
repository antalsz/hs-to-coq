Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.
Require Import Data.Map.Internal.
Import GHC.Num.Notations.
Require Import OrdTactic.
Require Import Psatz.
Require Import Tactics.
Set Bullet Behavior "Strict Subproofs".

Lemma Eq_Tuple_Trans: forall {e a} `{EqLaws e} `{EqLaws a} (x1 x2 x3 : e) (y1 y2 y3 : a),
  (x1, y1) == (x2, y2) = true -> (x2, y2) == (x3, y3) = true -> (x1, y1) == (x3, y3) = true.
Proof.
  intros. unfold op_zeze__ in *. unfold Eq_pair___ in *. unfold op_zeze____ in *. unfold eq_pair in *.
  rewrite andb_true_iff in *. destruct H3. destruct H4. split. eapply Eq_Transitive. apply H3. apply H4.
  eapply Eq_Transitive. apply H5. apply H6.
Qed.

Lemma Eq_Tuple_Sym: forall {e a} `{EqLaws e} `{EqLaws a} (x1 x2 : e) (y1 y2 : a),
  (x1, y1) == (x2, y2) = true <-> (x2, y2) == (x1, y1) = true.
Proof.
  intros. unfold op_zeze__ in *. unfold Eq_pair___  in *. unfold op_zeze____ in *. unfold eq_pair in *.
  rewrite andb_true_iff in *. rewrite andb_true_iff in *. split; intros.
  - destruct H3. split. apply Eq_Symmetric. apply H3. apply Eq_Symmetric. apply H4.
  - destruct H3. split. apply Eq_Symmetric. apply H3. apply Eq_Symmetric. apply H4.
Qed. 

Lemma Eq_Tuple_Refl: forall {e a} `{EqLaws e} `{EqLaws a} (x :e) (y : a),
  (x, y) == (x, y) = true.
Proof.
  intros. unfold_zeze. unfold eq_pair. rewrite andb_true_iff. split; apply Eq_Reflexive.
Qed.

Lemma eq_tuple_prop: forall {a} {b} `{Eq_ a} `{EqLaws a} `{Eq_ b} `{EqLaws b}
  (x1 x2 : a) (y1 y2 : b),
  (x1, y1) == (x2, y2) = true <-> x1 == x2 = true /\ y1 == y2 = true.
Proof.
  intros. unfold op_zeze__. unfold Eq_pair___. unfold op_zeze____. unfold eq_pair.
  unfold op_zeze__. unfold op_zeze____. rewrite andb_true_iff. reflexivity.
Qed.

Lemma prop_bool: forall (b1: bool) (b2: bool),
  b1 = b2 <-> (b1 = true <-> b2 = true).
Proof.
  intros. split; intros.
  - split; intros.
    + subst. reflexivity.
    + subst. reflexivity.
  - destruct H. destruct b1. symmetry. apply H. reflexivity.
    destruct b2. apply H0. reflexivity. reflexivity.
Qed.

Lemma eq_tuple_eq: forall {a} {b} `{Eq_ a} `{EqLaws a} `{Eq_ b} `{EqLaws b}
  (x1 x2 : a) (y1 y2 : b),
  (x1, y1) == (x2, y2) = (x1 == x2) && (y1 == y2).
Proof. 
  intros. rewrite prop_bool. rewrite andb_true_iff. apply eq_tuple_prop.
Qed.

(*First, we need lawful [Eq] and [Ord] instances for pairs*)
Global Instance EqLaws_Pair {a} {b} `{EqLaws a} `{EqLaws b} : EqLaws (a * b).
Proof.
  constructor.
  - unfold "==". unfold Eq_pair___. unfold op_zeze____. unfold eq_pair. unfold ssrbool.reflexive.
    intros. destruct x. unfold is_true. rewrite andb_true_iff. split; apply Eq_Reflexive.
  - unfold "==". unfold Eq_pair___. unfold op_zeze____. unfold eq_pair. unfold ssrbool.symmetric.
    intros. destruct x. destruct y. assert ((a0 == a1) = (a1 == a0)) by (order a).
    assert ((b0 == b1) = (b1 == b0)) by (order b). rewrite H3. rewrite H4. reflexivity.
  - unfold "==". unfold Eq_pair___. unfold op_zeze____. unfold eq_pair. unfold ssrbool.transitive.
    intros. destruct x. destruct y. destruct z. unfold is_true in *.
    rewrite andb_true_iff in H3. rewrite andb_true_iff in H4. destruct H3. destruct H4.
    eapply Eq_Tuple_Trans. rewrite eq_tuple_prop. split. apply H3. apply H5. rewrite eq_tuple_prop.
    split. apply H4. apply H6.
  - intros. unfold "==", "/=". unfold Eq_pair___. unfold op_zeze____ , op_zsze____ .
    destruct (eq_pair x y). reflexivity. reflexivity.
Qed.

(*If a and b are lawful members of [Ord], then so is a * b*)
Instance OrdLaws_Pair {a} {b} `{OrdLaws a} `{OrdLaws b} : OrdLaws (a * b).
Proof.
  constructor.
  - intros. destruct a0. destruct b0. unfold "<=", "==" in *. unfold Ord_pair___, Eq_pair___ in *.
    unfold ord_default, op_zeze____  in *. simpl in *.
    rewrite andb_true_iff.  rewrite negb_true_iff in *. 
    destruct (compare a1 a0) eqn : ?. destruct (compare b0 b1) eqn : ?. split. order a. order b.
    inversion H1. split. order a. assert (compare a0 a1 = Eq) by (order a). rewrite H3 in H2.
    assert (compare b1 b0 = Lt) by (order b). rewrite H4 in H2. inversion H2. inversion H1.
    assert (compare a0 a1 = Lt) by (order a). rewrite H3 in H2. inversion H2. 
  - intros. destruct a0. destruct c. destruct b0. unfold "<=" in *. unfold Ord_pair___  in *.
    unfold compare_pair in *. unfold ord_default in *. simpl in *. rewrite negb_true_iff in *.
    repeat (try (destruct (compare a2 a0) eqn : ?); try (destruct (compare a1 a2) eqn : ?);
    try (destruct (compare b0 b1) eqn : ?); try (destruct (compare b2 b0) eqn : ?);
    try (destruct (compare a1 a0) eqn : ?); try (destruct (compare b2 b1) eqn : ?); try (order a);
    try (order b)).
  - intros. destruct a0. destruct b0. unfold "<=" in *. unfold Ord_pair___ in *. unfold compare_pair in *.
    unfold ord_default. unfold ord_default in *. simpl. rewrite negb_true_iff. rewrite negb_true_iff.
    destruct (compare a1 a0) eqn : ?. assert (compare a0 a1 = Eq) by (order a). rewrite H1.
    destruct (compare b0 b1) eqn : ?. left. reflexivity. right. assert (compare b1 b0 <> Lt) by (order b).
    destruct (compare b1 b0). reflexivity. contradiction. reflexivity. left. reflexivity.
    right. destruct (compare a0 a1) eqn : ?. order a. order a. reflexivity.
    left. reflexivity.
  - intros. unfold compare.   unfold "<=" in *. unfold Ord_pair___ in *. unfold compare_pair in *.
    unfold ord_default. simpl. rewrite negb_false_iff. destruct a0. destruct b0. 
    split; intros. destruct (compare a0 a1). rewrite H1. reflexivity. reflexivity. inversion H1.
    destruct (compare a0 a1). destruct (compare b1 b0). inversion H1. reflexivity. inversion H1.
    reflexivity. inversion H1.
  - intros. unfold compare. unfold "==". unfold Ord_pair___ , Eq_pair___ . unfold compare_pair,op_zeze____ .
    unfold ord_default, eq_pair. simpl. destruct a0. destruct b0. split; intros. destruct (compare a0 a1) eqn : ?.
    inversion H. rewrite Ord_compare_Eq in Heqc. inversion H0. rewrite Ord_compare_Eq0 in H1. rewrite andb_true_iff.
    split; assumption. inversion H1. inversion H1. rewrite andb_true_iff in H1. destruct H1.
    inversion H. inversion H0. apply Ord_compare_Eq in H1. apply Ord_compare_Eq0 in H2. rewrite H1. assumption.
  - intros. unfold compare. unfold Ord_pair___ , "<=". unfold compare_pair. unfold ord_default. simpl.
    destruct a0. destruct b0. split; intros. rewrite negb_false_iff.  
    destruct (compare a0 a1) eqn : ?. assert (compare a1 a0 = Eq) by (order a). rewrite H2.
    assert (compare b0 b1 = Lt) by (order b). rewrite H3. reflexivity. inversion H1. inversion H1.
    assert (compare a1 a0 = Lt) by (order a). rewrite H2. reflexivity.
    rewrite negb_false_iff in H1. destruct (compare a1 a0) eqn : ?.
    assert (compare a0 a1 = Eq) by (order a). rewrite H2. destruct (compare b0 b1) eqn : ?.
    inversion H1. order b. inversion H1. assert (compare a0 a1 = Gt) by (order a). rewrite H2.
    reflexivity. inversion H1.
  - intros. unfold "<", "<=". unfold Ord_pair___.  unfold compare_pair; unfold ord_default; simpl.
    rewrite negb_involutive. reflexivity.
  - intros. unfold "<=", ">=". unfold Ord_pair___. unfold compare_pair; unfold ord_default; simpl.
    reflexivity.
  - intros. unfold ">", "<=". unfold Ord_pair___.  unfold compare_pair; unfold ord_default; simpl.
    rewrite negb_involutive. reflexivity.
Qed.