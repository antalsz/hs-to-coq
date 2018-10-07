(**
Lemmas related to the Coq base library
*)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Lemma Forall_and:
  forall {a} (P Q : a -> Prop) xs,
  (Forall P xs /\ Forall Q xs) <->  Forall (fun x =>  P x /\ Q x) xs.
Proof.
  intros.
  rewrite !Forall_forall in *.
  firstorder.
Qed.

Lemma Forall_app:
  forall {a} (P : a -> Prop) xs ys,
  Forall P (xs ++ ys) <->  Forall P xs /\ Forall P ys.
Proof.
  intros.
  rewrite !Forall_forall in *.
  setoid_rewrite in_app_iff.
  firstorder.
Qed.


Lemma Forall2_symmetric:
  forall {a} (P : a -> a -> Prop) xs,
  (forall x, P x x) -> Forall2 P xs xs.
Proof.
  intros.
  induction xs.
  * constructor.
  * constructor; auto.
Qed.

Lemma Forall2_impl_Forall_r:
  forall {a b} (P : a -> b -> Prop) (Q : b -> Prop)  xs ys,
  Forall2 P xs ys ->
  (forall x y, P x y -> Q y) ->
  Forall Q ys.
Proof.
  intros.
  induction H.
  * constructor.
  * constructor; intuition.
    eapply H0; eassumption.
Qed.

Lemma existsb_morgan:
  forall a p (xs : list a),
  existsb p xs = negb (forallb (fun x => negb (p x)) xs).
Proof.
  intros.
  induction xs.
  * simpl. intuition congruence.
  * simpl. rewrite IHxs, negb_andb, negb_involutive.
    reflexivity.
Qed.

Lemma existsb_false_iff_forallb:
  forall a p (xs : list a),
  existsb p xs = false <-> forallb (fun x => negb (p x)) xs = true.
Proof.
  intros.
  induction xs.
  * simpl. intuition congruence.
  * simpl. rewrite orb_false_iff, andb_true_iff, negb_true_iff, IHxs.
    reflexivity.
Qed.




Definition sublistOf {a} (xs ys : list a) := incl ys xs.

Lemma sublistOf_cons {a} x (xs ys : list a):
  sublistOf ys (x :: xs) <-> (In x ys /\ sublistOf ys xs).
Proof.
  intros.
  unfold sublistOf, incl.
  intuition.
  destruct H; subst; auto.
Qed.

