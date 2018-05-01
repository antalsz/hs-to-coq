Require Import GHC.Base.
Require State.
Require Traversable.

Set Bullet Behavior "Strict Subproofs".

Local Ltac expand_pairs :=
match goal with
  |- context[let (_,_) := ?e in _] =>
  rewrite (surjective_pairing e)
end.

Definition SP {a} {s} (P Q : s -> Prop) (R : a -> Prop) (act : State.State s a) :=
  forall s, P s -> Q (snd (State.runState' act s)) /\ R (fst (State.runState' act s)).

Definition StateInvariant {a} {s} (P : s -> Prop) (act : State.State s a) :=
  SP P P (fun _ => True) act.


Lemma SP_snd_runState:
  forall {a s} (P P' : s -> Prop) (R : a -> Prop) (act : State.State s a) (x : s),
  SP P P' R act ->
  P x ->
  P' (snd (State.runState act x)).
Proof.
  intros.
  unfold State.runState.
  expand_pairs. simpl.
  apply H. assumption.
Qed.

Lemma SP_return:
  forall {a s} (P : s -> Prop) (Q : a -> Prop) (x : a),
  Q x -> SP P P Q (return_ x).
Proof. intros. intros s0 HP. split; assumption. Qed.


Lemma StateInvariant_return:
  forall {a s} (P : s -> Prop) (x : a),
  StateInvariant P (return_ x).
Proof. intros. apply SP_return. trivial. Qed.

Lemma SP_put:
  forall {s} (P P' : s -> Prop) x,
  P' x ->
  SP P P' (fun _ => True) (State.put x).
Proof. intros. intros s0 _. split; [ apply H | trivial ]. Qed.

Lemma SP_get:
  forall {s} (P : s -> Prop),
  SP P P P State.get.
Proof. intros. intros s0 H. split; assumption. Qed.


Lemma SP_bind:
  forall {a b s} P P' P'' R R' (act1 : State.State s a) (act2 : a -> State.State s b),
  SP P P' R act1 ->
  (forall x, R x -> SP P' P'' R' (act2 x)) ->
  SP P P'' R' (act1 >>= act2).
Proof.
  intros ?????????? H1 H2.
  intros s0 H.
  simpl.
  expand_pairs; simpl.
  eapply H2; apply H1; assumption.
Qed.

Lemma StateInvariant_bind:
  forall {a b s} P (act1 : State.State s a) (act2 : a -> State.State s b),
  StateInvariant P act1 ->
  (forall x, StateInvariant P (act2 x)) ->
  StateInvariant P (act1 >>= act2).
Proof.
  intros. eapply SP_bind.
  * apply H.
  * intros ? _.  apply H0.
Qed.

Lemma StateInvariant_bind_return: (*  acommon pattern *)
  forall {a b s} P (act1 : State.State s a) (f : a -> b),
  StateInvariant P act1 ->
  StateInvariant P (act1 >>= (fun x => return_ (f x))).
Proof.
  intros.
  apply StateInvariant_bind.
  * apply H.
  * intro. apply StateInvariant_return.
Qed.

Lemma StateInvariant_liftA2:
  forall {a b c s} P (f : a -> b -> c) (act1 : State.State s a) (act2 : State.State s b),
  StateInvariant P act1 ->
  StateInvariant P act2 ->
  StateInvariant P (liftA2 f act1 act2).
Proof.
  intros.
  unfold liftA2, State.Applicative__State, liftA2__, State.Applicative__State_liftA2,
         State.Applicative__State_op_zlztzg__.
  intros s0 HPs0.
  simpl.
  repeat (expand_pairs;simpl).
  split; only 2: trivial.
  apply H0. apply H. apply HPs0.
Qed.

Lemma StateInvariant_mapM:
  forall {a b s} P (act : a -> State.State s b) (xs : list a),
  (forall x, In x xs -> StateInvariant P (act x)) ->
  StateInvariant P (Traversable.mapM act xs).
Proof.
  intros ?????? Hact.
  unfold Traversable.mapM, Traversable.Traversable__list, Traversable.mapM__,
         Traversable.Traversable__list_mapM, Traversable.Traversable__list_traverse.
  induction xs.
  * apply StateInvariant_return.
  * simpl.
    apply StateInvariant_liftA2.
    - apply Hact. left. reflexivity.
    - apply IHxs. intros x Hin. apply Hact. right. assumption.
Qed.

Lemma StateInvariant_forM:
  forall {a b s} P (act : a -> State.State s b) (xs : list a),
  (forall x, In x xs -> StateInvariant P (act x)) ->
  StateInvariant P (Traversable.forM xs act).
Proof.
  intros.
  unfold Traversable.forM, flip.
  apply StateInvariant_mapM.
  assumption.
Qed.



Definition RevStateInvariant {a} {s} (P : s -> Prop) (act : State.State s a)  (R : a -> Prop) :=
  forall s, P (snd (State.runState' act s)) -> P s /\ R (fst (State.runState' act s)).
  
Lemma RevStateInvariant_runState {a} {s} (P : s -> Prop)  (act : State.State s a)  (R : a -> Prop)(s0 : s) :
  RevStateInvariant P act R ->
  P (snd (State.runState act s0)) ->
  R (fst (State.runState act s0)).
Proof.  unfold State.runState in *. expand_pairs. intros. apply H. apply H0. Qed.

Lemma RevStateInvariant_return {a} {s} (P : s -> Prop) (x : a)  (R : a -> Prop):
  R x ->
  RevStateInvariant P (return_ x) R.
Proof. intros. intros ??. simpl in *. intuition. Qed.

Lemma RevStateInvariant_bind {a b} {s} (P : s -> Prop)
    (act1 : State.State s a) (act2 : a -> State.State s b)
    (Q : a -> Prop) (R : b -> Prop):
  RevStateInvariant P (act1) Q ->
  (forall x,  RevStateInvariant P (act2 x) (fun x' => Q x -> R x')) ->
  RevStateInvariant P (act1 >>= act2) R.
Proof.
  intros Hact1 Hact2.
  unfold RevStateInvariant,
         op_zgzgze__, State.Monad__State, op_zgzgze____, State.Monad__State_op_zgzgze__ in *.
  simpl in *.
  intro s0.
  expand_pairs. simpl in *.
  intros HPs''.
  split.
  * apply Hact1.
    apply (Hact2 (fst (State.runState' act1 s0)) (snd (State.runState' act1 s0)) HPs'').
  * apply Hact2.
    + apply HPs''.
    + apply Hact1.
      apply (Hact2 (fst (State.runState' act1 s0)) (snd (State.runState' act1 s0)) HPs'').
Qed.

Lemma RevStateInvariant_impl {a} {s} (P : s -> Prop)
    (act1 : State.State s a) (R Q : a -> Prop):
  RevStateInvariant P act1 R ->
  (forall x, R x -> Q x) ->
  RevStateInvariant P act1 Q.
Proof.
  intros Hact1 Himpl.
  split.
  * apply Hact1. apply H.
  * apply Himpl. apply Hact1. apply H.
Qed.


Lemma RevStateInvariant_bind_return {a b} {s} (P : s -> Prop)
    (act1 : State.State s a) (f : a -> b)
    (R : b -> Prop):
  RevStateInvariant P act1 (fun x => R (f x)) ->
  RevStateInvariant P (act1 >>= (fun x => return_ (f x))) R.
Proof.
  intros Hact1.
  eapply RevStateInvariant_bind.
  * apply Hact1.
  * intro x.
    apply RevStateInvariant_return.
    auto.
Qed.


Lemma RevStateInvariant_liftA2:
  forall {a b c s} P (f : a -> b -> c) (act1 : State.State s a) (act2 : State.State s b) R1 R2 (R3 : c -> Prop),
  RevStateInvariant P act1 R1 ->
  RevStateInvariant P act2 R2 ->
  (forall x y, R1 x -> R2 y -> R3 (f x y)) ->
  RevStateInvariant P (liftA2 f act1 act2) R3.
Proof.
  intros ??????????? Hact1 Hact2 Hf s1.
  unfold liftA2, State.Applicative__State, liftA2__, State.Applicative__State_liftA2,
         State.Applicative__State_op_zlztzg__.
  simpl; repeat (expand_pairs;simpl).
  intro HPs3.
  split.
  * apply Hact1.
    apply Hact2.
    assumption.
  * apply Hf.
    + apply Hact1.
      apply Hact2.
      assumption.
    + apply Hact2.
      assumption.
Qed.

Lemma RevStateInvariant_mapM:
  forall {a b s} P (act : a -> State.State s b) (xs : list a) R,
  (forall x, In x xs -> RevStateInvariant P (act x) R) ->
  RevStateInvariant P (Traversable.mapM act xs) (Forall R).
Proof.
  intros ??????? Hact.
  unfold Traversable.mapM, Traversable.Traversable__list, Traversable.mapM__,
         Traversable.Traversable__list_mapM, Traversable.Traversable__list_traverse.
  induction xs.
  * apply RevStateInvariant_return. constructor.
  * simpl.
    apply RevStateInvariant_liftA2 with (R1 := R) (R2 := Forall R).
    - apply Hact. left. reflexivity.
    - apply IHxs. intros x Hin. apply Hact. right. assumption.
    - intros. constructor; assumption.
Qed.

Lemma RevStateInvariant_forM:
  forall {a b s} P (act : a -> State.State s b) (xs : list a) R,
  (forall x, In x xs -> RevStateInvariant P (act x) R) ->
  RevStateInvariant P (Traversable.forM xs act) (Forall R).
Proof.
  intros.
  unfold Traversable.forM, flip.
  apply RevStateInvariant_mapM.
  assumption.
Qed.
