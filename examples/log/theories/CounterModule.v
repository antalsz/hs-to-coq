Require Counter.

Require Import GHC.Base.

Require Import RelationClasses.
Require Import Psatz.

Module Type CounterSig.
  Parameter Counter : Type -> Type.
  
  Parameter Inc : Counter unit.

  Parameter GE : forall A, Counter A -> Counter A -> Prop.

  Declare Instance PreOrder_GE {A} : PreOrder (GE A).

  Declare Instance Counter_functor : Functor Counter.
  Declare Instance Counter_applicative : Applicative Counter.
  Declare Instance Counter_monad : Monad Counter.

  Axiom inc_bind_l : forall (m : Counter unit), GE unit (Inc >> m) Inc.
  Axiom inc_bind_r : forall (m : Counter unit), GE unit (m >> Inc) Inc.
End CounterSig.

Open Scope Z_scope.

Module CounterImpl : CounterSig.
  Definition WF {A} (m : Counter.Counter A) : Prop :=
    exists i, forall n,
        i >= 0 /\
        let (_, n') := Counter.runC m n in (n' = n + i).

(*  Definition m1 : Counter.Counter unit :=
    Counter.MkCounter (fun n => if n == 0 then (tt, 100) else (tt, n+1)).
  Definition m2 := Counter.inc. *)
  
(*  Definition WF {A} (m : Counter.Counter A) : Prop :=
    forall n B (p : Counter.Counter B),
      let (_, a) := Counter.runC (p >> m) n in
      let (_, b) := Counter.runC p n in
      (a >= b)%Z. *)
  
  Definition Counter A := { x : Counter.Counter A | WF x }.
  Unset Printing Notations.

  Program Definition Inc : Counter unit := Counter.inc.
  Next Obligation.
    exists 1. intros n. split; [lia|].
    cbn. reflexivity.
  Defined.

  Program Definition GE A (m1 m2 : Counter A) : Prop :=
    forall n,
      let (_, a) := Counter.runC m1 n in
      let (_, b) := Counter.runC m2 n in
      (a >= b)%Z.

  Instance PreOrder_GE {A} : PreOrder (GE A).
  constructor.
  - intros x n. destruct x. simpl.
    destruct (Counter.runC x n). lia.
  - intros x y z. unfold GE.
    destruct x, y, z. simpl.
    intros H1 H2 n. specialize (H1 n). specialize (H2 n).
    destruct (Counter.runC x), (Counter.runC x0), (Counter.runC x1). lia.
  Qed.

  Local Lemma fmap_WF : forall a b f x,
      WF x ->
      WF (@fmap _ _ a b f x).
  Proof.
    intros. destruct H.
    exists x0. intros n. cbn.
    specialize (H n). intuition.
    destruct (Counter.runC x n); assumption.
  Qed.

  Program Instance Counter_functor : Functor Counter :=
    fun _ k__ =>
      k__ {| fmap__ := fun {a b} => @fmap Counter.Counter _ a b;
             op_zlzd____ := fun {a b} => @op_zlzd__ Counter.Counter _ a b |}.
  Next Obligation.
    apply fmap_WF. destruct x0. simpl. assumption.
  Defined.
  Next Obligation.
    cbn. unfold Counter.Functor__Counter_op_zlzd__, op_z2218U__.
    apply fmap_WF. destruct x0. simpl. assumption.
  Defined.

  Local Lemma pure_WF : forall a x,
      WF (@pure _ _ _ a x).
  Proof.
    exists 0. intros n. cbn. lia.
  Qed.

  Local Lemma ap_WF : forall a b f x,
      WF f ->
      WF x ->
      WF (@op_zlztzg__ _ _ _ a b f x).
  Proof.
    intros a b f x Hf Hx.
    destruct Hf, Hx.
    exists (x0 + x1). intros n. cbn.
    specialize (H n). destruct (Counter.runC f n).
    specialize (H0 i). destruct (Counter.runC x i).
    lia.
  Qed.

  Program Instance Counter_applicative : Applicative Counter :=
    fun _ k__ =>
      k__ {| liftA2__ := fun {a} {b} {c} => @liftA2 Counter.Counter _ _ a b c;
             op_zlztzg____ := fun {a} {b} => @op_zlztzg__ Counter.Counter _ _ a b ;
             op_ztzg____ := fun {a} {b} => @op_ztzg__ Counter.Counter _ _ a b ;
             pure__ := fun {a} => @pure Counter.Counter _ _ a |}.
  Next Obligation.
    cbn. unfold Counter.Applicative__Counter_liftA2.
    destruct x0, x1. simpl.
    apply ap_WF; try assumption.
    apply fmap_WF; assumption.
  Defined.
  Next Obligation.
    destruct x, x0. simpl. apply ap_WF; assumption.
  Defined.
  Next Obligation.
    destruct x, x0. simpl. cbn.
    unfold Counter.Applicative__Counter_op_ztzg__. cbn.
    unfold Counter.Functor__Counter_op_zlzd__, op_z2218U__.
    apply ap_WF; try assumption.
    apply fmap_WF; assumption.
  Defined.
  Next Obligation.
    apply pure_WF.
  Defined.

  Print Assumptions Counter_applicative.

  Local Lemma return_WF : forall a x,
      WF (@return_ _ _ _ _ a x).
  Proof.
    apply pure_WF.
  Qed.

  Lemma counter_increment_from : forall A (m : Counter.Counter A) n1 n2,
      WF m ->
      let (_, i) := Counter.runC m n1 in
      let (_, j) := Counter.runC m n2 in
      j + n1 = i + n2.
  Proof.
    intros. destruct H.
    assert (forall n : Int, x >= 0 /\ (let (_, n') := Counter.runC m n in n' = n + x)) by assumption.
    specialize (H n1). specialize (H0 n2).
    destruct (Counter.runC m n1). destruct (Counter.runC m n2). lia.
  Qed.

  Lemma counter_increment_from_0 : forall A (m : Counter.Counter A) n,
      WF m ->
      let (_, i) := Counter.runC m 0 in
      let (_, j) := Counter.runC m n in
      j = i + n.
  Proof.
    intros. pose proof (counter_increment_from A m 0 n H).
    destruct (Counter.runC m 0). destruct (Counter.runC m n). lia.
  Qed.

  Import Counter.
  Definition m1 : Counter Int := MkCounter (fun n => (n, n)).
  Definition m2 : Int -> Counter unit := fun x => MkCounter (fun n => (tt, n + Z.max x 0)).

  Goal WF m1.
  Proof.
    exists 0. intros. cbn. split; lia.
  Qed.

  Goal forall a, WF (m2 a).
  Proof.
    intros. exists (Z.max a 0).
    intros. cbn. split; lia.
  Qed.

  Definition x := runC (m1 >>= m2) 1.
  Compute x.

  Local Lemma bind_WF : forall a b m k,
      WF m ->
      (forall x, WF (k x)) ->
      WF (@op_zgzgze__ _ _ _ _ a b m k).
  Proof.
    intros a b m k Hm Hk.
    assert (WF m) by assumption.
    destruct Hm. unfold WF. cbn.
    specialize (H0 0). destruct (Counter.runC m 0) eqn:Hm0. pose proof Hk.
    specialize (Hk a0). destruct Hk. specialize (H2 i).
    destruct (Counter.runC (k a0) i) eqn:Hka0i. exists i0. intros.
    intuition. subst. destruct (Counter.runC m n) eqn:Hmn.
    pose proof (counter_increment_from_0 _ m n H).
    pose proof (counter_increment_from _ (k a1) i x (H1 a1)).
    specialize (H1 a1). destruct H1. specialize (H1 i).
    destruct (Counter.runC (k a1) i).
    destruct (Counter.runC (k a1) i1). intuition. subst.
    rewrite Hm0, Hmn in H2. subst.
    rewrite Hm0 in H1. rewrite Hmn in H1.
    assert (i1 = i + n).
    { pose proof counter_increment_from_0.
    destruct (Counter.runC (k a0) i). split.
    2: { intuition. subst. rewrite <- Z.add_assoc. reflexivity.
    - assert (x + x0 >= 0).
    
    destruct (Counter.runC p n).
    specialize (Hm i _ (return_ tt)). revert Hm. simpl.
    destruct (Counter.runC m i).
    specialize (Hk a0 i0 _ (return_ tt)). revert Hk. simpl.
    destruct (Counter.runC (k a0)). lia.
  Qed.

  Program Instance Counter_monad : Monad Counter :=
    fun _ k__ =>
      k__ {| op_zgzg____ := fun {a} {b} => @op_zgzg__ Counter.Counter _ _ _ a b;
             op_zgzgze____ := fun {a} {b} => @op_zgzgze__ Counter.Counter _ _ _ a b;
             return___ := fun {a} => @return_ Counter.Counter _ _ _ a |}.
  Next Obligation.
    destruct x, x0. cbn.
    unfold Counter.Monad__Counter_op_zgzg__.
    apply bind_WF; [assumption|].
    intros. assumption.
  Defined.
  Next Obligation.
    destruct x. cbn.
    apply bind_WF; [assumption|].
    intros. remember (x0 x1) as c.
    destruct c. simpl. assumption.
  Defined.
  Next Obligation.
    apply return_WF.
  Defined.

  Theorem inc_bind_l : forall (m : Counter unit), GE unit (Inc >> m) Inc.
  Proof.
    intros m i. destruct m. simpl.
    specialize (w i unit Counter.inc).
    revert w. cbn. tauto.
  Qed.
  
  Theorem inc_bind_r : forall (m : Counter unit), GE unit (m >> Inc) Inc.
  Proof.
    intros m i. destruct m. simpl.
    specialize (w i unit Counter.inc).
    revert w. cbn.
    remember (Counter.runC x) as cx.
  Admitted.
End CounterImpl.

Import CounterImpl.

Lemma compute_ex1 :
  GE _ (Inc >> Inc) Inc.
Proof.
  apply inc_bind_l.
Qed.
      
