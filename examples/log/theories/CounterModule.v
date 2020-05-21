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

Module CounterImpl : CounterSig.
  Definition WF {A} (m : Counter.Counter A) : Prop :=
    forall n B (p : Counter.Counter B),
      let (_, a) := Counter.runC (p >> m) n in
      let (_, b) := Counter.runC p n in
      (a >= b)%Z.
  
  Definition Counter A := { x : Counter.Counter A | WF x }.

  Program Definition Inc : Counter unit := Counter.inc.
  Next Obligation.
    intros n B p. cbn.
    destruct (Counter.runC p n). lia.
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
    intros. intros n B p. cbn.
    destruct (Counter.runC p n).
    destruct x. cbn.
    specialize (H i unit (return_ tt)). revert H.
    simpl. destruct (runC i). tauto.
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
    intros a x n B p. cbn.
    destruct (Counter.runC p n).
    simpl. lia.
  Qed.

  Local Lemma ap_WF : forall a b f x,
      WF f ->
      WF x ->
      WF (@op_zlztzg__ _ _ _ a b f x).
  Proof.
    intros a b f x Hf Hx n B p. cbn.
    destruct (Counter.runC p n).
    specialize (Hf i _ (return_ tt)). revert Hf.
    simpl. destruct (Counter.runC f i).
    specialize (Hx i0 _ (return_ tt)). revert Hx.
    simpl. destruct (Counter.runC x i0).
    intros; lia.
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

  Local Lemma bind_WF : forall a b m k,
      WF m ->
      (forall x, WF (k x)) ->
      WF (@op_zgzgze__ _ _ _ _ a b m k).
  Proof.
    intros a b m k Hm Hk n B p. cbn.
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
      
