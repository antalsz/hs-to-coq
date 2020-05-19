Require Import Counter.
Require Import Freer.
Require Import CounterExtInd.

Require Import GHC.Base.
Require Import Proofs.Freer.

Require Import RelationClasses.
Require Import Psatz.

Coercion interp_ext : CounterExt >-> Counter.

Definition equiv_res_CounterExtInd {A} (m1 m2 : CounterExt A) : Prop :=
  forall n,
    let (_, a) := runC m1 n in
    let (_, b) := runC m2 n in
    a = b.

Definition ge_res_CounterExtInd {A} (m1 m2 : CounterExt A) : Prop :=
  forall n,
    let (_, a) := runC m1 n in
    let (_, b) := runC m2 n in
    (a >= b)%Z.

Notation "a ≊ b" := (equiv_res_CounterExtInd a b) (at level 100).
Notation "a ⪎ b" := (ge_res_CounterExtInd a b) (at level 100).

Instance equiv_res_CounterExtInd_equiv {A : Type} : Equivalence (@equiv_res_CounterExtInd A).
Proof.
  constructor.
  - intros x n. destruct (runC x n). reflexivity.
  - intros x y. unfold equiv_res_CounterExtInd. intros H n.
    specialize (H n). revert H.
    destruct (runC x n). destruct (runC y n).
    intros. rewrite H. reflexivity.
  - intros x y z. unfold equiv_res_CounterExtInd. intros H1 H2 n.
    specialize (H1 n). specialize (H2 n). revert H1 H2.
    destruct (runC x n).
    destruct (runC y n).
    destruct (runC z n).
    intros. rewrite H1, H2. reflexivity.
Qed.

Lemma computation_ex1:
  inc >> inc ⪎ inc.
Proof.
  unfold ge_res_CounterExtInd.
  intros n. cbn. lia.
Qed.

Lemma left_Ret_id : forall A (m : CounterExt A) (r : A),
    Ret r >> m ≊ m.
Proof.
  intros A m. induction m.
  - intros r'. cbv. reflexivity.
  - intros r'. destruct e.
    intros n. cbn. specialize (H tt r' (n+1)%Z). assumption.
Qed.

Lemma right_Ret_id : forall A (m : CounterExt A) r,
    m >> Ret r ≊ m.
Proof.
  intros A m. induction m.
  - intros r'. cbv. reflexivity.
  - intros r'. destruct e.
    intros n. cbn. specialize (H tt r' (n+1)%Z). assumption.
Qed.

Theorem commutativity : forall A (m1 m2 : CounterExt A),
    m1 >> m2 ≊ m2 >> m1.
Proof.
  intros A m1. induction m1.
  - intros. rewrite right_Ret_id.
    cbn. reflexivity.
  - induction m2.
    + rewrite left_Ret_id, right_Ret_id. reflexivity.
    + destruct e, e0. intros n. cbn. 
      specialize (H0 tt (n+1)%Z).
      replace (runC (interp_ext (bind (f0 tt) (fun _ : A => Vis Inc f))) (n + 1)%Z)
        with (runC (interp_ext (f0 tt >> Vis Inc f)) (n + 1)%Z) by reflexivity.
      remember (runC (interp_ext (f0 tt >> Vis Inc f)) (n + 1)%Z) as r. destruct r.
      remember (runC (interp_ext (Vis Inc f >> f0 tt)) (n + 1)%Z) as r0. destruct r0.
      rewrite <- H0. cbn in Heqr0.
      remember (runC (interp_ext (bind (f tt) (fun _ : A => Vis Inc f0))) (n + 1)%Z) as r1. destruct r1.
      clear Heqr. generalize dependent n. induction (f tt).
      * cbn. intro n.
        destruct (runC (interp_ext (f0 tt)) (n + 1 + 1)%Z). do 2 inversion 1. reflexivity.
      * intro n. destruct e. cbn. specialize (H1 tt (n+1)%Z). assumption.
Qed.
