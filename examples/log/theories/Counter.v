Require Import Counter.

Require Import GHC.Base.
Require Import Psatz.

Definition equiv_res_Counter {A} (m1 m2 : Counter A) : Prop :=
  forall n,
    let (_, a) := runC m1 n in
    let (_, b) := runC m2 n in
    a = b.

Definition ge_res_Counter {A} (m1 m2 : Counter A) : Prop :=
  forall n,
    let (_, a) := runC m1 n in
    let (_, b) := runC m2 n in
    (a >= b)%Z.

Notation "a ≊ b" := (equiv_res_Counter a b) (at level 100).
Notation "a ⪎ b" := (ge_res_Counter a b) (at level 100).

Lemma computation_ex1:
  inc >> inc ⪎ inc.
Proof.
  unfold ge_res_Counter.
  apply Z.peano_ind.
  - cbv. congruence.
  - intros x. cbn. intros. lia.
  - intros x. cbn. intros. lia.
Qed.

Theorem commutativity : forall A (m1 m2 : Counter A),
  m1 >> m2 ≊ m2 >> m1.
Abort.

Definition m1 : Counter unit := MkCounter (fun _ => (tt, #0)).
