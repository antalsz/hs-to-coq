Require Import Log.
Require Import GHC.Base.

Lemma length_bind : forall m1 m2,
    length (collect (m1 >> m2)) = length (collect (m2 >> m1)).
Proof.
  intros m1 m2.
  unfold collect, op_zgzg__.  simpl.
Abort.

Definition m1 : Output unit := MkOutput (fun s => (tt, nil)).
Definition m2 : Output unit := out 65%N.

Goal length (collect (m1 >> m2)) <> length (collect (m2 >> m1)).
Proof.
  compute. congruence.
Qed.

