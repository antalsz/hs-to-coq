Require Import Prelude.
Require Import CompilerRev.

Import ListNotations.

Ltac applying f := unfold f; fold f.

(* A version of the proof that goes into as much detail
   as Hutton does. *)
Lemma comp_correct_helper: forall e s c,
    exec (comp' e c) s = exec c (eval e :: s).
Proof.
  induction e; intros.
  - applying comp'.
    applying exec.
    applying (eval).
    reflexivity.
  - applying comp'.
    rewrite IHe1.
    rewrite IHe2.
    applying exec.
    applying (eval).
    reflexivity.
Qed.

Theorem comp_correct: forall e,
    exec (comp e) [] = Some [eval e].
Proof.
  intros; apply comp_correct_helper; auto.
Qed.