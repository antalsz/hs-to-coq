Require Import Prelude.
Require Import CompilerRev.

Import ListNotations.

Lemma comp_correct_helper: forall e s c,
    exec (comp' e c) s = exec c (eval e :: s).
Proof.
  induction e; intros; auto.
  simpl.
  rewrite IHe1.
  rewrite IHe2.
  auto.
Qed.

Theorem comp_correct: forall e,
    exec (comp' e []) [] = Some [eval e].
Proof.
  intros; apply comp_correct_helper; auto.
Qed.