Require Import GHC.Num.
Require Import GHC.MVar.
Require Import Control.Concurrent.MVar.
Require Import Proofs.Control.Concurrency.Interp.

Require Import Locks.

Axiom decode_encode_word : forall (w : Word),
    decode (encode w) = Some w.

Ltac forward := first
                  [apply SafeFinished; reflexivity |
                   eapply SafeRunning; [try reflexivity |] |
                   apply DeadlockBlocked; reflexivity |
                   eapply DeadlockRunning; [try reflexivity |]
                  ].
                   
Theorem example_prog_safe : safe_single_prog example.
Proof.
  do 3 forward.
  - simpl; rewrite decode_encode_word. reflexivity.
  - forward.
Qed.

Lemma deadlock_prog_deadlock : deadlock_single_prog deadlock.
Proof.
  do 2 forward.
Qed.

Theorem deadlock_prog_unsafe : ~ safe_single_prog deadlock.
Proof.
  apply deadlock_unsafe. apply deadlock_prog_deadlock.
Qed.
