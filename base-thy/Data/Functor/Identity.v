Require Import Data.Functor.Identity.
Require Import Proofs.GHC.Base.

Instance instance_FunctorLaws_identity : FunctorLaws Identity.
Proof.
  constructor; intros; destruct x; reflexivity.
Qed.

Instance instance_ApplicativeLaws_identity : ApplicativeLaws Identity.
Proof.
  constructor; intros; cbn.
  all: repeat (match goal with
               | [v : Identity ?a |- _] =>
                 destruct v
               | _ => reflexivity
               end).
Qed.                 

Instance instance_MonadLaws_identity : MonadLaws Identity.
Proof.
  constructor; intros; cbn; try reflexivity.
  destruct m. reflexivity.
Qed.
