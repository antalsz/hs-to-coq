Require Import Control.Monad.Trans.Reader.
Require Import Data.Functor.Identity.
Require Import Proofs.GHC.Base.
Require Import Proofs.Data.Functor.Identity.

Require Import Coq.Logic.FunctionalExtensionality.

Instance ReaderTFunctorLaws {r} {m} `{(FunctorLaws m)} : FunctorLaws (ReaderT r m).
Proof.
  destruct H0.
  constructor; intros; destruct x; cbn;
    unfold Reader.Functor__ReaderT_fmap, mapReaderT, Base.op_z2218U__;
    f_equal; apply functional_extensionality; intro x; eauto.
Qed.

Instance ReaderFunctorLaws {r} : FunctorLaws (Reader r).
Proof.
  eapply ReaderTFunctorLaws.
  (** This ending must be [Defined] instead of [Qed], because we want
  to expose the fact that [Reader]'s proofs are based on [ReaderT]'s
  proofs, for reusability. *)
Defined. 

Instance ReaderTApplicativeLaws {r} {m} `{FunctorLaws m} `{ApplicativeLaws m} : ApplicativeLaws (ReaderT r m).
Proof.
  destruct H1.
  constructor; intros.
  all: repeat (match goal with
               | [v : ReaderT _ _ _ |- _] =>
                 destruct v
               end);
    cbn; unfold Reader.Applicative__ReaderT_op_zlztzg__, Reader.Applicative__ReaderT_pure.
  - f_equal; apply functional_extensionality; intros;  apply applicative_identity.
  - f_equal; apply functional_extensionality; intros. apply applicative_composition.
  - unfold Base.op_z2218U__, liftReaderT.
    f_equal; apply functional_extensionality; intros. apply applicative_homomorphism.
  - f_equal; apply functional_extensionality; intros. apply applicative_interchange.
  - unfold Reader.Applicative__ReaderT_liftA2, Reader.Applicative__ReaderT_op_zlztzg__; reflexivity.
  - unfold Reader.Functor__ReaderT_fmap, mapReaderT.
    f_equal; apply functional_extensionality; intros. apply applicative_fmap.
Qed.

Instance ReaderApplicativeLaws {r} : ApplicativeLaws (Reader r).
Proof.
  apply ReaderTApplicativeLaws.
Defined.
