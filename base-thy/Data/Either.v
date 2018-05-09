Require Import GHC.Base.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Proofs.GHC.Base.
Require Import Data.Either.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Bullet Behavior "Strict Subproofs".

Instance EqLaws_Data_Either_Either {a b} `{EqLaws a} `{EqLaws b} : EqLaws (Either a b).
Proof.
  split; repeat unfold op_zeze__, op_zsze__, op_zeze____, op_zsze____,
  Either.Eq___Either,
  Either.Eq___Either_op_zeze__,
  Either.Eq___Either_op_zsze__.
  - case=> ? /=; apply Eq_refl.
  - do 2 case=> ? //=; apply Eq_sym.
  - do 3 case=> ? //=; apply Eq_trans.
  - do 2 case => ? //=; rewrite negb_involutive; reflexivity.
Qed.

Instance EqExact_Data_Either_Either {a b} `{EqExact a} `{EqExact b} : EqExact (Either a b).
Proof.
  split ;
    unfold op_zeze__, op_zsze__,
    Eq___Either ,  op_zeze____, op_zsze____=> - [xl|xr] [yl|yr] //=; try (by constructor);
    case E: (_ == _); constructor; move/Eq_eq in E;
    by [rewrite E | contradict E; case: E].
Qed.

Instance instance_FunctorLaws_Data_Either_Either {a} : FunctorLaws (Either a).
Proof.
  split; repeat unfold fmap, instance_GHC_Base_Functor__Data_Either_Either_a_,
         Either.Functor__Either.
  - intros. destruct x. auto.
    auto.
  - intros. destruct x. auto.
    unfold "_∘_". auto.
Qed.

Instance instance_ApplicativeLaws_Data_Either_Either {a} : ApplicativeLaws (Either a).
Proof.
  split;
    repeat (unfold pure, instance_Applicative__Data_Either_Either_a_,
    Either.Applicative__Either_pure,
    Either.Applicative__Either_op_zlztzg__,
    Either.Functor__Either_fmap; simpl).
  - intros. destruct v; auto.
  - intros. destruct u; destruct v; destruct w; auto.
  - intros. auto.
  - intros. destruct u; auto.
  - intros. destruct x, y; auto.
  - by move=> ? ? f [].
Qed.

Instance instance_MonadLaws_Data_Either_Either {a} : MonadLaws (Either a).
Proof.
  split; intros;
   repeat (unfold pure, Either.Applicative__Either,
    Either.Applicative__Either_pure,
    Either.Applicative__Either_op_zlztzg__,
    Either.Functor__Either_fmap,
    Either.Monad__Either_return_,
    Either.Monad__Either_op_zgzgze__; simpl).
  - auto.
  - destruct m; auto.
  - destruct m; try destruct (k x); auto.
  - auto.
  - auto.
Qed.
