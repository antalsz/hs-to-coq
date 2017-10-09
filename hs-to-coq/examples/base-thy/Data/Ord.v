Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import Data.Ord.

From mathcomp Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".

Instance EqLaws_Down {a} `{EqLaws a} : EqLaws (Down a).
Proof.
  split.
  - case=> * /=; apply Eq_refl.
  - do 2 case=> ? //=; apply Eq_sym.
  - do 3 case=> ? //=; apply Eq_trans.
  - do 2 case=> ? //=; apply Eq_inv.
Qed.

Instance EqExact_Down {a} `{EqExact a} : EqExact (Down a).
Proof.
  split=> - [x] [y] /=.
  case E: (x == y); constructor; move/Eq_eq in E.
  + by rewrite E.
  + by contradict E; case: E.
Qed.
