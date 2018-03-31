Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import Data.Ord.

From mathcomp Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".

Instance EqLaws_Down {a} `{EqLaws a} : EqLaws (Down a).
Proof.
  split;
  unfold op_zeze__, op_zsze__;
  unfold Ord.Eq___Down;
  unfold op_zeze____, op_zsze____;
  unfold Ord.Eq___Down_op_zsze__;
  unfold Ord.Eq___Down_op_zeze__;
  unfold coerce, Coercible_Unpeel, unpeel, repeel, Unpeel_refl;
  unfold "_==_";
  unfold "_/=_".

  - case=> * /=; apply Eq_refl.
  - do 2 case=> ? //=; apply Eq_sym.
  - do 3 case=> ? //=; apply Eq_trans.
  - do 2 case=> ? //=; apply Eq_inv.
Qed.

Instance EqExact_Down {a} `{EqExact a} : EqExact (Down a).
Proof.
  split;
  unfold op_zeze__, op_zsze__;
  unfold Ord.Eq___Down;
  unfold op_zeze____, op_zsze____;
  unfold Ord.Eq___Down_op_zsze__;
  unfold Ord.Eq___Down_op_zeze__;
  unfold coerce, Coercible_Unpeel, unpeel, repeel, Unpeel_refl;
  unfold Unpeel_arrow, Unpeel_Down, unpeel, repeel.
  unfold Eq___Down
     => - [x] [y] /=.
  case E: (x == y); constructor; move/Eq_eq in E.
  + by rewrite E.
  + by contradict E; case: E.
Qed.
