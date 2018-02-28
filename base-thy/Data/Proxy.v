Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import Data.Proxy.

From mathcomp Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".

Instance HasOk_Either {a} : HasOk (Proxy a) :=
  { IsOk _ := True }.

Instance EqLaws_Proxy {a} : EqLaws (Proxy a).
Proof. by split. Qed.

Instance EqExact_Proxy {a} : EqExact (Proxy a).
Proof. by split; repeat case; constructor. Qed.
