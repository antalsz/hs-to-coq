Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import Data.Proxy.

From Coq Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".

Instance EqLaws_Proxy {a} : EqLaws (Proxy a).
Proof. by split. Qed.

Instance EqExact_Proxy {a} : EqExact (Proxy a).
Proof. by split; repeat case; constructor. Qed.
