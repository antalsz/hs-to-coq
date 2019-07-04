From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat.
Set Bullet Behavior "Strict Subproofs".

Require Import GHC.Base.

Require Import OrdList.

Require Import Proofs.GHC.Base.
Require Import Proofs.Data.Foldable.

Lemma fromOL_nilOL_nil {a} : OrdList.fromOL OrdList.nilOL = nil :> list a.
Proof. done. Qed.

Lemma appOL_nilOL_right {a} (ol : OrdList.OrdList a) : OrdList.appOL ol OrdList.nilOL = ol.
Proof. by rewrite /OrdList.appOL /=; case: ol. Qed.

Lemma concatOL_map_nilOL_nilOL {a b} (xs : list a) (f : a -> OrdList.OrdList b) :
  (forall x, In x xs -> f x = OrdList.nilOL) -> 
  OrdList.concatOL (map f xs) = OrdList.nilOL.
Proof.
  rewrite /OrdList.concatOL.
  elim: xs => [|x xs IH] //= NIL; hs_simpl.
  rewrite NIL /=; last by left.
  rewrite IH //.
  by move=> y IN; apply NIL; right.
Qed.
