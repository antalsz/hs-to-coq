Require Import Bag.
From mathcomp Require Import ssreflect.

Theorem bag_cons_ok {A} (x : A) (b : Bag A) :
  bagToList (consBag x b) = cons x (bagToList b).
Proof.
  elim: b => //=.
Qed.
