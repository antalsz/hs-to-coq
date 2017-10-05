Require Import Bag.
Require Import Coq.Lists.List.
Import ListNotations.

From mathcomp Require Import ssreflect.

Theorem bag_cons_ok {A} (x : A) (b : Bag A) :
  bagToList (consBag x b) = x :: bagToList b.
Proof. elim: b => //. Qed.

Theorem unit_bag_ok {A} (x : A) :
  bagToList (unitBag x) = [ x ].
Proof. reflexivity. Qed.
