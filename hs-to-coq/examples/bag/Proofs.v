Require Import Bag.
Require Import Coq.Lists.List.
Import ListNotations.

From mathcomp Require Import ssreflect.
Set Bullet Behavior "Strict Subproofs".

Theorem unit_bag_ok {A} (x : A) :
  bagToList (unitBag x) = [ x ].
Proof. reflexivity. Qed.

(* TODO: prove that Coq fold_right is the same as GHC foldr *)

Lemma fold_right_cons {A} (tail l : list A) :
  fold_right cons tail l = l ++ tail.
Proof.
  elim: l => [| x l IH] //=.
  by rewrite IH.
Qed.

Corollary fold_right_cons_nil {A} (l : list A) :
  fold_right cons [] l = l.
Proof. by rewrite fold_right_cons app_nil_r. Qed.

Theorem foldrBag_ok {A R} (f : A -> R -> R) (z : R) (b : Bag A) :
  foldrBag f z b = fold_right f z (bagToList b).
Proof.
  elim: b R f z => [|x | l IHl r IHr | xs] //= R f z.
  - rewrite /bagToList /=.
    rewrite (IHr _ cons []) fold_right_cons_nil.
    rewrite !IHl IHr.
    by rewrite -fold_right_app fold_right_cons.
  - by rewrite /bagToList /= fold_right_cons_nil.
Qed.

Theorem unionBags_ok {A} (b1 b2 : Bag A) :
  bagToList (unionBags b1 b2) = bagToList b1 ++ bagToList b2.
Proof.
  by case: b1 => *; case: b2 => *;
     rewrite /bagToList //=
             ?foldrBag_ok ?fold_right_cons_nil ?fold_right_cons
             ?app_assoc ?app_nil_r.
Qed.

Theorem bag_cons_ok {A} (x : A) (b : Bag A) :
  bagToList (consBag x b) = x :: bagToList b.
Proof. elim: b => //. Qed.
