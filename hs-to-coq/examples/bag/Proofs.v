Require Import Bag.
Require Import Coq.Lists.List.
Import ListNotations.

From mathcomp Require Import ssreflect ssrfun.
Set Bullet Behavior "Strict Subproofs".

Theorem unitBag_ok {A} (x : A) :
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

Theorem consBag_ok {A} (x : A) (b : Bag A) :
  bagToList (consBag x b) = x :: bagToList b.
Proof. elim: b => //. Qed.

Theorem snocBag_ok {A} (b : Bag A) (x : A) :
  bagToList (snocBag b x) = bagToList b ++ [x].
Proof. by rewrite /snocBag unionBags_ok unitBag_ok. Qed.

Theorem mapBag_ok {A B} (f : A -> B) (b : Bag A) :
  bagToList (mapBag f b) = map f (bagToList b).
Proof.
  elim: b => [| x | l IHl r IHr | xs] //=.
  - rewrite /bagToList /=.
    rewrite !foldrBag_ok !fold_right_cons_nil !fold_right_cons.
    rewrite IHl IHr.
    by rewrite map_app.
  - rewrite /bagToList /= !fold_right_cons_nil.
    admit. (* Coq map vs. Haskell map *)
Admitted.

Theorem bagToList_listToBag {A} (l : list A) :
  bagToList (listToBag l) = l.
Proof. by elim: l => [| x l IH] //=; rewrite /bagToList /= fold_right_cons_nil. Qed.

(* Is there a partial inverse theorem?  The direct inverse isn't true because
   there are multiple equivalent bags -- for example, `ListBag [x]` and
   `UnitBag x`. *)
