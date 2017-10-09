Require Import Bag.

Require Import Data.Foldable.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import ListUtils.

From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Bullet Behavior "Strict Subproofs".

(**** Bag invariant *****)

Fixpoint well_formed_bag {A} (b : Bag A) : bool :=
  match b with
  | Mk_EmptyBag              => true
  | Mk_UnitBag _             => true
  | Mk_TwoBags Mk_EmptyBag _ => false
  | Mk_TwoBags _ Mk_EmptyBag => false
  | Mk_TwoBags l r           => well_formed_bag l && well_formed_bag r
  | Mk_ListBag []            => false
  | Mk_ListBag (_ :: _)      => true
  end.
Arguments well_formed_bag _ : simpl nomatch.

Theorem eval_wf_TwoBags {A} (l r : Bag A) :
  well_formed_bag (Mk_TwoBags l r) =
  [&& ~~ isEmptyBag l, ~~ isEmptyBag r, well_formed_bag l & well_formed_bag r].
Proof. by case: l; case: r. Qed.

(***** Universal quantification over bags ****)

(* Someday should be `allBag`, which isn't in 8.0.2's `Bag.hs`, but is in 8.2's *)
Fixpoint all_bag {A} (p : A -> bool) (b : Bag A) : bool :=
  match b with
  | Mk_EmptyBag    => true
  | Mk_UnitBag x   => p x
  | Mk_TwoBags l r => all_bag p l && all_bag p r
  | Mk_ListBag xs  => all p xs
  end.

Theorem all_bag_xpredT {A} (b : Bag A) :
  all_bag xpredT b.
Proof.
  elim: b => [| x | l IHl r IHr | xs] //=.
  - by rewrite IHl IHr.
  - apply all_xpredT.
Qed.

(***** Bag correctness theorems *****)

Lemma foldr_wf {A B} (p : A -> bool) (f : A -> Bag B -> Bag B) (z : Bag B) :
  (forall x b, p x -> well_formed_bag b -> well_formed_bag (f x b)) ->
  well_formed_bag z ->
  forall xs : list A, all p xs -> well_formed_bag (foldr f z xs).
Proof. by move=> f_wf z_wf xs; elim: xs => [|x xs IH] //= /andP [? ?]; apply f_wf, IH. Qed.

Corollary foldr_wf' {A B} (f : A -> Bag B -> Bag B) (z : Bag B) :
  (forall x b, well_formed_bag b -> well_formed_bag (f x b)) ->
  well_formed_bag z ->
  forall xs : list A, well_formed_bag (foldr f z xs).
Proof.
  move=> f_wf z_wf xs; apply (foldr_wf xpredT) => //=.
  - by move=> *; apply f_wf.
  - apply all_xpredT.
 Qed.

Theorem unitBag_wf {A} (x : A) :
  well_formed_bag (unitBag x).
Proof. done. Qed.

Theorem unionBags_wf {A} (b1 b2 : Bag A) :
  well_formed_bag b1 -> well_formed_bag b2 ->
  well_formed_bag (unionBags b1 b2).
Proof. case: b1; case: b2 => * //=; intuition. Qed.

Theorem unionManyBags_wf {A} (bs : list (Bag A)) :
  all well_formed_bag bs ->
  well_formed_bag (unionManyBags bs).
Proof. rewrite /unionManyBags; apply foldr_wf => //=; apply unionBags_wf. Qed.

Theorem snocBag_wf {A} (b : Bag A) (x : A) :
  well_formed_bag b ->
  well_formed_bag (snocBag b x).
Proof. by move=> wf; rewrite /snocBag; apply unionBags_wf. Qed.

Theorem mapBag_wf {A B} (f : A -> B) (b : Bag A) :
  well_formed_bag b ->
  well_formed_bag (mapBag f b).
Proof.
  elim: b => [| x | l IHl r IHr | xs] //=.
  - rewrite !eval_wf_TwoBags => /and4P[]*; apply/and4P; split => //=.
    + by destruct l.
    + by destruct r.
    + by apply IHl.
    + by apply IHr.
  - by case: xs.
Qed.

(* TODO mapBagM mapBagM_ mapAndUnzipBagM *)

(* Not strictly necessary, but useful later *)
Lemma foldrBag_wf {A B} (p : A -> bool) (f : A -> Bag B -> Bag B) (z : Bag B) :
  (forall x b, p x -> well_formed_bag b -> well_formed_bag (f x b)) ->
  well_formed_bag z ->
  forall b : Bag A, all_bag p b -> well_formed_bag (foldrBag f z b).
Proof.
  move=> f_wf z_wf b; elim: b z z_wf => [| x | l IHl r IHr | xs] //= z z_wf.
  - by move=> wf; apply f_wf.
  - by move => /andP [wf_l wf_r]; apply IHl; first apply IHr.
  - by apply foldr_wf.
Qed.

(* Not strictly necessary, but useful later *)
Lemma foldrBag_wf' {A B} (f : A -> Bag B -> Bag B) (z : Bag B) :
  (forall x b, well_formed_bag b -> well_formed_bag (f x b)) ->
  well_formed_bag z ->
  forall b : Bag A, well_formed_bag (foldrBag f z b).
Proof.
  move=> f_wf z_wf b; apply (foldrBag_wf xpredT) => //=.
  - by move=> *; apply f_wf.
  - apply all_bag_xpredT.
 Qed.

Theorem listToBag_wf {A} (l : list A) :
  well_formed_bag (listToBag l).
Proof. by case: l. Qed.

Theorem partitionBag_wf {A} (p : A -> bool) (b : Bag A) :
  let: (bt, bf) := partitionBag p b
  in well_formed_bag bt && well_formed_bag bf.
Proof.
  elim: b => [| x | l IHl r IHr | xs] //=.
  - by case: (p x).
  - case: (partitionBag p l) IHl => [lt lf] /andP[] IHlt IHlf;
    case: (partitionBag p r) IHr => [rt rf] /andP[] IHrt IHrf.
    by rewrite !unionBags_wf.
  - by case: (Data.OldList.partition p xs) => *; rewrite !listToBag_wf.
Qed.

(* TODO flatMapBagM flatMapBagPairM *)

Theorem filterBag_wf {A} (p : A -> bool) (b : Bag A) :
  well_formed_bag (filterBag p b).
Proof.
  elim: b => [| x | l IHl r IHr | xs] //=.
  - by case: (p x).
  - by apply unionBags_wf.
  - by apply listToBag_wf.
Qed.

(* TODO filterBagM *)

Theorem emptyBag_wf {A} : well_formed_bag (@Mk_EmptyBag A).
Proof. done. Qed.

Theorem consBag_wf {A} (x : A) (b : Bag A) :
  well_formed_bag b ->
  well_formed_bag (consBag x b).
Proof. by move=> wf; rewrite /consBag; apply unionBags_wf. Qed.

Theorem concatBag_wf {A} (bb : Bag (Bag A)) :
  all_bag well_formed_bag bb ->
  well_formed_bag (concatBag bb).
Proof. rewrite /concatBag; apply foldrBag_wf => //=; apply unionBags_wf. Qed.

Theorem catBagMaybes_wf {A} (b : Bag (option A)) :
  well_formed_bag (catBagMaybes b).
Proof.
  rewrite /catBagMaybes; apply foldrBag_wf' => [[x|] b'|] //=.
  apply consBag_wf.
Qed.
