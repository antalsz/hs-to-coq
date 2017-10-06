Require Import Bag.

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

Theorem wf_inv_TwoBags {A} (l r : Bag A) :
  well_formed_bag (Mk_TwoBags l r) ->
  l <> Mk_EmptyBag /\ r <> Mk_EmptyBag /\
  well_formed_bag l /\ well_formed_bag r.
Proof.
  by elim: l => //=; elim: r => //= *;
     match goal with [wf : is_true (_ && _) |- _] => move: wf => /andP end;
     split => //=.
Qed.

Theorem wf_inv_ListBag {A} (xs : list A) :
  well_formed_bag (Mk_ListBag xs) ->
  xs <> [].
Proof. by case: xs. Qed.

Theorem eval_wf_TwoBags {A} (l r : Bag A) :
  well_formed_bag (Mk_TwoBags l r) =
  [&& ~~ isEmptyBag l, ~~ isEmptyBag r, well_formed_bag l & well_formed_bag r].
Proof. by case: l; case: r. Qed.

(***** Bag correctness theorems *****)

Theorem unitBag_ok {A} (x : A) :
  bagToList (unitBag x) = [ x ].
Proof. reflexivity. Qed.

(* TODO: prove that Coq fold_right is the same as GHC foldr *)

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

Lemma bagToList_TwoBags {A} (l r : Bag A) :
  bagToList (Mk_TwoBags l r) = bagToList l ++ bagToList r.
Proof.
  by rewrite /bagToList //= !foldrBag_ok !fold_right_cons_nil !fold_right_cons.
Qed.

Theorem unionBags_ok {A} (b1 b2 : Bag A) :
  bagToList (unionBags b1 b2) = bagToList b1 ++ bagToList b2.
Proof. by case: b1 => *; case: b2 => *; rewrite -bagToList_TwoBags. Qed.

Theorem unionManyBags_ok {A} (bs : list (Bag A)) :
  bagToList (unionManyBags bs) = concat (map bagToList bs).
Proof.
  rewrite /unionManyBags; elim: bs => [|b bs IH] //=.
  by rewrite unionBags_ok IH.
Qed.

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
    apply hs_coq_map.
Qed.

Theorem bagToList_listToBag {A} (l : list A) :
  bagToList (listToBag l) = l.
Proof. by elim: l => [| x l IH] //=; rewrite /bagToList /= fold_right_cons_nil. Qed.

(* Is there a partial inverse theorem?  The direct inverse isn't true because
   there are multiple equivalent bags -- for example, `ListBag [x]` and
   `UnitBag x`. *)

Theorem isEmptyBag_ok {A} (b : Bag A) :
  well_formed_bag b ->
  isEmptyBag b = null (bagToList b).
Proof.
  elim: b => [| x | l IHl r IHr | xs] //=.
  - rewrite eval_wf_TwoBags => /and4P [nel ner wfl wfr] *.
    rewrite bagToList_TwoBags app_null.
    by rewrite -IHl // -IHr // (negbTE nel).
  - by case: xs.
Qed.

Theorem foldBag_ok {A R} (f : R -> R -> R) (u : A -> R) (z : R) (b : Bag A) :
  associative f ->
  foldBag f u z b = fold_right f z (map u (bagToList b)).
Proof.
  move=> f_assoc.
  elim: b z => [| x | l IHl r IHr | xs] //= z; rewrite /bagToList /=.
  - rewrite !foldrBag_ok fold_right_cons_nil fold_right_cons.
    by rewrite IHl IHr  -fold_right_app map_app.
  - by rewrite fold_right_cons_nil fold_right_map.
Qed.

Theorem filterBag_ok {A} (p : A -> bool) (b : Bag A) :
  bagToList (filterBag p b) = filter p (bagToList b).
Proof.
  elim: b => [| x | l IHl r IHr | xs] //=.
  - by case: (p x).
  - by rewrite unionBags_ok bagToList_TwoBags filter_app IHl IHr.
  - rewrite bagToList_listToBag /bagToList /= fold_right_cons_nil.
    apply hs_coq_filter.
Qed.

Theorem emptyBag_ok {A} : bagToList (@Mk_EmptyBag A) = [].
Proof. reflexivity. Qed.

Theorem consBag_ok {A} (x : A) (b : Bag A) :
  bagToList (consBag x b) = x :: bagToList b.
Proof. elim: b => //. Qed.

Definition concatBag {A} (bb : Bag (Bag A)) :
  bagToList (concatBag bb) = concat (map bagToList (bagToList bb)).
Proof.
  rewrite /concatBag foldrBag_ok.
  elim: (bagToList bb) => [|b bs IH] //=.
  by rewrite unionBags_ok IH.
Qed.

Definition catBagMaybes {A} (b : Bag (option A)) :
  bagToList (catBagMaybes b) =
  flat_map (fun o => match o with Some x => [x] | None => [] end) (bagToList b).
Proof.
  rewrite /catBagMaybes foldrBag_ok.
  elim: (bagToList b) => [|[x|] xs IH] //=.
  by rewrite consBag_ok IH.
Qed.
