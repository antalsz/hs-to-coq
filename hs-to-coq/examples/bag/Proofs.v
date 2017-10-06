Require Import Bag.
Require GHC.List.

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope program_scope.

From mathcomp Require Import ssreflect ssrfun ssrbool.
Set Bullet Behavior "Strict Subproofs".

(**** Lists *****)

Theorem fold_right_cons {A} (tail l : list A) :
  fold_right cons tail l = l ++ tail.
Proof.
  elim: l => [| x l IH] //=.
  by rewrite IH.
Qed.

Corollary fold_right_cons_nil {A} (l : list A) :
  fold_right cons [] l = l.
Proof. by rewrite fold_right_cons app_nil_r. Qed.

Theorem fold_right_map {A B C} (f : B -> C -> C) (z : C) (g : A -> B) (l : list A) :
  fold_right f z (map g l) = fold_right (f ∘ g) z l.
Proof.
  elim: l => [|x l IH] //=.
  by rewrite IH.
Qed.

Theorem fold_right_fold_right {A} (f : A -> A -> A) (z : A) (l1 l2 : list A) :
  associative f -> left_id z f ->
  fold_right f (fold_right f z l2) l1 = f (fold_right f z l1) (fold_right f z l2).
Proof.
  move=> f_assoc z_left_id.
  elim: l1 => [|x1 l1 IH] //=.
  by rewrite IH f_assoc.
Qed.

Theorem filter_app {A} (p : A -> bool) (l1 l2 : list A) :
  filter p (l1 ++ l2) = filter p l1 ++ filter p l2.
Proof.
  elim: l1 => [|x1 l1 IH] //=.
  case: (p x1) => //=.
  by rewrite IH.
Qed.

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
    admit. (* Coq map vs. Haskell map *)
Admitted.

Theorem bagToList_listToBag {A} (l : list A) :
  bagToList (listToBag l) = l.
Proof. by elim: l => [| x l IH] //=; rewrite /bagToList /= fold_right_cons_nil. Qed.

(* Is there a partial inverse theorem?  The direct inverse isn't true because
   there are multiple equivalent bags -- for example, `ListBag [x]` and
   `UnitBag x`. *)

Lemma app_null {A} (xs ys : list A) :
  GHC.List.null (xs ++ ys) = GHC.List.null xs && GHC.List.null ys.
Proof. case: xs => //=. Qed.

Theorem isEmptyBag_ok {A} (b : Bag A) :
  well_formed_bag b ->
  isEmptyBag b = GHC.List.null (bagToList b).
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
    admit. (* Coq filter vs. Haskell filter *)
Admitted.

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
