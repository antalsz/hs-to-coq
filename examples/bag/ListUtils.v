Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope program_scope.

Require Import Coq.ZArith.ZArith.

Require Data.Foldable.
Require Data.Monoid.
Require Import Proofs.Data.Foldable.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Bullet Behavior "Strict Subproofs".

(***** null *****)

Definition null {A} (l : list A) : bool :=
  match l with
  | []     => true
  | _ :: _ => false
  end.

Theorem app_null {A} (xs ys : list A) :
  null (xs ++ ys) = null xs && null ys.
Proof. case: xs => //=. Qed.

(***** all and any *****)

Fixpoint all {A} (p : A -> bool) (l : list A) : bool :=
  match l with
  | []      => true
  | x :: xs => p x && all p xs
  end.

Fixpoint any {A} (p : A -> bool) (l : list A) : bool :=
  match l with
  | []      => false
  | x :: xs => p x || any p xs
  end.

Theorem all_xpred0 {A} (l : list A) :
  all xpred0 l = null l.
Proof. by case: l. Qed.

Theorem all_xpredT {A} (l : list A) :
  all xpredT l.
Proof. by elim: l. Qed.

Theorem any_xpred0 {A} (l : list A) :
  ~~ any xpred0 l.
Proof. by elim: l. Qed.

Theorem any_xpredT {A} (l : list A) :
  any xpredT l = ~~ null l.
Proof. by case: l. Qed.

Theorem all_app {A} (p : A -> bool) (l1 l2 : list A) :
  all p (l1 ++ l2) = all p l1 && all p l2.
Proof. by elim: l1 => [|x1 l1 IH] //=; rewrite IH andbA. Qed.

Theorem any_app {A} (p : A -> bool) (l1 l2 : list A) :
  any p (l1 ++ l2) = any p l1 || any p l2.
Proof. by elim: l1 => [|x1 l1 IH] //=; rewrite IH orbA. Qed.

Theorem all_ext {A} (p1 p2 : A -> bool) (l : list A) :
  p1 =1 p2 ->
  all p1 l = all p2 l.
Proof. by move=> ext; elim: l => [|x l IH] //=; rewrite ext IH. Qed.

Theorem any_ext {A} (p1 p2 : A -> bool) (l : list A) :
  p1 =1 p2 ->
  any p1 l = any p2 l.
Proof. by move=> ext; elim: l => [|x l IH] //=; rewrite ext IH. Qed.

Theorem allP {A} (p : A -> bool) (l : list A) :
  reflect (Forall p l) (all p l).
Proof.
  elim: l => [|x l IH] /=.
  - by left.
  - case p_x: (p x) => /=.
    + case: IH => [Forall_l | Exists_not_l].
      * by left; constructor.
      * by right; contradict Exists_not_l; inversion Exists_not_l.
    + by right; inversion 1; rewrite ->p_x in *.
Qed.

Theorem anyP {A} (p : A -> bool) (l : list A) :
  reflect (Exists p l) (any p l).
Proof.
  elim: l => [|x l IH] /=.
  - right; inversion 1.
  - case p_x: (p x) => /=.
    + by left; constructor.
    + case: IH => [Exists_l | Forall_not_l].
      * by left; apply Exists_cons_tl.
      * by right; contradict Forall_not_l; inversion Forall_not_l => //=; rewrite ->p_x in *.
Qed.

(***** filter *****)

Theorem filter_app {A} (p : A -> bool) (l1 l2 : list A) :
  filter p (l1 ++ l2) = filter p l1 ++ filter p l2.
Proof.
  elim: l1 => [|x1 l1 IH] //=.
  case: (p x1) => //=.
  by rewrite IH.
Qed.

Theorem filter_xpredT {A} (l : list A) :
  filter xpredT l = l.
Proof. by elim: l => [| ? ? IH] //=; rewrite IH. Qed.

(***** fold_right *****)

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

Theorem hs_coq_any_list {A} (p : A -> bool) (l : list A) :
  Data.Foldable.any p l = any p l.
Proof.
  rewrite /Data.Foldable.any
          /Data.Foldable.foldMap /Foldable.Foldable__list /Foldable.foldMap__
          /= /Data.Foldable.Foldable__list_foldMap
          /Data.Foldable.Foldable__list_foldr /=
          /Base.mempty /SemigroupInternal.Monoid__Any /Base.mempty__
          /SemigroupInternal.Monoid__Any_mempty
          /Base.op_z2218U__.
  rewrite -(orbF (any p l)); move: false => b.
  elim: l => [|x l IH] //=.
  rewrite -orbA -IH /compose /=.
  by case: (GHC.Base.foldr _ _ _); case: (p x).
Qed.

(***** partition *****)

Theorem partition_app {A} (p : A -> bool) (l r : list A) :
  let: (t,  f)  := partition p (l ++ r) in
  let: (lt, lf) := partition p l        in
  let: (rt, rf) := partition p r
  in t = lt ++ rt /\ f = lf ++ rf.
Proof.
  elim: l => [|x l IH] //=.
  - by case: (partition p r).
  - case: (partition p r) (partition p l) (partition p (l ++ r)) IH
      => [rt rf] [lt lf] [? ?] [-> ->].
    by case: (p x).
Qed.

Corollary partition_app_1 {A} (p : A -> bool) (l r : list A) :
  fst (partition p (l ++ r)) = fst (partition p l) ++ fst (partition p r).
Proof.
  by move: (partition p (l ++ r)) (partition p l) (partition p r) (partition_app p l r)
       => [? ?] [? ?] [? ?] [-> ->].
Qed.

Corollary partition_app_2 {A} (p : A -> bool) (l r : list A) :
  snd (partition p (l ++ r)) = snd (partition p l) ++ snd (partition p r).
Proof.
  by move: (partition p (l ++ r)) (partition p l) (partition p r) (partition_app p l r)
       => [? ?] [? ?] [? ?] [-> ->].
Qed.

(***** Zlength *****)

Section Z.

Open Scope Z_scope.

Theorem Zlength_app {A} (l r : list A) :
  Zlength (l ++ r) = Zlength l + Zlength r.
Proof. by rewrite Zlength_correct app_length Nat2Z.inj_add -!Zlength_correct. Qed.

End Z.
