Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope program_scope.

From mathcomp Require Import ssreflect ssrfun ssrbool.
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
