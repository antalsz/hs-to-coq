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

(***** filter *****)

Theorem filter_app {A} (p : A -> bool) (l1 l2 : list A) :
  filter p (l1 ++ l2) = filter p l1 ++ filter p l2.
Proof.
  elim: l1 => [|x1 l1 IH] //=.
  case: (p x1) => //=.
  by rewrite IH.
Qed.

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
