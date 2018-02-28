(******************************************************************************)
(** Imports **)

(* SSReflect *)
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
Set Bullet Behavior "Strict Subproofs".

(* Basic Haskell libraries *)
Require Import GHC.Base      Proofs.GHC.Base.
Require Import GHC.List      Proofs.GHC.List.
Require Import GHC.Enum.
Require Import Data.Foldable Proofs.Data.Foldable.
Require Import Data.OldList  Proofs.Data.OldList.

(* IntSet for non-IntSet theorems *)
Require IntSetProofs.

(******************************************************************************)
(** Name dismabiguation -- MUST BE COPIED LOCALLY **)

Notation list    := Coq.Init.Datatypes.list.
Notation seq     := Coq.Lists.List.seq.
Notation reflect := ssrbool.reflect.
  (* Why do I need `reflect`?  What other `reflect` is in scope? *)

(******************************************************************************)
(** Notation disambiguation **)

Infix "=="  := op_zeze__ : bool_scope.
Infix "===" := eq_op (at level 70, no associativity) : bool_scope.

Notation "x == y :> A"  := (op_zeze__ (x : A) (y : A)) : bool_scope.
Notation "x === y :> A" := (eq_op     (x : A) (y : A)) (at level 70, y at next level, no associativity) : bool_scope.

(******************************************************************************)
(** Easier simplification **)

Global Arguments "$"          {_ _}     / _ _.
Global Arguments id           {_}       / _.
Global Arguments Datatypes.id {_}       / _.
Global Arguments "∘"          {_ _}     _ _ _ /.

(******************************************************************************)
(** bool **)

Theorem bool_eq_iff (b1 b2 : bool) : b1 = b2 <-> (b1 <-> b2).
Proof.
  move: b1 b2 => [] [] //.
  all: split; try solve[discriminate | case=> *; exfalso; auto].
Qed.  

(******************************************************************************)
(** EqTypes **)

(* EqType <-> EqExact translation *)

Theorem eqType_EqExact {A : eqType} `{EqExact A} (x y : A) : (x === y) = (x == y).
Proof. by case E: (x === y); case E': (x == y)=> //; move: E E' => /eqP ? /Eq_eq ?. Qed.

Theorem EqExact_eqType {A : eqType} `{EqExact A} (x y : A) : (x == y) = (x === y).
Proof. by rewrite eqType_EqExact. Qed.

(* EqExact decidability *)

Theorem EqExact_cases {A} `{EqExact A} (x y : A) :
  {x == y /\ x = y} + {x /= y /\ x <> y}.
Proof.
  replace (x /= y) with (~~ (x == y)).
  * destruct (Eq_eq x y).
    - apply left. intuition.
    - apply right. intuition.
  * rewrite Eq_exact_inv negb_involutive. reflexivity.
Qed.

Corollary EqExact_dec {A} `{EqExact A} (x y : A) :
  {x = y} + {x <> y}.
Proof. generalize (EqExact_cases x y); tauto. Qed.

(* Int is an EqType *)

Lemma Int_eqbP : Equality.axiom (_==_ : Int -> Int -> bool).
Proof. exact Eq_eq. Qed.

Canonical Int_eqMixin := EqMixin Int_eqbP.
Canonical Int_eqType := Eval hnf in EqType Int Int_eqMixin.

(******************************************************************************)
(** Foldable and lists **)

Theorem Foldable_and_all {F} `{Foldable F} : and (t := F) =1 all id.
Proof. done. Qed.

Theorem Foldable_all_ssreflect {A} (p : A -> bool) (xs : list A) : all p xs = seq.all p xs.
Proof. by rewrite IntSetProofs.Foldable_all_forallb. Qed.

Theorem hs_coq_reverse_rev {A} (xs : list A) : reverse xs = rev xs.
Proof.
  rewrite /reverse.
  replace (rev xs) with (rev xs ++ [::]) by rewrite app_nil_r //.
  elim: xs [::] => [|x xs IH] //= acc.
  by rewrite IH -app_assoc.
Qed.

(******************************************************************************)
(** List membership (`elem`, `In`, `\in`) **)

Theorem elem_in {A : eqType} `{EqExact A} (xs : list A) (a : A) :
  elem a xs = (a \in xs).
Proof. by elim: xs => [|x xs IH] //=; rewrite inE -IH eqType_EqExact. Qed.

Theorem in_elem {A : eqType} `{EqExact A} (xs : list A) (a : A) :
  a \in xs = elem a xs.
Proof. symmetry; apply elem_in. Qed.

Theorem elemN {A} `{Eq_ A} (a : A) : elem a [::] = false.
Proof. done. Qed.

Theorem elemC {A} `{Eq_ A} (a x : A) (xs : list A) : elem a (x :: xs) = (a == x) || elem a xs.
Proof. done. Qed.

Theorem elemP {A} `{EqExact A} (x : A) (xs : list A) :
  reflect (In x xs) (elem x xs).
Proof.
  elim: xs => [|y ys IH] //=; first by constructor.
  rewrite elemC; case CMP: (x == y) => /=.
  - by constructor; left; symmetry; apply/Eq_eq.
  - apply/equivP; first exact IH.
    split; first by right.
    case=> // ?; subst.
    destruct (Eq_eq x x); try congruence.
Qed.

Theorem elem_app {A} `{Eq_ A} (a : A) (xs ys : list A) :
  elem a (xs ++ ys) = elem a xs || elem a ys.
Proof. by elim: xs => [|x xs] //=; rewrite !elemC -orbA => ->. Qed.

Theorem elem_by_In {A} `{EqExact A} (xs : list A) (x : A) :
  reflect (In x xs) (elem_by _==_ x xs).
Proof.
  elim: xs => [|x' xs IH] /=; first by constructor.
  apply iff_reflect; split;
    try move=> /orP;
    move=> [? | ?];
    try apply/orP;
    solve [by left; apply/Eq_eq | by right; apply/IH].
Qed.

(* Non-Haskell theorems about In *)

Theorem InP {A : eqType} (x : A) (xs : list A) :
  reflect (In x xs) (x \in xs).
Proof.
  elim: xs => [|y ys IH] //=.
  - by rewrite seq.in_nil; constructor.
  - rewrite inE; case CMP: (x === y) => /=.
    + by constructor; left; apply/eqP; rewrite eq_sym.
    + apply/equivP; first exact IH.
      split; first by right.
      case=> // ?; subst.
      by move: CMP; rewrite eq_refl.
Qed.

Theorem In_split {A} (x : A) (xs : list A) :
  In x xs <->
  exists pre post, xs = pre ++ x :: post.
Proof.
  split.
  - elim: xs => [|x' xs IH] //= [? | IN]; first subst x'.
    + by exists [::], xs.
    + move: (IH IN) => [pre [post ->]].
      by exists (x' :: pre), post.
  - move=> [pre [post ->]].
    by elim: pre => [|p pre IH] //=; [left | right].
Qed.

(******************************************************************************)
(** Enum **)

(* Missing function *)
Fixpoint iterates (n : nat) {a} (f : a -> a) (z : a) : list a :=
  match n with
  | O    => nil
  | S n' => z :: iterates n' f (f z)
  end.

Lemma eftInt_aux_fuel_case (x y : Int) (p : GHC.Enum.eftInt_aux_fuel x y) :
  (exists (gt : (x >? y)%Z = true),                  p = @GHC.Enum.done x y gt) \/
  (exists (p' : GHC.Enum.eftInt_aux_fuel (x+1)%Z y), p = @GHC.Enum.step x y p').
Proof.
  case: p => [x' y' gt | x' y' p'].
  - by left; exists gt.
  - by right; exists p'.
Qed.

Theorem eftInt_aux_iterates (from to : Int) p :
  @GHC.Enum.eftInt_aux from to p = iterates (Z.to_nat (to - from + #1)) (fun x => x + #1) from.
Proof.
  move: to p.
  elim: from => [| from IHfrom | from IHfrom].
  - elim=> [| to IHto | to IHto].
    + move=> p; move: (eftInt_aux_fuel_case _ _ p) => [[gt def_p] | [p' def_p]]; subst p.
      * by contradict gt.
      * admit.
    + simpl.
Admitted.

Require Import GHC.Num.
Theorem enumFromTo_Int_iterates (from to : Int) :
  enumFromTo from to = iterates (Z.to_nat (to - from + #1)) (fun x => x + #1) from.
Proof. apply eftInt_aux_iterates. Qed.
