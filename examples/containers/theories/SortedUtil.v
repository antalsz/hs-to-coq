(******************************************************************************)
(** Imports **)

(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

(* SSReflect *)
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
Set Bullet Behavior "Strict Subproofs".

(* Sortedness *)
Require Import Coq.Sorting.Sorted Coq.Sorting.Permutation.

(* Basic Haskell libraries *)
Require Import GHC.Base      Proofs.GHC.Base.
Require Import Data.Foldable Proofs.Data.Foldable.
Require Import Data.OldList  Proofs.Data.OldList.

(* Working with Haskell *)
Require Import SortSorted.
Require Import OrdTactic.
Require Import HSUtil.

(******************************************************************************)
(** Name dismabiguation -- copied from HSUtil **)

Notation list    := Coq.Init.Datatypes.list.
Notation seq     := Coq.Lists.List.seq.
Notation reflect := ssrbool.reflect.

(******************************************************************************)
(** Basic facts about StronglySorted **)

Theorem StronglySorted_R_ext' {A} (R1 R2 : A -> A -> Prop) (xs : list A) :
  (forall a b, R1 a b <-> R2 a b) ->
  StronglySorted R1 xs -> StronglySorted R2 xs.
Proof.
  move=> R12_iff; elim: xs => [|x xs IH] SS1; first by constructor.
  inversion SS1 as [|x' xs' SS1' All1]; subst x' xs'.
  constructor; first by apply IH.
  eapply Forall_impl; last exact All1.
  apply R12_iff.
Qed.

Corollary StronglySorted_R_ext {A} (R1 R2 : A -> A -> Prop) (xs : list A) :
  (forall a b, R1 a b <-> R2 a b) ->
  StronglySorted R1 xs <-> StronglySorted R2 xs.
Proof. by split; apply StronglySorted_R_ext'; last symmetry. Qed.

Theorem StronglySorted_snoc {A} (R : A -> A -> Prop) (x : A) (xs : list A) :
  StronglySorted R xs -> Forall (R^~ x) xs -> StronglySorted R (xs ++ [:: x]).
Proof.
  elim: xs => [|x' xs IH] /= SS' AllRev'; first by constructor.
  inversion SS'     as [|x'' xs' SS   All];    subst x'' xs'.
  inversion AllRev' as [|x'' xs' Rx'x AllRev]; subst x'' xs'.
  constructor.
  - by apply IH.
  - move: All AllRev; rewrite !Forall_forall => /= All AllRev a.
    rewrite in_app_iff => -[IN | [? | //]]; last subst a=> //.
    by apply All.
Qed.    

Theorem StronglySorted_rev' {A} (R : A -> A -> Prop) (xs : list A) :
  StronglySorted R xs -> StronglySorted (fun a b => R b a) (rev xs).
Proof.
  elim: xs => [|x xs IH] /= SS'; first by constructor.
  inversion SS' as [|x' xs' SS All]; subst x' xs'.
  move: (IH SS) => IH'.
  apply StronglySorted_snoc; first by apply IH.
  move: All; rewrite !Forall_forall => All a; rewrite -in_rev; apply All.
Qed.

Corollary StronglySorted_rev {A} (R : A -> A -> Prop) (xs : list A) :
  StronglySorted R xs <-> StronglySorted (fun a b => R b a) (rev xs).
Proof.
  split; first apply StronglySorted_rev'.
  rewrite -{2}(rev_involutive xs)=> SS.
  by eapply StronglySorted_rev', StronglySorted_R_ext; last exact SS.
Qed.

Theorem StronglySorted_app {A} (R : A -> A -> Prop) (xs ys : list A) :
  StronglySorted R (xs ++ ys) -> StronglySorted R xs /\ StronglySorted R ys.
Proof.
  elim: xs => [|x xs IH] //= SS; first by auto using StronglySorted.
  inversion SS as [|x' rest SS' All E1]; subst x' rest.
  move: (IH SS') => [SS_xs SS_ys]; split=> //.
  constructor=> //.
  apply/Forall_forall=> a In_a; move: All => /Forall_forall/(_ a).
  by rewrite in_app_iff; apply; left.
Qed.

(******************************************************************************)
(** StronglySorted and NoDup (and similar) **)

Theorem StronglySorted_irrefl_not_in {A} (R : A -> A -> Prop) (x : A) (xs : list A) :
  (forall a, ~ R a a) ->
  StronglySorted R (x :: xs) ->
  ~ In x xs.
Proof.
  move=> irrefl_R SS_xxs; inversion SS_xxs as [|x' xs' SS_xs R_x_xs E1]; subst x' xs'; clear SS_xxs.
  elim: xs SS_xs R_x_xs => [|x' xs IH] SS_xs R_x_xs //=.
  move=> [? | In_x_xs]; first subst x'.
  - inversion_clear R_x_xs; eapply irrefl_R; eassumption.
  - apply IH=> //.
    + by inversion SS_xs.
    + by inversion R_x_xs.
Qed.

Theorem StronglySorted_irrefl_NoDup {A} (R : A -> A -> Prop) (xs : list A) :
  (forall a, ~ R a a) ->
  StronglySorted R xs ->
  NoDup xs.
Proof.
  move=> irrefl_R.
  elim: xs => [|x xs IH] SS_xxs //=; constructor.
  - eapply StronglySorted_irrefl_not_in; eassumption.
  - by apply IH; inversion SS_xxs.
Qed.

Theorem StronglySorted_eq_In {A} (R : A -> A -> Prop) (xs ys : list A) :
  (forall a, ~ R a a) ->
  (forall a b c, R a b -> R b c -> R a c) ->
  StronglySorted R xs ->
  StronglySorted R ys ->
  (xs = ys) <-> (forall a, In a xs <-> In a ys).
Proof.
  move=> irrefl_R trans_R SS_xs; elim: SS_xs ys =>  {xs} [|x xs SS_xs IH_xs R_xs] /= ys SS_ys.
  all: case: ys SS_ys => [|y ys] //= SS_ys.
  all: split; try discriminate.
  all: try by (move=> /(_ x) || move=> /(_ y)); simpl; tauto.
  - by inversion 1.
  - move=> ext_eq.
    have NIn_x_xs: ~ In x xs by eapply StronglySorted_irrefl_not_in; eauto using StronglySorted.
    have NIn_y_ys: ~ In y ys by eapply StronglySorted_irrefl_not_in.
    have E: x = y; last subst y. {
      inversion SS_ys; subst.
      move: (ext_eq x) => [fwd_x bwd_x].
      move: (ext_eq y) => [fwd_y bwd_y].
      case: (fwd_x (or_introl erefl)) => [// | In_x_ys].
      case: (bwd_y (or_introl erefl)) => [// | In_y_xs].
      have Rxy: (R x y) by eapply Forall_forall; eassumption.
      have Ryx: (R y x) by eapply Forall_forall; eassumption.
      by move: (trans_R _ _ _ Rxy Ryx) => /irrefl_R.
    }
    f_equal.
    apply IH_xs; first by inversion SS_ys.
    move=> a; move: (ext_eq a) => [fwd bwd].
    split=> [a_xs | a_ys].
    + have x_a_disj: (x <> a) by contradict NIn_x_xs; subst.
      by move: (fwd (or_intror a_xs))=> [].
    + have x_a_disj: (x <> a) by contradict NIn_y_ys; subst.
      by move: (bwd (or_intror a_ys))=> [].
Qed.

Theorem StronglySorted_NoDup {A} (R R' : A -> A -> Prop) :
  (forall x,       R  x x) ->
  (forall x,     ~ R' x x) ->
  
  (forall x y z, R  x y -> R  y z -> R  x z) ->
  (forall x y z, R' x y -> R' y z -> R' x z) ->
  
  (forall x y, R  x y <-> (x =  y \/ R' x y)) ->
  (forall x y, R' x y <-> (x <> y /\ R  x y)) ->
  
  forall xs,
    StronglySorted R xs -> NoDup xs -> StronglySorted R' xs.
Proof.
  move=> R_refl R'_irrefl R_trans R'_trans R_def R'_def.
  elim=> [|x xs IH] //= Sorted_xxs NoDup_xxs; first by constructor.
  inversion Sorted_xxs as [|x' xs' Sorted_xs R_x_xs E1];  subst x' xs'; clear Sorted_xxs.
  inversion NoDup_xxs  as [|x' xs' NIn_x_xs NoDup_xs E1]; subst x' xs'; clear NoDup_xxs.
  constructor; first by apply IH.
  clear IH Sorted_xs NoDup_xs.
  elim: xs R_x_xs NIn_x_xs => [|x' xs IH] //= R_x_x'xs NIn_x_x'xs.
  inversion R_x_x'xs as [|x'' xs' R_x_x' R_x_xs E1]; subst x'' xs'; clear R_x_x'xs.
  constructor.
  - apply R'_def; split=> //.
    by contradict NIn_x_x'xs; subst; left.
  - apply IH=> //=.
    by contradict NIn_x_x'xs; right.
Qed.  

(******************************************************************************)
(** Previous StronglySorted theorems with specific relations **)

Corollary StronglySorted_Zlt_eq_In (xs ys : list Int) :
  StronglySorted Z.lt xs ->
  StronglySorted Z.lt ys ->
  (xs = ys) <-> (forall a, In a xs <-> In a ys).
Proof. apply StronglySorted_eq_In; [exact Z.lt_irrefl | exact Z.lt_trans]. Qed.

Corollary StronglySorted_Ord_eq_In {A} `{OrdLaws A} (xs ys : list A) :
  StronglySorted _<_ xs ->
  StronglySorted _<_ ys ->
  (xs = ys) <-> (forall a, In a xs <-> In a ys).
Proof.
  apply StronglySorted_eq_In; order A.
Qed.

Corollary StronglySorted_NoDup_Ord {A} `{OrdLaws A} `{!EqExact A} (xs : list A) :
  StronglySorted _<=_ xs ->
  NoDup xs ->
  StronglySorted _<_ xs.
Proof.
  apply StronglySorted_NoDup; try order A.
  - move=> x y; split=> [LExy | [-> | LTxy]]; try order A.
    move: LExy; case Cxy: (compare x y); try order A.
    move: Cxy => /Ord_compare_Eq/Eq_eq; order A.
  - move=> x y; split=> [LTxy | [Nxy LExy]]; try order A.
    rewrite Ord_lt_le; apply/negP; contradict Nxy.
    by apply/Eq_eq; order A.
Qed.

(******************************************************************************)
(** Basic facts about NoDup **)

Theorem NoDup_reorder {A} (pre : list A) (x : A) (post : list A) :
  NoDup (pre ++ x :: post) <-> NoDup (x :: (pre ++ post)).
Proof.
  elim: pre => [|p pre IH] //=; split=> [ND_mid | ND_fst].
  - inversion ND_mid as [|p' rest NIn_p ND_mid' E1]; subst p' rest.
    move/IH in ND_mid'; inversion ND_mid' as [|x' rest NIn_x ND_mid'' E1]; subst x' rest.
    constructor=> //.
    + move=> [? | //]; subst p.
      apply NIn_p; rewrite in_app_iff /=; auto.
    + constructor=> //.
      contradict NIn_p; move: NIn_p.
      rewrite !in_app_iff /=; tauto.
  - inversion ND_fst  as [|x' rest NIn_x ND_fst'  E1]; subst x' rest.
    inversion ND_fst' as [|p' rest NIn_p ND_fst'' E1]; subst p' rest.
    constructor=> //.
    + contradict NIn_p; move: NIn_p.
      rewrite !in_app_iff /= => -[? | [? | ?]]; try tauto; subst p.
      by exfalso; apply NIn_x; left.
    + apply IH; constructor=> //.
      by contradict NIn_x; right.
Qed.

(******************************************************************************)
(** Theorems about sort and nub **)

Theorem sortN {A} `{OrdLaws A} :
  sort [::] = [::].
Proof. done. Qed.

Theorem sort1 {A} `{OrdLaws A} `{!EqExact A} (x : A) :
  sort [:: x] = [:: x].
Proof. done. Qed.

Theorem sort_StronglySorted {A} `{OrdLaws A} (xs : list A) :
  StronglySorted _<=_ (sort xs).
Proof.
  eapply Sorted_StronglySorted, sort_sorted; try typeclasses eauto.
  order A.
Qed.

Theorem sort_elem {A} `{Ord A} (xs : list A) :
  forall x, elem x (sort xs) = elem x xs.
Proof. apply elem_Permutation, sort_permutation. Qed.

Theorem sort_In {A} `{Ord A} (xs : list A) :
  forall x, In x (sort xs) <-> In x xs.
Proof. move=> ?; apply (Permutation_in' erefl), sort_permutation. Qed.

Theorem sort_NoDup {A} `{OrdLaws A} `{!EqExact A} (xs : list A) :
  NoDup xs <-> NoDup (sort xs).
Proof. apply Permutation_NoDup', Permutation_sym, sort_permutation. Qed.

Theorem nub_NoDup {A} `{EqExact A} (xs : list A) : NoDup (nub xs).
Proof.
  rewrite /nub /nubBy.
  have: NoDup ([::] : list A) by constructor.
  move: {1 3}[::].
  elim: xs => [|x xs IH] /= acc acc_uniq; first by constructor.
  case MEM: (elem_by _==_ x acc).
  + by apply IH.
  + constructor.
    * clear IH.
      have: In x (x :: acc) by constructor.
      move: (x :: acc); clear acc acc_uniq MEM.
      elim: xs => [|x' xs IH] acc IN //=.
      case EQ: (x == x') => //=.
      -- move/Eq_eq in EQ; subst x'.
         by move: (IN) => /elem_byP ->; apply IH.
      -- case MEM': (elem_by _==_ x' acc) => //=; first by apply IH.
         move=> [? | IN']; first by subst x'; contradict EQ; rewrite Eq_refl.
         eapply IH; last apply IN'.
         by right.
    * eapply IH; constructor=> //.
      by apply/elem_byP; rewrite MEM.
Qed.

Corollary StronglySorted_sort_nub {A} `{OrdLaws A} `{!EqExact A} (xs : list A) :
  StronglySorted _<_ (sort (nub xs)).
Proof.
  apply StronglySorted_NoDup_Ord; first by apply sort_StronglySorted.
  have decA: forall x y : A, {x = y} + {x <> y} by move=> x y; case: (EqExact_cases x y); tauto.
  rewrite -sort_NoDup; apply nub_NoDup.
Qed.

Corollary StronglySorted_sort_nub_Zlt (xs : list Int) :
  StronglySorted Z.lt (sort (nub xs)).
Proof.
  eapply StronglySorted_R_ext; last by apply StronglySorted_sort_nub.
  by unfold "<", Ord_Integer___ => /= a b; rewrite -Z.ltb_lt.
Qed.
