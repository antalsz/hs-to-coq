(******************************************************************************)
(** Imports **)

(* SSReflect *)
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
Set Bullet Behavior "Strict Subproofs".

(* Sortedness *)
Require Import Coq.Sorting.Sorted.

(* Basic Haskell libraries *)
Require Import GHC.Base      Proofs.GHC.Base.
Require Import Data.Foldable Proofs.Data.Foldable.
Require Import Data.OldList  Proofs.Data.OldList.

(* Working with Haskell *)
Require Import OrdTactic.
Require Import HSUtil.

(******************************************************************************)
(** Name dismabiguation -- copied from HSUtil **)

Notation list    := Coq.Init.Datatypes.list.
Notation seq     := Coq.Lists.List.seq.
Notation reflect := ssrbool.reflect.

(******************************************************************************)
(** Basic facts about StronglySorted **)

Theorem StronglySorted_irrefl_no_duplicates {A} (R : A -> A -> Prop) (x : A) (xs : list A) :
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
    have NIn_x_xs: ~ In x xs by eapply StronglySorted_irrefl_no_duplicates; eauto using StronglySorted.
    have NIn_y_ys: ~ In y ys by eapply StronglySorted_irrefl_no_duplicates.
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
(** Basic facts about StronglySorted for specific relations **)

Corollary StronglySorted_Zlt_eq_In (xs ys : list Int) :
  StronglySorted Z.lt xs ->
  StronglySorted Z.lt ys ->
  (xs = ys) <-> (forall a, In a xs <-> In a ys).
Proof. apply StronglySorted_eq_In; [exact Z.lt_irrefl | exact Z.lt_trans]. Qed.

Corollary StronglySorted_NoDup_Ord {A} `{OrdLaws A} `{!EqExact A} (xs : list A) :
  StronglySorted _<=_ xs ->
  NoDup xs ->
  StronglySorted _<_ xs.
Proof.
  apply StronglySorted_NoDup.
  - apply OrdTactic.Lemmas.Ord_le_refl.
  - move=> a.
    rewrite Ord_lt_le.
    apply/negP; rewrite negbK.
    apply OrdTactic.Lemmas.Ord_le_refl.
  - apply Ord_trans_le.
  - move=> a b c.
    rewrite !Ord_lt_le.
    move=> /negbTE NLEba /negbTE NLEcb.
    have: (c <= a) = false by eapply OrdTactic.Lemmas.Ord_trans_lt; eassumption.
    by move=> ->.
  - move=> x y; split=> [LExy | [-> | LTxy]].
    + move: LExy; case Cxy: (compare x y).
      * move: Cxy; rewrite Ord_compare_Eq.
        by move=> /Eq_eq-> _; left.
      * move: Cxy; rewrite Ord_compare_Lt.
        by rewrite Ord_lt_le=> -> _; right.
      * move: Cxy; rewrite Ord_compare_Gt.
        by move=> ->.
    + apply OrdTactic.Lemmas.Ord_le_refl.
    + move: LTxy.
      rewrite Ord_lt_le=> /negbTE; rewrite <-Ord_compare_Lt.
      case NLExy: (x <= y) => //; move: NLExy.
      by rewrite <-Ord_compare_Gt=> ->.
  - move=> x y; split=> [LTxy | [Nxy LExy]].
    + split=> [Exy|].
      * by move: LTxy; rewrite Exy Ord_lt_le OrdTactic.Lemmas.Ord_le_refl.
      * move: LTxy.
        rewrite Ord_lt_le=> /negP.
        by case: (Ord_total x y) => ->.
    + rewrite Ord_lt_le; apply/negP; contradict Nxy.
      by apply/Eq_eq; apply Ord_antisym.
Qed.

(** Basic facts about NoDup **)

Theorem NoDup_length_perm {A} (xs ys : list A) :
  NoDup xs ->
  length xs = length ys ->
  (forall a, In a xs <-> In a ys) ->
  NoDup ys.
Proof.
  rewrite !hs_coq_length_list !Zlength_correct Nat2Z.inj_iff.
  elim: xs ys => [|x xs IH] [|y ys] //=.
  move=> NoDup_xxs Slen_eq ext_eq.
  inversion NoDup_xxs as [|x' xs' NIn_x_xs NoDup_xs E1]; subst.
  case: (Slen_eq) => len_eq.
  constructor.
  - admit.
  - apply IH=> //.
    move=> a; move: (ext_eq a)=> -[fwd_a bwd_a].
    split.
    + move=> In_a_xs; move: (In_a_xs) => /or_intror/fwd_a [? | //]; subst a.
      move: (ext_eq x) => [fwd_x bwd_x].
      move: (fwd_x (or_introl erefl)) => [? | In_x_ys]; first by subst y.
      move: (In_x_ys) => /In_split [pre_ys [post_ys def_ys]].
      move: (In_a_xs) => /In_split [pre_xs [post_xs def_xs]].
      subst; apply in_or_app=> /=.
      have NIn_x_pre_xs:  ~ In x pre_xs  by move=> IN; apply NIn_x_xs, in_or_app; left.
      have NIn_x_post_xs: ~ In x post_xs by move=> IN; apply NIn_x_xs, in_or_app; do 2 right.
Abort.

(******************************************************************************)
(** Hypotheses about sort **)

Hypothesis sort_StronglySorted : forall {A} `{OrdLaws A} (xs : list A), StronglySorted _<=_ (sort xs).
Hypothesis sort_length         : forall {A} `{OrdLaws A} (xs : list A), length (sort xs) = length xs.
Hypothesis sort_elem           : forall {A} `{OrdLaws A} (xs : list A), forall x, elem x (sort xs) <-> elem x xs.

(******************************************************************************)
(** Theorems about sort and nub **)

Theorem nub_NoDup {A} `{Eq_ A} {HExact : EqExact A} {HLaws : EqLaws A}  (xs : list A) : NoDup (nub xs).
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
         by move: (IN) => /elem_by_In ->; apply IH.
      -- case MEM': (elem_by _==_ x' acc) => //=; first by apply IH.
         move=> [? | IN']; first by subst x'; contradict EQ; rewrite Eq_refl.
         eapply IH; last apply IN'.
         by right.
    * eapply IH; constructor=> //.
      by apply/elem_by_In; rewrite MEM.
Qed.

Corollary StronglySorted_sort_nub {A} `{OrdLaws A} `{!EqExact A} (xs : list A) :
  StronglySorted _<_ (sort (nub xs)).
Proof.
  apply StronglySorted_NoDup_Ord; first by apply sort_StronglySorted.
  have decA: forall x y : A, {x = y} + {x <> y} by move=> x y; case: (EqExact_cases x y); tauto.
  apply NoDup_count_occ with decA.
  suff: count_occ decA (@sort A HEq HOrd (@nub A HEq xs)) = count_occ decA (@nub A HEq xs)
    by move=> ->; apply NoDup_count_occ, nub_NoDup.
Abort.

Theorem Sort_eq {A : eqType} `{OrdLaws A} `{!EqExact A} (xs ys : list A) :
  StronglySorted _<=_ xs ->
  StronglySorted _<=_ ys ->
  (xs == ys) = seq.all (fun a => a \in xs) ys && seq.all (fun b => b \in ys) xs.
Proof.
  elim: xs ys => [|x xs IH_xs] [|y ys] //=.
  inversion_clear 1 as [|X1 X2 SS_xs FA_xs X3]; inversion_clear 1 as [|X1 X2 SS_ys FA_ys X3].
  unfold "=="; rewrite /Eq_list /=; case CMP: (x == y).
  - move: CMP => /Eq_eq ? /=; subst y.
    replace (eqlist xs ys) with (xs == ys) by done; rewrite IH_xs //.
    admit.
  - 
Abort.
