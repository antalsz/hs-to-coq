(******************************************************************************)
(** Imports **)

(* SSReflect *)
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
Set Bullet Behavior "Strict Subproofs".

(* Sortedness *)
Require Import Coq.Sorting.Sorted.

(* Basic Haskell libraries *)
Require Import GHC.Base      Proofs.GHC.Base.
Require Import GHC.List      Proofs.GHC.List.
Require Import Data.Foldable Proofs.Data.Foldable.
Require Import Data.OldList  Proofs.Data.OldList.
Require Import Data.Bits.

(* IntSet *)
Require Import Data.IntSet.Internal.
Require Import IntSetProperties.
Require Import IntSetProofs.

(* Working with Haskell *)
Require Import OrdTactic.
Require Import HSUtil IntSetUtil SortedUtil.

(******************************************************************************)
(** Name dismabiguation -- copied from HSUtil **)

Notation list    := Coq.Init.Datatypes.list.
Notation seq     := Coq.Lists.List.seq.
Notation reflect := ssrbool.reflect.

(******************************************************************************)
(** Theorems **)
(** The quoted comments and the section headers are taken directly from
    `intset-properties.hs`. **)

(********************************************************************
  Valid IntMaps
********************************************************************)

Theorem thm_Valid : toProp prop_Valid.
Proof.
  rewrite /prop_Valid /forValidUnitTree /forValid /=; apply valid_correct.
Qed.

(********************************************************************
  Construction validity
********************************************************************)

Theorem thm_EmptyValid : toProp prop_EmptyValid.
Proof. done. Qed.

Theorem thm_SingletonValid : toProp prop_SingletonValid.
Proof.
  rewrite /prop_SingletonValid /= => x POS_x.
  by apply valid_correct, singleton_WF.
Qed.

Theorem thm_InsertIntoEmptyValid : toProp prop_InsertIntoEmptyValid.
Proof.
  rewrite /prop_InsertIntoEmptyValid /= => x POS.
  by apply valid_correct, insert_WF.
Qed.

(********************************************************************
  Single, Member, Insert, Delete, Member, FromList
********************************************************************)

Theorem thm_Single : toProp prop_Single.
Proof. by rewrite /prop_Single /= => x POS_x; apply/Eq_eq. Qed.

Theorem thm_Member : toProp prop_Member.
Proof.
  rewrite /prop_Member /= => xs POS_xs n POS_n.
  rewrite !Foldable_all_ssreflect; apply/allP => /= k.
  by rewrite fromList_member // Eq_refl.
Qed.

Theorem thm_NotMember : toProp prop_NotMember.
Proof.
  rewrite /prop_NotMember /= => xs POS_xs n POS_n.
  rewrite !Foldable_all_ssreflect; apply/allP => /= k.
  by rewrite /notMember /notElem /= fromList_member // Eq_refl.
Qed.

(* SKIPPED: test_LookupSomething, prop_LookupLT, prop_LookupGT, prop_LookupLE, prop_LookupGE *)

Theorem thm_InsertDelete : toProp prop_InsertDelete.
Proof.
  rewrite /prop_InsertDelete /= => x POS s WF_s.

  move: (insert_WF x _ WF_s   POS) => WF_ins.
  move: (delete_WF x _ WF_ins POS) => WF_res.
  case x_nin_s: (~~ member x s) => //=; split=> /=; first by apply valid_correct.

  apply/eqIntSetMemberP => // k POS_k.
  rewrite delete_member // insert_member //.
  rewrite Eq_inv andb_orr andbN orFb.
  
  case: (EqExact_cases k x) => [[Beq Peq] | [Bneq Pneq]].
  - by rewrite Peq; move: x_nin_s => /negbTE->; rewrite andbF.
  - by rewrite Bneq andTb.
Qed.

(* Cheating: manually forgetting POS constraint *)
Theorem thm_MemberFromList : toProp prop_MemberFromList.
Proof.
  rewrite /prop_MemberFromList /= => xs _(* POS_xs *).
  set abs_xs := flat_map _ xs.
  apply/andP; split.
  all: rewrite Foldable_all_ssreflect; apply/allP => /= k; rewrite in_elem.
  - rewrite fromList_member //.
    subst abs_xs; elim: xs => [|x xs IH] //=.
    case: (x /= #0) => //=.
    constructor; last assumption.
    apply Z.abs_nonneg.
  - rewrite /notMember /notElem /= fromList_member //.
    + move=> k_abs; have k_pos: (0 <= k)%Z. {
        subst abs_xs; elim: xs k_abs => [|x xs IH] //=.
        rewrite elem_app=> /orP[] //.
        case NZ: (x /= #0)=> //=.
        rewrite elemC elemN orbF => /Eq_eq ->.
        apply Z.abs_nonneg.
      }
      clear k_abs; subst abs_xs; elim: xs => [|x xs IH] //=.
      rewrite elem_app negb_orb IH andbT.
      by case: k k_pos {IH}; case: x.
    + apply Forall_forall=> {k} k; rewrite in_flat_map => -[x [_]].
      case CMP: (x /= #0) => //= -[] //= <-.
      apply Z.abs_nonneg.
Qed.      

(********************************************************************
  Union, Difference and Intersection
********************************************************************)

Theorem thm_UnionInsert : toProp prop_UnionInsert.
Proof.
  rewrite /prop_UnionInsert /= => x POS_x s WF_s.

  move: (singleton_WF x POS_x)          => WF_sing.
  move: (union_WF     _ _ WF_s WF_sing) => WF_union.
  move: (insert_WF    x _ WF_s POS_x)   => WF_ins.

  split=> /=; first by apply valid_correct.
  
  apply/eqIntSetMemberP => // k POS_k.
  by rewrite union_member // singleton_member // insert_member // orbC.
Qed.

Theorem thm_UnionAssoc : toProp prop_UnionAssoc.
Proof.
  rewrite /prop_UnionAssoc /= => s1 WF1 s2 WF2 s3 WF3.
  
  move: (union_WF _ _ WF1  WF2)  => WF12.
  move: (union_WF _ _ WF2  WF3)  => WF23.
  move: (union_WF _ _ WF12 WF3)  => WF123.
  move: (union_WF _ _ WF1  WF23) => WF123'.
  
  apply/eqIntSetMemberP => // k POS_k.
  by rewrite !union_member // orbA.
Qed.

Theorem thm_UnionComm : toProp prop_UnionComm.
Proof.
Proof.
  rewrite /prop_UnionComm /= => s1 WF1 s2 WF2.
  
  move: (union_WF _ _ WF1 WF2) => WF12.
  move: (union_WF _ _ WF2 WF1) => WF21.
  
  apply/eqIntSetMemberP => // k POS_k.
  by rewrite !union_member // orbC.
Qed.

Theorem thm_Diff : toProp prop_Diff.
Proof.
  rewrite /prop_Diff /= => xs POS_xs ys POS_ys.
  
  move: (fromList_WF   xs POS_xs)       => WF_xs.
  move: (fromList_WF   ys POS_ys)       => WF_ys.
  move: (difference_WF _ _ WF_xs WF_ys) => WF_diff.
  
  split=> /=; first by apply valid_correct.
  apply/Eq_eq/StronglySorted_Ord_eq_In.
  - by apply toList_sorted.
  - apply StronglySorted_NoDup_Ord; first apply sort_StronglySorted.
    rewrite -sort_NoDup.
    apply diff_preserves_NoDup, nub_NoDup.
  - move=> a.
    rewrite !(rwP (elemP _ _)).
    rewrite sort_elem.
    rewrite diff_NoDup_elem; last apply nub_NoDup.
    rewrite !nub_elem.
    rewrite toAscList_member // difference_member // !fromList_member //.
Qed.

Theorem thm_Int : toProp prop_Int.
Proof.
  rewrite /prop_Int /= => xs POS_xs ys POS_ys.

  move: (fromList_WF     xs POS_xs)       => WF_xs.
  move: (fromList_WF     ys POS_ys)       => WF_ys.
  move: (intersection_WF _ _ WF_xs WF_ys) => WF_both.

  split=> /=; first by apply valid_correct.
  apply/Eq_eq; fold toList.
  apply StronglySorted_Zlt_eq_In;
    [by apply to_List_sorted | apply StronglySorted_sort_nub_Zlt | ].
  move=> a.
  by rewrite !(rwP (elemP _ _))
             toList_member // intersection_member // !fromList_member //
             sort_elem nub_elem intersect_elem.
Qed.

Theorem thm_disjoint : toProp prop_disjoint.
Proof.
  rewrite /prop_disjoint /= => s1 WF1 s2 WF2.
  
  move: (intersection_WF _ _ WF1 WF2) => WF12.
  
  apply/Eq_eq/bool_eq_iff.
  rewrite disjoint_member // null_member //.
  split=> [is_disjoint | is_not_intersection] k.
  - rewrite intersection_member //; apply negbTE.
    rewrite negb_andb; apply is_disjoint.
  - move: (is_not_intersection k).
    rewrite intersection_member // => /negbT.
    by rewrite negb_andb.
Qed.

(********************************************************************
  Lists
********************************************************************)

(* SKIPPED: prop_Ordered *)

Theorem thm_List : toProp prop_List.
Proof.
  rewrite /prop_List /=; rewrite -/toList => xs POS_xs.
Proof.
  have WF_xs: WF (fromList xs) by apply fromList_WF.
  apply/Eq_eq/StronglySorted_Ord_eq_In.
  - apply StronglySorted_sort_nub.
  - apply toList_sorted, fromList_WF=> //.
  - move=> a.
    by rewrite !(rwP (elemP _ _))
               toList_member // fromList_member //
               sort_elem nub_elem.
Qed.

Theorem thm_DescList : toProp prop_DescList.
Proof.
  rewrite /prop_DescList /= => xs POS_xs.
  replace (toDescList (fromList xs)) with (reverse (toAscList (fromList xs)))
    by by rewrite !hs_coq_reverse_rev toDescList_spec //; apply fromList_WF.
  apply/Eq_eq; f_equal; apply/Eq_eq.
  by apply thm_List.
Qed.

Theorem thm_AscDescList : toProp prop_AscDescList.
Proof.
  rewrite /prop_AscDescList /= => xs POS_xs.
  rewrite /toAscList toDescList_spec; last by apply fromList_WF.
  by rewrite hs_coq_reverse_rev rev_involutive Eq_refl.
Qed.

(* SKIPPED: prop_fromList *)

(********************************************************************
  Bin invariants
********************************************************************)

(* "Check the invariant that the mask is a power of 2." *)
Theorem thm_MaskPow2 : toProp prop_MaskPow2.
Proof.
  simpl; elim=> [p m l IHl r IHr | p m | ] WF_s //=.
  apply/and3P; split.
  - rewrite /powersOf2 enumFromTo_Int_iterates.
    cbv -[Z.pow member fromList].

    inversion WF_s; inversion H; inversion HD; subst.
    rewrite /rMask.
    destruct r0 as [r0_1 r0_2].
    
    (*
    rewrite /powersOf2 enumFromTo_Int_iterates.
    cbv -[Zpow member fromList].

    
    move: (WF_s) => /WF_Bin_children [/IHl Pl /IHr Pr].
    move: Pl Pr; rewrite /prop_MaskPow2.

rewrite /powersOf2 enumFromTo_Int_iterates.
    cbv -[Zpow member fromList].
    
    simpl

 /=.
    replace (GHC.Enum.eftInt 0%Z 63%Z) with (eftInt 0%Z 63%Z) by admit.
    

    cbv -[member fromList flat_map Zpow].

    rewrite /Enum.eftInt_fuel.
    
  - apply IHl; move: WF_s; apply WF_Bin_left.
  - apply IHr; move: WF_s; apply WF_Bin_right.
  *)
Abort.

(* "Check that the prefix satisfies its invariant." *)
Theorem thm_Prefix : toProp prop_Prefix.
Proof.
Abort.

(* "Check that the left elements don't have the mask bit set, and the right ones
   do." *)
Theorem thm_LeftRight : toProp prop_LeftRight.
Proof.
  rewrite /prop_LeftRight /= => -[p m l r | // | // ] WF_x; move: (WF_x) => /WF_Bin_children [WF_l WF_r].
  rewrite !Foldable_and_all !Foldable_all_ssreflect !flat_map_cons_f;
    apply/andP; split; apply/allP => /= b /mapP [] x; rewrite in_elem toList_member // => x_in {b}->.
  - case: (WF_x) => [f /Sem_Desc0 [rng DESC0]].
    inversion_clear DESC0 as [|s rng' f' rng_ f'_ DESC rng'_rng f_f'].
    inversion DESC; subst.
Abort.

(********************************************************************
  IntSet operations are like Set operations
********************************************************************)

(* "Check that IntSet.isProperSubsetOf is the same as Set.isProperSubsetOf." *)
Theorem thm_isProperSubsetOf : toProp prop_isProperSubsetOf.
Proof.
Abort.

(* "In the above test, isProperSubsetOf almost always returns False (since a
   random set is almost never a subset of another random set).  So this second
   test checks the True case." *)
Theorem thm_isProperSubsetOf2 : toProp prop_isProperSubsetOf2.
Proof.
  rewrite /prop_isProperSubsetOf2 /= => s1 WF1 s2 WF2.
  move: (union_WF _ _ WF1 WF2) => WF12.
  apply/Eq_eq/bool_eq_iff.
  
  rewrite isProperSubsetOf_member //; intuition.
  apply/implyP=> k_in_s1.
  by rewrite union_member // k_in_s1 orTb.
Qed.

Theorem thm_isSubsetOf : toProp prop_isSubsetOf.
Proof.
  rewrite /prop_isSubsetOf /= => s1 WF1 s2 WF2.
Abort.

Theorem thm_isSubsetOf2 : toProp prop_isSubsetOf2.
Proof.
  rewrite /prop_isSubsetOf2 /= => s1 WF1 s2 WF2.
  move: (union_WF _ _ WF1 WF2) => WF12.
  rewrite isSubsetOf_member // => k.
  rewrite union_member //.
  by apply/implyP => ->.
Qed.

Theorem thm_size : toProp prop_size.
Proof.
  rewrite /prop_size /= => s WF_s.
  rewrite size_spec //.
  split=> /=.
  - change @foldl' with @foldl; rewrite foldl_spec // -Zlength_correct.
    apply/Eq_eq.
    replace (Zlength (toList s)) with (Zlength (toList s) + 0%Z) by rewrite /= Z.add_0_r //.
    move: 0%Z => /=; elim: (toList s) => [|x xs IH] //= z.
    by rewrite Zlength_cons -IH Z.add_succ_comm.
  - by rewrite hs_coq_length_list Zlength_correct Eq_refl.
Qed.

(* SKIPPED: prop_findMax, prop_findMin *)

Theorem thm_ord : toProp prop_ord.
Proof.
  rewrite /prop_ord /= => s1 WF1 s2 WF2.
  apply Eq_refl.
Qed.

(* SKIPPED: prop_readShow *)

Theorem thm_foldR : toProp prop_foldR.
Proof.
  rewrite /prop_foldR /= => s WF_s.
  by rewrite Eq_refl.
Qed.

Theorem thm_foldR' : toProp prop_foldR'.
Proof.
  rewrite /prop_foldR' /= => s WF_s.
  by rewrite Eq_refl.
Qed.

Theorem thm_foldL : toProp prop_foldL.
Proof.
  rewrite /prop_foldL /= => s WF_s.
  by rewrite foldl_spec // -hs_coq_foldl_base Eq_refl.
Qed.

Theorem thm_foldL' : toProp prop_foldL'.
Proof.
  rewrite /prop_foldL' /=; change @foldl' with @foldl; apply thm_foldL.
Qed.

Theorem thm_map : toProp prop_map.
Proof.
  rewrite /prop_map /map /= => s WF_s.
  rewrite map_id.
  have POS_s: Forall [eta Z.le 0] (toList s) by apply/Forall_forall; apply toList_In_nonneg.
  apply/eqIntSetMemberP=> //; first by apply fromList_WF.
  move=> k POS_k.
  by rewrite fromList_member // toList_member // Eq_refl.
Qed.

(* SKIPPED: prop_maxView, prop_minView *)

Theorem thm_split : toProp prop_split.
Proof.
Abort.

Theorem thm_splitMember : toProp prop_splitMember.
Proof.
Abort.

Theorem thm_splitRoot : toProp prop_splitRoot.
Proof.
Abort.

Theorem thm_partition : toProp prop_partition.
Proof.
  rewrite /prop_partition /= => s WF_s _ _.
  rewrite partition_filter //.
  
  have WF_odd:   WF (filter GHC.Real.odd                 s) by apply filter_WF.
  have WF_even:  WF (filter (fun k => ~~ GHC.Real.odd k) s) by apply filter_WF.
  move: (union_WF _ _ WF_odd WF_even) => WF_union.
  
  rewrite !Foldable_all_ssreflect.
  repeat (split=> /=); try by apply valid_correct.
  - apply/allP=> /= k.
    by rewrite in_elem toList_member // filter_member // => /andP[].
  - apply/allP=> /= k.
    rewrite in_elem toList_member // filter_member // => /andP[].
    by rewrite /GHC.Real.odd negb_involutive.
  - apply/eqIntSetMemberP=> // k POS_k.
    rewrite union_member // !filter_member //.
    by case: (member k s)=> //=; rewrite orb_negb_r.
Qed.

Theorem thm_filter : toProp prop_filter.
Proof.
  rewrite /prop_filter /= => s WF_s _ _.
  
  have WF_odd:   WF (filter GHC.Real.odd                 s) by apply filter_WF.
  have WF_even:  WF (filter GHC.Real.even                s) by apply filter_WF.
  have WF_even': WF (filter (fun k => ~~ GHC.Real.odd k) s) by apply filter_WF.
  move: (union_WF _ _ WF_odd WF_even) => WF_union.
  
  repeat (split=> /=); try by apply valid_correct.
  rewrite partition_filter //.
  apply/andP; split; first by apply Eq_refl.
  apply/eqIntSetMemberP=> // k POS_k.
  rewrite !filter_member //.
  by rewrite /GHC.Real.odd negb_involutive.
Qed.

(* SKIPPED: prop_bitcount *)
