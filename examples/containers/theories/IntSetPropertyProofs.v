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
Require Import GHC.Enum      Proofs.GHC.Enum.
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
    apply is_disjoint.
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
  (* We do `...; [|done|done]` and the next rewrite both together instead of
     `//=` to avoid ever trying to simplify `powersOf2`, which would both
     generate [0..63] *and do the exponentiation*. *)
  simpl; elim=> [p m l IHl r IHr | p m | ] WFs; [|done|done].
  rewrite /prop_MaskPow2 -/prop_MaskPow2.
  move: (WFs) => /WF_Bin_children [WFl WFr].
  apply/and3P; split; [| apply IHl, WFl | apply IHr, WFr].
  rewrite /powersOf2 flat_map_cons_f; change @GHC.Base.map with @Coq.Lists.List.map.
  rewrite fromList_member.
  - rewrite (lock enumFromTo).
    apply/elemP; rewrite in_map_iff.
    move: (valid_maskPowerOfTwo _ WFs) => /= /and3P [/Eq_eq/bitcount_0_1_power_Z_N [i ->] _ _].
    exists (Z.of_N i); split => //.
    rewrite -(lock eftInt) eftInt_In.
    admit. (* Unprovable *)
  - apply Forall_forall => m' /in_map_iff [i [<-{m'} _]].
    by apply Z.pow_nonneg.
Abort.

(* "Check that the prefix satisfies its invariant." *)
Theorem thm_Prefix : toProp prop_Prefix.
Proof.
  elim => [p m | p bm | ] //.
  rewrite /prop_Prefix -/prop_Prefix /toList (lock toAscList) /= => l IHl r IHr WFs;
    move: (WFs) => /WF_Bin_children [WFl WFr].
  move: (WFs) => [fs SEMs];
    inversion SEMs as [|s' [ps ms] fs' DESCs]; subst s' fs';
    inversion DESCs as [|l' rng_l fl r' rng_r fr p' m' rng_s' fs'
                         DESCl DESCr POSrng subrange_l subrange_r def_p def_m def_fs];
    subst p' m' l' r' rng_s' fs' p m.
  apply/and3P; split; try by (apply IHl || apply IHr).
  
  rewrite !Foldable_all_ssreflect; apply/allP => /= x.
  rewrite -(lock toAscList) in_elem toAscList_member // (member_Sem SEMs) => MEM_x.
  
  rewrite /match_ /mask; apply/Eq_eq.
  case: (WF_Bin_mask_power_Z_Z WFs) => [i def_mask_s POS_i].
  rewrite mask_to_upper_bits //; last by apply Z.lt_le_pred; move: POSrng => /N2Z.inj_lt.
  rewrite Z.succ_pred -Z.ldiff_land Z.ldiff_ones_r; last apply N2Z.is_nonneg.
  by move: (Desc_inside DESCs MEM_x); rewrite /inRange => /Z.eqb_spec ->.
Qed.

(* "Check that the left elements don't have the mask bit set, and the right ones
   do." *)
Theorem thm_LeftRight : toProp prop_LeftRight.
Proof.
  rewrite /prop_LeftRight /= => -[p m l r | // | // ] WFs; move: (WFs) => /WF_Bin_children [WFl WFr].
  move: (WFs) => /valid_maskRespected /= /andP [mask_l mask_r]; move: mask_l mask_r.
  rewrite !Foldable_and_all !Foldable_all_ssreflect !flat_map_cons_f /zero /elems /toList.
  move=> /allP /= mask_l /allP /= mask_r.
  apply/andP; split; apply/allP => /= b /mapP [] /= x x_in {b}->; apply/Eq_eq.
  - by move: (mask_l _ x_in) => /Z.eqb_spec ->.
  - move: (mask_r _ x_in) => /Z.eqb_spec.
    case: (WF_Bin_mask_power_Z_Z WFs) => [i ? POS_i]; subst m.
    rewrite -Z.shiftl_1_l => NEQ_bits.
    apply Z_eq_testbits_pos => ix POS_ix.
    rewrite Z.land_spec Z.shiftl_spec // testbit_1.
    case: (Z.eq_dec ix i) => [? | NEQ]; first subst.
    + rewrite Z.sub_diag /= andbT Z_testbit_eq; apply/negP.
      by contradict NEQ_bits; apply/Z.eqb_spec.
    + suff: ~~ (ix - i =? 0)%Z by move=> /negbTE ->; rewrite andbF.
      apply/negP => /Z.eqb_spec ?; omega.
Qed.

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
  
  rewrite isProperSubsetOf_member //; split; first by intuition.
  move=> s1_diff; split=> // k k_in_s1.
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
  by rewrite union_member // => ->; rewrite orTb.
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
  rewrite /prop_splitRoot /= => -[p m l r | p m | ] WFs //=.
  - move: (WFs) => /WF_Bin_children [WFl WFr].
    have WFlr: WF (union l r) by apply union_WF.
    have WFrl: WF (union r l) by apply union_WF.
    
    have: (m > 0%Z). {
      move: (WFs) => [fs SEMs];
        inversion SEMs as [|s' [ps ms] fs' DESCs];
        subst s' fs';
        inversion DESCs as [|l' rng_l fl r' rng_r fr p' m' rng_s' fs'
                             DESCl DESCr POSrng subrange_l subrange_r def_p def_m def_fs];
        subst p' m' l' r' rng_s' fs' p m.
      unfold ">", Ord_Integer___ => /=.
      apply/Z.ltb_spec0; apply Z.pow_pos_nonneg => //.
      zify; simpl in *; omega.
    }
    move=> /(Ord_gt_not_lt _ _)/negbTE ->.
    
    rewrite /unions !hs_coq_foldl_list /= !(union_eq empty) /=.
    apply/andP; split.
    + apply null_list_none => -[x y] /in_flat_map [kl [/elemP IN_kl /in_flat_map [kr [/elemP IN_kr IN_xy]]]].
      move: IN_kl IN_kr; rewrite !toList_member // => IN_kl IN_kr.
      move: (Bin_left_lt_right WFs _ IN_kl _ IN_kr) IN_xy.
      by move=> /(Ord_lt_not_gt _ _)/negbTE ->.
    + by apply/eqIntSetMemberP => // k POS_k; rewrite Bin_member // union_member //.
  - apply/andP; split; by [elim: (foldrBits _ _ _ _) | apply/Eq_eq].
Qed.

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
