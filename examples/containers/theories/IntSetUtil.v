(******************************************************************************)
(** Imports **)

(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

(* SSReflect *)
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
Set Bullet Behavior "Strict Subproofs".

(* Sortedness *)
Require Import Coq.Sorting.Sorted.

(* Basic Haskell libraries *)
Require Import GHC.Base      Proofs.GHC.Base.
Require Import Data.Foldable Proofs.Data.Foldable.
Require Import Data.Bits.

(* IntSet library *)
Require Import Data.IntSet.Internal.
Require Import Utils.Containers.Internal.BitUtil.
Require Import Popcount.

(* IntSet proofs *)
Require Import DyadicIntervals.
Require Import IntSetProofs.

(* Bit manipulation *)
Require Import BitUtils.

(* Working with Haskell *)
Require Import HSUtil SortedUtil.

(******************************************************************************)
(** Name dismabiguation -- copied from HSUtil **)

Notation list    := Coq.Init.Datatypes.list.
Notation seq     := Coq.Lists.List.seq.
Notation reflect := ssrbool.reflect.

(******************************************************************************)
(** Bit manipulation **)

Theorem bitcount_0_1_power (n : Word) :
  bitcount #0 n = #1 <-> exists i, n = (2^i)%N.
Proof.
  rewrite /bitcount /popCount /=; change 1%Z with (Z.of_N 1%N); rewrite N2Z.inj_iff.
  split=> [/N_popcount_1_pow2 [i def_n] | [i ->{n}]].
  - by exists i.
  - apply N_popcount_pow2.
Qed.

Theorem bitcount_0_1_power_Z_N (n : Int) :
  bitcount #0 (Z.to_N n) = #1 <-> exists i, n = (2 ^ Z.of_N i)%Z.
Proof.
  change 2%Z with (Z.of_N 2%N); rewrite bitcount_0_1_power; split=> -[i def_n]; exists i.
  - rewrite -N2Z.inj_pow -def_n Z2N.id //.
    case: n def_n => [|n|n] //=.
    have: (0 < 2^i)%N by apply N_pow_pos_nonneg.
    by case: (2^i)%N.
  - by rewrite def_n -N2Z.inj_pow N2Z.id.
Qed.

Theorem bitcount_0_1_power_Z_Z (n : Int) :
  bitcount #0 (Z.to_N n) = #1 <-> ex2 (fun i => n = 2^i)%Z (fun i => 0 <= i)%Z.
Proof.
  rewrite bitcount_0_1_power_Z_N; split=> [[i def_n] | [i def_n POS_i]].
  - exists (Z.of_N i) => //; apply N2Z.is_nonneg.
  - exists (Z.to_N i); rewrite def_n Z2N.id //.
Qed.

Theorem WF_Bin_mask_power_Z_Z {p : Prefix} {m : Mask} {l r : IntSet} :
  WF (Bin p m l r) ->
  ex2 (fun i => m = 2^i)%Z (fun i => 0 <= i)%Z.
Proof.
  move=> /valid_maskPowerOfTwo /= /and3P [/Eq_eq BITS _ _].
  by apply bitcount_0_1_power_Z_Z.
Qed.

(******************************************************************************)
(** Well-formedness (WF) theorems **)

Theorem empty_WF : WF empty.
Proof. by exists xpred0; constructor. Qed.
Hint Resolve empty_WF.

Theorem WF_Bin_children (p : Prefix) (m : Mask) (l r : IntSet) :
  WF (Bin p m l r) -> WF l /\ WF r.
Proof.
  case=> fn;
    inversion 1    as [|s bounds fn' desc];
    subst s fn';
    inversion desc as [|l' bounds_l fn_l r' bounds_r fn_r
                        p' m' bounds' fn'
                        desc_l desc_r is_pos sub_l sub_r def_p def_m spec_fn];
    subst p' m' l' r' bounds' fn'.
  split; [exists fn_l | exists fn_r]; eauto using DescSem.
Qed.

Corollary WF_Bin_left (p : Prefix) (m : Mask) (l r : IntSet) :
  WF (Bin p m l r) -> WF l.
Proof. by move=> /WF_Bin_children []. Qed.

Corollary WF_Bin_right (p : Prefix) (m : Mask) (l r : IntSet) :
  WF (Bin p m l r) -> WF r.
Proof. by move=> /WF_Bin_children []. Qed.

(******************************************************************************)
(** Sortedness theorems in terms of Ord **)

Theorem toList_sorted (s : IntSet) :
  WF s ->
  StronglySorted _<_ (toList s).
Proof.
  move=> WF_s; apply StronglySorted_R_ext with Z.lt; last by apply to_List_sorted.
  move=> a b; unfold "<", Ord_Integer___ => /=.
  symmetry; apply rwP.
  apply/Z.ltb_spec0.
Qed.

Theorem toAscList_sorted (s : IntSet) :
  WF s ->
  StronglySorted _<_ (toAscList s).
Proof.
  apply toList_sorted.
Qed.

Theorem toDescList_sorted (s : IntSet) :
  WF s ->
  StronglySorted _>_ (toDescList s).
Proof.
  move=> WF_s; rewrite toDescList_spec //.
  rewrite -StronglySorted_rev.
  by apply toList_sorted.
Qed.

(******************************************************************************)
(** Functions in terms of other functions **)

Theorem partition_filter (s : IntSet) (p : Int -> bool) :
  WF s ->
  partition p s = (filter p s, filter (fun k => ~~ p k) s).
Proof. by move=> WF_s; rewrite -partition_fst -partition_snd //; case: (partition p s). Qed.

Theorem split_splitMember (x : Int) (s : IntSet) :
  WF s ->
  let: (l,m,r) := splitMember x s in
  split x s = (l, r) /\ member x s = m.
Proof.
  move=> [fs Sem_s].
  apply splitMember_Sem with fs => //= l fl r fr m' Sem_l Sem_r <-{m'} def_fl def_fr.
  split.
  - apply split_Sem with fs => //= l' fl' r' fr' Sem_l' Sem_r' def_fl' def_fr'.
    f_equal; eauto using Sem_unique.
  - by apply member_Sem.
Qed.  

Theorem split_splitMember' (x : Int) (s : IntSet) :
  WF s ->
  split x s = ((splitMember x s).1.1, (splitMember x s).2) /\ member x s = (splitMember x s).1.2.
Proof. by move=> /(split_splitMember x); case: (splitMember x s) => [[? ?] ?]. Qed.

Theorem splitMember_split (x : Int) (s : IntSet) :
  WF s ->
  let: (l,r) := split x s in
  splitMember x s = (l, member x s, r).
Proof. by move=> /(split_splitMember x); case: (splitMember x s) => [[? ?] ?] [-> ->]. Qed.

Theorem splitMember_split' (x : Int) (s : IntSet) :
  WF s ->
  splitMember x s = ((split x s).1, member x s, (split x s).2).
Proof. by move=> /(splitMember_split x); case: (split x s) => [? ?]. Qed.

Theorem split_filter (x : Int) (s : IntSet) :
  WF s ->
  split x s = (filter (fun y => y < x) s, filter (fun y => y > x) s).
Proof.
  move=> [fs Sem_s].
  apply split_Sem with fs => //= l fl r fr Sem_l Sem_r def_fl def_fr.
  f_equal; eauto using Sem_unique, filter_Sem.
Qed.

Theorem splitMember_filter (x : Int) (s : IntSet) :
  WF s ->
  splitMember x s = (filter (fun y => y < x) s, member x s, filter (fun y => y > x) s).
Proof.
  by move=> WFs; move: (WFs) (WFs) => /(splitMember_split' x) -> /(split_filter x) ->.
Qed.

(******************************************************************************)
(** Basic properties of Sem **)

Theorem Sem_Desc0 : forall s f, Sem s f -> exists r, Desc0 s r f.
Proof.
  apply Sem_ind => [f false_f | s r f Desc_srf].
  - by exists (0%Z,0%N); apply Desc0Nil.
  - by exists r; apply (Desc0NotNil s r f r f); rewrite // isSubrange_refl.
Qed.

Theorem Sem_extensional (s : IntSet) (f1 f2 : Z -> bool) :
  Sem s f1 ->
  Sem s f2 ->
  f1 =1 f2.
Proof.
  move=> S1 S2 k;
    inversion S1 as [f1' E1 | s1 r1 f1' D1];
    subst f1' s;
    inversion S2 as [f2' E2 | s2 r2 f2' D2];
    subst f2';
    try subst s1; try subst s2.
  - by rewrite E1 E2.
  - inversion D2.
  - inversion D1.
  - by eauto using Desc_unique_f.
Qed.

Theorem Sem_member (s : IntSet) :
  WF s ->
  Sem s (member ^~ s).
Proof.
  move=> [f def_f].
  apply Sem_change_f with f => //.
  by move: (def_f) => /member_Sem.
Qed.

(******************************************************************************)
(** Low-level IntSet membership theorems **)

Theorem Nil_member :
  forall k, member k Nil = false.
Proof. done. Qed.

Theorem Nil_member' :
  forall k, ~~ member k Nil.
Proof. done. Qed.

Theorem Tip_member (p : Prefix) (bm : BitMap) :
  WF (Tip p bm) ->
  forall k, member k (Tip p bm) = bitmapInRange (Z.shiftr p (Z.log2 (Z.of_N WIDTH)), N.log2 WIDTH) bm k.
Proof.
  move=> [fs SEMs] k;
    inversion SEMs  as [| s' rng fs' DESCs]; subst s' fs';
    inversion DESCs as [p' bm' rng' fs' NN_p def_p def_bits_r def_fs isbm_bm |]; subst p' bm' rng' fs' p.
  erewrite member_Desc, def_fs; last eassumption.
  f_equal.
  replace rng with (fst rng, rBits rng) by rewrite -surjective_pairing //.
  f_equal => //; rewrite /rPrefix.
  rewrite Z.shiftr_shiftl_l; last apply N2Z.is_nonneg.
  by rewrite def_bits_r /=.
Qed.

Theorem Bin_member (p : Prefix) (msk : Mask) (l r : IntSet) :
  WF (Bin p msk l r) ->
  forall k, member k (Bin p msk l r) = member k l || member k r.
Proof.
  move=> [fs SEMs] k;
    inversion SEMs  as [| s' rng fs' DESCs];
    subst s' fs';
    inversion DESCs as [| l' rng_l fl r' rng_r fr p' msk' rng' fs'
                          DESCl DESCr POS_bits SUBRl SUBRr def_p def_msk def_fs];
    subst l' r' p' msk' rng' fs' p msk.
  erewrite !member_Desc, def_fs; eauto.
Qed.

Theorem Bin_left_lt_right {p msk : Z} {l r : IntSet} :
  WF (Bin p msk l r) ->
  forall kl, member kl l -> forall kr, member kr r -> kl < kr.
Proof.
  move=> WFs; move: (WFs) => [fs SEMs];
    inversion SEMs as [|s' rng_s fs' DESCs];
    subst s' fs';
    inversion DESCs as [|l' rng_l fl r' rng_r fr p' msk' rng_s' fs'
                         DESCl DESCr POSrng subrange_l subrange_r def_p def_m def_fs];
    subst p' msk' l' r' rng_s' fs' p msk.
  
  move=> kl MEM_kl kr MEM_kr.
  move: MEM_kl MEM_kr; erewrite !member_Desc; try eassumption.
  move=> /(Desc_inside DESCl)/(inRange_isSubrange_true _ _ _ subrange_l)/inRange_bounded IN_kl
         /(Desc_inside DESCr)/(inRange_isSubrange_true _ _ _ subrange_r)/inRange_bounded IN_kr.
  move: IN_kl IN_kr; rewrite rPrefix_halfRange_otherhalf // => IN_kl IN_kr.
  apply/Z.ltb_spec0; omega.
Qed.

(******************************************************************************)
(** Working with IntSets by membership **)

Theorem eqIntSetMemberP {s1 s2 : IntSet} :
  WF s1 -> WF s2 ->
  reflect (forall x, (0 <= x)%Z -> member x s1 = member x s2) (s1 == s2).
Proof.
  move=> WF1 WF2.
  set s1' := exist _ _ WF1; set s2' := exist _ _ WF2.
  move: (IntSetWSfun.equal_1 s1' s2') (IntSetWSfun.equal_2 s1' s2').
  rewrite /= /IntSetWSfun.Equal /= /IntSetWSfun.In_set => Equal_eq eq_Equal.
  apply iff_reflect; split.
  - move=> KEYS; apply Equal_eq=> /= n; apply eq_iff_eq_true.
    move: KEYS; cbv -[member Z.of_N "<="%Z eqb is_true].
    apply; apply N2Z.is_nonneg.
  - move=> /eq_Equal KEYS n POS_n.
    move: (KEYS (Z.to_N n)); cbv -[member Z.of_N Z.to_N eqb iff].
    rewrite Z2N.id //.
    by case: (member _ s1); case: (member _ s2); intuition.
Qed.

(* Prove the spec for `forall k, member k (F ... s ...) = ...` in terms of
   `F_Sem`, where `F` is a function that produces an `IntSet` from another
   `IntSet`. *)
Ltac member_by_Sem SEM :=
  repeat (move=> /Sem_member ? || move=> ?);
  erewrite member_Sem;
    last (eapply SEM; try eassumption; reflexivity);
    reflexivity.

Theorem insert_member (x : Int) (s : IntSet) :
  (0 <= x)%Z -> WF s ->
  forall k, member k (insert x s) = (k == x) || member k s.
Proof. member_by_Sem insert_Sem. Qed.

Theorem delete_member (x : Int) (s : IntSet) :
  (0 <= x)%Z -> WF s ->
  forall k, member k (delete x s) = (k /= x) && member k s.
Proof. member_by_Sem delete_Sem. Qed.

Theorem union_member (s1 s2 : IntSet) :
  WF s1 -> WF s2 ->
  forall k, member k (union s1 s2) = member k s1 || member k s2.
Proof. member_by_Sem union_Sem. Qed.

Theorem intersection_member (s1 s2 : IntSet) :
  WF s1 -> WF s2 ->
  forall k, member k (intersection s1 s2) = member k s1 && member k s2.
Proof. member_by_Sem intersection_Sem. Qed.

Theorem difference_member (s1 s2 : IntSet) :
  WF s1 -> WF s2 ->
  forall k, member k (difference s1 s2) = member k s1 && ~~ member k s2.
Proof. member_by_Sem difference_Sem. Qed.

Theorem unions_member (ss : list IntSet) :
  Forall WF ss ->
  forall k, member k (unions ss) = any (member k) ss.
Proof.
  move=> WF_ss k.
  rewrite /unions hs_coq_foldl_list Foldable_any_ssreflect.
  rewrite -(orFb (has _ _)); change false with (member k empty); have: (WF empty) by [].
  elim: ss empty WF_ss => [|s ss IH] z WF_sss WF_z //=;
    [by rewrite orbF | inversion WF_sss as [|s' ss' WF_s WF_ss]; subst s' ss'].
  rewrite IH //; last by apply union_WF.
  by rewrite union_member // orbA.
Qed.

Theorem empty_member :
  forall k, member k empty = false.
Proof. done. Qed.

Theorem empty_member' :
  forall k, ~~ member k empty.
Proof. done. Qed.

Theorem singleton_member (x : Int) :
  (0 <= x)%Z ->
  forall k, member k (singleton x) = (k == x).
Proof. member_by_Sem singleton_Sem. Qed.

Theorem null_member (s : IntSet) :
  WF s ->
  null s <-> forall k, member k s = false.
Proof.
  move=> [f Sem_s]; move: (Sem_s) => /null_Sem null_Sem_iff.
  split.
  - move=> null_s k; erewrite member_Sem; last eassumption.
    by apply null_Sem_iff.
  - move=> no_members; apply null_Sem_iff=> k.
    erewrite <-member_Sem; last eassumption.
    by apply no_members.
Qed.

Theorem disjoint_member (s1 s2 : IntSet) :
  WF s1 -> WF s2 ->
  disjoint s1 s2 <-> (forall k, ~~ (member k s1 && member k s2)).
Proof.
  move=> [f1 Sem1] [f2 Sem2]; move: (disjoint_Sem _ _ _ _ Sem1 Sem2) => disjoint_iff.
  split.
  - move=> /disjoint_iff is_disjoint k.
    erewrite !member_Sem; try eassumption.
    case: (is_disjoint k) => -> /=; intuition.
  - move=> is_disjoint; apply disjoint_iff => k.
    erewrite <-!member_Sem; try eassumption.
    move: (is_disjoint k) => [] /negbTE ->; tauto.
Qed.

Theorem isSubsetOf_member (s1 s2 : IntSet) :
  WF s1 -> WF s2 ->
  isSubsetOf s1 s2 <-> (forall k, member k s1 -> member k s2).
Proof.
  move=> [f1 Sem1] [f2 Sem2]; move: (isSubsetOf_Sem _ _ _ _ Sem1 Sem2) => subset_iff.
  split.
  - move=> /subset_iff is_subset k.
    erewrite !member_Sem; try eassumption.
    apply is_subset.
  - move=> is_subset; apply subset_iff=> k.
    erewrite <-!member_Sem; try eassumption.
    apply (is_subset k).
Qed.

Theorem isProperSubsetOf_member (s1 s2 : IntSet) :
  WF s1 -> WF s2 ->
  isProperSubsetOf s1 s2 <-> (forall k, member k s1 -> member k s2) /\ (s1 /= s2).
Proof.
  move=> [f1 Sem1] [f2 Sem2]; move: (isProperSubsetOf_Sem _ _ _ _ Sem1 Sem2) => proper_subset_iff.
  split.
  - move=> /proper_subset_iff [is_subset is_proper]; split.
    + move=> k; erewrite !member_Sem; try eassumption.
      apply is_subset.
    + rewrite Neq_inv; apply/Eq_eq=> ?; subst s2.
      case: is_proper => [] i; apply.
      erewrite Sem_extensional; eauto.
  - move=> [is_subset is_proper]; apply proper_subset_iff; split.
    + move=> k; erewrite <-!member_Sem; try eassumption.
      apply (is_subset k).
    + have distinct: s1 <> s2 by move=> ?; subst; move: is_proper; rewrite Neq_inv Eq_refl.
      eapply Sem_differ_witness; eassumption.
Qed.

Theorem fromList_member (xs : list Int) :
  Forall (fun x => 0 <= x)%Z xs ->
  forall k, member k (fromList xs) = elem k xs.
Proof.
  move=> POS_xs k.
  move: (fromList_Sem xs POS_xs) => [f [SEM DEF]].
  erewrite member_Sem; last by eapply SEM.
  move: (DEF k); case: (f k) => DEF_k.
  all: by symmetry; apply/elemP/DEF_k.
Qed.

Theorem toList_member (s : IntSet) :
  WF s ->
  forall k, elem k (toList s) = member k s.
Proof.
  move=> /Sem_member/toList_In SEM k.
  by case CONT: (member k s) (SEM k) => SEM_k; apply/elemP/SEM_k.
Qed.

Theorem toAscList_member (s : IntSet) :
  WF s ->
  forall k, elem k (toAscList s) = member k s.
Proof. apply toList_member. Qed.

Theorem toDescList_member (s : IntSet) :
  WF s ->
  forall k, elem k (toDescList s) = member k s.
Proof. 
  move=> WF_s; rewrite toDescList_spec // => k.
  by rewrite rev_elem toList_member.
Qed.

Theorem map_member (s : IntSet) (f : Int -> Int) :
  WF s -> (forall k, member k s -> (0 <= f k)%Z) ->
  forall k, member k (map f s) <-> ex2 (fun k' => member k' s) (fun k' => k = f k').
Proof.
  move=> WF_s POS_f k.
  rewrite /map /=; change @GHC.Base.map with @seq.map; rewrite fromList_member.
  - rewrite elem_in; eapply iff_trans.
    + split; first by move=> /mapP/=; apply.
      move=> [k' k'_in ->].
      by apply map_f.
    + split; move=> [k' IN ?]; subst; exists k'=> //.
      * by rewrite -toList_member // elem_in.
      * rewrite in_elem toList_member //.
  - rewrite Forall_forall=> x; rewrite Zle_is_le_bool; move: x.
    rewrite -forallb_forall -Foldable_all_forallb Foldable_all_ssreflect all_map.
    apply/allP=> /= k'.
    rewrite in_elem toList_member // => /POS_f.
    by rewrite Zle_is_le_bool.
Qed.

Theorem filter_member (s : IntSet) (p : Int -> bool) :
  WF s ->
  forall k, member k (filter p s) = member k s && p k.
Proof. member_by_Sem filter_Sem. Qed.

Theorem partition_member_1 (s : IntSet) (p : Int -> bool) :
  WF s ->
  forall k, member k (partition p s).1 = member k s && p k.
Proof. by move=> *; rewrite partition_fst filter_member. Qed.

Theorem partition_member_2 (s : IntSet) (p : Int -> bool) :
  WF s ->
  forall k, member k (partition p s).2 = member k s && ~~ p k.
Proof. by move=> *; rewrite partition_snd // filter_member. Qed.

Theorem split_member_1 (x : Int) (s : IntSet) :
  WF s ->
  forall k, member k (split x s).1 = member k s && (k < x).
Proof. by move=> WFs k; rewrite split_filter //= filter_member. Qed.

Theorem split_member_2 (x : Int) (s : IntSet) :
  WF s ->
  forall k, member k (split x s).2 = member k s && (k > x).
Proof. by move=> WFs k; rewrite split_filter //= filter_member. Qed.

Theorem splitMember_member_1 (x : Int) (s : IntSet) :
  WF s ->
  forall k, member k (splitMember x s).1.1 = member k s && (k < x).
Proof. by move=> WFs k; rewrite splitMember_filter //= filter_member. Qed.

Theorem splitMember_member_bool (x : Int) (s : IntSet) :
  WF s ->
  (splitMember x s).1.2 = member x s.
Proof. by move=> WFs; rewrite splitMember_filter. Qed.

Theorem splitMember_member_2 (x : Int) (s : IntSet) :
  WF s ->
  forall k, member k (splitMember x s).2 = member k s && (k > x).
Proof. by move=> WFs k; rewrite splitMember_filter //= filter_member. Qed.
