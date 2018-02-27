(******************************************************************************)
(** Imports **)

(* SSReflect *)
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype.
Set Bullet Behavior "Strict Subproofs".

(* Basic Haskell libraries *)
Require Import GHC.Base      Proofs.GHC.Base.
Require Import Data.Foldable Proofs.Data.Foldable.

(* IntSet *)
Require Import Data.IntSet.Internal.
Require Import IntSetProofs.
Module IntSetFSet := Foo.

(* Util *)
Require Import HSUtil.

(******************************************************************************)
(** Name dismabiguation -- copied from HSUtil **)

Notation list    := Coq.Init.Datatypes.list.
Notation seq     := Coq.Lists.List.seq.
Notation reflect := ssrbool.reflect.

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
(** Working with IntSets by membership **)

Theorem eqIntSetMemberP {s1 s2 : IntSet} :
  WF s1 -> WF s2 ->
  reflect (forall x, (0 <= x)%Z -> member x s1 = member x s2) (s1 == s2).
Proof.
  move=> WF1 WF2.
  set s1' := exist _ _ WF1; set s2' := exist _ _ WF2.
  move: (IntSetFSet.equal_1 s1' s2') (IntSetFSet.equal_2 s1' s2').
  rewrite /= /IntSetFSet.Equal /= /IntSetFSet.In_set => Equal_eq eq_Equal.
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

Theorem isSubsetOf_member (s1 s2 : IntSet) :
  WF s1 -> WF s2 ->
  isSubsetOf s1 s2 <-> (forall k, member k s1 ==> member k s2).
Proof.
  move=> [f1 Sem1] [f2 Sem2]; move: (isSubsetOf_Sem _ _ _ _ Sem1 Sem2) => subset_iff.
  split.
  - move=> /subset_iff is_subset k.
    erewrite !member_Sem; try eassumption.
    apply/implyP/is_subset.
  - move=> is_subset; apply subset_iff=> k.
    erewrite <-!member_Sem; try eassumption.
    move: (is_subset k) => /implyP; apply.
Qed.

Theorem isProperSubsetOf_member (s1 s2 : IntSet) :
  WF s1 -> WF s2 ->
  isProperSubsetOf s1 s2 <-> (forall k, member k s1 ==> member k s2) /\ (s1 /= s2).
Proof.
  move=> [f1 Sem1] [f2 Sem2]; move: (isProperSubsetOf_Sem _ _ _ _ Sem1 Sem2) => proper_subset_iff.
  split.
  - move=> /proper_subset_iff [is_subset is_proper]; split.
    + move=> k; erewrite !member_Sem; try eassumption.
      apply/implyP/is_subset.
    + rewrite Neq_inv; apply/Eq_eq=> ?; subst s2.
      case: is_proper => [] i; apply.
      erewrite Sem_extensional; eauto.
  - move=> [is_subset is_proper]; apply proper_subset_iff; split.
    + move=> k; erewrite <-!member_Sem; try eassumption.
      move: (is_subset k) => /implyP; apply.
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

Theorem partition_filter (s : IntSet) (p : Int -> bool) :
  WF s ->
  partition p s = (filter p s, filter (fun k => ~~ p k) s).
Proof. by move=> WF_s; rewrite -partition_fst -partition_snd //; case: (partition p s). Qed.

Theorem partition_member_1 (s : IntSet) (p : Int -> bool) :
  WF s ->
  forall k, member k (partition p s).1 = member k s && p k.
Proof. by move=> *; rewrite partition_fst filter_member. Qed.

Theorem partition_member_2 (s : IntSet) (p : Int -> bool) :
  WF s ->
  forall k, member k (partition p s).2 = member k s && ~~ p k.
Proof. by move=> *; rewrite partition_snd // filter_member. Qed.
