Require Import Omega.
Require Import Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Bool.Bool.
Local Open Scope Z_scope.

Require Import BitUtils.
Require Import CTZ.
Require Import DyadicIntervals.
Require Import Tactics.
Require Import OrdTactic.

(** ** Utilities about sorted (specialized to [N.lt]) *)

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Sorted.

Lemma sorted_append:
  forall l1 l2 x,
  StronglySorted N.lt l1 ->
  StronglySorted N.lt l2 ->
  (forall y, In y l1 -> y < x)%N ->
  (forall y, In y l2 -> x <= y)%N ->
  StronglySorted N.lt (l1 ++ l2).
Proof.
  intros ??? Hsorted1 Hsorted2 Hlt Hge.
  induction Hsorted1.
  * apply Hsorted2.
  * simpl. apply SSorted_cons.
    + apply IHHsorted1.
      intros y Hy.
      apply Hlt.
      right.
      assumption.
    + rewrite Forall_forall.
      intros z Hz.
      rewrite in_app_iff in Hz.
      destruct Hz.
      - rewrite Forall_forall in H.
        apply H; auto.
      - apply N.lt_le_trans with (m := x).
        apply Hlt. left. reflexivity.
        apply Hge. assumption.
Qed.

Lemma sorted_append':
  forall a l1 l2 (f : a -> Z) x,
  StronglySorted (fun x y => Z.lt (f x) (f y)) l1 ->
  StronglySorted (fun x y => Z.lt (f x) (f y)) l2 ->
  (forall y, In y l1 -> f y <  f x)%Z ->
  (forall y, In y l2 -> f x <= f y)%Z ->
  StronglySorted (fun x y => Z.lt (f x) (f y)) (l1 ++ l2).
Proof.
  intros ????? Hsorted1 Hsorted2 Hlt Hge.
  induction Hsorted1.
  * apply Hsorted2.
  * simpl. apply SSorted_cons.
    + apply IHHsorted1.
      intros y Hy.
      apply Hlt.
      right.
      assumption.
    + rewrite Forall_forall.
      intros z Hz.
      rewrite in_app_iff in Hz.
      destruct Hz.
      - rewrite Forall_forall in H.
        apply H; auto.
      - apply Z.lt_le_trans with (m := f x).
        apply Hlt. left. reflexivity.
        apply Hge. assumption.
Qed.


Lemma StronglySorted_map:
  forall a b (R1 : a -> a -> Prop) (R2 : b -> b -> Prop) (f : a -> b) (l : list a),
    StronglySorted R1 l ->
    (forall (x y : a), In x l -> In y l -> R1 x y -> R2 (f x) (f y)) ->
    StronglySorted R2 (List.map f l).
Proof.
  intros.
  induction H.
  * simpl. constructor.
  * simpl. constructor.
    + apply IHStronglySorted; intuition.
    + clear IHStronglySorted.
      rewrite Forall_forall.
      intros.
      rewrite in_map_iff in H2.
      destruct H2 as [?[[]?]].
      apply H0.
      left. reflexivity.
      right. assumption.
      rewrite Forall_forall in H1.
      apply H1.
      assumption.
Qed.

(** *** Stuff about [option] *)

Definition oro {a} : option a -> option a -> option a :=
  fun x y => match x with
    | Some v => Some v
    | None => y
    end.

(** ** IntMap-specific operations

These definitions and lemmas are used to link some concepts from the IntMap
implementation to the range sets above.
*)

Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import GHC.Num.
Import GHC.Num.Notations.
Require Import Data.Bits.
Import Data.Bits.Notations.
Require Import Data.IntSet.InternalWord.
Require Import IntWord.
Require Import Popcount.
Local Open Scope N_scope.
Set Bullet Behavior "Strict Subproofs".

(** A tactic to remove all relevant Haskell type class methods, and
exposes the underlying Coq concepts.
*)

Ltac unfoldMethods :=
  unfold op_zsze__, op_zeze__, Eq___Int, Eq___Word, Eq___IntSet, op_zsze____, op_zeze____,
         op_zl__, op_zg__, Ord__Int, Ord__Word, op_zl____,  op_zg____,
         GHC.Real.fromIntegral, GHC.Real.instance__Integral_Int__74__,
         fromInteger, GHC.Real.toInteger,
         Num_Word__, Num__Word, Num__Int,
         op_zm__, op_zp__, Num_Integer__,
         Prim.seq,
         op_zdzn__,
         xor, op_zizazi__, op_zizbzi__, Bits.complement,
         Bits__Int, Bits__Word,
         id, op_z2218U__ in *.


(* Move to IntWord *)
Lemma intToN_inj_iff:
  forall i1 i2, intToN i1 = intToN i2 <-> i1 = i2.
Admitted.
Lemma wordToN_inj_iff:
  forall x y, wordToN x = wordToN y <-> x = y.
Admitted.
(* Move to IntWord *)
Lemma wordToN_NToWord: (* Lets add preconditionn later *)
  forall x, wordToN (NToWord x) = x.
Admitted.
Lemma intToN_NToInt: (* Lets add precondition later *)
  forall x, intToN (NToInt x) = x.
Admitted.
Lemma intToZ_ZToInt: (* Lets add precondition later *)
  forall x, intToZ (ZToInt x) = x.
Admitted.
Lemma NToWord_wordToN:
  forall x, NToWord (wordToN x) = x.
Admitted.
Lemma NToInt_intToN:
  forall x, NToInt (intToN x) = x.
Admitted.
Lemma ZToInt_intToZ:
  forall x, ZToInt (intToZ x) = x.
Admitted.


Ltac Int_Word_N :=
  unfold wordFromInt in *;
  rewrite ?intToN_inj_iff, ?wordToN_inj_iff,
          ?wordToN_NToWord, ?intToN_NToInt,
          ?NToWord_wordToN, ?NToInt_intToN,
          ?intToZ_ZToInt,   ?ZToInt_intToZ
  in *.


(** We hardcode the width of the leaf bit maps to 64 bits *)

Definition WIDTH := 64%N.
Definition tip_width := N.log2 WIDTH.

(** *** Lemmas about [prefixOf] *)

Lemma rPrefix_shiftr:
  forall e,
  NToInt (rPrefix (N.shiftr (intToN e) tip_width, tip_width)) = prefixOf e.
Admitted.
(* 
Proof.
  intros.
  unfold rPrefix, prefixOf, suffixBitMask.
  unfoldMethods.
  rewrite <- N.ldiff_ones_r.
  reflexivity.
Qed.
*)
(*  
Lemma prefixOf_eq_shiftr:
  forall i p, 
  (prefixOf i =? N.shiftl p tip_width) = ((N.shiftr i tip_width) =? p).
Proof.
  intros.
  unfold prefixOf, suffixBitMask.
  unfoldMethods.
  rewrite -> N.ldiff_ones_r.
  replace tip_width with 6 by reflexivity.
  rewrite eq_iff_eq_true.
  rewrite !N.eqb_eq.
  rewrite -> N_shiftl_inj by omega.
  reflexivity.
Qed.
 *)

(** This lemma indicaes that [prefixOf] implements the check of whether
    the number is part of a tip-sized range. *)

Lemma prefixOf_eqb_spec:
  forall r i,
  (rBits r = N.log2 WIDTH)%N ->
  intToN (prefixOf i) =? rPrefix r = inRange (intToN i) r.
Admitted.
(*
Proof.
  intros.
  destruct r; simpl in *; subst.
  rewrite prefixOf_eq_shiftr.
  reflexivity.
Qed.
*)

(* Lemma prefixOf_mono:
  forall x y, x <= y -> prefixOf x <= prefixOf y.
Proof.
  intros.
  rewrite <- !rPrefix_shiftr.
  unfold rPrefix.
  rewrite !N.shiftl_mul_pow2 by (intro Htmp; inversion Htmp).
  rewrite !N.shiftr_div_pow2 by (intro Htmp; inversion Htmp).
  apply N.mul_le_mono_nonneg_r. nonneg.
  apply N.div_le_mono. apply N.pow_nonzero; Nomega.
  assumption.
Qed.
*)

(* Lemma prefixOf_rPrefix: forall r, rBits r = N.log2 WIDTH ->
  (prefixOf (rPrefix r) = rPrefix r).
Proof.
  intros.
  destruct r as [p b]. simpl in *. subst.
  rewrite <- rPrefix_shiftr.
  unfold rPrefix, tip_width, tip_width. simpl N.log2.
  rewrite N.shiftr_shiftl_l by reflexivity.
  replace (6 - 6) with 0 by Nomega.
  rewrite N.shiftl_0_r.
  reflexivity.
Qed.   *)

(* Lemma prefixOf_suffixOf:
  forall i, prefixOf i + suffixOf i = i.
Proof.
  intros.
  rewrite <- rPrefix_shiftr.
  unfold rPrefix, tip_width, tip_width. simpl id.
  rewrite N.shiftr_div_pow2 by omega.
  rewrite N.shiftl_mul_pow2 by omega.
  unfold prefixOf, suffixOf, suffixBitMask, WIDTH in *.
  unfoldMethods.
  simpl N.log2.
  rewrite N.land_ones by omega.
  symmetry.
  rewrite N.mul_comm.
  apply N.div_mod.
  intro Htmp; inversion Htmp.
Qed.
 *)

(** *** Lemmas about [suffixOf] *)

(* Lemma suffixOf_lt_WIDTH: forall e, suffixOf e < WIDTH.
  intros.
  unfold suffixOf, suffixBitMask.
  unfoldMethods.
  rewrite N.land_ones.
  change (e mod 64 < 64).
  apply N.mod_upper_bound.
  Nomega.
Qed.
 *)

Lemma bitmapOfSuffix_pow : forall x, wordToN (bitmapOfSuffix (NToInt x)) = 2^x.
Admitted.
(*
Proof. intros. apply N.shiftl_1_l. Qed.
 *)

(* Lemma suffixOf_plus_bitmapOf:
  forall x,
  (N.ones (suffixOf x) + bitmapOf x)%N = N.ones (N.succ (suffixOf x)).
Proof.
  intros.
  unfold bitmapOf.
  rewrite bitmapOfSuffix_pow.
  rewrite !N.ones_equiv.
  rewrite N.pow_succ_r by nonneg.
  Nomega.
Qed.
 *)

(** *** Operation: [rMask]
Calculates a mask in the sense of the IntSet implementation:
A single bit set just to the right of the prefix.
(Somewhat illdefined for singleton ranges).
*)

Definition rMask   : range -> N :=
   fun '(p,b) => 2^(b - 1).

(** *** Verification of [nomatch] *)

Lemma nomatch_spec:
  forall i r,
  (0 < rBits r)%N ->
  nomatch i (NToInt (rPrefix r)) (NToInt (rMask r)) =
  negb (inRange (intToN i) r).
(* Proof.
  intros.
  destruct r as [p b]. simpl in *.
  unfold nomatch, zero, inRange.
  unfoldMethods.
  unfold mask, maskW.
  unfoldMethods.
  f_equal.
  rewrite eq_iff_eq_true.
  rewrite !N.eqb_eq.
  rewrite <- N.pow_succ_r  by Nomega.
  replace (N.succ (b - 1)) with b by Nomega.
  rewrite N.sub_1_r.
  rewrite <- N.ones_equiv.
  rewrite -> N.ldiff_ones_r by nonneg.
  rewrite -> N_shiftl_inj by nonneg.
  reflexivity.
Qed.
 *)
Admitted.

Lemma match_nomatch: forall x p ms,
  match_ x p ms = negb (nomatch x p ms).
Proof.
  intros. unfold match_, nomatch. unfoldMethods.
  rewrite negb_involutive.
  reflexivity.
Qed.


(** *** Verification of [zero] *)

Lemma zero_spec:
  forall i r,
  (0 < rBits r)%N ->
  zero i (NToInt (rMask r)) = negb (N.testbit (intToN i) (rBits r - 1)).
Proof.
  intros.
  destruct r as [p b]. simpl in *.
  unfold zero. unfoldMethods.
Admitted.
(* 
  apply N_land_pow2_eq.
Qed. *)

(**
The IntSet code has a repeating pattern consisting of calls to [nomatch] and [zero].
The following two lemmas capture that pattern concisely.
*)

Lemma nomatch_zero:
  forall {a} i r (P : a -> Prop) left right otherwise,
  (0 < rBits r)%N ->
  (inRange (intToN i) r = false -> P otherwise) ->
  (inRange (intToN i) (halfRange r false) = true  -> inRange (intToN i) (halfRange r true) = false -> P left) ->
  (inRange (intToN i) (halfRange r false) = false -> inRange (intToN i) (halfRange r true) = true -> P right) ->
  P (if nomatch i (NToInt (rPrefix r)) (NToInt (rMask r)) then otherwise else 
     if zero i (NToInt (rMask r)) then left else right).
Proof.
  intros.
  rewrite nomatch_spec by auto.
  rewrite if_negb.
  destruct (inRange (intToN i) r) eqn:?.
  * rewrite zero_spec by auto. 
    rewrite if_negb.
    destruct (N.testbit (intToN i) (rBits r - 1)) eqn:Hbit.
    + apply H2.
      rewrite halfRange_inRange_testbit by auto. rewrite Hbit. reflexivity.
      rewrite halfRange_inRange_testbit by auto. rewrite Hbit. reflexivity.
    + apply H1.
      rewrite halfRange_inRange_testbit by auto. rewrite Hbit. reflexivity.
      rewrite halfRange_inRange_testbit by auto. rewrite Hbit. reflexivity.
  * apply H0; reflexivity.
Qed.

Lemma nomatch_zero_smaller:
  forall {a} r1 r (P : a -> Prop) left right otherwise,
  (rBits r1 < rBits r)%N ->
  (rangeDisjoint r1 r = true -> P otherwise) ->
  (isSubrange r1 (halfRange r false) = true  -> isSubrange r1 (halfRange r true) = false -> P left) ->
  (isSubrange r1 (halfRange r false) = false -> isSubrange r1 (halfRange r true) = true -> P right) ->
  P (if nomatch (NToInt (rPrefix r1)) (NToInt (rPrefix r)) (NToInt (rMask r)) then otherwise else 
     if zero (NToInt (rPrefix r1)) (NToInt (rMask r)) then left else right).
Proof.
  intros ????????.
  assert (rBits r1 <= rBits r)%N by Nomega.
  assert (forall h, rBits r1 <= rBits (halfRange r h))%N
    by (intros; rewrite rBits_halfRange; Nomega).
  rewrite <- smaller_not_subrange_disjoint_iff; auto.
  repeat rewrite <- smaller_inRange_iff_subRange by auto.
  apply nomatch_zero; only 1: Nomega.
  all: Int_Word_N; intuition.
Qed.

(** Two ranges with the same size, are either the same, or they are disjoint *)
Lemma same_size_compare:
  forall {a} r1 r2 (P : a -> Prop) same different,
  (rBits r1 = rBits r2) ->
  (r1 = r2 -> P same) ->
  (rangeDisjoint r1 r2 = true -> P different) ->
  P (if rPrefix r1 =? rPrefix r2 then same else different).
Proof.
  intros.
  destruct (N.eqb_spec (rPrefix r1) (rPrefix r2)).
  * apply H0.
    apply rPrefix_rBits_range_eq; auto.
  * apply H1.
    apply different_prefix_same_bits_disjoint; auto.
Qed.


(** *** Verification of [branchMask] *)

Lemma branchMask_spec:
  forall r1 r2,
  branchMask (NToInt (rPrefix r1)) (NToInt (rPrefix r2)) = NToInt (rMask (commonRangeDisj r1 r2)).
Proof.
  intros.
  destruct r1 as [p1 b1], r2 as [p2 b2].
  simpl.
  unfold branchMask.
  unfold msDiffBit.
  rewrite N.add_sub.
Admitted. (* 
  reflexivity.
Qed. *)

(** *** Verification of [mask] *)

Lemma mask_spec:
  forall r1 r2,
  mask (NToInt (rPrefix r1)) (NToInt (rMask (commonRangeDisj r1 r2))) = NToInt (rPrefix (commonRangeDisj r1 r2)).
Proof.
  intros.
  assert (0 < msDiffBit (rPrefix r1) (rPrefix r2))%N by apply msDiffBit_pos.
  destruct r1 as [p1 b1], r2 as [p2 b2].
  unfold mask, maskW.
  cbn -[N.mul] in *.
  rewrite <- N.ldiff_ones_r by nonneg.
Admitted.
(*
  rewrite <- N.pow_succ_r'.
  rewrite <- N.add_1_r.
  rewrite N.sub_add by lia.
  rewrite N.sub_1_r.
  rewrite <- N.ones_equiv.
  reflexivity.
Qed.
*)

(** *** Verification of [shorter] *)

Lemma shorter_spec:
  forall r1 r2,
  (0 < rBits r1)%N ->
  (0 < rBits r2)%N ->
  shorter (NToInt (rMask r1)) (NToInt (rMask r2)) = (rBits r2 <? rBits r1)%N.
Proof.
  intros.
  destruct r1 as [p1 b1], r2 as [p2 b2]. simpl in *.
Admitted.
(*  
  change ((2 ^ (b2 - 1)) <? (2 ^ (b1 - 1)) = (b2 <? b1)).
  apply eq_true_iff_eq.
  rewrite !N.ltb_lt.
  rewrite <- N.pow_lt_mono_r_iff by Nomega.
  Nomega.
Qed.
*)

(** *** Operation: [bitmapInRange]

Looks up values, which are in the given range, as bits in the given bitmap.
*)

Definition bitmapInRange r bm i :=
  if inRange i r then N.testbit (wordToN bm) (N.land i (N.ones (rBits r)))
                 else false.

Lemma bitmapInRange_outside:
  forall r bm i, inRange i r = false -> bitmapInRange r bm i = false.
Proof. intros. unfold bitmapInRange. rewrite H. reflexivity. Qed.

Lemma bitmapInRange_inside:
  forall r bm i, bitmapInRange r bm i = true -> inRange i r = true.
Proof. intros. unfold bitmapInRange in *. destruct (inRange i r); auto.  Qed.


Lemma bitmapInRange_0:
  forall r i, bitmapInRange r (NToWord 0%N) i = false.
Proof.
  intros.
  unfold bitmapInRange.
  destruct (inRange i r); auto.
Admitted.
(* Qed. *)

Lemma bitmapInRange_lor:
  forall r bm1 bm2 i,
    bitmapInRange r (NToWord (N.lor bm1 bm2)) i =
    orb (bitmapInRange r (NToWord bm1) i) (bitmapInRange r (NToWord bm2) i).
Proof.
  intros.
  unfold bitmapInRange.
  destruct (inRange i r); try reflexivity.
Admitted. (* 
  rewrite N.lor_spec; reflexivity.
Qed. *)

Lemma bitmapInRange_lxor:
  forall r bm1 bm2 i,
    bitmapInRange r (NToWord (N.lxor bm1 bm2)) i =
    xorb (bitmapInRange r (NToWord bm1) i) (bitmapInRange r (NToWord bm2) i).
Proof.
  intros.
  unfold bitmapInRange.
  destruct (inRange i r); try reflexivity.
Admitted.
(*   rewrite N.lxor_spec; reflexivity.
Qed.
 *)
 
 Lemma bitmapInRange_lnot: (* Misses some precondition *)
  forall r bm i,
    bitmapInRange r (NToWord (N.lnot bm WIDTH)) i =
    negb (bitmapInRange r (NToWord bm) i).
Admitted.
 
Lemma bitmapInRange_land:
  forall r bm1 bm2 i,
    bitmapInRange r (NToWord (N.land bm1 bm2)) i =
    andb (bitmapInRange r (NToWord bm1) i) (bitmapInRange r (NToWord bm2) i).
Proof.
  intros.
  unfold bitmapInRange.
  destruct (inRange i r); try reflexivity.
Admitted. (* 
  rewrite N.land_spec; reflexivity.
Qed. *)

Lemma bitmapInRange_ldiff:
  forall r bm1 bm2 i,
    bitmapInRange r (NToWord (N.ldiff bm1 bm2)) i =
    andb (bitmapInRange r (NToWord bm1) i) (negb (bitmapInRange r (NToWord bm2) i)).
Proof.
  intros.
  unfold bitmapInRange.
  destruct (inRange i r); try reflexivity.
Admitted.
(* 
  rewrite N.ldiff_spec; reflexivity.
Qed. *)


Lemma bitmapInRange_bitmapOf:
  forall e i,
  bitmapInRange (N.shiftr (intToN e) 6, N.log2 WIDTH) (bitmapOf e) i = (i =? (intToN e)).
Proof.
  intros.
  unfold bitmapInRange, inRange. simpl id.
  rewrite <- andb_lazy_alt.
  unfold bitmapOf, suffixOf, suffixBitMask.
  unfoldMethods.
  rewrite bitmapOfSuffix_pow.
  rewrite -> N.pow2_bits_eqb by nonneg.
  rewrite -> N.eqb_sym.
  Int_Word_N.
Admitted.
(*  
  rewrite <- N_eq_shiftr_land_ones.
  apply N.eqb_sym.
Qed.
*)

Lemma bitmapInRange_pow:
  forall r e i,
  (e < 2^rBits r)%N ->
  bitmapInRange r (NToWord (2 ^ e))%N i = (rPrefix r + e =? i).
Proof.
  intros.
  destruct r as [p b].
  unfold bitmapInRange.
  simpl in *.
  destruct (N.eqb_spec (N.shiftr i b) p).
Admitted.
(*
  * rewrite N.pow2_bits_eqb.
    transitivity (e =? N.land i (N.ones b)).
    - rewrite eq_iff_eq_true.
      rewrite !N.eqb_eq.
      intuition.
    - rewrite eq_iff_eq_true.
      rewrite !N.eqb_eq.
      rewrite N.land_ones by nonneg.
      rewrite N.shiftr_div_pow2 in e0 by nonneg.
      rewrite N.div_mod with (a := i) (b := 2^b) at 2
        by (apply N.pow_nonzero; Nomega).
      rewrite N.shiftl_mul_pow2 by nonneg.
      rewrite N.mul_comm.
      subst; Nomega.
  * symmetry.
    rewrite N.eqb_neq.
    contradict n.
    subst.
    rewrite N.shiftr_div_pow2 by nonneg.
    rewrite N.shiftl_mul_pow2 by nonneg.
    rewrite N.div_add_l by (apply N.pow_nonzero; Nomega).
    enough (e/2^b = 0) by lia.
    apply N.div_small.
    assumption.
Qed.
*)

Lemma bitmapInRange_ones:
  forall r n i,
  rBits r = N.log2 WIDTH ->
  inRange i r = true ->
  bitmapInRange r (NToWord (N.ones n)) i = (intToN (suffixOf (NToInt i)) <? n).
Proof.
  intros ?????.
  unfold bitmapInRange; rewrite H0.
  unfold suffixOf, suffixBitMask, WIDTH in *.
  rewrite H; clear H.
  unfoldMethods.
  simpl.
  rewrite eq_iff_eq_true.
  rewrite N.ltb_lt.
Admitted. (*
  rewrite N.ones_spec_iff.
  intros.
  reflexivity.
Qed. *)

(** *** Operation: [intoRange]

This is the inverse of bitmapInRange, in a way.
*)

Definition intoRange r i := N.lor (rPrefix r) i.

Definition inRange_intoRange:
  forall r i,
  (i < 2^(rBits r))%N ->
  inRange (intoRange r i) r = true.
Proof.
  intros.
  destruct r as [p b]; unfold intoRange, inRange, rPrefix, rBits, snd in *; subst.
  rewrite N.shiftr_lor.
  rewrite N.shiftr_shiftl_l by lia.
  replace (_ - _) with 0 by lia.
  rewrite N.shiftr_div_pow2 by nonneg.
  rewrite N.div_small.
  rewrite N.lor_0_r, N.shiftl_0_r. apply N.eqb_refl.
  assumption.
Qed.

Definition bitmapInRange_intoRange:
  forall r i bm,
  (i < 2^(rBits r))%N ->
  bitmapInRange r bm (intoRange r i) = N.testbit (wordToN bm) i.
Proof.
  intros.
  unfold bitmapInRange.
  rewrite inRange_intoRange by assumption.
  f_equal.
  destruct r as [p b]; unfold intoRange, inRange, rPrefix, rBits, snd in *; subst.
  rewrite N.land_lor_distr_l.
  rewrite N_land_shiftl_ones.
  rewrite N.lor_0_l.
  rewrite !N.land_ones by nonneg.
  rewrite N.mod_small by assumption.
  reflexivity.
Qed.

(** *** Operation: [isTipPrefix]

A Tip prefix is a number with [N.log2 WIDTH] zeros at the end.
*)

Definition isTipPrefix (p : N) := N.land p (intToN suffixBitMask) = 0.

Lemma isTipPrefix_suffixMask: forall p, isTipPrefix p -> N.land p (intToN suffixBitMask) = 0.
Proof. intros.  apply H. Qed.


Lemma isTipPrefix_prefixOf: forall e, isTipPrefix (intToN (prefixOf e)).
Proof.
  intros.
  unfold isTipPrefix, prefixOf, suffixBitMask.
  unfoldMethods.
Admitted.
(*
  rewrite N.land_ones.
  rewrite N.ldiff_ones_r.
  rewrite N.shiftl_mul_pow2.
  apply N.mod_mul.
  intro Htmp; inversion Htmp.
Qed. *)

Lemma isTipPrefix_shiftl_shiftr:
   forall p, isTipPrefix p -> p = N.shiftl (N.shiftr p 6) 6.
Proof.
  intros.
  rewrite <- N.ldiff_ones_r.
  symmetry.
  etransitivity.
  Focus 2. apply  N.lor_ldiff_and.
  pose proof (isTipPrefix_suffixMask p H).
  unfold suffixBitMask in H0.
  rewrite H0.
  rewrite N.lor_0_r.
Admitted. (* 
  reflexivity.
Qed. *)


(** *** Operation: [isBitMask]

A Tip bit mask is a non-zero number with [WIDTH] bits.
*)

Definition isBitMask (bm : N) :=
  (0 < bm /\ bm < 2^WIDTH)%N.

(** Sometimes, we need to allow zero. *)

Definition isBitMask0 (bm : N) := (bm < 2^WIDTH)%N.

Create HintDb isBitMask.
Ltac isBitMask := solve [auto with isBitMask].


Lemma isBitMask_isBitMask0:
  forall bm, isBitMask bm -> isBitMask0 bm.
Proof. intros. unfold isBitMask0, isBitMask in *. intuition. Qed.
Hint Resolve isBitMask_isBitMask0 : isBitMask.

Lemma isBitMask0_zero_or_isBitMask:
  forall bm, isBitMask0 bm <-> (bm = 0%N \/ isBitMask bm).
Proof.
  intros.
  unfold isBitMask, isBitMask0.
  assert (0 <= bm)%N by nonneg.
  rewrite N.lt_eq_cases in H.
  intuition; subst; reflexivity.
Qed.

Lemma isBitMask_isBitMask_and_noneg:
  forall bm, isBitMask bm <-> (bm <> 0%N /\ isBitMask0 bm).
Proof.
  intros.
  unfold isBitMask, isBitMask0. Nomega.
Qed.

Lemma isBitMask_testbit:
  forall bm, isBitMask bm -> (exists i, i < WIDTH /\ N.testbit bm i = true)%N.
Proof.
  intros.
  exists (N.log2 bm); intuition.
  * destruct H.
    destruct (N.lt_decidable 0%N (N.log2 bm)).
    - apply N.log2_lt_pow2; try assumption.
    - assert (N.log2 bm = 0%N) by 
        (destruct (N.log2 bm); auto; contradict H1; reflexivity).
      rewrite H2. reflexivity.
  * apply N.bit_log2.
    unfold isBitMask in *.
    destruct bm; simpl in *; intuition; compute in H1; congruence.
Qed.
 
Lemma isBitMask_lor:
  forall bm1 bm2, isBitMask bm1 -> isBitMask bm2 -> isBitMask (N.lor bm1 bm2).
Proof.
  intros.
  assert (0 < N.lor bm1 bm2)%N.
  * destruct (isBitMask_testbit bm1 H) as [j[??]].
    assert (N.testbit (N.lor bm1 bm2) j = true) by
     (rewrite N.lor_spec, H2; auto).
    enough (0 <> N.lor bm1 bm2)%N by 
     (destruct (N.lor bm1 bm2); auto; try congruence; apply pos_pos).
    contradict H3; rewrite <- H3.
    rewrite N.bits_0. congruence.
  * split; try assumption.
    unfold isBitMask in *; destruct H, H0.
    rewrite N_lt_pow2_testbits in *.
    intros j?.
    rewrite N.lor_spec.
    rewrite H2, H3 by assumption.
    reflexivity.
Qed.
Hint Resolve isBitMask_lor : isBitMask.

Lemma isBitMask0_land:
  forall bm1 bm2, isBitMask0 bm1 -> isBitMask0 bm2 -> isBitMask0 (N.land bm1 bm2).
Proof.
  intros.
  unfold isBitMask0 in *.
  rewrite N_lt_pow2_testbits in *.
  intros j?.
  rewrite N.land_spec.
  rewrite H, H0 by assumption.
  reflexivity.
Qed.
Hint Resolve isBitMask0_land : isBitMask.

Lemma isBitMask0_lxor:
  forall bm1 bm2, isBitMask0 bm1 -> isBitMask0 bm2 -> isBitMask0 (N.lxor bm1 bm2).
Proof.
  intros.
  unfold isBitMask0 in *.
  rewrite N_lt_pow2_testbits in *.
  intros j?.
  rewrite N.lxor_spec.
  rewrite H, H0 by assumption.
  reflexivity.
Qed.
Hint Resolve isBitMask0_lxor : isBitMask.


Lemma isBitMask0_ldiff:
  forall bm1 bm2, isBitMask0 bm1 -> isBitMask0 (N.ldiff bm1 bm2).
Proof.
  intros.
  unfold isBitMask0 in *.
  rewrite N_lt_pow2_testbits in *.
  intros j?.
  rewrite N.ldiff_spec.
  rewrite H by assumption.
  reflexivity.
Qed.
Hint Resolve isBitMask0_ldiff : isBitMask.

Lemma isBitMask0_lor:
  forall bm1 bm2, isBitMask0 bm1 -> isBitMask0 bm2 -> isBitMask0 (N.lor bm1 bm2).
Proof.
  intros.
  unfold isBitMask0 in *.
  rewrite N_lt_pow2_testbits in *.
  intros j?.
  rewrite N.lor_spec.
  rewrite H, H0 by assumption.
  reflexivity.
Qed.
Hint Resolve isBitMask0_lor : isBitMask.

Lemma isBitMask0_ones:
  forall n, (n <= WIDTH)%N ->
  isBitMask0 (N.ones n).
Proof.
  intros.
  induction n using N.peano_ind; simpl.
    constructor.
  rewrite N.ones_equiv.
  unfold isBitMask0.
  apply N.pow_le_mono_r with (a:=2%N) in H; [|Nomega].
  assert (0 < 2 ^ N.succ n)%N.
    apply N_pow_pos_nonneg.
    constructor.
  Nomega.
Qed.
Hint Resolve isBitMask0_ones : isBitMask.


Lemma isBitMask_bitmapOf: forall e, isBitMask (wordToN (bitmapOf e)).
Proof.
  intros.
Admitted.
(*   unfold isBitMask, bitmapOf, suffixOf, suffixBitMask, shiftLL.
  unfold op_zizazi__, Bits.complement, Bits__N, instance_Bits_Int, complement_Int.
  unfold fromInteger, Num_Word__.
  rewrite bitmapOfSuffix_pow.
  rewrite N.land_ones.
  constructor.
  * apply N_pow_pos_nonneg. reflexivity.
  * apply N.pow_lt_mono_r. reflexivity.
    apply N.mod_upper_bound; compute; congruence.
Qed. *)
Hint Resolve isBitMask_bitmapOf : isBitMask.

Lemma isBitMask0_outside:
  forall bm i,
    isBitMask0 bm -> (WIDTH <= i)%N -> N.testbit bm i = false.
Proof.
  intros.
  unfold isBitMask0 in H.
  rewrite N_lt_pow2_testbits in H.
  intuition.
Qed.

Lemma isBitMask_log2_lt_WIDTH:
  forall bm,
  isBitMask bm -> (N.log2 bm < WIDTH)%N.
Proof. intros. apply N.log2_lt_pow2; apply H. Qed.
Hint Resolve isBitMask_log2_lt_WIDTH : isBitMask.

Lemma isBitMask_ctz_lt_WIDTH:
  forall bm,
  isBitMask0 bm -> (N_ctz bm < WIDTH)%N.
Proof.
  intros.
  destruct (N.ltb_spec (N_ctz bm) WIDTH); try assumption; exfalso.
  assert (bm = 0%N).
  { apply N.bits_inj; intro j.
    rewrite N.bits_0.
    destruct (N.ltb_spec j WIDTH).
    + apply N_bits_below_ctz; Nomega.
    + apply isBitMask0_outside; assumption.
  }
  subst. unfold WIDTH in H0.
  simpl in H0.
  Nomega.
Qed.
Hint Resolve isBitMask_ctz_lt_WIDTH : isBitMask.

(** *** Verification of [revNat] *)

Require RevNatSlowProofs.

Lemma revNat_spec:
  forall n i, (i < WIDTH)%N ->
  N.testbit (wordToN (revNat n)) i = N.testbit (wordToN n) (WIDTH - 1 - i)%N.
Proof.
Admitted.
(*   exact (RevNatSlowProofs.revNat_spec).
Qed.
 *)

Lemma isBitMask0_revNat:
  forall n, isBitMask0 (wordToN (revNat n)).
Proof.
Admitted.
(*   exact (RevNatSlowProofs.isBitMask0_revNat).
Qed. *)
Hint Resolve isBitMask0_revNat : isBitMask.


Lemma isBitMask0_clearbit:
  forall n i,
  isBitMask0 n -> isBitMask0 (N.clearbit n i).
Proof.
  intros.
  unfold isBitMask0 in *.
  eapply N.le_lt_trans.
  apply clearbit_le.
  assumption.
Qed.
Hint Resolve isBitMask0_clearbit : isBitMask.

Lemma clearbit_revNat:
  forall n i, (i < WIDTH)%N ->
  N.clearbit (wordToN (revNat n)) i
  = wordToN (revNat (NToWord ((N.clearbit (wordToN n) (WIDTH - 1 - i)))))%N.
Proof.
  intros.
  apply N.bits_inj. intro j.
  destruct (N.ltb_spec j WIDTH).
  * rewrite !revNat_spec by assumption.
    rewrite !N.clearbit_eqb.
    rewrite !revNat_spec by assumption.
    destruct (N.eqb_spec i j), (N.eqb_spec (WIDTH - 1 - i) (WIDTH - 1 - j))%N; try reflexivity; try Nomega.
Admitted.
(*   * rewrite !isBitMask0_outside by isBitMask.
    reflexivity.
Qed.
 *)

Lemma revNat_eq_0:
  forall bm, (wordToN (revNat bm) = 0)%N <-> (wordToN bm = 0)%N.
Proof.
  intros. split; intro.
  * apply N.bits_inj; intro j.
    destruct (N.ltb_spec j WIDTH).
Admitted.
(*     - apply N.bits_inj_iff in H0. specialize (H0 (WIDTH - 1 - j)%N).
      rewrite N.bits_0 in *.
      rewrite revNat_spec in H0 by (assumption || Nomega).
      replace (WIDTH - 1 - (WIDTH - 1 - j))%N with j in H0 by Nomega.
      assumption.
    - rewrite N.bits_0 in *.
      apply isBitMask0_outside; auto.
  * subst. reflexivity.
Qed. *)

Lemma revNat_eqb_0:
  forall bm,(wordToN (revNat bm) =? 0)%N = (wordToN bm =? 0)%N.
Proof.
  intros.
  rewrite eq_iff_eq_true.
  rewrite !N.eqb_eq.
  apply revNat_eq_0.
Qed.


Lemma isBitMask_revNat:
  forall n, isBitMask (wordToN n) -> isBitMask (wordToN (revNat n)).
Proof.
  intros.
  rewrite isBitMask_isBitMask_and_noneg in *.
  intuition.
  rewrite revNat_eq_0 in H by assumption. intuition.
Qed.
Hint Resolve isBitMask_revNat : isBitMask.

Lemma revNat_revNat:
  forall n, revNat (revNat n) = n.
Proof.
  intros.
Admitted.
(*
  apply N.bits_inj_iff; intro i.
  destruct (N.ltb_spec i WIDTH).
  * rewrite !revNat_spec; try isBitMask.
    replace (WIDTH - 1 - (WIDTH - 1 - i))%N with i by Nomega.
    reflexivity.
    Nomega.
  * rewrite !isBitMask0_outside; isBitMask.
Qed.
*)

Lemma revNat_lxor:
  forall n m, isBitMask0 n -> isBitMask0 m ->
    revNat (NToWord (N.lxor n m)) =
    NToWord (N.lxor (wordToN (revNat (NToWord n))) (wordToN (revNat (NToWord m)))).
Proof.
  intros.
Admitted.
(*
  apply N.bits_inj_iff; intro i.
  destruct (N.ltb_spec i WIDTH).
  * rewrite !revNat_spec, !N.lxor_spec, !revNat_spec; isBitMask.
  * rewrite N.lxor_spec.
    rewrite !isBitMask0_outside; isBitMask.
Qed.*)

Lemma revNat_ldiff:
  forall n m, isBitMask0 n -> isBitMask0 m ->
    revNat (NToWord (N.ldiff n m)) = NToWord (N.ldiff (wordToN (revNat (NToWord n))) (wordToN (revNat (NToWord m)))).
Proof.
  intros.
Admitted.
(*  
  apply N.bits_inj_iff; intro i.
  destruct (N.ltb_spec i WIDTH).
  * rewrite !revNat_spec, !N.ldiff_spec, !revNat_spec; isBitMask.
  * rewrite N.ldiff_spec.
    rewrite !isBitMask0_outside; isBitMask.
Qed. *)

Lemma pow_isBitMask:
  forall i, (i < WIDTH)%N -> isBitMask (2^i)%N.
Proof.
  intros.
  split.
  * apply N_pow_pos_nonneg; Nomega.
  * apply N.pow_lt_mono_r; Nomega.
Qed.
Hint Resolve pow_isBitMask : isBitMask.

Lemma revNat_pow:
  forall i,
  (i < WIDTH)%N ->
  (revNat (NToWord (2 ^ i)) = NToWord (2 ^ (WIDTH - 1 - i)))%N.
Proof.
  intros.
Admitted.
(* 
  apply N.bits_inj_iff; intro j.
  destruct (N.ltb_spec j WIDTH).
  * rewrite !revNat_spec by assumption.
    rewrite !N.pow2_bits_eqb.
    rewrite eq_iff_eq_true.
    rewrite !N.eqb_eq.
    Nomega.
  * rewrite isBitMask0_outside by isBitMask.
    symmetry.
    apply N.pow2_bits_false.
    Nomega.
Qed. *)

(** *** Verification of [highestBitMask] and [lowestBitMask] *)

(** And the operations they are based on, [N.log2] and [N_ctz]. *)

(*
Lemma N_ctz_log2:
  forall bm, isBitMask bm ->
  N_ctz bm = (WIDTH - 1 - N.log2 (revNatSafe bm))%N.
Proof.
  intros.
  apply N_ctz_bits_unique.
  * apply H.
  * rewrite <- revNat_spec by isBitMask.
    apply N.bit_log2.
    rewrite revNat_eq_0 by isBitMask.
    unfold isBitMask in H; Nomega.
  * intros.
    rewrite <- (revNat_revNat bm) by isBitMask.
    rewrite revNat_spec by Nomega.
    apply N.bits_above_log2.
    Nomega.
Qed.


Lemma N_log2_ctz:
  forall bm, isBitMask bm ->
  N.log2 bm = (WIDTH - 1 - N_ctz (revNatSafe bm))%N.
Proof.
  intros.
  rewrite N_ctz_log2 by isBitMask.
  rewrite revNat_revNat by isBitMask.
  assert (N.log2 bm < WIDTH)%N by isBitMask.
  Nomega.
Qed.

*)
Lemma isBitMask0_lowestBitMask:
  forall bm, isBitMask0 bm -> isBitMask0 (wordToN (lowestBitMask (NToWord bm))).
Proof.
  intros.
  unfold lowestBitMask.
  unfold isBitMask0 in *.
Admitted.
(*   
  apply N.pow_lt_mono_r; try Nomega.
  isBitMask.
Qed. *)
Hint Resolve isBitMask0_lowestBitMask : isBitMask.


Lemma isBitMask_highestBitMask:
  forall bm, isBitMask bm -> isBitMask (wordToN (highestBitMask (NToWord bm))).
Proof.
  intros.
  split.
Admitted.
(*   * change (0 < 2^N.log2 bm)%N.
    apply N_pow_pos_nonneg; Nomega.
  * apply N.pow_lt_mono_r.
    Nomega.
    isBitMask.
Qed.
Hint Resolve isBitMask_highestBitMask : isBitMask.
 *)

Lemma lxor_pow2_clearbit:
  forall a i,
  N.testbit a i = true ->
  N.lxor a (2 ^ i)%N = N.clearbit a i.
Proof.
  intros.
  apply N.bits_inj. intro j.
  rewrite N.lxor_spec, N.pow2_bits_eqb, N.clearbit_eqb.
  destruct (N.eqb_spec i j).
  * subst.
    destruct (N.testbit _ _) eqn:?; try reflexivity; congruence.
  * destruct (N.testbit _ _) eqn:?; try reflexivity.
Qed.

(* Lemma lxor_lowestBitMask:
  forall bm,
  isBitMask bm ->
  N.lxor bm (lowestBitMask bm) = N.clearbit bm (N_ctz bm).
Proof.
  intros.
  apply lxor_pow2_clearbit.
  apply N_bit_ctz.
  unfold isBitMask in *. Nomega.
Qed.
 *)
 
Lemma split_highestBitMask:
  forall bm,
  isBitMask bm ->
  bm = N.lor (N.clearbit bm (N.log2 bm)) (2^(N.log2 bm))%N.
Proof.
  intros.
  apply N.bits_inj; intro j.
  rewrite N.lor_spec, N.clearbit_eqb.
  rewrite !N.pow2_bits_eqb.
  destruct (N.eqb_spec (N.log2 bm) j).
  * subst.
    destruct (N.testbit _ _) eqn:?; try reflexivity; exfalso.
    rewrite N.bit_log2 in Heqb by (unfold isBitMask in *; Nomega).
    congruence.
  * destruct (N.testbit _ _) eqn:?; try reflexivity.
Qed.


(** *** Bitmasks with one bit *)

Lemma clearbit_log2_0:
  forall bm,
  isBitMask bm ->
  N.clearbit bm (N.log2 bm) = 0%N  ->
  bm = (2^N.log2 bm)%N.
Proof.
  intros.
  apply N.bits_inj; intro j.
  rewrite N.pow2_bits_eqb.
  apply N.bits_inj_iff in H0. specialize (H0 j).
  rewrite N.clearbit_eqb in H0.
  rewrite N.bits_0 in H0.
  destruct (N.eqb_spec (N.log2 bm) j).
  * subst.
    apply N.bit_log2.
    destruct H; Nomega.
  * simpl in H0. rewrite andb_true_r in H0.
    assumption.
Qed.

(* Lemma clearbit_ctz_0:
  forall bm,
  isBitMask bm ->
  N.clearbit bm (N_ctz bm) = 0%N  ->
  bm = (2^N_ctz bm)%N.
Proof.
  intros.
  apply N.bits_inj; intro j.
  rewrite N.pow2_bits_eqb.
  apply N.bits_inj_iff in H0. specialize (H0 j).
  rewrite N.clearbit_eqb in H0.
  rewrite N.bits_0 in H0.
  destruct (N.eqb_spec (N_ctz bm) j).
  * subst.
    apply N_bit_ctz.
    destruct H; Nomega.
  * simpl in H0. rewrite andb_true_r in H0.
    assumption.
Qed.
 *)

(** *** Bitmasks with more than one  bit *)


Definition hasTwoBits bm := isBitMask bm /\ N.clearbit bm (N_ctz bm) <> 0%N.

Lemma isBitMask_twoBits:
  forall bm,
  hasTwoBits bm -> isBitMask bm.
Proof. intros. apply H. Qed.
Hint Immediate isBitMask_twoBits : isBitMask.

Lemma hasTwoBits_revNat:
  forall bm,
  hasTwoBits bm ->
  hasTwoBits (wordToN (revNat (NToWord bm))).
Admitted.
(* Proof.
  intros.
  unfold hasTwoBits in *. destruct H.
  split; try isBitMask.
  contradict H0.
  rewrite clearbit_revNat in H0 by isBitMask.
  rewrite revNat_eq_0 in H0 by isBitMask.
  rewrite <- N_log2_ctz in H0 by isBitMask.
  apply clearbit_log2_0 in H0; try isBitMask.
  rewrite H0; clear H0.
  rewrite N_ctz_pow2.
  apply clearbit_pow2_0.
Qed.
 *)
Lemma log2_clearbit_ctz:
  forall bm,
  hasTwoBits bm ->
  N.log2 (N.clearbit bm (N_ctz bm)) = N.log2 bm.
Proof.
  intros. destruct H.
  apply N.log2_bits_unique.
  * rewrite N.clearbit_eqb.
    rewrite N.bit_log2 by (unfold isBitMask in H; Nomega).
    rewrite andb_true_l.
    rewrite negb_true_iff.
    rewrite N.eqb_neq.
    contradict H0.
    apply N.bits_inj. intro j.
    rewrite N.bits_0.
    rewrite N.clearbit_eqb.
    destruct (N.ltb_spec j WIDTH).
    - destruct (N.eqb_spec (N_ctz bm) j).
      + subst.
        simpl.
        apply andb_false_r.
      + enough (N.testbit bm j = false) by (replace (N.testbit bm j); apply andb_false_l).
        destruct (N.ltb_spec j (N.log2 bm)).
        ** apply N_bits_below_ctz. Nomega.
        ** apply N.bits_above_log2. Nomega.
    - rewrite isBitMask0_outside by isBitMask.
      apply andb_false_l.
  * intros j Hj.
    rewrite N.clearbit_eqb.
    rewrite N.bits_above_log2 by assumption.
    reflexivity.
Qed.

Lemma ctz_clearbit_log2:
  forall bm,
  hasTwoBits bm ->
  N_ctz (N.clearbit bm (N.log2 bm)) = N_ctz bm.
Proof.
  intros. destruct H.
  apply N_ctz_bits_unique.
  * enough (N.clearbit bm (N.log2 bm) <> 0)%N by Nomega.
    contradict H0.
    apply clearbit_log2_0 in H0; try assumption.
    rewrite H0.
    rewrite N_ctz_pow2.
    rewrite clearbit_pow2_0.
    reflexivity.
  * rewrite N.clearbit_eqb.
    rewrite N_bit_ctz by (unfold isBitMask in H; Nomega).
    rewrite andb_true_l.
    rewrite negb_true_iff.
    rewrite N.eqb_neq.
    contradict H0.
    apply N.bits_inj. intro j.
    rewrite N.bits_0.
    rewrite N.clearbit_eqb.
    destruct (N.ltb_spec j WIDTH).
    - destruct (N.eqb_spec (N_ctz bm) j).
      + subst.
        simpl.
        apply andb_false_r.
      + enough (N.testbit bm j = false) by (replace (N.testbit bm j); apply andb_false_l).
        destruct (N.ltb_spec j (N.log2 bm)).
        ** apply N_bits_below_ctz. Nomega.
        ** apply N.bits_above_log2. Nomega.
    - rewrite isBitMask0_outside by isBitMask.
      apply andb_false_l.
  * intros j Hj.
    rewrite N.clearbit_eqb.
    rewrite N_bits_below_ctz by assumption.
    reflexivity.
Qed.

Lemma isBitMask_clearbit_twoBits:
  forall bm,
  hasTwoBits bm ->
  isBitMask (N.clearbit bm (N.log2 bm)).
Proof.
  intros.
  rewrite isBitMask_isBitMask_and_noneg; split.
  * destruct H.
    contradict H0.
    apply clearbit_log2_0 in H0; try isBitMask.
    rewrite H0.
    rewrite N_ctz_pow2.
    apply clearbit_pow2_0.
  * destruct H. isBitMask.
Qed.
Hint Resolve isBitMask_clearbit_twoBits : isBitMask.

(** *** Induction along a bitmask *)

Lemma bits_ind:
  forall bm (P : N -> Prop),
  isBitMask0 bm ->
  P (0%N) ->
  (forall bm, isBitMask bm -> P (N.clearbit bm (N.log2 bm)) -> P bm) ->
  P bm.
Proof.
  intros bm P Hbm HP0 HPstep.
  
  revert Hbm.
  apply well_founded_ind with (R := N.lt) (a := bm); try apply N.lt_wf_0.
  clear bm. intros bm IH Hbm0.

  destruct (N.eqb_spec bm 0%N).
  * subst. apply HP0.
  * assert (0 < bm)%N by Nomega.
    assert (Hbm : isBitMask bm) by (unfold isBitMask in Hbm0; unfold isBitMask; auto).
    clear H Hbm0.
    apply HPstep; auto.
    apply IH.
    - apply clearbit_lt.
      apply N.bit_log2.
      assumption.
    - isBitMask.
Qed.

Lemma bits_ind_up:
  forall bm (P : N -> Prop),
  isBitMask0 bm ->
  P (0%N) ->
  (forall bm, isBitMask bm -> P (N.clearbit bm (N_ctz bm)) -> P bm) ->
  P bm.
Proof.
  intros bm P Hbm HP0 HPstep.
  
  revert Hbm.
  apply well_founded_ind with (R := N.lt) (a := bm); try apply N.lt_wf_0.
  clear bm. intros bm IH Hbm0.

  destruct (N.eqb_spec bm 0%N).
  * subst. apply HP0.
  * assert (0 < bm)%N by Nomega.
    assert (Hbm : isBitMask bm) by (unfold isBitMask in Hbm0; unfold isBitMask; auto).
    clear H Hbm0.
    apply HPstep; auto.
    apply IH.
    - apply clearbit_lt.
      apply N_bit_ctz.
      Nomega.
    - isBitMask.
Qed.

(** *** Lemmas about [popcount] *)

Lemma popcount_N_0:
  N_popcount 0%N = 0%N.
Proof.
  reflexivity.
Qed.

Lemma popCount_N_bm:
  forall bm,
  (0 < bm)%N ->
  N_popcount bm = N.succ (N_popcount (N.clearbit bm (N.log2 bm)%N)).
Proof.
  intros.
  rewrite N.clearbit_spec'.
  pose proof (N_popcount_diff bm (2^N.log2 bm)%N).
  replace (N.land (2 ^ N.log2 bm) bm)%N with (2 ^ N.log2 bm)%N in *;
  only 1: replace (N.ldiff (2 ^ N.log2 bm) bm)%N with 0%N in *.
  * rewrite N_popcount_pow2 in *.
    simpl N_popcount in *.
    simpl N.double in *.
    Nomega.
  * symmetry.
    apply N.bits_inj; intro j.
    rewrite N.bits_0.
    rewrite N.ldiff_spec.
    rewrite N.pow2_bits_eqb.
    destruct (N.eqb_spec (N.log2 bm) j).
    + subst.
      rewrite N.bit_log2 by Nomega. reflexivity.
    + reflexivity.
  * symmetry.
    apply N.bits_inj; intro j.
    rewrite N.land_spec.
    rewrite N.pow2_bits_eqb.
    destruct (N.eqb_spec (N.log2 bm) j).
    + subst.
      rewrite N.bit_log2 by Nomega. reflexivity.
    + reflexivity.
Qed.


(** ** Well-formed IntSets.

This section introduces the predicate to describe the well-formedness of
an IntSet. It has parameters that describe the range that this set covers,
and a function that carries it denotation. This way, invariant preservation
and functional correctness of an operation can be expressed in one go.
*)

Inductive Desc : IntSet -> range -> (N -> bool) -> Prop :=
  | DescTip : forall p bm r f,
    p = NToInt (rPrefix r) ->
    rBits r = N.log2 WIDTH ->
    (forall i, f i = bitmapInRange r bm i) ->
    isBitMask (wordToN bm) ->
    Desc (Tip p bm) r f
  | DescBin : forall s1 r1 f1 s2 r2 f2 p msk r f,
    Desc s1 r1 f1 ->
    Desc s2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = NToInt (rPrefix r) ->
    msk = NToInt (rMask r) -> 
    (forall i, f i = f1 i || f2 i) ->
    Desc (Bin p msk s1 s2) r f.


(** A variant that also allows [Nil], or sets that do not
    cover the full given range, but are certainly contained in them.
    This is used to describe operations that may delete elements.
 *)

Inductive Desc0 : IntSet -> range -> (N -> bool) -> Prop :=
  | Desc0Nil : forall r f, (forall i, f i = false) -> Desc0 Nil r f
  | Desc0NotNil :
      forall s r f r' f',
      forall (HD : Desc s r f),
      forall (Hsubrange: isSubrange r r' = true)
      (Hf : forall i, f' i = f i),
      Desc0 s r' f'.

(** A variant that also allows [Nil] and does not reqiure a range. Used
    for the top-level specification.
 *)

Inductive Sem : IntSet -> (N -> bool) -> Prop :=
  | SemNil : forall f, (forall i, f i = false) -> Sem Nil f
  | DescSem : forall s r f (HD : Desc s r f), Sem s f.

(** The highest level: Just well-formedness.
 *)

Definition WF (s : IntSet) : Prop := exists f, Sem s f.


(** ** Lemmas related to well-formedness *)


(** All of these respect extensionality of [f] *)

Lemma Desc_change_f:
  forall s r f f',
  Desc s r f -> (forall i, f' i = f i) -> Desc s r f'.
Proof.
  intros.
  induction H.
  * eapply DescTip; try eassumption.
    intro i. rewrite H0, H2. reflexivity.
  * eapply DescBin; try eassumption.
    intro i. rewrite H0, H7. reflexivity.
Qed.

Lemma Sem_change_f:
  forall s f f',
  Sem s f -> (forall i, f' i = f i) -> Sem s f'.
Proof.
  intros.
  destruct H.
  * apply SemNil.
    intro i. rewrite H0, H. reflexivity.
  * eapply DescSem. eapply Desc_change_f. eassumption.
    intro i. rewrite H0. reflexivity.
Qed.


Lemma Desc_Desc0:
  forall s r f, Desc s r f -> Desc0 s r f.
Proof. intros.
  eapply Desc0NotNil.
  * eassumption.
  * apply isSubrange_refl.
  * intro. reflexivity.
Qed.

Lemma Desc0_Sem:
  forall s r f, Desc0 s r f -> Sem s f.
Proof.
  intros.
  destruct H.
  * apply SemNil; eassumption.
  * eapply DescSem. eapply Desc_change_f. eassumption. assumption.
Qed.

Lemma Desc0_WF:
  forall s r f, Desc0 s r f -> WF s.
Proof.
  intros. eexists. eapply Desc0_Sem. eassumption.
Qed.

Lemma Desc_larger_WIDTH:
  forall {s r f}, Desc s r f -> (N.log2 WIDTH <= rBits r)%N.
Proof.
  intros ??? HD.
  induction HD; subst.
  * destruct r. simpl in *. subst. reflexivity.
  * etransitivity. apply IHHD1.
    etransitivity. eapply subRange_smaller. eassumption.
    eapply subRange_smaller. apply isSubrange_halfRange.
    assumption.
Qed.

Lemma Desc_outside:
 forall {s r f i}, Desc s r f -> inRange i r = false -> f i = false.
Proof.
 intros ???? HD Houtside.
 induction HD;subst.
 * rewrite H1.
   apply bitmapInRange_outside; auto.
 * rewrite H4; clear H4.
   rewrite IHHD1 by inRange_false.
   rewrite IHHD2 by inRange_false.
   reflexivity.
Qed.

Lemma Desc_inside:
 forall {s r f i}, Desc s r f -> f i = true -> inRange i r = true.
Proof.
 intros ???? HD Hf.
 destruct (inRange i r) eqn:?; intuition.
 rewrite (Desc_outside HD) in Hf by assumption.
 congruence.
Qed.

Lemma Desc0_outside:
  forall {s r f i}, Desc0 s r f -> inRange i r = false -> f i = false.
Proof.
  intros.
  destruct H; auto.
  rewrite Hf.
  rewrite (Desc_outside HD) by inRange_false.
  reflexivity.
Qed.

Lemma Desc0_subRange:
  forall {s r r' f}, Desc0 s r f -> isSubrange r r' = true -> Desc0 s r' f.
Proof.
  intros.
  induction H.
  * apply Desc0Nil; assumption.
  * eapply Desc0NotNil; try eassumption.
    isSubrange_true.
Qed.


Lemma isBitMask_bitmapInRange:
  forall r bm, rBits r = Nlog2 WIDTH -> isBitMask (wordToN bm) ->
    exists i, bitmapInRange r bm i = true.
Proof.
  intros.
  destruct (isBitMask_testbit _ H0) as [j[??]].
  exists (intoRange r j).
  rewrite bitmapInRange_intoRange; try assumption.
  replace (rBits r); assumption.
Qed.

(** The [Desc] predicate only holds for non-empty sets. *)
Lemma Desc_some_f:
  forall {s r f}, Desc s r f -> exists i, f i = true.
Proof.
  intros ??? HD.
  induction HD; subst.
  + destruct (isBitMask_bitmapInRange _ _ H0 H2) as [j ?].
    exists j.
    rewrite H1.
    assumption.
  + destruct IHHD1  as [j?].
    exists j.
    rewrite H4.
    rewrite H2.
    reflexivity.
Qed.

(** The [Desc] predicate is right_unique *)
Lemma Desc_unique_f:
  forall {s r1 f1 r2 f2}, Desc s r1 f1 -> Desc s r2 f2 -> (forall i, f1 i = f2 i).
Proof.
  intros ????? HD.
  revert r2 f2.
  induction HD; subst.
  + intros r2 f2 HD2 i.
    inversion_clear HD2.
    (* assert (r = r2) by (apply rPrefix_rBits_range_eq; congruence); subst. *)
    assert (r = r2). apply rPrefix_rBits_range_eq; admit.
    rewrite H1, H4.
    subst.
    reflexivity.
  + intros r3 f3 HD3 i.
    inversion_clear HD3.
    rewrite H10, H4.
    erewrite IHHD1 by eassumption.
    erewrite IHHD2 by eassumption.
    reflexivity.
Admitted.

(** *** Tactics *)

(** This auxillary tactic destructs one boolean atom in the argument *)

Ltac split_bool_go expr :=
  lazymatch expr with 
    | true       => fail
    | false      => fail
    | Some _     => fail
    | None       => fail
    | match ?x with _ => _ end => split_bool_go x || (simpl x; cbv match)
    | negb ?x    => split_bool_go x
    | ?x && ?y   => split_bool_go x || split_bool_go y
    | ?x || ?y   => split_bool_go x || split_bool_go y
    | xorb ?x ?y => split_bool_go x || split_bool_go y
    | oro ?x ?y  => split_bool_go x || split_bool_go y
    | ?bexpr     => destruct bexpr eqn:?
  end.

(** This auxillary tactic destructs one boolean or option atom in the goal *)

Ltac split_bool :=
  match goal with 
    | [ |- ?lhs = ?rhs] => split_bool_go lhs || split_bool_go rhs
  end.

(** This tactic solves goal of the forms
 [ forall i, f1 i = f2 i || f3 i ]
 by introducing [i], rewriting with all premises of the form
 [forall i, f1 i = … ]
 and then destructing on all boolean atoms. It leaves unsolved cases
 as subgoal.
*)

Ltac solve_f_eq :=
  let i := fresh "i" in
  intro i; simpl;
  repeat
    ( (rewrite bitmapInRange_lxor; Int_Word_N)
    + (rewrite bitmapInRange_lnot; Int_Word_N)
    + (rewrite bitmapInRange_land; Int_Word_N)
    + (rewrite bitmapInRange_lor; Int_Word_N)
    + match goal with 
      | [ H : forall i : N, ?f i = _ |- context [?f i] ] => rewrite H
      end);
  repeat split_bool;
  try reflexivity.

Ltac point_to_inRange :=
  lazymatch goal with 
    | [ HD : Desc ?s ?r ?f, Hf : ?f ?i = true |- _ ] 
      => apply (Desc_inside HD) in Hf
    | [ H : bitmapInRange ?r ?bm ?i = true |- _ ]
      => apply bitmapInRange_inside in H
  end.

Ltac pose_new prf :=
  let prop := type of prf in
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => pose proof prf
  end.

Ltac saturate_inRange :=
  match goal with
   | [ Hsr : isSubrange ?r1 ?r2 = true, Hir : inRange ?i ?r1 = true |- _ ]
     => pose_new (inRange_isSubrange_true i r1 r2 Hsr Hir)
   | [ HrBits : (0 < rBits ?r)%N, Hir : inRange ?i (halfRange ?r ?h) = true |- _ ]
     => pose_new (inRange_isSubrange_true i _ r (isSubrange_halfRange r h HrBits) Hir)
  end.

Ltac inRange_disjoint :=
  match goal with
   | [ H1 : inRange ?i (halfRange ?r false) = true,
       H2 : inRange ?i (halfRange ?r true) = true |- _ ]
     => exfalso;
        refine (rangeDisjoint_inRange_false_false i _ _ _ H1 H2);
        apply halves_disj; auto
   | [ H1 : isSubrange ?r (halfRange ?r2 false) = true,
       H2 : isSubrange ?r (halfRange ?r2 true) = true |- _ ]
     => exfalso;
        refine (rangeDisjoint_isSubrange_false_false r _ _ _ H1 H2);
        apply halves_disj; auto
   | [ H  : rangeDisjoint ?r1 ?r2 = true,
       H1 : inRange ?i ?r1 = true,
       H2 : inRange ?i ?r2 = true |- _ ]
     => exfalso;
        apply (rangeDisjoint_inRange_false_false i _ _ H H1 H2)
   end.

(**
 Like [solve_f_eq], but tries to solve the resulting bugus cases
 using reasoning about [inRange]. *)

Ltac solve_f_eq_disjoint :=
  solve_f_eq;
  repeat point_to_inRange;
  repeat saturate_inRange;
  try inRange_disjoint. (* Only try this, so that we see wher we are stuck. *)

(** *** Uniqueness of representation *)

Lemma both_halfs:
  forall i1 i2 r1 r2,
  (0 < rBits r2)%N ->
  inRange i1 r1 = true ->
  inRange i2 r1 = true ->
  inRange i1 (halfRange r2 false) = true ->
  inRange i2 (halfRange r2 true) = true ->
  isSubrange r2 r1 = true.
Proof.
  intros.
  destruct (N.ltb_spec (rBits r1) (rBits r2)).
  * exfalso.
    assert (isSubrange r1 (halfRange r2 false) = true)
      by (apply inRange_both_smaller_subRange with (i := i1);
          try assumption; rewrite rBits_halfRange; Nomega).
    assert (isSubrange r1 (halfRange r2 true) = true)
      by (apply inRange_both_smaller_subRange with (i := i2);
          try assumption; rewrite rBits_halfRange; Nomega).
    assert (isSubrange r1 r2 = true) by isSubrange_true.
    pose proof (smaller_subRange_other_half _ _ H4).
    rewrite H7, H6, H5 in H8. intuition.
  * apply inRange_both_smaller_subRange with (i := i1).
    + eapply inRange_isSubrange_true; [apply isSubrange_halfRange; assumption|eassumption].
    + assumption.
    + assumption.
Qed.

Lemma criss_cross:
  forall i1 i2 i3 i4 r1 r2,
  (0 < rBits r1)%N ->
  (0 < rBits r2)%N ->
  inRange i1 (halfRange r1 false) = true ->
  inRange i2 (halfRange r1 true) = true ->
  inRange i3 (halfRange r2 false) = true ->
  inRange i4 (halfRange r2 true) = true ->
  inRange i1 r2 = true ->
  inRange i2 r2 = true ->
  inRange i3 r1 = true ->
  inRange i4 r1 = true ->
  r1 = r2.
Proof.
  intros.
  apply isSubrange_antisym.
  + eapply both_halfs with (i1 := i1) (i2 := i2); eassumption.
  + eapply both_halfs with (i1 := i3) (i2 := i4); eassumption.  
Qed.

Lemma larger_f_imp:
  forall s1 r1 f1 s2 r2 f2,
  (rBits r2 < rBits r1)%N ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i : N, f1 i = true -> f2 i = true) ->
  False.
Proof.
  intros ??? ??? Hsmaller HD1 HD2 Hf.
  destruct HD1.
  * pose proof (Desc_larger_WIDTH HD2).
    Nomega.
  * subst.
    assert (isSubrange r2 (halfRange r false) = true).
      { destruct (Desc_some_f HD1_1) as [i Hi].
        pose proof (Desc_inside HD1_1 Hi).
        specialize (H4 i).
        rewrite (Desc_outside HD1_2) in H4 by inRange_false.
        rewrite orb_false_r in H4.
        rewrite <- H4 in Hi; clear H4.
        apply Hf in Hi; clear Hf.
        apply (Desc_inside HD2) in Hi.
        apply inRange_both_smaller_subRange with (i := i).
        * inRange_true.
        * inRange_true.
        * rewrite rBits_halfRange. Nomega.
      }
    assert (isSubrange r2 (halfRange r true) = true).
      { destruct (Desc_some_f HD1_2) as [i Hi].
        pose proof (Desc_inside HD1_2 Hi).
        specialize (H4 i).
        rewrite (Desc_outside HD1_1) in H4 by inRange_false.
        rewrite orb_false_l in H4.
        rewrite <- H4 in Hi; clear H4.
        apply Hf in Hi; clear Hf.
        apply (Desc_inside HD2) in Hi.
        apply inRange_both_smaller_subRange with (i := i).
        * inRange_true.
        * inRange_true.
        * rewrite rBits_halfRange. Nomega.
      }
      inRange_disjoint.
Qed.


Lemma Desc_unique:
  forall s1 r1 f1 s2 r2 f2,
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i, f1 i = f2 i) ->
  s1 = s2.
Proof.
  intros ?????? HD1.
  revert s2 r2 f2.
  induction HD1.
  * intros s2 r2 f2 HD2 Hf.
    destruct HD2.
    + subst.
      assert (r = r0).
      { destruct (isBitMask_bitmapInRange r bm H0 H2) as [i Hbit].
        assert (Hir : inRange i r = true)
          by (eapply bitmapInRange_inside; eassumption).
        specialize (Hf i).
        specialize (H1 i).
        specialize (H5 i).
        rewrite H1 in Hf; clear H1.
        rewrite H5 in Hf; clear H5.
        rewrite Hbit in Hf; symmetry in Hf.
        apply bitmapInRange_inside in Hf.
        apply inRange_both_same with (i := i); try assumption; Nomega.
      }
      subst.
      f_equal.
      enough (forall j, j < WIDTH -> N.testbit (wordToN bm) j = N.testbit (wordToN bm0) j) by admit.
      intros j Hlt.
      set (i := intoRange r0 j).
      specialize (H1 i).
      specialize (H5 i).
      specialize (Hf i).
      rewrite Hf in H1 by assumption; clear Hf.
      rewrite H1 in H5; clear H1.
      subst i.
      rewrite !bitmapInRange_intoRange in H5
        by (replace (rBits r0); assumption).
      assumption.
    + exfalso. subst.
      eapply larger_f_imp with (r1 := r0) (r2 := r).
      - assert (N.log2 WIDTH <= rBits r1)%N by (eapply Desc_larger_WIDTH; eauto).
        apply subRange_smaller in H4. rewrite rBits_halfRange in H4.
        Nomega.
      - eapply DescBin with (s1 := s1) (s2 := s2); try eassumption; reflexivity.
      - eapply DescTip; try eassumption; reflexivity.
      - intros i Hi. rewrite Hf. assumption.
  * intros s3 r3 f3 HD3 Hf.
    destruct HD3.
    + exfalso. subst.
      eapply larger_f_imp with (r1 := r) (r2 := r0).
      - assert (N.log2 WIDTH <= rBits r1)%N by (eapply Desc_larger_WIDTH; eauto).
        apply subRange_smaller in H0. rewrite rBits_halfRange in H0.
        Nomega.
      - eapply DescBin with (s1 := s1) (s2 := s2); try eassumption; reflexivity.
      - eapply DescTip; try eassumption; reflexivity.
      - intros i Hi. rewrite <- Hf. assumption.
    + subst.
      assert (r4 = r). {
        destruct (Desc_some_f HD3_1) as [i1 Hi1].
        destruct (Desc_some_f HD3_2) as [i2 Hi2].
        destruct (Desc_some_f HD1_1) as [i3 Hi3].
        destruct (Desc_some_f HD1_2) as [i4 Hi4].
        apply criss_cross with i1 i2 i3 i4; try assumption.
        * apply (Desc_inside HD3_1) in Hi1; inRange_true.
        * apply (Desc_inside HD3_2) in Hi2; inRange_true.
        * apply (Desc_inside HD1_1) in Hi3; inRange_true.
        * apply (Desc_inside HD1_2) in Hi4; inRange_true.
        * specialize (H10 i1); rewrite Hi1 in H10.
          rewrite orb_true_l in H10.
          rewrite <- Hf in H10.
          specialize (H4 i1); rewrite H10 in H4; clear H10; symmetry in H4.
          rewrite orb_true_iff in H4; destruct H4.
          + apply (Desc_inside HD1_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
        * specialize (H10 i2); rewrite Hi2 in H10.
          rewrite orb_true_r in H10.
          rewrite <- Hf in H10.
          specialize (H4 i2); rewrite H10 in H4; clear H10; symmetry in H4.
          rewrite orb_true_iff in H4; destruct H4.
          + apply (Desc_inside HD1_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD1_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
        * specialize (H4 i3); rewrite Hi3 in H4.
          rewrite orb_true_l in H4.
          rewrite -> Hf in H4.
          specialize (H10 i3); rewrite H4 in H10; clear H4; symmetry in H10.
          rewrite orb_true_iff in H10; destruct H10.
          + apply (Desc_inside HD3_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD3_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
        * specialize (H4 i4); rewrite Hi4 in H4.
          rewrite orb_true_r in H4.
          rewrite -> Hf in H4.
          specialize (H10 i4); rewrite H4 in H10; clear H4; symmetry in H10.
          rewrite orb_true_iff in H10; destruct H10.
          + apply (Desc_inside HD3_1) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
          + apply (Desc_inside HD3_2) in H2.
            eapply inRange_isSubrange_true; [|eassumption].
            isSubrange_true.
      }
      subst.
      assert (IH_prem_1 : (forall i : N, f1 i = f0 i)). {
        intro i.
        specialize (H4 i). specialize (H10 i). specialize (Hf i).
        destruct (inRange i (halfRange r false)) eqn:?.
        -- rewrite (Desc_outside HD1_2) in H4 by inRange_false.
           rewrite orb_false_r in H4.
           rewrite <- H4; clear H4.

           rewrite (Desc_outside HD3_2) in H10 by inRange_false.
           rewrite orb_false_r in H10.
           rewrite <- H10; clear H10.

           assumption.
        -- rewrite (Desc_outside HD1_1) by inRange_false.
           rewrite (Desc_outside HD3_1) by inRange_false.
           reflexivity.
      }
      assert (IH_prem_2 : (forall i : N, f2 i = f3 i)). {
        intro i.
        specialize (H4 i). specialize (H10 i). specialize (Hf i).
        destruct (inRange i (halfRange r true)) eqn:?.
        -- rewrite (Desc_outside HD1_1) in H4 by inRange_false.
           rewrite orb_false_l in H4.
           rewrite <- H4; clear H4.
           
           rewrite (Desc_outside HD3_1) in H10 by inRange_false.
           rewrite orb_false_l in H10.
           rewrite <- H10; clear H10.
           
           assumption.
        -- rewrite (Desc_outside HD1_2) by inRange_false.
           rewrite (Desc_outside HD3_2) by inRange_false.
           reflexivity.
      }
      specialize (IHHD1_1 _ _ _ HD3_1 IH_prem_1).
      destruct IHHD1_1; subst.
      specialize (IHHD1_2 _ _ _ HD3_2 IH_prem_2).
      destruct IHHD1_2; subst.
      reflexivity.
Admitted.

Lemma Sem_unique:
  forall s1 f1 s2 f2,
  Sem s1 f1 -> Sem s2 f2 ->
  (forall i, f1 i = f2 i) ->
  s1 = s2.
Proof.
  intros.
  destruct H, H0.
  * reflexivity.
  * exfalso.
    destruct (Desc_some_f HD) as [i Hi]. 
    rewrite <- H1 in Hi.
    rewrite H in Hi.
    congruence.
  * exfalso.
    destruct (Desc_some_f HD) as [i Hi]. 
    rewrite -> H1 in Hi.
    rewrite H in Hi.
    congruence.
  * eapply Desc_unique; eassumption.
Qed.

Theorem Sem_extensional (s : IntSet) (f1 f2 : N -> bool) :
  Sem s f1 ->
  Sem s f2 ->
  forall i, f1 i = f2 i.
Proof.
  intros S1 S2 k;
    inversion S1 as [f1' E1 | s1 r1 f1' D1];
    subst f1' s;
    inversion S2 as [f2' E2 | s2 r2 f2' D2];
    subst f2';
    try subst s1; try subst s2.
  - now rewrite E1,E2.
  - inversion D2.
  - inversion D1.
  - eauto using Desc_unique_f.
Qed.

(** *** Verification of [equal] *)

Lemma equal_spec:
  forall s1 s2, equal s1 s2 = true <-> s1 = s2.
Proof.
  induction s1; intro s2; destruct s2;
    try solve [simpl; intuition congruence].
  * simpl. unfoldMethods.
    rewrite !andb_true_iff.
    rewrite !N.eqb_eq.
    rewrite !intToN_inj_iff.
    rewrite IHs1_1.
    rewrite IHs1_2.
    intuition congruence.
  * simpl. unfoldMethods.
    rewrite !andb_true_iff.
    rewrite !N.eqb_eq.
    rewrite !intToN_inj_iff, !wordToN_inj_iff.
    intuition congruence.
Qed.

(** *** Verification of [nequal] *)

Lemma nequal_spec:
  forall s1 s2, nequal s1 s2 = negb (equal s1 s2).
Proof.
  induction s1; intro s2; destruct s2;
    try solve [simpl; intuition congruence].
  * simpl. unfoldMethods.
    rewrite !negb_andb.
    rewrite IHs1_1.
    rewrite IHs1_2.
    intuition congruence.
  * simpl. unfoldMethods.
    rewrite !negb_andb.
    intuition congruence.
Qed.

(** *** Verification of [isSubsetOf] *)

Lemma isSubsetOf_disjoint:
  forall s1 r1 f1 s2 r2 f2,
  rangeDisjoint r1 r2 = true ->
  Desc s1 r1 f1 -> Desc s2 r2 f2 ->
  (forall i : N, f1 i = true -> f2 i = true) <-> False.
Proof.
  intros ??? ??? Hdis HD1 HD2.
  intuition.
  destruct (Desc_some_f HD1) as [i Hi].
  eapply rangeDisjoint_inRange_false_false with (i := i).
  ** eassumption.
  ** eapply Desc_inside; eassumption.
  ** apply H in Hi.
     apply (Desc_inside HD2) in Hi.
     assumption.
Qed.

Lemma pointwise_iff:
  forall {a} (P Q Z : a -> Prop),
  (forall i, P i -> (Q i <-> Z i)) ->
  (forall i, P i -> Q i) <-> (forall i, P i -> Z i).
Proof. intuition; specialize (H0 i); specialize (H i); intuition. Qed.

(* Move somewhere else *)
Lemma isBitMask0_wordToN:
  forall bm, isBitMask0 (wordToN bm).
Admitted.
Hint Resolve isBitMask0_wordToN : isBitMask.
Lemma isBitMask0_lnot:
  forall n, isBitMask0 (N.lnot n WIDTH).
Admitted.
Hint Resolve isBitMask0_lnot : isBitMask.


Program Fixpoint isSubsetOf_Desc
  s1 r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  isSubsetOf s1 s2 = true <-> (forall i, f1 i = true -> f2 i = true) := _.
Next Obligation.
  revert isSubsetOf_Desc H H0.
  intros IH HD1 HD2.
  destruct HD1, HD2.
  * (* Both are tips *)
    simpl; subst. unfoldMethods. Int_Word_N.
    rewrite andb_true_iff.
    rewrite !N.eqb_eq.
    destruct (N.eqb_spec (rPrefix r) (rPrefix r0)).
    - replace r0 with r in * by (apply rPrefix_rBits_range_eq; congruence). clear r0.
      intuition.
      ** rewrite H1 in H.
         rewrite H5.
         unfold bitmapInRange. unfold bitmapInRange in H.
         destruct (inRange i r); try congruence.
         set (j := N.land i  _) in *.
         apply N.bits_inj_iff in H7. specialize (H7 j).
         rewrite N.land_spec, N.lnot_spec_low, N.bits_0 in H7 by admit.
         destruct (N.testbit (wordToN bm) j), (N.testbit (wordToN bm0) j); simpl in *; try congruence.
      ** apply N.bits_inj_iff; intro j.
         rewrite N.bits_0.
         destruct (N.ltb_spec j WIDTH).
         ++ rewrite N.land_spec, N.lnot_spec_low by assumption.
            do 2 split_bool; try reflexivity; exfalso.
            apply not_true_iff_false in Heqb0.
            contradict Heqb0.
            set (i := intoRange r j).
            assert (Hbmir : bitmapInRange r bm0 i = N.testbit (wordToN bm0) j)
              by (apply bitmapInRange_intoRange; replace (rBits r); assumption).
            rewrite <- Hbmir; clear Hbmir.
            rewrite <- H5.
            apply H.
            rewrite H1.
            assert (Hbmir : bitmapInRange r bm i = N.testbit (wordToN bm) j)
              by (apply bitmapInRange_intoRange; replace (rBits r); assumption).
            rewrite Hbmir.
            assumption.
         ++ apply isBitMask0_outside. isBitMask. assumption.
    - rewrite isSubsetOf_disjoint.
      ** intuition.
      ** apply different_prefix_same_bits_disjoint; try eassumption; congruence.
      ** eapply DescTip with (p := NToInt (rPrefix r)) (r := r) (bm := bm); try eassumption; try congruence.
      ** eapply DescTip with (p := NToInt (rPrefix r0)) (r := r0) (bm := bm0); try eassumption; try congruence.

  * (* Tip left, Bin right *)
    simpl; subst.
    apply nomatch_zero_smaller.
    - assert (N.log2 WIDTH <= rBits r1)%N by (eapply Desc_larger_WIDTH; eauto).
      apply subRange_smaller in H4. rewrite rBits_halfRange in H4.
      lia.
    - intros Hdisj.
      rewrite isSubsetOf_disjoint.
      ** intuition.
      ** eassumption.
      ** eapply DescTip; try eassumption; try reflexivity.
      ** eapply (DescBin s1 _ _ s2); try eassumption; try reflexivity.
    - intros.
       etransitivity; [eapply IH with (f2 := f1)|].
       + simpl. omega.
       + eapply DescTip with (p := NToInt (rPrefix r)) (r := r) (bm := bm); try eassumption; try congruence.
       + eassumption.
       + apply pointwise_iff. intros i Hi. 
         assert (inRange i r = true). {
           rewrite H1 in Hi.
           apply bitmapInRange_inside in Hi.
           assumption.
         }
         rewrite H8.
         rewrite (Desc_outside HD2_2) by inRange_false.
         rewrite orb_false_r. reflexivity.
    - intros.
       etransitivity; [eapply IH with (f2 := f2)|].
       + simpl. omega.
       + eapply DescTip with (p := NToInt (rPrefix r)) (r := r) (bm := bm); try eassumption; try congruence.
       + eassumption.
       + apply pointwise_iff. intros i Hi. 
         assert (inRange i r = true). {
           rewrite H1 in Hi.
           apply bitmapInRange_inside in Hi.
           assumption.
         }
         rewrite H8.
         rewrite (Desc_outside HD2_1) by inRange_false.
         rewrite orb_false_l. reflexivity.

  * (* Bin right, Tip left *)
    intuition; exfalso.
    eapply larger_f_imp with (r1 := r) (r2 := r2).
    - assert (N.log2 WIDTH <= rBits r1)%N by (eapply Desc_larger_WIDTH; eauto).
      apply subRange_smaller in H0. rewrite rBits_halfRange in H0.
      Nomega.
    - eapply DescBin with (s1 := s1) (s2 := s0); try eassumption; reflexivity.
    - eapply DescTip; try eassumption; reflexivity.
    - intros i Hi. apply H9. assumption.
  * (* Bin both sides *)
    simpl; subst.
    rewrite shorter_spec by assumption.
    rewrite shorter_spec by assumption.
    destruct (N.ltb_spec (rBits r4) (rBits r)); [|destruct (N.ltb_spec (rBits r) (rBits r4))].
    - (* left is bigger than right *)
      intuition; exfalso.
      eapply larger_f_imp with (r1 := r) (r2 := r4).
      -- assumption.
      -- eapply DescBin with (s1 := s1) (s2 := s0); try eassumption; reflexivity.
      -- eapply DescBin with (s1 := s2) (s2 := s3); try eassumption; reflexivity.
      -- assumption.
    - (* right is bigger than left *)
      match goal with [ |- ((?x && ?y) = true) <-> ?z ] =>
        enough (Htmp : (if x then y else false) = true <-> z)
        by (destruct x; try rewrite andb_true_iff; intuition congruence)
      end.
      match goal with [ |- context [match_ ?x ?y ?z] ] =>
        replace (match_ x y z) with (negb (nomatch x y z))
          by (unfold nomatch, match_; unfoldMethods; rewrite negb_involutive; reflexivity)
      end.
      rewrite if_negb.
      apply nomatch_zero_smaller; try assumption.
      ** intro Hdisj.
         rewrite isSubsetOf_disjoint.
         -- intuition.
         -- eassumption.
         -- eapply DescBin with (s1 := s1) (s2 := s0); try eassumption; reflexivity.
         -- eapply DescBin with (s1 := s2) (s2 := s3); try eassumption; reflexivity.
      ** intros.
         etransitivity; [eapply IH with (f2 := f2)|].
         + simpl. omega.
         + eapply DescBin with (s1 := s1) (s2 := s0) (r := r); try eassumption; reflexivity.
         + eassumption.
         + apply pointwise_iff. intros i Hi. 
           assert (inRange i r = true). {
             rewrite H4 in Hi.
             rewrite orb_true_iff in Hi; destruct Hi as [Hi | Hi];
             (apply (Desc_inside HD1_1) in Hi || apply (Desc_inside HD1_2) in Hi);
             eapply inRange_isSubrange_true; swap 1 2; try eassumption; isSubrange_true.
           }
           rewrite H10.
           rewrite (Desc_outside HD2_2) by inRange_false.
           rewrite orb_false_r. reflexivity.
      ** intros.
         etransitivity; [eapply IH with (f2 := f3)|].
         + simpl. omega.
         + eapply DescBin with (s1 := s1) (s2 := s0) (r := r); try eassumption; reflexivity.
         + eassumption.
         + apply pointwise_iff. intros i Hi. 
           assert (inRange i r = true). {
             rewrite H4 in Hi.
             rewrite orb_true_iff in Hi; destruct Hi as [Hi | Hi];
             (apply (Desc_inside HD1_1) in Hi || apply (Desc_inside HD1_2) in Hi);
             eapply inRange_isSubrange_true; swap 1 2; try eassumption; isSubrange_true.
           }
           rewrite H10.
           rewrite (Desc_outside HD2_1) by inRange_false.
           rewrite orb_false_l. reflexivity.
    - (* same sized bins *)
      unfoldMethods. Int_Word_N.
      destruct (N.eqb_spec (rPrefix r) (rPrefix r4)).
      + replace r4 with r in * by (apply rPrefix_rBits_range_eq; Nomega). clear r4.
        simpl.
        rewrite andb_true_iff.
        rewrite (IH s1 r1 f1 s2 r2 f2); try assumption; simpl; try omega.
        rewrite (IH s0 r0 f0 s3 r3 f3); try assumption; simpl; try omega.
        intuition.
        ++ rewrite H10. rewrite H4 in H8.
           rewrite orb_true_iff in H8.
           destruct H8.
           ** apply H9 in H8.
              rewrite H8.
              rewrite orb_true_l.
              reflexivity.
           ** apply H11 in H8.
              rewrite H8.
              rewrite orb_true_r.
              reflexivity.
        ++ specialize (H4 i). specialize (H10 i).
           rewrite H9 in H4.
           apply (Desc_inside HD1_1) in H9.
           rewrite orb_true_l in H4.
           apply H8 in H4. rewrite H10 in H4.
           rewrite (Desc_outside HD2_2) in H4 by inRange_false.
           rewrite orb_false_r in H4.
           assumption.
        ++ specialize (H4 i). specialize (H10 i).
           rewrite H9 in H4. 
           apply (Desc_inside HD1_2) in H9.
           rewrite orb_true_r in H4.
           apply H8 in H4. rewrite H10 in H4.
           rewrite (Desc_outside HD2_1) in H4 by inRange_false.
           rewrite orb_false_l in H4.
           assumption.
      + rewrite isSubsetOf_disjoint.
        ** intuition.
        ** apply different_prefix_same_bits_disjoint; try eassumption; Nomega.
        ** eapply DescBin with (s1 := s1) (s2 := s0); try eassumption; reflexivity.
        ** eapply DescBin with (s1 := s2) (s2 := s3); try eassumption; reflexivity.
Admitted.

Lemma isSubsetOf_Sem:
  forall s1 f1 s2 f2,
  Sem s1 f1 -> Sem s2 f2 ->
  isSubsetOf s1 s2 = true <-> (forall i, f1 i = true -> f2 i = true).
Proof.
  intros ???? HSem1 HSem2.
  destruct HSem1.
  * replace (isSubsetOf Nil s2) with true by (destruct s2; reflexivity).
    intuition; exfalso.
    rewrite H in H1; congruence.
  * destruct HSem2.
    + replace (isSubsetOf s Nil) with false by (destruct HD; reflexivity).
      intuition; exfalso.
      destruct (Desc_some_f HD) as [i Hi].
      apply H0 in Hi.
      rewrite H in Hi.
      congruence.
    + eapply isSubsetOf_Desc; eassumption.
Qed.


Lemma isSubsetOf_refl:
  forall s f,
  Sem s f ->
  isSubsetOf s s = true.
Proof.
  intros.
  rewrite isSubsetOf_Sem by eassumption.
  intuition.
Qed.

Lemma isSubsetOf_antisym:
  forall s1 f1 s2 f2,
  Sem s1 f1 -> Sem s2 f2 ->
  isSubsetOf s1 s2 = true ->
  isSubsetOf s2 s1 = true ->
  s1 = s2.
Proof.
  intros.
  rewrite isSubsetOf_Sem in H1 by eassumption.
  rewrite isSubsetOf_Sem in H2 by eassumption.
  eapply Sem_unique; try eassumption.
  intro i. specialize (H1 i). specialize (H2 i).
  apply eq_true_iff_eq.
  intuition.
Qed.


(** *** Verification of [member] *)

Lemma member_Desc:
 forall {s r f i}, Desc s r f -> member i s = f (intToN i).
Proof.
 intros ???? HD.
 induction HD; subst.
 * simpl.
   change (((prefixOf i == NToInt (rPrefix r)) && ((bitmapOf i .&.bm) /= #0)) = f (intToN i)).
   unfoldMethods. Int_Word_N.
   rewrite -> prefixOf_eqb_spec by assumption.
   rewrite H1.

   unfold bitmapOf, suffixOf, suffixBitMask, bitmapInRange.
   unfoldMethods.
   replace (intToN (ZToInt 63)) with 63 by admit.
   rewrite bitmapOfSuffix_pow.
   rewrite N_land_pow2_testbit.

   rewrite H0.
   reflexivity.
 * rewrite H4. clear H4.
   simpl member.
   rewrite IHHD1, IHHD2. clear IHHD1 IHHD2.

   apply nomatch_zero; [auto|..]; intros.
   + rewrite (Desc_outside HD1) by inRange_false.
     rewrite (Desc_outside HD2) by inRange_false.
     reflexivity.
   + rewrite (Desc_outside HD2) by inRange_false.
     rewrite orb_false_r. reflexivity.
   + rewrite (Desc_outside HD1) by inRange_false.
     rewrite orb_false_l. reflexivity.
Admitted.

Lemma member_Desc0:
  forall {s r f i}, Desc0 s r f -> member i s = f (intToN i).
Proof.
  intros.
  destruct H; simpl; auto.
  rewrite Hf.
  eapply member_Desc; eauto.
Qed.

Lemma member_Sem:
  forall {s f i}, Sem s f -> member i s = f (intToN i).
Proof.
  intros.
  destruct H.
  * rewrite H. reflexivity.
  * erewrite member_Desc; eauto.
Qed.

Lemma Desc_has_member: 
  forall {s r f}, Desc s r f -> exists i, member i s = true.
Proof.
  intros ??? HD.
  destruct (Desc_some_f HD) as [j?].
  exists (NToInt j).
  rewrite (member_Desc HD). Int_Word_N. intuition.
Qed.

(** *** Verification of [notMember] *)

Lemma notMember_Sem:
  forall {s f i}, Sem s f -> notMember i s = negb (f (intToN i)).
Proof.
  intros.
  change (negb (member i s) = negb (f (intToN i))).
  f_equal.
  apply member_Sem.
  assumption.
Qed.

(** *** Verification of [null] *)

Lemma null_Sem:
  forall {s f}, Sem s f -> null s = true <-> (forall i, f i = false).
Proof.
  intros s f HSem.
  destruct HSem.
  * intuition.
  * assert (null s = false) by (destruct HD; reflexivity).
    intuition try congruence.
    destruct (Desc_some_f HD).
    specialize (H0 x).
    congruence.
Qed.

(** *** Verification of [empty] *)

Lemma empty_Sem (f : N -> bool) : Sem empty f <-> forall i, f i = false.
Proof.
  split.
  - now inversion 1; intros; subst.
  - now constructor.
Qed.

Lemma empty_WF : WF empty.
Proof. now exists (fun _ => false); constructor. Qed.
Hint Resolve empty_WF.

(** *** Verification of [singleton] *)

Lemma singleton_Desc:
  forall e,
   Desc (singleton e) (N.shiftr (intToN e) 6, N.log2 WIDTH) (fun x => x =? intToN e).
Proof.
  intros.
  apply DescTip; try nonneg; try isBitMask.
  symmetry; apply rPrefix_shiftr.
  intro i.
  symmetry; apply bitmapInRange_bitmapOf.
Qed.

Lemma singleton_Sem:
  forall e, Sem (singleton e) (fun x => x =? (intToN e)).
Proof.
  intros.
  eapply DescSem.
  apply singleton_Desc; assumption.
Qed.

Lemma singleton_WF:
  forall e, WF (singleton e).
Proof. intros. eexists. apply singleton_Sem; auto. Qed.

(** *** Verification of [insert] *)

Lemma link_Desc:
    forall p1' s1 r1 f1 p2' s2 r2 f2 r f,
    Desc s1 r1 f1 ->
    Desc s2 r2 f2 ->
    p1' = NToInt (rPrefix r1) ->
    p2' = NToInt (rPrefix r2) ->
    rangeDisjoint r1 r2 = true->
    r = commonRangeDisj r1 r2 ->
    (forall i, f i = f1 i || f2 i) ->
  Desc (link p1' s1 p2' s2) r f.
Proof.
  intros; subst.
  unfold link.
  rewrite branchMask_spec.
  rewrite mask_spec.
  rewrite -> zero_spec by (apply commonRangeDisj_rBits_pos; eapply Desc_rNonneg; eassumption).
  Int_Word_N.
  rewrite if_negb.
  match goal with [ |- context [N.testbit ?i ?b] ]  => destruct (N.testbit i b) eqn:Hbit end.
  * assert (Hbit2 : N.testbit (rPrefix r2) (rBits (commonRangeDisj r1 r2) - 1) = false).
    { apply not_true_is_false.
      rewrite <- Hbit.
      apply not_eq_sym.
      apply commonRangeDisj_rBits_Different; try (eapply Desc_rNonneg; eassumption); auto.
    }
    rewrite rangeDisjoint_sym in H3.
    rewrite -> commonRangeDisj_sym in * by (eapply Desc_rNonneg; eassumption).
    apply (DescBin _ _ _ _ _ _ _ _ _ f H0 H); auto.
    + apply commonRangeDisj_rBits_pos; (eapply Desc_rNonneg; eassumption).
    + rewrite <- Hbit2.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
    + rewrite <- Hbit at 1.
      rewrite -> commonRangeDisj_sym by (eapply Desc_rNonneg; eassumption).
      rewrite rangeDisjoint_sym in H3.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
    + solve_f_eq.
  * assert (Hbit2 : N.testbit (rPrefix r2) (rBits (commonRangeDisj r1 r2) - 1) = true).
    { apply not_false_iff_true.
      rewrite <- Hbit.
      apply not_eq_sym.
      apply commonRangeDisj_rBits_Different; try (eapply Desc_rNonneg; eassumption); auto.
    }
    apply (DescBin _ _ _ _ _ _ _ _ _ f H H0); auto.
    + apply commonRangeDisj_rBits_pos; (eapply Desc_rNonneg; eassumption).
    + rewrite <- Hbit.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
    + rewrite <- Hbit2 at 1.
      rewrite -> commonRangeDisj_sym by (eapply Desc_rNonneg; eassumption).
      rewrite rangeDisjoint_sym in H3.
      apply isSubrange_halfRange_commonRangeDisj;
        try (eapply Desc_rNonneg; eassumption); auto.
Qed.

Lemma insertBM_Desc:
  forall p' bm r1 f1,
  forall s2 r2 f2,
  forall r f, 
  Desc (Tip p' bm) r1 f1 ->
  Desc s2 r2 f2 ->
  r = commonRange r1 r2 ->
  (forall i, f i = f1 i || f2 i) ->
  Desc (insertBM p' bm s2) r f.
Proof.
  intros ????????? HDTip HD ??; subst.
  assert (p' = NToInt (rPrefix r1)) by (inversion HDTip; auto); subst.
  assert (rBits r1 = N.log2 WIDTH)  by (inversion HDTip; auto).
  generalize dependent f.
  induction HD as [p2' bm2 r2 f2|s2 r2 f2 s3 r3 f3 p2' r]; subst; intros f' Hf.
  * simpl.
    unfoldMethods.
    Int_Word_N.
    apply same_size_compare; try Nomega; intros.
    + subst.
      rewrite commonRange_idem.
      inversion_clear HDTip.
      apply DescTip; auto.
      - solve_f_eq.
      - Int_Word_N. isBitMask.
    + rewrite rangeDisjoint_sym in *.
      eapply link_Desc; try apply HDTip; auto.
      - apply DescTip; auto.
      - apply disjoint_commonRange; auto.
  * simpl. unfoldMethods.

    assert (N.log2 WIDTH <= rBits r2)%N by (eapply Desc_larger_WIDTH; eauto).
    assert (rBits r2 <= rBits (halfRange r0 false))%N by (apply subRange_smaller; auto).
    assert (rBits (halfRange r0 false) < rBits r0)%N by (apply halfRange_smaller; auto).
    assert (rBits r1 < rBits r0)%N by Nomega.

    apply nomatch_zero_smaller; try assumption; intros.
    + eapply link_Desc; eauto; try (inversion HDTip; auto).
      eapply DescBin; eauto.
      apply disjoint_commonRange; assumption.
    + rewrite -> (isSubrange_commonRange_r r1 r0) in * by isSubrange_true.
      eapply DescBin; try apply HD2; try apply IHHD1 with (f := fun j => f1 j || f2 j); auto.
      ** isSubrange_true; eapply Desc_rNonneg; eassumption.
      ** solve_f_eq.
    + rewrite -> (isSubrange_commonRange_r r1 r0) in * by isSubrange_true.
      eapply DescBin; try apply HD1; try apply IHHD2 with (f := fun j => f1 j || f3 j); auto.
      ** isSubrange_true; eapply Desc_rNonneg; eassumption.
      ** solve_f_eq.
Qed.

Lemma insert_Desc:
  forall e r1,
  forall s2 r2 f2,
  forall r f, 
  Desc s2 r2 f2 ->
  r1 = (N.shiftr (intToN e) tip_width, tip_width) ->
  r = commonRange r1 r2 ->
  (forall i, f i = (i =? intToN e) || f2 i) ->
  Desc (insert e s2) r f.
Proof.
  intros.
  eapply insertBM_Desc.
  eapply DescTip; try nonneg.
  * symmetry. apply rPrefix_shiftr.
  * reflexivity.
  * isBitMask.
  * eassumption.
  * congruence.
  * intros j. rewrite H2. f_equal.
    symmetry. apply bitmapInRange_bitmapOf.
Qed.

Lemma insert_Nil_Desc:
  forall e r f,
  r = (N.shiftr (intToN e) tip_width, tip_width) ->
  (forall i, f i = (i =? intToN e)) ->
  Desc (insert e Nil) r f.
Proof.
  intros; subst.
  apply DescTip; try nonneg.
  * symmetry. apply rPrefix_shiftr.
  * intros j. rewrite H0. symmetry. apply bitmapInRange_bitmapOf.
  * isBitMask.
Qed.

Lemma insert_Sem:
  forall e s2 f2 f,
  Sem s2 f2 ->
  (forall i, f i = (i =? intToN e) || f2 i) ->
  Sem (insert e s2) f.
Proof.
  intros.
  destruct H.
  * eapply DescSem. apply insert_Nil_Desc; auto.
    solve_f_eq.
  * eapply DescSem. eapply insert_Desc; eauto.
Qed.

Lemma insert_WF:
  forall n s, WF s -> WF (insert n s).
Proof.
  intros.
  destruct H.
  eexists.
  eapply insert_Sem; eauto.
  intro i; reflexivity.
Qed.

(** *** Verification of the smart constructors [tip] and [bin] *)

Lemma tip_Desc0:
  forall p bm r f,
    p = NToInt (rPrefix r) ->
    rBits r = N.log2 WIDTH ->
    (forall i, f i = bitmapInRange r bm i) ->
    isBitMask0 (wordToN bm) ->
    Desc0 (tip p bm) r f.
Proof.
  intros.
  unfold tip.
  unfoldMethods.
  Int_Word_N.
  simpl (Z.to_N 0).
  rewrite isBitMask0_zero_or_isBitMask in H2.
  destruct H2.
  * assert (bm = NToWord 0) by admit.
    subst. Int_Word_N.
    rewrite N.eqb_refl.
    apply Desc0Nil.
    intro j. rewrite H1.
    apply bitmapInRange_0.
  * replace (wordToN bm =? 0)%N with false
      by admit.
(*       by (symmetry; apply N.eqb_neq; intro; subst; inversion H2; inversion H). *)
    apply Desc_Desc0.
    apply DescTip; auto.
Admitted.

Lemma bin_Desc0:
  forall s1 r1 f1 s2 r2 f2 p msk r f,
    Desc0 s1 r1 f1 ->
    Desc0 s2 r2 f2 ->
    (0 < rBits r)%N ->
    isSubrange r1 (halfRange r false) = true ->
    isSubrange r2 (halfRange r true) = true ->
    p = NToInt (rPrefix r) ->
    msk = NToInt (rMask r) -> 
    (forall i, f i = f1 i || f2 i) ->
    Desc0 (bin p msk s1 s2) r f.
Proof.
  intros.
  destruct H, H0.
  * apply Desc0Nil.
    intro j. rewrite H6, H, H0. reflexivity.
  * replace (bin _ _ _ _) with s by (destruct s; reflexivity).
    eapply Desc0NotNil; eauto.
    + isSubrange_true.
    + solve_f_eq.
  * replace (bin _ _ _ _) with s by (destruct s; reflexivity).
    eapply Desc0NotNil; try eassumption.
    + isSubrange_true.
    + solve_f_eq.
  * replace (bin p msk s s0) with (Bin p msk s s0)
      by (destruct s, s0; try reflexivity; try inversion HD; try inversion HD0).
    apply Desc_Desc0.
    eapply DescBin; try eassumption.
    + isSubrange_true.
    + isSubrange_true.
    + solve_f_eq.
Qed.

(** *** Verification of [delete] *)

Lemma deleteBM_Desc:
  forall p' bm s2 r1 r2 f1 f2 f,
  Desc (Tip p' bm) r1 f1 ->
  Desc s2 r2 f2 ->
  (forall i, f i = negb (f1 i) && f2 i) ->
  Desc0 (deleteBM p' bm s2) r2 f.
Proof.
  intros ???????? HTip HD Hf.
  revert dependent f.
  induction HD; intros f' Hf'; subst.
  * simpl deleteBM; unfold Prim.seq.
    inversion_clear HTip; subst.
    unfoldMethods. Int_Word_N.
    apply same_size_compare; try Nomega; intros.
    + subst.
      apply tip_Desc0; auto.
      - solve_f_eq.
      - isBitMask.
    + apply Desc_Desc0.
      apply DescTip; auto.
      solve_f_eq_disjoint.
  * simpl. unfold Prim.seq.
    inversion_clear HTip; subst.

    assert (N.log2 WIDTH <= rBits r2)%N by (eapply Desc_larger_WIDTH; eauto).
    assert (rBits r2 <= rBits (halfRange r true))%N by (apply subRange_smaller; auto).
    assert (rBits (halfRange r true) < rBits r)%N by (apply halfRange_smaller; auto).
    assert (rBits r1 < rBits r)%N by Nomega.

    apply nomatch_zero_smaller; try assumption; intros.
    + rewrite rangeDisjoint_sym in *.
      apply Desc_Desc0.
      eapply DescBin; try eassumption; try reflexivity.
      intro.
        rewrite Hf'. rewrite H4. rewrite H5.
        destruct (inRange i r) eqn:Hir.
        - rewrite bitmapInRange_outside by inRange_false.
          reflexivity.
        - rewrite (Desc_outside HD1) by inRange_false.
          rewrite (Desc_outside HD2) by inRange_false.
          split_bool; reflexivity.
    + eapply bin_Desc0.
      ** apply IHHD1.
         intro. reflexivity.
      ** apply Desc_Desc0; eassumption.
      ** assumption.
      ** assumption.
      ** assumption.
      ** reflexivity.
      ** reflexivity.
      ** solve_f_eq_disjoint.
    + eapply bin_Desc0.
      ** apply Desc_Desc0; eassumption.
      ** apply IHHD2.
         intro. reflexivity.
      ** assumption.
      ** assumption.
      ** assumption.
      ** reflexivity.
      ** reflexivity.
      ** solve_f_eq_disjoint.
Qed.

Lemma delete_Desc:
  forall e s r f f',
  Desc s r f ->
  (forall i, f' i = negb (i =? intToN e) && f i) ->
  Desc0 (delete e s) r f'.
Proof.
  intros.
  unfold delete, Prim.seq.
  eapply deleteBM_Desc.
  * eapply DescTip; try nonneg.
    + symmetry. apply rPrefix_shiftr.
    + reflexivity.
    + isBitMask.
  * eassumption.
  * setoid_rewrite bitmapInRange_bitmapOf. assumption.
Qed.

Lemma delete_Sem:
  forall e s f f',
  Sem s f ->
  (forall i, f' i = negb (i =? intToN e) && f i) ->
  Sem (delete e s) f'.
Proof.
  intros.
  destruct H.
  * apply SemNil.
    solve_f_eq.
  * eapply Desc0_Sem.
    eapply delete_Desc; try eassumption.
Qed.

Lemma delete_WF:
  forall n s,
  WF s -> WF (delete n s).
Proof.
  intros.
  destruct H.
  eexists.
  eapply delete_Sem; try eassumption.
  intro i. reflexivity.
Qed.

(** *** Verification of [union] *)

(** The following is copied from the body of [union] *)

Definition union_body s1 s2 := match s1, s2 with
  | (Bin p1 m1 l1 r1 as t1) , (Bin p2 m2 l2 r2 as t2) => 
     let union2 :=
       if nomatch p1 p2 m2 : bool
       then link p1 t1 p2 t2
       else if zero p1 m2 : bool
            then Bin p2 m2 (union t1 l2) r2
            else Bin p2 m2 l2 (union t1 r2) in
     let union1 :=
       if nomatch p2 p1 m1 : bool
       then link p1 t1 p2 t2
       else if zero p2 m1 : bool
            then Bin p1 m1 (union l1 t2) r1
            else Bin p1 m1 l1 (union r1 t2) in
     if shorter m1 m2 : bool
     then union1
     else if shorter m2 m1 : bool
          then union2
          else if p1 == p2 : bool
                   then Bin p1 m1 (union l1 l2) (union r1 r2)
                   else link p1 t1 p2 t2
  | (Bin _ _ _ _ as t) , Tip kx bm => insertBM kx bm t
  | (Bin _ _ _ _ as t) , Nil => t
  | Tip kx bm , t => insertBM kx bm t
  | Nil , t => t
  end.

Lemma union_eq s1 s2 :
  union s1 s2 = union_body s1 s2.
Proof.
  unfold union, union_func.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext.
  unfold projT1, projT2.
  unfold union_body.
  repeat lazymatch goal with
    | [ |- _ = match ?x with _ => _ end ] => destruct x
    | _ => reflexivity
  end.
Qed.

Program Fixpoint union_Desc
  s1 r1 f1 s2 r2 f2 f
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  (forall i, f i = f1 i || f2 i) ->
  Desc (union s1 s2) (commonRange r1 r2) f 
  := fun HD1 HD2 Hf => _.
Next Obligation.
  rewrite union_eq.
  unfold union_body.
  inversion HD1; subst.
  * eapply insertBM_Desc; try eassumption; try reflexivity.
  * set (sl := Bin (NToInt (rPrefix r1)) (NToInt (rMask r1)) s0 s3) in *.
    inversion HD2; subst.
    + rewrite commonRange_sym by (eapply Desc_rNonneg; eassumption).
      eapply insertBM_Desc; try eassumption; try reflexivity.
      solve_f_eq.
    + set (sr := Bin (NToInt (rPrefix r2)) (NToInt (rMask r2)) s1 s4) in *.
      rewrite !shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r1)); [|destruct (N.ltb_spec (rBits r1) (rBits r2))].
      ++ apply nomatch_zero_smaller; try assumption; intros.
        - rewrite rangeDisjoint_sym in *.
          rewrite disjoint_commonRange in * by assumption.
          eapply link_Desc;
            [ eapply DescBin with (r := r1); try eassumption; try reflexivity
            | eapply DescBin with (r := r2); try eassumption; try reflexivity
            |..]; auto.
        - rewrite -> (isSubrange_commonRange_l r1 r2) in * by isSubrange_true.
          eapply DescBin; [eapply union_Desc|eassumption|..]; try eassumption; try reflexivity.
          ** subst sl sr. simpl. omega.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** solve_f_eq.
        - rewrite -> (isSubrange_commonRange_l r1 r2) in *  by isSubrange_true.
          eapply DescBin; [eassumption|eapply union_Desc|..]; try eassumption; try reflexivity.
          ** subst sl sr. simpl. omega.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** solve_f_eq.
      ++ apply nomatch_zero_smaller; try assumption; intros.
        - rewrite disjoint_commonRange in * by assumption.
          eapply link_Desc;
            [ eapply DescBin with (r := r1); try eassumption; try reflexivity
            | eapply DescBin with (r := r2); try eassumption; try reflexivity
            |..]; auto.
        - rewrite -> (isSubrange_commonRange_r r1 r2) in * by isSubrange_true.
          eapply DescBin; [eapply union_Desc|eassumption|..]; try eassumption; try reflexivity.
          ** subst sl sr. simpl. omega.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** solve_f_eq.
        - rewrite -> (isSubrange_commonRange_r r1 r2) in *  by isSubrange_true.
          eapply DescBin; [eassumption|eapply union_Desc|..]; try eassumption; try reflexivity.
          ** subst sl sr. simpl. omega.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** solve_f_eq.
      ++ unfoldMethods. Int_Word_N.
         apply same_size_compare; try Nomega; intros.
        - subst.
          rewrite commonRange_idem in *.
          eapply DescBin; try assumption; try reflexivity.
          ** eapply union_Desc.
             -- subst sl sr. simpl. omega.
             -- eassumption.
             -- eassumption.
             -- intro i. reflexivity.
          ** eapply union_Desc.
             -- subst sl sr. simpl. omega.
             -- eassumption.
             -- eassumption.
             -- intro i. reflexivity.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** isSubrange_true; eapply Desc_rNonneg; eassumption.
          ** solve_f_eq.
      - rewrite disjoint_commonRange in * by assumption.
        eapply link_Desc;
          [ eapply DescBin with (r := r1); try eassumption; try reflexivity
          | eapply DescBin with (r := r2); try eassumption; try reflexivity
          |..]; auto.
Qed.

Lemma union_Sem:
  forall s1 f1 s2 f2,
  Sem s1 f1 ->
  Sem s2 f2 ->
  Sem (union s1 s2) (fun i => f1 i || f2 i).
Proof.
  intros.
  destruct H; [|destruct H0].
  * eapply Sem_change_f. apply H0.
    solve_f_eq.
  * eapply Sem_change_f. eapply DescSem.
    replace (union s Nil) with s by (destruct s; reflexivity).
    eapply HD.
    solve_f_eq.
  * eapply DescSem.
    eapply union_Desc; try eassumption.
    solve_f_eq.
Qed.

Lemma union_WF:
  forall s1 s2, WF s1 ->  WF s2 -> WF (union s1 s2).
Proof.
  intros.
  destruct H, H0.
  eexists. apply union_Sem; eassumption.
Qed.

Local Ltac union_Sem_reasoning :=
  repeat intros [? ?];
  repeat match goal with
         | SEMs : Sem ?s ?fs, SEMt : Sem ?t ?ft |- context[union ?s ?t] =>
           match goal with
           | _ : Sem (union s t) _ |- _ => fail 1
           |                          _ => specialize (union_Sem s fs t ft SEMs SEMt) as ?
           end
         end;
  eapply Sem_unique; try eassumption;
  intros; simpl.

Lemma union_assoc (s1 s2 s3 : IntSet) :
  WF s1 ->
  WF s2 ->
  WF s3 ->
  union s1 (union s2 s3) = union (union s1 s2) s3.
Proof. now union_Sem_reasoning; rewrite orb_assoc. Qed.

Lemma union_comm (s1 s2 : IntSet) :
  WF s1 ->
  WF s2 ->
  union s1 s2 = union s2 s1.
Proof. now union_Sem_reasoning; rewrite orb_comm. Qed.

(** *** Verification of [unions] *)

Require Import Proofs.Data.Foldable. 

Lemma Forall_rev:
  forall A P (l : list A), Forall P (rev l) <-> Forall P l.
Proof.
  intros.
  rewrite !Forall_forall.
  setoid_rewrite <- in_rev.
  reflexivity.
Qed.

(* Needs more than a trivial rephrasing for word-sizes IntMaps *)
(*
Lemma unions_Sem (ss : list IntSet) :
  Forall WF ss ->
  Sem (unions ss) (fun i => existsb (member i) ss).
Proof.
  unfold unions; rewrite hs_coq_foldl_list, <-fold_left_rev_right.
  remember (rev ss) as rss eqn:def_rss.
  replace ss with (rev rss) by now subst; apply rev_involutive.
  clear def_rss.
  rewrite Forall_rev.
  induction rss as [|s rss IH]; simpl; intros WFrss'.
  - now constructor.
  - inversion WFrss' as [|s_ rss_ WFs WFrss]; subst s_ rss_.
    eapply Sem_change_f; [|intros; rewrite existsb_app; simpl; rewrite orb_false_r; reflexivity].
    apply union_Sem.
    + now apply IH.
    + destruct WFs as [f SEM].
      apply Sem_change_f with f; trivial.
      now intros; apply member_Sem.
Qed.

Lemma unions_WF (ss : list IntSet) :
  Forall WF ss ->
  WF (unions ss).
Proof. now eexists; apply unions_Sem. Qed.
*)

(** *** Verification of [intersection] *)

(** The following is copied from the body of [intersection] *)

Definition intersection_body s1 s2 := match s1, s2 with
  | (Bin p1 m1 l1 r1 as t1) , (Bin p2 m2 l2 r2 as t2) =>
      let intersection2 :=
         if nomatch p1 p2 m2 : bool
         then Nil
         else if zero p1 m2 : bool
              then intersection t1 l2
              else intersection t1 r2 in
       let intersection1 :=
         if nomatch p2 p1 m1 : bool
         then Nil
         else if zero p2 m1 : bool
              then intersection l1 t2
              else intersection r1 t2 in
       if shorter m1 m2 : bool
       then intersection1
       else if shorter m2 m1 : bool
            then intersection2
            else if p1 GHC.Base.== p2 : bool
                 then bin p1 m1 (intersection l1 l2) (intersection r1
                                                     r2)
                 else Nil
  | (Bin _ _ _ _ as t1) , Tip kx2 bm2 =>
     (fix intersectBM arg_11__
     := match arg_11__ as arg_11__' return (arg_11__' = arg_11__ -> IntSet) with
          | Bin p1 m1 l1 r1 => fun _ =>
                               if nomatch kx2 p1 m1 : bool
                               then Nil
                               else if zero kx2 m1 : bool
                                    then intersectBM l1
                                    else intersectBM r1
          | Tip kx1 bm1 => fun _ =>
                           if kx1 GHC.Base.== kx2 : bool
                           then tip kx1 (bm1 Data.Bits..&.(**) bm2)
                           else Nil
          | Nil => fun _ => Nil
      end eq_refl) t1
  | Bin _ _ _ _ , Nil => Nil
  | Tip kx1 bm1 , t2 =>
      (fix intersectBM arg_18__
          := match arg_18__  as arg_18__' return (arg_18__' = arg_18__ -> IntSet) with
               | Bin p2 m2 l2 r2 => fun _ =>
                                    if nomatch kx1 p2 m2 : bool
                                    then Nil
                                    else if zero kx1 m2 : bool
                                         then intersectBM l2
                                         else intersectBM r2
               | Tip kx2 bm2 => fun _ =>
                                if kx1 GHC.Base.== kx2 : bool
                                then tip kx1 (bm1 Data.Bits..&.(**) bm2)
                                else Nil
               | Nil => fun _ => Nil
             end eq_refl) t2
  | Nil , _ => Nil
  end.

Lemma intersection_eq s1 s2 :
  intersection s1 s2 = intersection_body s1 s2.
Proof.
  unfold intersection, intersection_func.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext.
  unfold projT1, projT2.
  unfold intersection_body.
  repeat match goal with
    | _ => progress replace (Sumbool.sumbool_of_bool false) with (@right (false = true) (false = false) (@eq_refl bool false))
by reflexivity
    | _ => progress replace (Sumbool.sumbool_of_bool true) with (@left (true = true) (true = false) (@eq_refl bool true))
by reflexivity
    | [ |- _ = match ?x with _ => _ end ] => destruct x
    | _ => assumption || reflexivity
    | [ |- _ ?x = _ ?x ] => induction x
  end.
Qed.


Program Fixpoint intersection_Desc
  s1 r1 f1 s2 r2 f2 f
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  (forall i, f i = f1 i && f2 i) ->
  Desc0 (intersection s1 s2) r1 f 
  := fun HD1 HD2 Hf => _.
Next Obligation.
  rewrite intersection_eq.
  unfold intersection_body.
  unfoldMethods.

  inversion HD1.
  * (* s1 is a Tip *)
    subst.
    clear intersection_Desc.
    generalize dependent f.
    induction HD2; intros f' Hf'; subst.
    + Int_Word_N.
      apply same_size_compare; try Nomega; intros.
      -- subst.
         apply tip_Desc0; auto.
         ** solve_f_eq.
         ** isBitMask.
      -- apply Desc0Nil.
         solve_f_eq_disjoint.
    + assert (N.log2 WIDTH <= rBits r0)%N by (eapply Desc_larger_WIDTH; eauto).
      assert (rBits r0 <= rBits (halfRange r false))%N by (apply subRange_smaller; auto).
      assert (rBits (halfRange r false) < rBits r)%N by (apply halfRange_smaller; auto).
      assert (rBits r1 < rBits r)%N by Nomega.

      apply nomatch_zero_smaller; try assumption; intros.
      - apply Desc0Nil.
        solve_f_eq_disjoint.
      - eapply Desc0_subRange; [apply IHHD2_1|]. clear IHHD2_1 IHHD2_2.
        ** solve_f_eq_disjoint.
        ** isSubrange_true; eapply Desc_rNonneg; eassumption.
      - eapply Desc0_subRange.
        ** apply IHHD2_2.
           solve_f_eq_disjoint.
        ** isSubrange_true; eapply Desc_rNonneg; eassumption.

  * (* s1 is a Bin *)
    inversion HD2.
    + (* s2 is a Tip *)

      (* Need to undo the split of s1 *)
      change (Desc0 ((fix intersectBM (arg_11__ : IntSet) : IntSet :=
        match arg_11__  as arg_11__' return (arg_11__' = arg_11__ -> IntSet) with
        | Bin p1 m1 l1 r5 =>
            fun _ =>
            if nomatch p0 p1 m1
            then Nil
            else if zero p0 m1 then intersectBM l1 else intersectBM r5
        | Tip kx1 bm1 =>
            fun _ =>
            if _GHC.Base.==_ kx1 p0 then tip kx1 (NToWord (N.land (wordToN bm1) (wordToN bm))) else Nil
        | Nil => fun _ => Nil
        end eq_refl) (Bin p msk s0 s3)) r1 f).
      rewrite  H7.
      clear dependent s0. clear dependent s3. clear dependent r0. clear dependent r3. clear dependent f0. clear dependent f3.
      clear H1.
      subst.

      (* Now we are essentially in the same situation as above. *)
      (* Unfortunately, the two implementations of [intersectionBM] are slightly 
         different in irrelevant details that make ist just hard enough to abstract
         over them in a lemma of its own. So let’s just copy’n’paste. *)
      clear intersection_Desc.
      generalize dependent f.
      induction HD1; intros f' Hf'; subst.
      ++ unfoldMethods. Int_Word_N.
         apply same_size_compare; try Nomega; intros.
         subst.
         apply tip_Desc0; auto.
         ** solve_f_eq_disjoint.
         ** isBitMask.
         ** apply Desc0Nil.
            solve_f_eq_disjoint.

      ++ assert (N.log2 WIDTH <= rBits r1)%N by (eapply Desc_larger_WIDTH; eauto).
         assert (rBits r1 <= rBits (halfRange r false))%N by (apply subRange_smaller; auto).
         assert (rBits (halfRange r false) < rBits r)%N by (apply halfRange_smaller; auto).
         assert (rBits r2 < rBits r)%N by Nomega.

         apply nomatch_zero_smaller; try assumption; intros.
         - apply Desc0Nil.
           solve_f_eq_disjoint.

         - eapply Desc0_subRange.
           ** apply IHHD1_1.
              solve_f_eq_disjoint.
           ** isSubrange_true; eapply Desc_rNonneg; eassumption.

         - eapply Desc0_subRange.
           ** apply IHHD1_2.
              solve_f_eq_disjoint.
           ** isSubrange_true; eapply Desc_rNonneg; eassumption.
 
    + subst.
      set (sl := Bin (NToInt (rPrefix r1)) (NToInt (rMask r1)) s0 s3) in *.
      set (sr := Bin (NToInt (rPrefix r2)) (NToInt (rMask r2)) s4 s5) in *.
      rewrite !shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r1)).
      ++ (* s2 is smaller than s1 *)
         apply nomatch_zero_smaller; try assumption; intros.
         - (* s2 is disjoint of s1 *)
           apply Desc0Nil.
           solve_f_eq_disjoint.

         - (* s2 is part of the left half of s1 *)
           eapply Desc0_subRange.
           eapply intersection_Desc; clear intersection_Desc; try eassumption.
           ** subst sl sr. simpl. omega.
           ** solve_f_eq_disjoint.
           ** isSubrange_true; eapply Desc_rNonneg; eassumption.
         - (* s2 is part of the right half of s1 *)
           eapply Desc0_subRange.
           eapply intersection_Desc; clear intersection_Desc; try eassumption.
           ** subst sl sr. simpl. omega.
           ** solve_f_eq_disjoint.
           ** isSubrange_true; eapply Desc_rNonneg; eassumption.

      ++ (* s2 is not smaller than s1 *)
        destruct (N.ltb_spec (rBits r1) (rBits r2)).
        -- (* s2 is smaller than s1 *)
          apply nomatch_zero_smaller; try assumption; intros.
          - (* s1 is disjoint of s2 *)
            apply Desc0Nil.
            solve_f_eq_disjoint.
          - (* s1 is part of the left half of s2 *)
            eapply Desc0_subRange.
            eapply intersection_Desc; clear intersection_Desc; try eassumption.
            ** subst sl sr. simpl. omega.
            ** solve_f_eq_disjoint.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.

          - (* s1 is part of the right half of s2 *)

            eapply Desc0_subRange.
            eapply intersection_Desc; clear intersection_Desc; try eassumption.
            ** subst sl sr. simpl. omega.
            ** solve_f_eq_disjoint.
            ** isSubrange_true; eapply Desc_rNonneg; eassumption.

        -- (* s1 and s2 are the same size *)
           Int_Word_N.
           apply same_size_compare; try Nomega; intros.
           - subst.
             eapply bin_Desc0; try assumption; try reflexivity.
             ** eapply intersection_Desc.
                --- subst sl sr. simpl. omega.
                --- eassumption.
                --- eassumption.
                --- intro i. reflexivity.
             ** eapply intersection_Desc.
                --- subst sl sr. simpl. omega.
                --- eassumption.
                --- eassumption.
                --- intro i. reflexivity.
             ** isSubrange_true; eapply Desc_rNonneg; eassumption.
             ** isSubrange_true; eapply Desc_rNonneg; eassumption.
             ** solve_f_eq_disjoint.
           - apply Desc0Nil.
             solve_f_eq_disjoint.
Qed.

Lemma intersection_Sem:
  forall s1 f1 s2 f2,
  Sem s1 f1 ->
  Sem s2 f2 ->
  Sem (intersection s1 s2) (fun i => f1 i && f2 i).
Proof.
  intros.
  destruct H; [|destruct H0].
  * apply SemNil. solve_f_eq.
  * replace (intersection s Nil) with Nil by (destruct s; reflexivity).
    apply SemNil. solve_f_eq.
  * eapply Desc0_Sem. eapply intersection_Desc; try eauto.
Qed.

Lemma intersection_WF:
  forall s1 s2, WF s1 ->  WF s2 -> WF (intersection s1 s2).
Proof.
  intros.
  destruct H, H0.
  eexists. apply intersection_Sem; eassumption.
Qed.

(** *** Verification of [difference] *)

(** The following is copied from the body of [difference] *)

Definition difference_body s1 s2 := match s1, s2 with
  | (Bin p1 m1 l1 r1 as t1) , (Bin p2 m2 l2 r2 as t2) =>
     let difference2 :=
       if nomatch p1 p2 m2 : bool
       then t1
       else if zero p1 m2 : bool
            then difference t1 l2
            else difference t1 r2 in
     let difference1 :=
       if nomatch p2 p1 m1 : bool
       then t1
       else if zero p2 m1 : bool
            then bin p1 m1 (difference l1 t2) r1
            else bin p1 m1 l1 (difference r1 t2) in
     if shorter m1 m2 : bool
     then difference1
     else if shorter m2 m1 : bool
          then difference2
          else if p1 GHC.Base.== p2 : bool
               then bin p1 m1 (difference l1 l2) (difference r1 r2)
               else t1
  | (Bin _ _ _ _ as t) , Tip kx bm => deleteBM kx bm t
  | (Bin _ _ _ _ as t) , Nil => t
  | (Tip kx bm as t1) , t2 =>
     (fix differenceTip arg_12__
        := match arg_12__ as arg_12__' return (arg_12__' = arg_12__ -> IntSet) with 
             | Bin p2 m2 l2 r2 => fun _ =>
                                  if nomatch kx p2 m2 : bool
                                  then t1
                                  else if zero kx m2 : bool
                                       then differenceTip l2
                                       else differenceTip r2
             | Tip kx2 bm2 => fun _ =>
                              if kx GHC.Base.== kx2 : bool
                              then tip kx (bm Data.Bits..&.(**) (Data.Bits.complement bm2))
                              else t1
             | Nil => fun _ => t1
           end eq_refl) t2
  | Nil , _ => Nil
  end.

Lemma difference_eq s1 s2 :
  difference s1 s2 = difference_body s1 s2.
Proof.
  unfold difference, difference_func.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext.
  unfold projT1, projT2.
  unfold difference_body.
  repeat match goal with
    | _ => progress replace (Sumbool.sumbool_of_bool false) with (@right (false = true) (false = false) (@eq_refl bool false))
by reflexivity
    | _ => progress replace (Sumbool.sumbool_of_bool true) with (@left (true = true) (true = false) (@eq_refl bool true))
by reflexivity
    | [ |- _ = match ?x with _ => _ end ] => destruct x
    | _ => assumption || reflexivity
    | [ |- _ ?x = _ ?x ] => induction x
  end.
Qed.

Program Fixpoint difference_Desc
  s1 r1 f1 s2 r2 f2 f
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  (forall i, f i = f1 i && negb (f2 i)) ->
  Desc0 (difference s1 s2) r1 f 
  := fun HD1 HD2 Hf => _.
Next Obligation.
  rewrite difference_eq.
  unfold difference_body.
  unfoldMethods.

  inversion HD1.
  * (* s1 is a Tip *)
    subst.
    clear difference_Desc.
    generalize dependent f.
    induction HD2; intros f' Hf'; subst.
    + Int_Word_N.
      apply same_size_compare; try Nomega; intros.
      -- subst.
         apply tip_Desc0; auto.
         ** solve_f_eq.
         ** isBitMask.
      -- eapply Desc0NotNil; try eassumption.
         ** apply isSubrange_refl.
         ** solve_f_eq_disjoint.
    + assert (N.log2 WIDTH <= rBits r0)%N by (eapply Desc_larger_WIDTH; eauto).
      assert (rBits r0 <= rBits (halfRange r false))%N by (apply subRange_smaller; auto).
      assert (rBits (halfRange r false) < rBits r)%N by (apply halfRange_smaller; auto).
      assert (rBits r1 < rBits r)%N by Nomega.

      apply nomatch_zero_smaller; try assumption; intros.
      - eapply Desc0NotNil; try eassumption.
        ** apply isSubrange_refl.
        ** solve_f_eq_disjoint.
      - eapply Desc0_subRange; [apply IHHD2_1|apply isSubrange_refl]. clear IHHD2_1 IHHD2_2.
        solve_f_eq_disjoint.
      - eapply Desc0_subRange; [apply IHHD2_2|apply isSubrange_refl]. clear IHHD2_1 IHHD2_2.
        solve_f_eq_disjoint.

  * (* s1 is a Bin *)
    inversion HD2.
    + (* s2 is a Tip *)
      subst.
      eapply deleteBM_Desc; try eassumption.
      solve_f_eq.
    + subst.
      set (sl := Bin (NToInt (rPrefix r1)) (NToInt (rMask r1)) s0 s3) in *.
      set (sr := Bin (NToInt (rPrefix r2)) (NToInt (rMask r2)) s4 s5) in *.
      rewrite !shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r1)).
      ** (* s2 is smaller than s1 *)
        apply nomatch_zero_smaller; try assumption; intros.
        - (* s2 is disjoint of s1 *)
          eapply Desc_Desc0; eapply DescBin; try eassumption; try reflexivity.
          solve_f_eq_disjoint.

        - (* s2 is part of the left half of s1 *)
          eapply bin_Desc0.
          ++ eapply difference_Desc; clear difference_Desc; try eassumption.
             subst sl sr. simpl. omega.
             intro i; reflexivity.
          ++ apply Desc_Desc0; eassumption.
          ++ eassumption.
          ++ eassumption.
          ++ eassumption.
          ++ reflexivity.
          ++ reflexivity.
          ++ solve_f_eq_disjoint.
        - (* s2 is part of the right half of s1 *)
          eapply bin_Desc0.
          ++ apply Desc_Desc0; eassumption.
          ++ eapply difference_Desc; clear difference_Desc; try eassumption.
             subst sl sr. simpl. omega.
             intro i; reflexivity.
          ++ eassumption.
          ++ eassumption.
          ++ eassumption.
          ++ reflexivity.
          ++ reflexivity.
          ++ solve_f_eq_disjoint.

      ** (* s2 is not smaller than s1 *)
        destruct (N.ltb_spec (rBits r1) (rBits r2)).
        -- (* s2 is smaller than s1 *)
          apply nomatch_zero_smaller; try assumption; intros.
          - (* s1 is disjoint of s2 *)
            eapply Desc_Desc0; eapply DescBin; try eassumption; try reflexivity.
            solve_f_eq_disjoint.
          - (* s1 is part of the left half of s2 *)
            eapply Desc0_subRange.
            eapply difference_Desc; clear difference_Desc; try eassumption.
            *** subst sl sr. simpl. omega.
            *** solve_f_eq_disjoint.
            *** apply isSubrange_refl.
          - (* s1 is part of the right half of s2 *)
            eapply Desc0_subRange.
            eapply difference_Desc; clear difference_Desc; try eassumption.
            *** subst sl sr. simpl. omega.
            *** solve_f_eq_disjoint.
            *** apply isSubrange_refl.

        -- (* s1 and s2 are the same size *)
          assert (rBits r1 = rBits r2) by Nomega.
          Int_Word_N.
          apply same_size_compare; try Nomega; intros.
          - subst.
            eapply bin_Desc0; try assumption; try reflexivity.
            ++ eapply difference_Desc.
               --- subst sl sr. simpl. omega.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ++ eapply difference_Desc.
               --- subst sl sr. simpl. omega.
               --- eassumption.
               --- eassumption.
               --- intro i. reflexivity.
            ++ assumption.
            ++ assumption.
            ++ solve_f_eq_disjoint.
          - eapply Desc_Desc0; eapply DescBin; try eassumption; try reflexivity.
            solve_f_eq_disjoint.
Qed.

Lemma difference_Sem:
  forall s1 f1 s2 f2,
  Sem s1 f1 ->
  Sem s2 f2 ->
  Sem (difference s1 s2) (fun i => f1 i && negb (f2 i)).
Proof.
  intros.
  destruct H; [|destruct H0].
  * apply SemNil. solve_f_eq.
  * replace (difference s Nil) with s by (destruct s; reflexivity).
    eapply DescSem.
    eapply Desc_change_f.
    eassumption.
    solve_f_eq.
  * eapply Desc0_Sem. eapply difference_Desc; try eauto.
Qed.

Lemma difference_WF:
  forall s1 s2, WF s1 ->  WF s2 -> WF (difference s1 s2).
Proof.
  intros.
  destruct H, H0.
  eexists. apply difference_Sem; eassumption.
Qed.

(** *** Verification of [disjoint] *)

(** The following is copied from the body of [disjoint] *)

Definition disjoint_body s1 s2 := match s1, s2 with
          | (Bin p1 m1 l1 r1 as t1) , (Bin p2 m2 l2 r2 as t2) =>
           let disjoint2 :=
             if nomatch p1 p2 m2
             then true
             else if zero p1 m2
                  then disjoint t1 l2
                  else disjoint t1 r2 in
           let disjoint1 :=
             if nomatch p2 p1 m1
             then true
             else if zero p2 m1
                  then disjoint l1 t2
                  else disjoint r1 t2 in
           if shorter m1 m2
           then disjoint1
           else if shorter m2 m1
                then disjoint2
                else if p1 GHC.Base.== p2
                     then andb (disjoint l1 l2) (disjoint r1 r2)
                     else true
          | (Bin _ _ _ _ as t1) , Tip kx2 bm2 =>
           let fix disjointBM arg_11__
             := match arg_11__ with
                  | Bin p1 m1 l1 r1 =>
                    if nomatch kx2 p1 m1
                    then true
                    else if zero kx2 m1
                         then disjointBM l1
                         else disjointBM r1
                  | Tip kx1 bm1 =>
                    if kx1 GHC.Base.== kx2
                    then (bm1 Data.Bits..&.(**) bm2)
                         GHC.Base.== GHC.Num.fromInteger 0
                    else true
                  | Nil => true
                end in
               disjointBM t1
          | Bin _ _ _ _ , Nil => true
          | Tip kx1 bm1 , t2 => let fix disjointBM arg_18__
            := match arg_18__ with
                 | Bin p2 m2 l2 r2 => if nomatch kx1 p2 m2
                                      then true
                                      else if zero kx1 m2
                                           then disjointBM l2
                                           else disjointBM r2
                 | Tip kx2 bm2 => if kx1 GHC.Base.== kx2
                                  then (bm1 Data.Bits..&.(**) bm2)
                                       GHC.Base.== GHC.Num.fromInteger 0
                                  else true
                 | Nil => true
               end in
            disjointBM t2
          | Nil , _ => true
        end.

Lemma disjoint_eq s1 s2 :
  disjoint s1 s2 = disjoint_body s1 s2.
Proof.
  unfold disjoint, disjoint_func.
  rewrite Wf.WfExtensionality.fix_sub_eq_ext.
  unfold projT1, projT2.
  unfold disjoint_body.
  repeat match goal with
    | _ => progress replace (Sumbool.sumbool_of_bool false) with (@right (false = true) (false = false) (@eq_refl bool false))
by reflexivity
    | _ => progress replace (Sumbool.sumbool_of_bool true) with (@left (true = true) (true = false) (@eq_refl bool true))
by reflexivity
    | [ |- _ = match ?x with _ => _ end ] => destruct x
    | _ => assumption || reflexivity
    | [ |- _ ?x = _ ?x ] => induction x
  end.
Qed.

Program Fixpoint disjoint_Desc
  s1 r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  disjoint s1 s2 = true <-> (forall i, f1 i && f2 i = false) := _.
Next Obligation.

  Ltac solve_eq_disjoint_specialize :=
   intro i;
   repeat match goal with H : (forall i, _) |- _ => specialize (H i) end;
   repeat split_bool;
   repeat point_to_inRange; repeat saturate_inRange; try inRange_disjoint;
   simpl in *; rewrite ?orb_true_r, ?andb_true_l in *; try congruence.

  rename H into HD1, H0 into HD0.
  rewrite disjoint_eq.
  unfold disjoint_body.
  unfoldMethods.
  inversion HD1.
  * (* s1 is a Tip *)
    subst.
    clear disjoint_Desc.
    induction HD0; intros; subst.
    + Int_Word_N.
      apply same_size_compare; try Nomega; intros.
      -- simpl. subst r1.
         rewrite N.eqb_eq.
         rewrite <- N.bits_inj_iff.
         unfold N.eqf.
         setoid_rewrite N.land_spec.
         setoid_rewrite N.bits_0.
         setoid_rewrite H4. setoid_rewrite H1.
         split; intro.
         ** intro i.
            unfold bitmapInRange.
            destruct (inRange i r).
            ++ apply H.
            ++ reflexivity.
         ** intro n.
            destruct (N.ltb_spec n (2 ^ rBits r))%N.
            ++ specialize (H (intoRange r n)).
               rewrite !bitmapInRange_intoRange in H by assumption.
               assumption.
            ++ replace (rBits r) in H6. change (WIDTH <= n)%N in H6.
               rewrite isBitMask0_outside by isBitMask.
               reflexivity.
      -- split; intro; try reflexivity.
         solve_f_eq_disjoint.
    + assert (N.log2 WIDTH <= rBits r0)%N by (eapply Desc_larger_WIDTH; eauto).
      assert (rBits r0 <= rBits (halfRange r false))%N by (apply subRange_smaller; auto).
      assert (rBits (halfRange r false) < rBits r)%N by (apply halfRange_smaller; auto).
      assert (rBits r1 < rBits r)%N by Nomega.

      apply nomatch_zero_smaller; try assumption; intros.
      - clear IHHD0_1 IHHD0_2.
        split; intro; try reflexivity.
        solve_f_eq_disjoint.
      - rewrite IHHD0_1; clear IHHD0_1 IHHD0_2.
        setoid_rewrite H7. setoid_rewrite H1.
        split; intro; solve_eq_disjoint_specialize.
      - rewrite IHHD0_2; clear IHHD0_1 IHHD0_2.
        setoid_rewrite H7. setoid_rewrite H1.
        split; intro; solve_eq_disjoint_specialize.

  * (* s1 is a Bin *)
    inversion HD0.
    + (* s2 is a Tip *)

      (* Need to undo the split of s1 *)
      change ((fix disjointBM (arg_11__ : IntSet) : bool :=
      match arg_11__ with
      | Bin p1 m1 l1 r5 =>
          if nomatch p0 p1 m1 then true else if zero p0 m1 then disjointBM l1 else disjointBM r5
      | Tip kx1 bm1 => if intToN kx1 =? intToN p0 then wordToN (NToWord (N.land (wordToN bm1) (wordToN bm))) =? wordToN (NToWord (Z.to_N 0)) else true
      | Nil => true
      end) (Bin p msk s0 s3) = true <->  (forall i : N, f1 i && f2 i = false)).
      rewrite H7.
      clear dependent s0. clear dependent s3. clear dependent r0. clear dependent r3. clear dependent f0. clear dependent f3.
      clear dependent p. clear dependent msk.
      clear H1.
      subst.

      (* Now we are essentially in the same situation as above. *)
      (* Unfortunately, the two implementations of [intersectionBM] are slightly 
         different in irrelevant details that make ist just hard enough to abstract
         over them in a lemma of its own. So let’s just copy’n’paste. *)

      clear disjoint_Desc.
      induction HD1; intros; subst.
      ++ Int_Word_N.
         apply same_size_compare; try Nomega; intros.
         -- simpl. subst r2.
            rewrite N.eqb_eq.
            rewrite <- N.bits_inj_iff.
            unfold N.eqf.
            setoid_rewrite N.land_spec.
            setoid_rewrite N.bits_0.
            setoid_rewrite H12. setoid_rewrite H1.
            split; intro.
            ** intro i.
               unfold bitmapInRange.
               destruct (inRange i r).
               +++ apply H.
               +++ reflexivity.
            ** intro n.
               destruct (N.ltb_spec n (2 ^ rBits r))%N.
               +++ specialize (H (intoRange r n)).
                   rewrite !bitmapInRange_intoRange in H by assumption.
                   assumption.
               +++ replace (rBits r) in H3. change (WIDTH <= n)%N in H3.
                   rewrite isBitMask0_outside by isBitMask.
                   reflexivity.
         -- split; intro; try reflexivity.
            solve_f_eq_disjoint.
      ++ assert (N.log2 WIDTH <= rBits r1)%N by (eapply Desc_larger_WIDTH; eauto).
         assert (rBits r1 <= rBits (halfRange r false))%N by (apply subRange_smaller; auto).
         assert (rBits (halfRange r false) < rBits r)%N by (apply halfRange_smaller; auto).
         assert (rBits r2 < rBits r)%N by Nomega.

        apply nomatch_zero_smaller; try assumption; intros.
        - clear IHHD1_1 IHHD1_2.
          split; intro; try reflexivity.
          solve_f_eq_disjoint.
        - rewrite IHHD1_1; clear IHHD1_1 IHHD1_2.
          setoid_rewrite H12. setoid_rewrite H4.
          split; intro; solve_eq_disjoint_specialize.
        - rewrite IHHD1_2; clear IHHD1_1 IHHD1_2.
          setoid_rewrite H12. setoid_rewrite H4.
          split; intro; solve_eq_disjoint_specialize.

    + subst.
      set (sl := Bin (NToInt (rPrefix r1)) (NToInt (rMask r1)) s0 s3) in *.
      set (sr := Bin (NToInt (rPrefix r2)) (NToInt (rMask r2)) s4 s5) in *.
      rewrite !shorter_spec by assumption.
      destruct (N.ltb_spec (rBits r2) (rBits r1)).
      ++ (* s2 is smaller than s1 *)
        apply nomatch_zero_smaller; try assumption; intros.
        - (* s2 is disjoint of s1 *)
          split; intro; try reflexivity.
          solve_f_eq_disjoint.

        - (* s2 is part of the left half of s1 *)
          rewrite disjoint_Desc; try eassumption.
          ** setoid_rewrite H6.
             split; intro; solve_eq_disjoint_specialize.
          ** subst sl sr. simpl. omega.
        - (* s2 is part of the right half of s1 *)
          rewrite disjoint_Desc; try eassumption.
          ** setoid_rewrite H6.
             split; intro; solve_eq_disjoint_specialize.
          ** subst sl sr. simpl. omega.

      ++ (* s2 is not smaller than s1 *)
        destruct (N.ltb_spec (rBits r1) (rBits r2)).
        -- (* s2 is smaller than s1 *)
          apply nomatch_zero_smaller; try assumption; intros.
          - (* s1 is disjoint of s2 *)
            split; intro; try reflexivity.
            solve_f_eq_disjoint.
          - (* s1 is part of the left half of s2 *)
            rewrite disjoint_Desc; try eassumption.
            ** setoid_rewrite H17.
               split; intro; solve_eq_disjoint_specialize.
            ** subst sl sr. simpl. omega.
          - (* s1 is part of the right half of s2 *)
            rewrite disjoint_Desc; try eassumption.
            ** setoid_rewrite H17.
               split; intro; solve_eq_disjoint_specialize.
            ** subst sl sr. simpl. omega.

        -- (* s1 and s2 are the same size *)
           Int_Word_N.
           apply same_size_compare; try Nomega; intros.
           - subst.
             rewrite andb_true_iff.
             rewrite !disjoint_Desc; try eassumption.
             ** setoid_rewrite H17. setoid_rewrite H6.
                intuition solve_eq_disjoint_specialize.
             ** subst sl sr. simpl. omega.
             ** subst sl sr. simpl. omega.
           - split; intro; try reflexivity.
             solve_f_eq_disjoint.
Qed.

Lemma disjoint_Sem s1 f1 s2 f2 :
  Sem s1 f1 -> Sem s2 f2 ->
  disjoint s1 s2 = true <-> (forall i, f1 i && f2 i = false).
Proof.
  intros HSem1 HSem2.
  destruct HSem1 as [f1 def_f1 | s1 r1 f1 HDesc1].
  * rewrite disjoint_eq; simpl.
    split; intro; try reflexivity.
    setoid_rewrite andb_false_iff; intuition.
  * destruct HSem2 as [f2 def_f2 | s2 r2 f2 HDesc2].
    + replace (disjoint s1 Nil) with true by (destruct s1; reflexivity).
      split; intro; try reflexivity.
      setoid_rewrite andb_false_iff; intuition.
    + eapply disjoint_Desc; eassumption.
Qed.


(** ** Verification of [split] *)

(* Punting on [split] for now while introducing fixed-width numbers.
   [splitGo] lemmas need a precondition that the tree contains
   only negative or only positive numbers.
 *)

(*
Definition splitGo : Key -> IntSet -> IntSet * IntSet.
Proof.
  let rhs := eval unfold split in split in
  match rhs with fun x s => match _ with Nil => match ?go _ _ with _ => _ end | _ => _ end => exact go end.
Defined.


Lemma splitGo_Sem :
  forall x s r f,
  Desc s r f ->
  forall (P : IntSet * IntSet -> Prop),
  (forall s1 f1 s2 f2,
    Sem s1 f1 -> Sem s2 f2 ->
    (forall i, f1 i = f i && (i <? x)) ->
    (forall i, f2 i = f i && (x <? i)) ->
    P (s1, s2)) ->
  P (splitGo x s) : Prop.
Proof.
  intros ???? HD.
  induction HD; intros X HX.
  * cbn -[bitmapOf prefixOf N.ones].
    fold WIDTH.
    destruct (N.ltb_spec x p); only 2: destruct (N.ltb_spec p (prefixOf x)).
    - (* s is Tip, x is below *)
      eapply HX.
      + constructor; intro; reflexivity.
      + eapply DescSem. constructor; try eassumption.
      + solve_f_eq.
        apply bitmapInRange_inside in Heqb.
        apply inRange_bounded in Heqb.
        rewrite N.ltb_lt in Heqb0.
        lia.
      + solve_f_eq.
        apply bitmapInRange_inside in Heqb.
        apply inRange_bounded in Heqb.
        rewrite N.ltb_ge in Heqb0.
        lia.
    - (* s is Tip, x is above *)
      eapply HX.
      + eapply DescSem. constructor; try eassumption.
      + constructor; intro; reflexivity.
      + solve_f_eq.
        apply bitmapInRange_inside in Heqb.
        rewrite <- prefixOf_eqb_spec in Heqb by assumption.
        rewrite N.eqb_eq in Heqb.
        rewrite N.ltb_ge in Heqb0. subst.
        apply prefixOf_mono in Heqb0. 
        lia.
      + solve_f_eq.
        apply bitmapInRange_inside in Heqb.
        rewrite <- prefixOf_eqb_spec in Heqb by assumption.
        rewrite N.eqb_eq in Heqb.
        rewrite N.ltb_lt in Heqb0. subst.
        assert (x <= i) by lia.
        apply prefixOf_mono in H. 
        lia.
    - (* s is Tip, x is part of it *)
      assert ((bitmapOf x - 1)%N = (N.ones (suffixOf x)%N)) as Htmp.
      { rewrite N.ones_equiv.
        rewrite N.pred_sub.
        unfold bitmapOf.
        rewrite bitmapOfSuffix_pow.
        reflexivity.
      }
      assert (prefixOf x = rPrefix r). {
        subst.
        unfold Prefix, Nat in *.
        apply prefixOf_mono in H3.
        rewrite prefixOf_rPrefix in H3 by assumption.
        lia.
      }
      rewrite Htmp; clear Htmp.
      eapply HX.
      + eapply Desc0_Sem.
        eapply tip_Desc0; try eassumption; try reflexivity.
        apply isBitMask0_land; try isBitMask.
        apply isBitMask0_ones.
        pose proof (suffixOf_lt_WIDTH x).
        lia.
      + eapply Desc0_Sem.
        eapply tip_Desc0; try eassumption; try reflexivity.
        apply isBitMask0_land; try isBitMask.
        apply isBitMask0_ldiff.
        apply isBitMask0_ones.
        Nomega.
      + intro i.
        rewrite H1.
        rewrite bitmapInRange_land.
        destruct (bitmapInRange r bm i) eqn:?; try reflexivity; simpl.
        apply bitmapInRange_inside in Heqb.
        rewrite bitmapInRange_ones by assumption.
        rewrite <- prefixOf_eqb_spec in Heqb by assumption.
        rewrite N.eqb_eq in *.
        unfold Prefix, Nat in *.
        pose proof (prefixOf_suffixOf i).
        pose proof (prefixOf_suffixOf x).
        apply eq_iff_eq_true.
        rewrite !N.ltb_lt.
        lia.
      + intro i.
        rewrite H1.
        rewrite bitmapInRange_land.
        destruct (bitmapInRange r bm i) eqn:?; try reflexivity; rewrite !andb_true_l.
        apply bitmapInRange_inside in Heqb.
        rewrite bitmapInRange_ldiff.
        rewrite bitmapInRange_ones by assumption.
        rewrite suffixOf_plus_bitmapOf.
        rewrite bitmapInRange_ones by assumption.
        rewrite <- prefixOf_eqb_spec in Heqb by assumption.
        rewrite N.eqb_eq in *.
        unfold Prefix, Nat in *.
        pose proof (prefixOf_suffixOf i).
        pose proof (prefixOf_suffixOf x).
        apply eq_iff_eq_true.
        rewrite andb_true_iff, negb_true_iff.
        rewrite !N.ltb_lt, N.ltb_ge.
        assert (suffixOf i < WIDTH) by apply suffixOf_lt_WIDTH.
        lia.
  * simpl. unfoldMethods.
    subst.
    rewrite match_nomatch.
    rewrite if_negb.
    apply nomatch_zero; try assumption; intros.
    + (* s is bin, x is outside *)
      apply inRange_false_bounded in H2.
      clear IHHD1 IHHD2.
      destruct (N.ltb_spec x (rPrefix r)).
      - (* s is bin, x is below *)
        eapply HX.
        ** constructor; intro; reflexivity.
        ** eapply DescSem. econstructor; try eassumption; reflexivity.
        ** intros i. simpl. rewrite H4.
           destruct (N.ltb_spec i x).
           ++ destruct (inRange i r) eqn:Hir; only 1: (apply inRange_bounded in Hir; lia).
              rewrite (Desc_outside HD1) by inRange_false.
              rewrite (Desc_outside HD2) by inRange_false.
              reflexivity.
           ++ rewrite andb_false_r. reflexivity.
        ** intros i. 
           destruct (N.ltb_spec x i).
           ++ rewrite andb_true_r. reflexivity.
           ++ destruct (inRange i r) eqn:Hir; only 1: (apply inRange_bounded in Hir; lia).
              rewrite H4.
              rewrite (Desc_outside HD1) by inRange_false.
              rewrite (Desc_outside HD2) by inRange_false.
              reflexivity.
      - (* s is bin, x is above *)
        eapply HX.
        ** eapply DescSem. econstructor; try eassumption; reflexivity.
        ** constructor; intro; reflexivity.
        ** intros i. simpl. rewrite H4.
           destruct (N.ltb_spec i x).
           ++ rewrite andb_true_r. reflexivity.
           ++ destruct (inRange i r) eqn:Hir; only 1: (apply inRange_bounded in Hir; lia).
              rewrite (Desc_outside HD1) by inRange_false.
              rewrite (Desc_outside HD2) by inRange_false.
              reflexivity.
        ** intros i. simpl. rewrite H4.
           destruct (N.ltb_spec x i).
           ++ destruct (inRange i r) eqn:Hir; only 1: (apply inRange_bounded in Hir; lia).
              rewrite (Desc_outside HD1) by inRange_false.
              rewrite (Desc_outside HD2) by inRange_false.
              reflexivity.
           ++ rewrite andb_false_r. reflexivity.
    + eapply IHHD1. clear IHHD1 IHHD2.
      intros sl fl sr fr Hsl Hsr Hfl Hfr.
      eapply HX; clear HX.
      - eassumption.
      - apply union_Sem; [ eassumption | eapply DescSem; eassumption].
      - intro i.
        rewrite H4, Hfl; clear H4 Hfl Hfr.
        destruct (f2 i) eqn:?, (N.ltb_spec i x);
          rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; simpl.

        apply (Desc_inside HD2) in Heqb.
        assert (inRange i (halfRange r true) = true) by inRange_true.
        apply inRange_bounded in H5.
        apply inRange_bounded in H2.
        rewrite rPrefix_halfRange_otherhalf in * by assumption.
        rewrite !rBits_halfRange in *.
        lia.
      - intro i.
        rewrite H4, Hfr; clear H4 Hfl Hfr.
        destruct (f2 i) eqn:?, (N.ltb_spec x i);
          rewrite ?andb_true_r, ?andb_false_r; try reflexivity; simpl.

        apply (Desc_inside HD2) in Heqb.
        assert (inRange i (halfRange r true) = true) by inRange_true.
        apply inRange_bounded in H5.
        apply inRange_bounded in H2.
        rewrite rPrefix_halfRange_otherhalf in * by assumption.
        rewrite !rBits_halfRange in *.
        lia.
    + eapply IHHD2. clear IHHD1 IHHD2.
      intros sl fl sr fr Hsl Hsr Hfl Hfr.
      eapply HX; clear HX.
      - apply union_Sem; [ eassumption | eapply DescSem; eassumption].
      - eassumption.
      - intro i.
        rewrite H4, Hfl; clear H4 Hfl Hfr.
        destruct (f1 i) eqn:?, (N.ltb_spec i x);
          rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; simpl.

        apply (Desc_inside HD1) in Heqb.
        assert (inRange i (halfRange r false) = true) by inRange_true.
        apply inRange_bounded in H5.
        apply inRange_bounded in H3.
        rewrite rPrefix_halfRange_otherhalf in * by assumption.
        rewrite !rBits_halfRange in *.
        lia.
      - intro i.
        rewrite H4, Hfr; clear H4 Hfl Hfr.
        destruct (f1 i) eqn:?, (N.ltb_spec x i);
          rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; simpl.
        apply (Desc_inside HD1) in Heqb.
        assert (inRange i (halfRange r false) = true) by inRange_true.
        apply inRange_bounded in H5.
        apply inRange_bounded in H3.
        rewrite rPrefix_halfRange_otherhalf in * by assumption.
        rewrite !rBits_halfRange in *.
        lia.
Qed.

Lemma split_Sem :
  forall x s f,
  Sem s f ->
  forall (P : IntSet * IntSet -> Prop),
  (forall s1 f1 s2 f2,
    Sem s1 f1 -> Sem s2 f2 ->
    (forall i, f1 i = f i && (i <? x)) ->
    (forall i, f2 i = f i && (x <? i)) ->
    P (s1, s2)) ->
  P (split x s) : Prop.
Proof.
  intros ??? HSem X HX.
  unfold split.
  fold splitGo.
  destruct HSem.
  * simpl. eapply HX; try constructor; try reflexivity; solve_f_eq.
  * destruct HD eqn:?; unfoldMethods.
    + eapply splitGo_Sem;
      only 1: eassumption;
      intros sl fl sr fr Hsl Hsr Hfl Hfr.
      eapply HX; eassumption.
    + simpl Z.to_N.
      destruct (N.ltb_spec msk 0).
      - (* This branch is invalid since we only allow positive members. Otherwise, we
           would have to do something here. *)
        exfalso.
        lia.
      - eapply splitGo_Sem;
        only 1: eassumption;
        intros sl fl sr fr Hsl Hsr Hfl Hfr.
        eapply HX; eassumption.
Qed.

Theorem split_WF (x : N) (s : IntSet) :
  WF s ->
  let '(l,r) := split x s in
  WF l /\ WF r.
Proof.
  intros [fs Sem_s].
  apply split_Sem with fs; [assumption|]; simpl; intros l fl r fr Sem_l Sem_r def_fl def_fr.
  split; [exists fl | exists fr]; assumption.
Qed.

Theorem split_WF' (x : N) (s : IntSet) :
  WF s ->
  WF (fst (split x s)) /\ WF (snd (split x s)).
Proof.
  generalize (split_WF x s); destruct (split x s); auto.
Qed.

Corollary split_1_WF (x : N) (s : IntSet) :
  WF s ->
  WF (fst (split x s)).
Proof. apply split_WF'. Qed.

Corollary split_2_WF (x : N) (s : IntSet) :
  WF s ->
  WF (snd (split x s)).
Proof. apply split_WF'. Qed.

(** ** Verification of [splitMember] *)

Definition splitMemberGo : Key -> IntSet -> IntSet * bool * IntSet.
Proof.
  let rhs := eval unfold splitMember in splitMember in
  match rhs with fun x t => match _ with | Nil => ?go x t | _ => _ end => exact go end.
Defined.

Lemma splitMemberGo_Sem :
  forall x s r f,
  Desc s r f ->
  forall (P : IntSet * bool * IntSet -> Prop),
  (forall s1 f1 s2 f2 b,
    Sem s1 f1 -> Sem s2 f2 ->
    f x = b ->
    (forall i, f1 i = f i && (i <? x)) ->
    (forall i, f2 i = f i && (x <? i)) ->
    P (s1, b, s2)) ->
  P (splitMemberGo x s) : Prop.
Proof.
  intros ???? HD.
  induction HD; intros X HX.
  * cbn -[bitmapOf prefixOf N.ones].
    fold WIDTH.
    destruct (N.ltb_spec x p); only 2: destruct (N.ltb_spec p (prefixOf x)).
    - (* s is Tip, x is below *)
      eapply HX.
      + constructor; intro; reflexivity.
      + eapply DescSem. constructor; try eassumption.
      + rewrite H1.
        apply bitmapInRange_outside.
        rewrite inRange_false_bounded_iff.
        lia.
      + solve_f_eq.
        apply bitmapInRange_inside in Heqb.
        apply inRange_bounded in Heqb.
        rewrite N.ltb_lt in Heqb0.
        lia.
      + solve_f_eq.
        apply bitmapInRange_inside in Heqb.
        apply inRange_bounded in Heqb.
        rewrite N.ltb_ge in Heqb0.
        lia.
    - (* s is Tip, x is above *)
      eapply HX.
      + eapply DescSem. constructor; try eassumption.
      + constructor; intro; reflexivity.
      + rewrite H1.
        apply bitmapInRange_outside.
        rewrite <- prefixOf_eqb_spec by assumption.
        rewrite N.eqb_neq.
        lia.
      + solve_f_eq.
        apply bitmapInRange_inside in Heqb.
        rewrite <- prefixOf_eqb_spec in Heqb by assumption.
        rewrite N.eqb_eq in Heqb.
        rewrite N.ltb_ge in Heqb0. subst.
        apply prefixOf_mono in Heqb0. 
        lia.
      + solve_f_eq.
        apply bitmapInRange_inside in Heqb.
        rewrite <- prefixOf_eqb_spec in Heqb by assumption.
        rewrite N.eqb_eq in Heqb.
        rewrite N.ltb_lt in Heqb0. subst.
        assert (x <= i) by lia.
        apply prefixOf_mono in H. 
        lia.
    - (* s is Tip, x is part of it *)
      assert ((bitmapOf x - 1)%N = (N.ones (suffixOf x)%N)) as Htmp.
      { rewrite N.ones_equiv.
        rewrite N.pred_sub.
        unfold bitmapOf.
        rewrite bitmapOfSuffix_pow.
        reflexivity.
      }
      rewrite Htmp.
      assert (prefixOf x = rPrefix r). {
        subst.
        unfold Prefix, Nat in *.
        apply prefixOf_mono in H3.
        rewrite prefixOf_rPrefix in H3 by assumption.
        lia.
      }
      assert (inRange x r = true). {
        rewrite <- prefixOf_eqb_spec by assumption.
        rewrite N.eqb_eq.
        assumption.
      }
      eapply HX.
      + eapply Desc0_Sem.
        eapply tip_Desc0; try eassumption; try reflexivity.
        apply isBitMask0_land; try isBitMask.
        apply isBitMask0_ones.
        pose proof (suffixOf_lt_WIDTH x).
        lia.
      + eapply Desc0_Sem.
        eapply tip_Desc0; try eassumption; try reflexivity.
        apply isBitMask0_land; try isBitMask.
        apply isBitMask0_ldiff.
        apply isBitMask0_ones.
        Nomega.
      + rewrite H1.
        unfold bitmapOf.
        rewrite bitmapOfSuffix_pow.
        rewrite N.land_comm.
        rewrite N_land_pow2_testbit.
        unfold bitmapInRange.
        replace (inRange x r).
        rewrite H0.
        reflexivity.
      + intro i.
        rewrite H1.
        rewrite bitmapInRange_land.
        destruct (bitmapInRange r bm i) eqn:?; try reflexivity; simpl.
        apply bitmapInRange_inside in Heqb.
        rewrite bitmapInRange_ones by assumption.
        rewrite <- prefixOf_eqb_spec in Heqb by assumption.
        rewrite N.eqb_eq in *.
        unfold Prefix, Int in *.
        pose proof (prefixOf_suffixOf i).
        pose proof (prefixOf_suffixOf x).
        apply eq_iff_eq_true.
        rewrite !N.ltb_lt.
        lia.
      + intro i.
        rewrite H1.
        rewrite bitmapInRange_land.
        destruct (bitmapInRange r bm i) eqn:?; try reflexivity; rewrite !andb_true_l.
        apply bitmapInRange_inside in Heqb.
        rewrite bitmapInRange_ldiff.
        rewrite bitmapInRange_ones by assumption.
        rewrite suffixOf_plus_bitmapOf.
        rewrite bitmapInRange_ones by assumption.
        rewrite <- prefixOf_eqb_spec in Heqb by assumption.
        rewrite N.eqb_eq in *.
        unfold Prefix, Int in *.
        pose proof (prefixOf_suffixOf i).
        pose proof (prefixOf_suffixOf x).
        apply eq_iff_eq_true.
        rewrite andb_true_iff, negb_true_iff.
        rewrite !N.ltb_lt, N.ltb_ge.
        assert (suffixOf i < WIDTH) by apply suffixOf_lt_WIDTH.
        lia.
  * simpl. unfoldMethods.
    subst.
    rewrite match_nomatch.
    rewrite if_negb.
    apply nomatch_zero; try assumption; intros.
    + (* s is bin, x is outside *)
      pose proof (inRange_false_bounded _ _ H2).
      clear IHHD1 IHHD2.
      destruct (N.ltb_spec x (rPrefix r)).
      - (* s is bin, x is below *)
        eapply HX; clear HX.
        ** constructor; intro; reflexivity.
        ** eapply DescSem. econstructor; try eassumption; reflexivity.
        ** rewrite H4.
           rewrite (Desc_outside HD1) by inRange_false.
           rewrite (Desc_outside HD2) by inRange_false.
           reflexivity.
        ** intros i. simpl. rewrite H4.
           destruct (N.ltb_spec i x).
           ++ destruct (inRange i r) eqn:Hir; only 1: (apply inRange_bounded in Hir; lia).
              rewrite (Desc_outside HD1) by inRange_false.
              rewrite (Desc_outside HD2) by inRange_false.
              reflexivity.
           ++ rewrite andb_false_r. reflexivity.
        ** intros i. 
           destruct (N.ltb_spec x i).
           ++ rewrite andb_true_r. reflexivity.
           ++ destruct (inRange i r) eqn:Hir; only 1: (apply inRange_bounded in Hir; lia).
              rewrite H4.
              rewrite (Desc_outside HD1) by inRange_false.
              rewrite (Desc_outside HD2) by inRange_false.
              reflexivity.
      - (* s is bin, x is above *)
        eapply HX.
        ** eapply DescSem. econstructor; try eassumption; reflexivity.
        ** constructor; intro; reflexivity.
        ** rewrite H4.
           rewrite (Desc_outside HD1) by inRange_false.
           rewrite (Desc_outside HD2) by inRange_false.
           reflexivity.
        ** intros i. simpl. rewrite H4.
           destruct (N.ltb_spec i x).
           ++ rewrite andb_true_r. reflexivity.
           ++ destruct (inRange i r) eqn:Hir; only 1: (apply inRange_bounded in Hir; lia).
              rewrite (Desc_outside HD1) by inRange_false.
              rewrite (Desc_outside HD2) by inRange_false.
              reflexivity.
        ** intros i. simpl. rewrite H4.
           destruct (N.ltb_spec x i).
           ++ destruct (inRange i r) eqn:Hir; only 1: (apply inRange_bounded in Hir; lia).
              rewrite (Desc_outside HD1) by inRange_false.
              rewrite (Desc_outside HD2) by inRange_false.
              reflexivity.
           ++ rewrite andb_false_r. reflexivity.
    + eapply IHHD1. clear IHHD1 IHHD2.
      intros sl fl sr fr b Hsl Hsr Hb Hfl Hfr.
      eapply HX; clear HX.
      - eassumption.
      - apply union_Sem; [ eassumption | eapply DescSem; eassumption].
      - rewrite H4. rewrite Hb.
        destruct b; try reflexivity; try simpl.
        apply (Desc_outside HD2).
        inRange_false.
      - intro i.
        rewrite H4, Hfl; clear H4 Hfl Hfr.
        destruct (f2 i) eqn:?, (N.ltb_spec i x);
          rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; simpl.

        apply (Desc_inside HD2) in Heqb0.
        assert (inRange i (halfRange r true) = true) by inRange_true.
        apply inRange_bounded in H5.
        apply inRange_bounded in H2.
        rewrite rPrefix_halfRange_otherhalf in * by assumption.
        rewrite !rBits_halfRange in *.
        lia.
      - intro i.
        rewrite H4, Hfr; clear H4 Hfl Hfr.
        destruct (f2 i) eqn:?, (N.ltb_spec x i);
          rewrite ?andb_true_r, ?andb_false_r; try reflexivity; simpl.

        apply (Desc_inside HD2) in Heqb0.
        assert (inRange i (halfRange r true) = true) by inRange_true.
        apply inRange_bounded in H5.
        apply inRange_bounded in H2.
        rewrite rPrefix_halfRange_otherhalf in * by assumption.
        rewrite !rBits_halfRange in *.
        lia.
    + eapply IHHD2. clear IHHD1 IHHD2.
      intros sl fl sr fr b Hsl Hsr Hb Hfl Hfr.
      eapply HX; clear HX.
      - apply union_Sem; [ eassumption | eapply DescSem; eassumption].
      - eassumption.
      - rewrite H4. rewrite Hb.
        destruct b; rewrite ?orb_false_r, ?orb_true_r; try reflexivity.
        apply (Desc_outside HD1).
        inRange_false.
      - intro i.
        rewrite H4, Hfl; clear H4 Hfl Hfr.
        destruct (f1 i) eqn:?, (N.ltb_spec i x);
          rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; simpl.

        apply (Desc_inside HD1) in Heqb0.
        assert (inRange i (halfRange r false) = true) by inRange_true.
        apply inRange_bounded in H5.
        apply inRange_bounded in H3.
        rewrite rPrefix_halfRange_otherhalf in * by assumption.
        rewrite !rBits_halfRange in *.
        lia.
      - intro i.
        rewrite H4, Hfr; clear H4 Hfl Hfr.
        destruct (f1 i) eqn:?, (N.ltb_spec x i);
          rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r; try reflexivity; simpl.
        apply (Desc_inside HD1) in Heqb0.
        assert (inRange i (halfRange r false) = true) by inRange_true.
        apply inRange_bounded in H5.
        apply inRange_bounded in H3.
        rewrite rPrefix_halfRange_otherhalf in * by assumption.
        rewrite !rBits_halfRange in *.
        lia.
Qed.

Lemma splitMember_Sem :
  forall x s f,
  Sem s f ->
  forall (P : IntSet * bool * IntSet -> Prop),
  (forall s1 f1 s2 f2 b,
    Sem s1 f1 -> Sem s2 f2 ->
    f x = b ->
    (forall i, f1 i = f i && (i <? x)) ->
    (forall i, f2 i = f i && (x <? i)) ->
    P (s1, b, s2)) ->
  P (splitMember x s) : Prop.
Proof.
  intros ??? HSem X HX.
  unfold splitMember.
  fold splitMemberGo.
  destruct HSem.
  * simpl. eapply HX; try constructor; try reflexivity; try solve_f_eq.
    apply H.
  * destruct HD eqn:?; unfoldMethods.
    + eapply splitMemberGo_Sem;
      only 1: eassumption;
      intros sl fl sr fr Hsl Hsr Hfl Hfr.
      eapply HX; eassumption.
    + simpl Z.to_N.
      destruct (N.ltb_spec msk 0).
      - (* This branch is invalid since we only allow positive members. Otherwise, we
           would have to do something here. *)
        lia.
      - eapply splitMemberGo_Sem;
        only 1: eassumption;
        intros sl fl sr fr Hsl Hsr Hfl Hfr.
        eapply HX; eassumption.
Qed.

Theorem splitMember_WF (x : N) (s : IntSet) :
  WF s ->
  let '(l,_,r) := splitMember x s in
  WF l /\ WF r.
Proof.
  intros [fs Sem_s].
  apply splitMember_Sem with fs; [assumption|]; simpl; intros l fl r fr b Sem_l Sem_r def_b def_fl def_fr.
  split; [exists fl | exists fr]; assumption.
Qed.

Theorem splitMember_WF' (x : N) (s : IntSet) :
  WF s ->
  WF (fst (fst (splitMember x s))) /\ WF (snd (splitMember x s)).
Proof.
  generalize (splitMember_WF x s); destruct (splitMember x s) as [[? ?] ?]; auto.
Qed.

Corollary splitMember_1_WF (x : N) (s : IntSet) :
  WF s ->
  WF (fst (fst (splitMember x s))).
Proof. apply splitMember_WF'. Qed.

Corollary splitMember_2_WF (x : N) (s : IntSet) :
  WF s ->
  WF (snd (splitMember x s)).
Proof. apply splitMember_WF'. Qed.
*)


(** *** Verification of [foldr] *)

(* We can extract the argument to [wfFix2] from the definition of [foldrBits]. *)
Definition foldrBits_go {a} (p : Int) (f : Int -> a -> a) (x : a) (bm : Nat)
  : (forall (bm : Nat), a -> (forall x', {_ : a | (wordTonat x' < wordTonat bm)%nat} -> a) -> a).
Proof.
  let rhs := eval unfold foldrBits in (foldrBits p f x bm) in
  match rhs with context[ GHC.Wf.wfFix2 _ _ _ ?f ] => exact f end.
Defined.

Lemma foldrBits_eq:
  forall {a} p (f : Int -> a -> a) x bm,
  foldrBits p f x bm = @foldrBits_go a p f x bm (revNat bm) x (fun x y => foldrBits p f (proj1_sig y) (revNat x)).
Proof.
  intros.
  unfold foldrBits.
  rewrite GHC.Wf.wfFix2_eq at 1.
  unfold foldrBits_go.
  destruct (Sumbool.sumbool_of_bool _); try reflexivity.
  f_equal.
  admit.
Admitted.
(*  
  rewrite revNat_revNat.
  reflexivity.
Qed.
*)


Lemma foldrBits_0:
  forall {a} p (f : Int -> a -> a) x,
  foldrBits p f x (NToWord 0%N) = x.
Proof.
  intros.
  (* This hopefully works once NToWord is implemented. *)
Fail apply foldrBits_eq.
Admitted.

Lemma foldrBits_bm:
  forall {a} p (f : Int -> a -> a) bm x,
  isBitMask (wordToN bm) ->
  foldrBits p f x bm =
    foldrBits p f (f (ZToInt (intToZ p + Z.of_N (N.log2 (wordToN bm)))%Z) x) 
        (NToWord (N.clearbit (wordToN bm) (N.log2 (wordToN bm)))).
Proof.
  intros.
  rewrite foldrBits_eq at 1 by isBitMask. unfold foldrBits_go, proj1_sig.
  unfoldMethods. Int_Word_N.
  replace (wordToN (revNat bm) =? Z.to_N 0)%N with false
    by (symmetry; apply N.eqb_neq; rewrite revNat_eq_0 by isBitMask; unfold isBitMask in *; Nomega).
  (* eek *)
  replace (Sumbool.sumbool_of_bool false) with (@right (false = true) (false = false) (@eq_refl bool false))
    by reflexivity.
  f_equal.
  * (* Needs a theory of indexOfTheOnlyBit *)
    admit.
    (*
    unfold lowestBitMask.
    unfold indexOfTheOnlyBit.
    rewrite N.log2_pow2 by Nomega.
    rewrite N_log2_ctz by isBitMask.
    unfold WIDTH.
    rewrite !N.add_sub_assoc. reflexivity.
    unfold WIDTH; Nomega.
    assert (N_ctz (revNatSafe bm) < WIDTH)%N by isBitMask.
    unfold WIDTH in *; lia.
    simpl. lia.
    *)
  * admit.
    (*
    rewrite lxor_lowestBitMask by isBitMask.
    rewrite clearbit_revNat by isBitMask.
    rewrite revNat_revNat by isBitMask.
    rewrite <- N_log2_ctz by isBitMask.
    reflexivity.
    *)
Admitted.

Definition foldr_go {a} k :=
   (fix go (arg_0__ : a) (arg_1__ : IntSet) {struct arg_1__} : a :=
     match arg_1__ with
     | Bin _ _ l r0 => go (go arg_0__ r0) l
     | Tip kx bm =>
         foldrBits kx k
           arg_0__ bm
     | Nil => arg_0__
     end).


(** *** Verification of [toList] *)

Lemma In_cons_iff:
  forall {a} (y x : a) xs, In y (x :: xs) <-> x = y \/ In y xs.
Proof. intros. reflexivity. Qed.

Lemma In_foldrBits_cons:
  forall i r bm l,
  rBits r = N.log2 WIDTH ->
  In i (foldrBits (NToInt (rPrefix r)) cons l bm) <-> (bitmapInRange r bm (intToN i) = true \/ In i l).
Proof.
  intros.

(* Needs a variant of [bits_ind] that works on [Word] *)
Admitted.
(*
  revert l.
  apply bits_ind with (bm := bm).
  * assumption.
  * intros.
    rewrite foldrBits_0.
    rewrite bitmapInRange_0. intuition congruence.
  * clear bm H. intros bm Hbm IH l.
    rewrite foldrBits_bm by isBitMask.
    rewrite -> IH.
    rewrite split_highestBitMask with (bm := bm) at 4 by assumption.
    rewrite bitmapInRange_lor.
    rewrite orb_true_iff.
    rewrite In_cons_iff.
    rewrite bitmapInRange_pow by (replace (rBits r); isBitMask).
    rewrite N.eqb_eq.
    solve [tauto].
Qed.
*)

Definition toList_go := foldr_go cons.

Lemma toList_go_In:
  forall s f, Sem s f ->
  forall l i, (f (intToN i) = true \/ In i l) <-> In i (toList_go l s).
Proof.
  intros ?? HS.
  destruct HS.
  * intuition. rewrite H in H1. congruence.
  * induction HD; intros; simpl; subst.
    + rewrite In_foldrBits_cons by isBitMask.
      rewrite H1; reflexivity.
    + unfold op_zl__, Ord_Integer___, op_zl____.
      rewrite <- IHHD1.
      rewrite <- IHHD2.
      rewrite H4.
      rewrite orb_true_iff.
      intuition.
Qed.

Lemma toList_go_In_nil:
  forall s f, Sem s f ->
  forall i, f (intToN i) = true <-> In i (toList_go nil s).
Proof.
  intros.
  rewrite <- toList_go_In by eassumption.
  intuition.
Qed.

Lemma toList_In:
  forall s f, Sem s f ->
  forall i, f (intToN i) = true <-> In i (toList s).
Proof.
  intros.
  pose proof (toList_go_In_nil s f H i) as Hgo.
  destruct H.
  * apply Hgo.
  * destruct HD.
    + apply Hgo.
    + subst. simpl.
      unfold op_zl__, Ord__Int, op_zl____.
      destruct (Z.ltb_spec (intToZ (NToInt (rMask r))) (intToZ (ZToInt 0))).
      - rewrite <- toList_go_In by (eapply DescSem; eassumption).
        rewrite <- toList_go_In by (eapply DescSem; eassumption).
        rewrite H4.
        rewrite orb_true_iff.
        intuition.
      - rewrite <- toList_go_In by (eapply DescSem; eassumption).
        rewrite <- toList_go_In by (eapply DescSem; eassumption).
        rewrite H4.
        rewrite orb_true_iff.
        intuition.
Qed.

Lemma toList_Bits_append:
  forall p l bm,
  foldrBits p cons l bm = foldrBits p cons nil bm  ++ l.
Proof.
  intros.
  revert l.
  (* Needs [bit_ind] for [Word] *)
Admitted.
(*
  apply bits_ind with (bm := bm).
  - isBitMask.
  - intros xs.
    rewrite !foldrBits_0.
    reflexivity.
  - clear bm H. intros bm Hbm IH xs.
    rewrite !foldrBits_bm with (bm0 := bm) by isBitMask.
    rewrite IH.
    rewrite IH with (l := _ :: nil).
    rewrite <- app_assoc.
    reflexivity.
Qed.
*)

Lemma toList_go_append:
  forall l s r f,
  Desc s r f ->
  toList_go l s = toList_go nil s ++ l.
Proof.
  intros. revert l.
  induction H; intro l.
  * simpl.
    apply toList_Bits_append; isBitMask.
  * simpl.
    rewrite IHDesc2.
    rewrite IHDesc1.
    rewrite IHDesc2 at 2.
    rewrite IHDesc1 with (l := toList_go nil s2 ++ nil).
    rewrite app_nil_r.
    rewrite app_assoc.
    reflexivity.
Qed.

Theorem toAscList_exact (s1 s2 : IntSet) :
  WF s1 ->
  WF s2 ->
  s1 = s2 <-> toAscList s1 = toAscList s2.
Admitted.
(*
Proof.
  intros [f1 Sem1] [f2 Sem2]; split; [now intros; subst | intros EQ].
  eapply Sem_unique; try eassumption.
  generalize (toList_In _ _ Sem1), (toList_In _ _ Sem2).
  unfold toList; rewrite EQ; intros def_f1 def_f2.
  intros i; generalize (def_f1 i), (def_f2 i).
  destruct (f1 i), (f2 i); intuition.
Qed.
*)


Theorem toList_exact (s1 s2 : IntSet) :
  WF s1 ->
  WF s2 ->
  s1 = s2 <-> toList s1 = toList s2.
Proof. apply toAscList_exact. Qed.

Theorem toList_toAscList : toList = toAscList.
Proof. reflexivity. Qed.

Theorem toAscList_toList : toAscList = toList.
Proof. reflexivity. Qed.

(** *** Sortedness of [toList] *)


Lemma to_List_Bits_below:
  forall p bm,
  forall y, In y (foldrBits p cons nil bm) ->
  (intToZ y <= intToZ p + Z.of_N (N.log2 (wordToN bm)))%Z.
Proof.
  intros p bm H.
Admitted.
(*
  apply bits_ind with (bm := bm).
  * assumption.
  * intros.
    rewrite foldrBits_0 in H0.
    inversion H0.
  * intros.
    rewrite foldrBits_bm in H2 by isBitMask.
    rewrite toList_Bits_append in H2 by isBitMask.
    apply in_app_iff in H2.
    destruct H2.
    + apply H1 in H2.
      transitivity (p + N.log2 (N.clearbit bm0 (N.log2 bm0))); try assumption.
      apply N.add_le_mono; try reflexivity.
      apply N.log2_le_mono.
      apply ldiff_le.
    + destruct H2 as [?|[]]. subst.
      reflexivity.
Qed.
*)

Lemma to_List_Bits_sorted:
  forall p bm,
  StronglySorted (fun x y => Z.lt (intToZ x) (intToZ y)) (foldrBits p cons nil bm).
Proof.
  intros.
Admitted.
(*  
  apply bits_ind with (bm := bm).
  * assumption.
  * rewrite foldrBits_0.
    apply SSorted_nil.
  * clear bm H.
    intros.
    rewrite foldrBits_bm by isBitMask.
    rewrite toList_Bits_append by isBitMask.
    apply sorted_append with (x := p + N.log2 bm).
    + assumption.
    + apply SSorted_cons; constructor.
    + intros.
      eapply N.le_lt_trans.
      eapply to_List_Bits_below; try eassumption; try isBitMask.
      enough (N.log2 (N.clearbit bm (N.log2 bm)) < N.log2 bm)%N by Nomega.
      assert (N.clearbit bm (N.log2 bm) <> 0)%N. {
        intro.
        rewrite H2 in H1.
        rewrite foldrBits_0 in H1.
        inversion H1.
      }
      apply N.log2_lt_pow2; try Nomega.
      rewrite clearbit_log2_mod by (unfold isBitMask in H; Nomega).
      apply N.mod_lt.
      apply N.pow_nonzero.
      Nomega.
    + intros y Hy. destruct Hy as [?|[]]. subst. reflexivity.
Qed.
*)

Lemma to_List_go_Desc_sorted:
  forall s r f, Desc s r f -> StronglySorted (fun x y => Z.lt (intToZ x) (intToZ y)) (toList_go nil s).
Proof.
  intros ??? HD.
  induction HD.
  * simpl. apply to_List_Bits_sorted.
  * simpl. subst.
    unfoldMethods.
    erewrite toList_go_append by (apply HD1).
    apply sorted_append' with (x := NToInt (rPrefix (halfRange r true))).
    + eapply IHHD1; eassumption.
    + eapply IHHD2; eassumption.
    + intros i Hi.
      rewrite rPrefix_halfRange_otherhalf by assumption.
      rewrite <- toList_go_In_nil in Hi by (eapply DescSem; eassumption).
      apply (Desc_inside HD1) in Hi.
      eapply inRange_isSubrange_true in Hi; try eassumption.
      admit.
      (*
      apply inRange_bounded.
      assumption.
      *)
    + intros i Hi.
      rewrite <- toList_go_In_nil in Hi by (eapply DescSem; eassumption).
      apply (Desc_inside HD2) in Hi.
      eapply inRange_isSubrange_true in Hi; try eassumption.
      admit.
      (*
      apply inRange_bounded.
      assumption.
      *)
Admitted.

Lemma to_List_Desc_sorted:
  forall s r f, Desc s r f -> StronglySorted (fun x y => Z.lt (intToZ x) (intToZ y)) (toList s).
Proof.
  intros ??? HD.
  destruct HD.
  * simpl. apply to_List_Bits_sorted.
  * simpl. subst.
    unfoldMethods.
    destruct (Z.ltb_spec (intToZ (NToInt (rMask r))) (intToZ (ZToInt 0))).
    - (* This branch used to be inaccessible. Now there is stuff to do. *)
      admit.

    - fold (foldr_go (@cons Key)).
      erewrite toList_go_append by (apply HD1).
      change (StronglySorted (fun x y : Int => (intToZ x < intToZ y)%Z) (toList_go nil s1 ++ toList_go nil s2)).
      apply sorted_append' with (x := NToInt (rPrefix (halfRange r true))).
      + eapply to_List_go_Desc_sorted; eassumption.
      + eapply to_List_go_Desc_sorted; eassumption.
      + intros i Hi.
        rewrite rPrefix_halfRange_otherhalf by assumption.
        rewrite <- toList_go_In_nil in Hi by (eapply DescSem; eassumption).
        apply (Desc_inside HD1) in Hi.
        eapply inRange_isSubrange_true in Hi; try eassumption.
        admit.
        (*
        apply inRange_bounded.
        assumption.
        *)
      + intros i Hi.
        rewrite <- toList_go_In_nil in Hi by (eapply DescSem; eassumption).
        apply (Desc_inside HD2) in Hi.
        eapply inRange_isSubrange_true in Hi; try eassumption.
        admit.
        (*
        apply inRange_bounded.
        assumption.
        *)
Admitted.

Lemma to_List_sorted:
  forall s, WF s -> StronglySorted (fun x y => Z.lt (intToZ x) (intToZ y)) (toList s).
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * apply SSorted_nil.
  * eapply to_List_Desc_sorted; eassumption.
Qed.

(** ** Verification of [toAscList] *)

Lemma toAscList_spec: @toAscList = @toList. Proof. reflexivity. Qed.

(** ** Verification of [elems] *)

Lemma elems_spec: @elems = @toList. Proof. reflexivity. Qed.


(** *** Verification of [foldl] *)

Definition foldl_go {a} k :=
  fix go (arg_0__ : a) (arg_1__ : IntSet) {struct arg_1__} : a :=
   match arg_1__ with
   | Bin _ _ l r0 => go (go arg_0__ l) r0
   | Tip kx bm => foldlBits kx k arg_0__ bm
   | Nil => arg_0__
   end.

Definition foldlBits_go {a} (p : Int) (f : a -> Int -> a) (x : a) (bm : Nat)
  : ((forall x', {_ : a | (wordTonat x' < wordTonat bm)%nat} -> a) -> a).
Proof.
  let rhs := eval unfold foldlBits in (foldlBits p f x bm) in
  match rhs with context[ GHC.Wf.wfFix2 _ _ _ ?f ] => exact (f bm x) end.
Defined.

Lemma foldlBits_eq:
  forall {a} p (f : a -> Int -> a) x bm,
  foldlBits p f x bm = @foldlBits_go a p f x bm (fun x y => foldlBits p f (proj1_sig y) x).
Admitted.
(* This should work once the termiation proof of foldlBits does not use an axiom. *) 
(*
Proof.
  intros.
  apply GHC.Wf.wfFix2_eq.
Qed. *)


Lemma foldlBits_0:
  forall {a} p (f : a -> Int -> a) x,
  foldlBits p f x (NToWord 0) = x.
Proof.
  intros.
  Fail apply foldlBits_eq.
  (* might work once no axioms are around *)
Admitted.

Lemma foldlBits_bm:
  forall {a} p (f : a -> Int -> a) bm x,
  isBitMask (wordToN bm) ->
  foldlBits p f x bm =
    foldlBits p f 
       (f x (ZToInt (intToZ p + Z.of_N (N_ctz (wordToN bm)))))
       (NToWord (N.clearbit (wordToN bm) (N_ctz (wordToN bm)))).
Proof.
  intros.
  rewrite foldlBits_eq at 1. unfold foldlBits_go, proj1_sig.
  unfoldMethods. Int_Word_N.
  replace (wordToN bm =? Z.to_N 0)%N with false
    by (symmetry; apply N.eqb_neq; unfold isBitMask in *; zify; rewrite Z2N.id; omega).
  (* eek *)
  replace (Sumbool.sumbool_of_bool false) with (@right (false = true) (false = false) (@eq_refl bool false))
    by reflexivity.
  f_equal.
  * admit.
    (* See above
    unfold lowestBitMask.
    unfold indexOfTheOnlyBit.
    rewrite N.log2_pow2 by Nomega.
    reflexivity.
    *)
  * admit.
    (*
    rewrite lxor_lowestBitMask by assumption.
    reflexivity.
    *)
Admitted.

Lemma foldl'Bits_foldlBits : @foldl'Bits = @foldlBits.
Admitted. (* Should work once we have termination proofs *)
(*
Proof.
  reflexivity.
Qed.
*)

Lemma foldlBits_high_bm_aux:
  forall {a} p (f : a -> Int -> a) bm,
  (wordToN bm <> 0)%N ->
  (forall x, foldlBits p f x bm =
    f (foldlBits p f x (NToWord (N.clearbit (wordToN bm) (N.log2 (wordToN  bm)))))
                       (ZToInt (intToZ p + Z.of_N (N.log2 (wordToN bm))))%Z).
Proof.
  intros.
  pose proof H.
  revert H0 x.
  (* Need induction scheme *)
Admitted.
(*
  apply bits_ind_up with (bm := bm).
  - isBitMask.
  - clear bm H. intros Hbm Hpos x.
    Nomega.
  - clear bm H. intros bm Hbm IH _ Hpos x.
    destruct (N.eqb_spec (N.clearbit bm (N_ctz bm)) (0%N)).
    * clear IH.
    
      rewrite foldlBits_bm by isBitMask.
      rewrite e.
      rewrite foldlBits_0.

      apply clearbit_ctz_0 in e; try isBitMask.
      rewrite e.
      rewrite N.log2_pow2 by nonneg.
      rewrite clearbit_pow2_0.
      rewrite foldlBits_0.

      replace bm with (2^N.log2 bm)%N
        by (rewrite e; rewrite N.log2_pow2 by nonneg; reflexivity).
      rewrite N_ctz_pow2.
      reflexivity.
    * assert (hasTwoBits bm) by (split; auto; isBitMask).
      rewrite foldlBits_bm by isBitMask.
      rewrite IH by (isBitMask || assumption).
      rewrite log2_clearbit_ctz by assumption.
      f_equal.
      etransitivity; [|rewrite foldlBits_bm by isBitMask;  reflexivity].
      rewrite ctz_clearbit_log2 by assumption.
      rewrite clearbit_clearbit_comm at 1.
      reflexivity.
Qed.
*)

Lemma foldlBits_high_bm:
  forall {a} p (f : a -> Int -> a) bm x,
  isBitMask (wordToN bm) ->
  foldlBits p f x bm =
  f (foldlBits p f x (NToWord (N.clearbit (wordToN bm) (N.log2 (wordToN  bm)))))
                     (ZToInt (intToZ p + Z.of_N (N.log2 (wordToN bm))))%Z.
Proof.
  intros.
  unfold isBitMask in H.
  apply foldlBits_high_bm_aux.
  Nomega.
Qed.

Lemma foldlBits_foldrBits:
  forall {a b}  k (x : a) p bm (k' : a -> b),
    k' (foldlBits p k x bm) = foldrBits p (fun x g a => g (k a x)) k' bm x.
Proof.
  intros.

  revert k'.
Admitted.
(*
  apply bits_ind with (bm := bm).
  - assumption.
  - intros.
    rewrite foldrBits_0.
    rewrite foldlBits_0.
    reflexivity.
  - clear bm H. intros bm Hbm IH k'.
    rewrite !@foldrBits_bm with (bm := bm) by isBitMask.
    rewrite !@foldlBits_high_bm with (bm := bm) by isBitMask.
    rewrite <- IH.
    reflexivity.
Qed.
*)

Lemma foldl_go_foldr_go:
  forall {a b}  k (x : a) s r f (k' : a -> b), Desc s r f ->
    k' (foldl_go k x s) = foldr_go (fun x g a => g (k a x)) k' s x.
Proof.
  intros.
  revert x k'; induction H; intros.
  * apply foldlBits_foldrBits; isBitMask.
  * simpl.
    rewrite IHDesc2 with (k' := k').
    rewrite IHDesc1 with (k' := foldr_go _ k' s2).
    reflexivity.
Qed.

Lemma foldl_foldr:
  forall {a} k (x : a) s, WF s ->
    foldl k x s = foldr (fun x g a => g (k a x)) id s x.
Proof.
 intros.
 destruct H as [f HSem].
 destruct HSem.
 * reflexivity.
 * revert x; destruct HD; intros.
   + simpl.
     apply foldlBits_foldrBits with (k' :=  fun x => x); isBitMask.
   + simpl.
     fold (foldl_go k).
     fold (foldr_go (fun (x0 : Key) (g : a -> a) (a0 : a) => g (k a0 x0))).
     unfoldMethods. Int_Word_N.
     destruct (Z.ltb_spec (intToZ msk)  0).
     - erewrite foldl_go_foldr_go with (k' := fun x => x) by eassumption.
       eapply foldl_go_foldr_go; eassumption.
     - erewrite foldl_go_foldr_go with (k' := fun x => x) by eassumption.
       eapply foldl_go_foldr_go; eassumption.
Qed.

Lemma fold_right_foldrBits_go:
  forall {a} f (x : a) p bm xs,
  fold_right f x (foldrBits p cons xs bm) = foldrBits p f (fold_right f x xs) bm.
Proof.
  intros.
  revert xs.
Admitted.
(*
  apply bits_ind with (bm := bm).
  - assumption.
  - intros xs.
    rewrite !foldrBits_0.
    reflexivity.
  - clear bm H. intros bm Hbm IH xs.
    rewrite !@foldrBits_bm with (bm := bm) by isBitMask.
    rewrite IH.
    reflexivity.
Qed.
*)

Lemma fold_right_toList_go:
  forall {a} f (x : a) s r f' xs, Desc s r f' -> 
  fold_right f x (foldr_go cons xs s) = foldr_go f (fold_right f x xs) s.
Proof.
  intros. 
  revert xs; induction H; intros.
  * apply fold_right_foldrBits_go; isBitMask.
  * simpl.
    rewrite IHDesc1.
    rewrite IHDesc2.
    reflexivity.
Qed.

Lemma fold_right_toList:
  forall {a} f (x : a) s xs, WF s-> 
  fold_right f x (foldr cons xs s) = foldr f (fold_right f x xs) s.
Proof.
  intros.
  destruct H as [f' HSem].
  destruct HSem.
  * reflexivity.
  * destruct HD.
    + apply fold_right_foldrBits_go; isBitMask.
    + simpl.
      unfoldMethods. Int_Word_N.
      fold (foldr_go (@cons Key)). 
      fold (foldr_go f).
      destruct (Z.ltb_spec (intToZ msk) 0).
      - do 2 erewrite fold_right_toList_go by eassumption. reflexivity.
      - do 2 erewrite fold_right_toList_go by eassumption. reflexivity.
Qed.

Lemma List_foldl_foldr:
  forall {a b} f (x : b) (xs : list a),
    fold_left f xs x = List.fold_right (fun x g a => g (f a x)) id xs x.
Proof.
  intros. revert x.
  induction xs; intro.
  * reflexivity.
  * simpl. rewrite IHxs. reflexivity.
Qed.

Lemma foldl_spec:
  forall {a} f (x : a) s, WF s ->
    foldl f x s = fold_left f (toList s) x.
Proof.
  intros.
  unfold toList, toAscList.
  rewrite foldl_foldr by assumption.
  rewrite List_foldl_foldr.
  rewrite fold_right_toList by assumption.
  reflexivity.
Qed.

(** *** Verification of [size] *)

(** Because [size] returns an [Int], it actually overflows
for large [IntSet], but the equations still hold, as overflow
is modulo. *)

Definition sizeGo : Int -> IntSet -> Int.
Proof.
  let size_rhs := eval unfold size in size in
  match size_rhs with ?f #0 => exact f end.
Defined.

Lemma popCount_N_length_toList_go:
  forall bm p l,
  (Z.of_N (N_popcount (wordToN bm)) + Z.of_nat (length l) = Z.of_nat (length (foldrBits p cons l bm)))%Z.
Proof.
  intros.
  revert l.
Admitted.  
(*
  apply bits_ind with (bm := bm).
  - isBitMask.
  - intros.
    rewrite foldrBits_0.
    reflexivity.
  - clear bm H. intros bm Hbm IH l.
    rewrite !@foldrBits_bm with (bm := bm) by isBitMask.
    rewrite popCount_N_bm by (unfold isBitMask in Hbm; Nomega).
    rewrite <- IH; clear IH.
    simpl.
    Nomega.
Qed.
*)

Lemma sizeGo_spec':
  forall x s r f, Desc s r f ->
  sizeGo x s = ZToInt (intToZ x + Z.of_nat (length (toList_go nil s)))%Z.
Proof.
  intros.
  intros.
  revert x; induction H; intro x.
  + simpl.
    unfold bitcount.
    rewrite <- popCount_N_length_toList_go.
    simpl.
    Int_Word_N.
    rewrite Z.add_0_r.
    rewrite Z.add_0_l.
    reflexivity.
  + simpl.
    erewrite toList_go_append with (s := s1) by eassumption.
    erewrite toList_go_append with (s := s2) by eassumption.
    rewrite IHDesc1.
    rewrite IHDesc2.
    rewrite !app_length.
    Int_Word_N.
    simpl length.
    unfold Nat in *.
    rewrite Nat.add_0_r.
    rewrite Nat2Z.inj_add.
    rewrite Z.add_assoc.
    reflexivity.
Qed.

Lemma sizeGo_spec:
  forall x s, WF s ->
  sizeGo x s = ZToInt (intToZ x + Z.of_nat (length (toList s)))%Z.
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * simpl.
    admit.
    (*    rewrite N.add_0_r. reflexivity. *)
  * destruct HD.
    + simpl.
      unfold bitcount.
      rewrite <- popCount_N_length_toList_go.
      simpl. Int_Word_N.
      rewrite Z.add_0_r.
      rewrite Z.add_0_l.
      reflexivity.
    + subst. simpl.
      unfoldMethods. Int_Word_N.
      destruct (Z.ltb_spec (intToZ (NToInt (rMask r))) 0).
      -- erewrite toList_go_append with (s := s1) by eassumption.
         erewrite toList_go_append with (s := s2) by eassumption.
         erewrite sizeGo_spec' by eassumption.
         erewrite sizeGo_spec' by eassumption.
         rewrite !app_length.
         simpl length.
         Int_Word_N.
         rewrite Nat2Z.inj_add.
         f_equal. lia.
      -- erewrite toList_go_append with (s := s1) by eassumption.
         erewrite toList_go_append with (s := s2) by eassumption.
         erewrite sizeGo_spec' by eassumption.
         erewrite sizeGo_spec' by eassumption.
         rewrite !app_length.
         simpl length.
         rewrite Nat.add_0_r.
         Int_Word_N.
         rewrite Nat2Z.inj_add.
         f_equal. lia.
Admitted.

Lemma size_spec:
  forall s, WF s ->
  size s = ZToInt (Z.of_nat (length (toList s))).
Proof.
  intros.
  unfold size.
  rewrite sizeGo_spec by assumption.
  simpl. Int_Word_N.  
  reflexivity.
Qed.

(** *** Verification of [toDescList] *)

(** The easiest complete specification simply relates this to [toList] *)

Lemma toDescList_spec:
  forall s, WF s -> toDescList s = rev (toList s).
Proof.
  intros.
  unfold toDescList.
  rewrite foldl_spec by assumption.
  rewrite <- fold_left_rev_right.
  generalize (rev (toList s)).
  intro xs.
  induction xs.
  * reflexivity.
  * simpl. rewrite IHxs. reflexivity.
Qed.

(** *** Verification of [fromList] *)

Lemma fromList_Sem:
  forall l,
  exists f,
  Sem (fromList l) f /\ (forall i, f (intToN i) = true <-> In i l).
Proof.
  intros l.
  unfold fromList.
  rewrite hs_coq_foldl_list.
  (* Rewrite to use fold_right instead of fold_left *)
  enough (forall l,
    exists f : N -> bool,
    Sem (fold_right (fun (x : Key) (t : IntSet) => insert x t) empty l) f /\
    (forall i, f (intToN i) = true <-> In i l)).
  {  specialize (H (rev l)).
     rewrite fold_left_rev_right in H.
     setoid_rewrite <- in_rev in H.
     assumption.
  }
  (* Now induction *)
  clear l.
  intros l.
  induction l; intros.
  * exists (fun _ => false).
    split.
    + constructor. auto.
    + intuition. congruence.
  * destruct IHl as [?[??]].
    eexists.
    split.
    + simpl.
      eapply insert_Sem; try eassumption.
      intro; reflexivity.
    + intro i. specialize (H0 i).
      simpl.
      destruct (N.eqb_spec (intToN i) (intToN a)); intuition Int_Word_N; try congruence.
Qed.

Lemma fromList_WF:
  forall l, WF (fromList l).
Proof.
  intros.
  destruct (fromList_Sem l) as [?[??]].
  econstructor.
  eassumption.
Qed.

(** *** Verification of [filter] *)

Definition filterBits p o bm :=
  (foldlBits (ZToInt 0)
     (fun (bm0 : BitMap) (bi : Key) =>
      if p (ZToInt (intToZ o + intToZ bi)%Z) : bool
      then NToWord (N.lor (wordToN bm0) (wordToN (bitmapOfSuffix bi)))
      else bm0)
      (NToWord 0%N)
      bm).

Lemma testbit_filterBits:
  forall p o bm i,
  N.testbit (wordToN (filterBits p o bm)) i =
  (N.testbit (wordToN bm) i && p (ZToInt ((intToZ o + Z.of_N i)%Z))).
Proof.
  intros.

  unfold filterBits.
  transitivity ((N.testbit (wordToN bm) i && p (ZToInt ((intToZ o + Z.of_N i)%Z))) || N.testbit (wordToN (NToWord 0%N)) i);
    try (rewrite N.bits_0; rewrite orb_false_r; reflexivity).
  enough (forall a,
  N.testbit
  (wordToN
     (foldlBits (ZToInt 0)
        (fun (bm0 : BitMap) (bi : Key) =>
         if p (ZToInt (intToZ o + intToZ bi))
         then NToWord (N.lor (wordToN bm0) (wordToN (bitmapOfSuffix bi)))
         else bm0) a bm)) i =
N.testbit (wordToN bm) i && p (ZToInt (intToZ o + Z.of_N i)) || N.testbit (wordToN a) i) by intuition.
Admitted.
(*
  apply bits_ind with (bm := bm).
  * assumption.
  * intros a.
    rewrite foldlBits_0.
    rewrite N.bits_0.
    rewrite andb_false_l.
    rewrite orb_false_l.
    reflexivity.
  * intros.
    unfold filterBits.
    rewrite foldlBits_high_bm by isBitMask.
    lazymatch goal with [|- N.testbit (if ?x then N.lor ?z ?y else ?z) ?i = _]  =>
      transitivity (N.testbit (N.lor z (if x then y else 0%N)) i);
        [destruct x; try rewrite N.lor_0_r; reflexivity|]
    end.
    rewrite N.lor_spec.
    rewrite H1; clear H1.
    rewrite N.clearbit_eqb.

    lazymatch goal with [|- context [N.testbit (if ?x then ?y else 0%N) ?i] ] =>
      replace (N.testbit (if x then y else 0%N) i)
         with (x && N.testbit y i)
           by (destruct x; try rewrite N.bits_0; repeat split_bool; reflexivity)
    end.
    rewrite N.add_0_l.
    rewrite bitmapOfSuffix_pow.
    rewrite !N.pow2_bits_eqb.

    destruct (N.eqb_spec (N.log2 bm0) i).
    + subst; repeat split_bool; try reflexivity; exfalso.
      rewrite N.bit_log2 in Heqb by (unfold isBitMask in *; Nomega).
      congruence.
    + repeat split_bool; try reflexivity; exfalso.
Qed.
*)

Lemma filter_Desc:
  forall p s r f f',
  Desc s r f -> 
  (forall i, f' i = f i && p (NToInt i)) ->
  Desc0 (filter p s) r f'.
Proof.
  intros.
  revert f' H0.
  induction H.
  * intros.
    simpl. subst.
    rewrite foldl'Bits_foldlBits.
    fold (filterBits p (NToInt (rPrefix r)) bm).
    eapply tip_Desc0; try assumption; try reflexivity.
    + intro i.
      rewrite H3.
      rewrite H1.
      unfold bitmapInRange.
      destruct (inRange i r) eqn:Hir.
      - rewrite testbit_filterBits by isBitMask.
        f_equal. f_equal.
        clear p H3.
        admit.
        (*
        rewrite N.div_mod with (a := i) (b := id WIDTH) at 1
          by (intro Htmp; inversion Htmp).
        f_equal.
        ** destruct r as [p b]. unfold inRange, rPrefix, rBits, snd in *.
           rewrite N.eqb_eq in Hir.
           subst.
           rewrite N.shiftl_mul_pow2 by nonneg.
           rewrite N.shiftr_div_pow2 by nonneg.
           rewrite N.mul_comm.
           reflexivity.
        ** rewrite N.land_ones by nonneg.
           rewrite H0.
           reflexivity.
        *)
      - rewrite andb_false_l. reflexivity.
    + isBitMask.
  * intros. subst. simpl.
    eapply bin_Desc0.
    + apply IHDesc1; intro; reflexivity.
    + apply IHDesc2; intro; reflexivity.
    + assumption.
    + assumption.
    + assumption.
    + reflexivity.
    + reflexivity.
    + solve_f_eq.
Admitted.

Lemma filter_Sem:
  forall p s f f',
  Sem s f -> 
  (forall i, f' i = f i && p (NToInt i)) ->
  Sem (filter p s) f'.
Proof.
  intros.
  destruct H.
  * apply SemNil.
    solve_f_eq.
  * eapply Desc0_Sem.
    eapply filter_Desc.
    eassumption.
    eassumption.
Qed.

Lemma filter_WF:
  forall p s, WF s -> WF (filter p s).
Proof.
  intros.
  destruct H.
  eexists.
  eapply filter_Sem.
  eassumption.
  intro. reflexivity.
Qed.

(** *** Verification of [partition] *)

(** Conveniently, [partition] uses [filterBits] *)

Lemma partition_fst:
  forall p s,
  fst (partition p s) = filter p s.
Proof.
  intros.
  induction s.
  * simpl.
    rewrite (surjective_pairing (partition p s1)).
    rewrite (surjective_pairing (partition p s2)).
    simpl.
    rewrite IHs1, IHs2.
    reflexivity.
  * reflexivity.
  * reflexivity.
Qed.

Lemma filterBits_neg:
  forall P p bm,
  N.lxor (wordToN bm) (wordToN (filterBits P p bm)) = wordToN (filterBits (fun x => negb (P x)) p bm).
Proof.
  intros.
  apply N.bits_inj; intro i.
  rewrite N.lxor_spec.
  rewrite testbit_filterBits by isBitMask.
  rewrite testbit_filterBits by isBitMask.
  repeat split_bool; reflexivity.
Qed.

Lemma partition_snd:
  forall p s,
  snd (partition p s) = filter (fun x => negb (p x)) s.
Proof.
  intros P s.
  induction s.
  * simpl.
    rewrite (surjective_pairing (partition P s1)).
    rewrite (surjective_pairing (partition P s2)).
    rewrite IHs1, IHs2.
    reflexivity.
  * simpl.
    rewrite foldl'Bits_foldlBits.
    f_equal.
    change (NToWord (N.lxor (wordToN b) (wordToN (filterBits P p b))) = filterBits (fun x => negb (P x)) p b).
    rewrite filterBits_neg.
    Int_Word_N.
    reflexivity.
  * reflexivity.
Qed.

Theorem partition_WF (p : Int -> bool) (s : IntSet) :
  WF s ->
  let '(l,r) := partition p s in
  WF l /\ WF r.
Proof.
  intros WFs;
    rewrite (surjective_pairing (partition p s)), partition_fst, partition_snd;
    auto using filter_WF.
Qed.

Theorem partition_WF' (p : Int -> bool) (s : IntSet) :
  WF s ->
  WF (fst (partition p s)) /\ WF (snd (partition p s)).
Proof.
  generalize (partition_WF p s); destruct (partition p s); auto.
Qed.

Corollary partition_1_WF (p : Int -> bool) (s : IntSet) :
  WF s ->
  WF (fst (partition p s)).
Proof. apply partition_WF'. Qed.

Corollary partition_2_WF (p : Int -> bool) (s : IntSet) :
  WF s ->
  WF (snd (partition p s)).
Proof. apply partition_WF'. Qed.

(** *** Constructiveness of inequality *)

(** I found this easiest to specify once we have [toList]: If two sets are not
equal, we find an element where they differ.*)

Lemma Sem_notSubset_witness:
  forall s1 f1 s2 f2,
    Sem s1 f1 -> Sem s2 f2 ->
    isSubsetOf s1 s2 = false <-> (exists i, f1 i = true /\ f2 i = false).
Admitted.
(*
  intros.
  split; intro.
  * assert (~ (Forall (fun i => f2 (intToN i) = true) (toList s1))).
    { intro.
      rewrite <- not_true_iff_false in H1.
      contradict H1.
      rewrite Forall_forall in H2.
      rewrite isSubsetOf_Sem by eassumption. 
      intros i Hi.
      apply H2.
      rewrite <- toList_In by eassumption.
      assumption.
    }
    rewrite <- Exists_Forall_neg in H2 by (intro i; destruct (f2 i); intuition).
    rewrite Exists_exists in H2.
    destruct H2 as [i [Hin Hf2]].
    rewrite not_true_iff_false in Hf2.
    rewrite <- toList_In in Hin by eassumption.
    exists i; intuition.
  * apply  not_true_iff_false.
    intro.
    rewrite isSubsetOf_Sem in H2 by eassumption.
    destruct H1 as [i [Hin Hf2]].
    specialize (H2 i).
    intuition congruence.
Qed.
*)

Lemma Sem_differ_witness:
  forall s1 f1 s2 f2,
    Sem s1 f1 -> Sem s2 f2 ->
    s1 <> s2 <-> (exists i, f1 i <> f2 i).
Proof.
  intros.
  transitivity (isSubsetOf s1 s2 = false \/ isSubsetOf s2 s1 = false).
  * destruct (isSubsetOf s1 s2) eqn:?, (isSubsetOf s2 s1) eqn:?; intuition try congruence.
    + exfalso. apply H1.
      eapply isSubsetOf_antisym; eassumption.
    + subst. erewrite isSubsetOf_refl in Heqb by eassumption. congruence.
    + subst. erewrite isSubsetOf_refl in Heqb by eassumption. congruence.
  * do 2 rewrite Sem_notSubset_witness by eassumption.
    intuition.
    + destruct H2 as [i?]. exists i. intuition congruence.
    + destruct H2 as [i?]. exists i. intuition congruence.    
    + destruct H1 as [i?].
      destruct (f1 i) eqn:?, (f2 i) eqn:?; try congruence.
      - left. exists i. intuition congruence.
      - right. exists i. intuition congruence.
Qed.

(** *** Verification of [isProperSubsetOf] *)

(** [subsetCmp] is a strange beast, as it returns an [ordering], but does not totally
order the sets. We first relate it to [equal] and [isSubsetOf], and then stich the specification
for [isProperSubsetOf] together using that. We use [difference] in the stiching,
hence the position of this section. *)

Program Fixpoint subsetCmp_equal
  s1 r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  subsetCmp s1 s2 = Eq <-> equal s1 s2 = true := _.
Next Obligation.
  revert subsetCmp_equal H H0.
  intros IH HD1 HD2.
  destruct HD1, HD2.
  * (* Both are tips *)
    simpl; subst. unfoldMethods. Int_Word_N.
    rewrite if_negb.
    destruct (N.eqb_spec (rPrefix r) (rPrefix r0)).
    - destruct (N.eqb_spec (wordToN bm) (wordToN bm0)); try intuition congruence.
      destruct (N.land (wordToN bm) (N.lnot (wordToN bm0) IntWord.WIDTH) =? 0)%N;
      intuition; rewrite ?andb_false_r in *; try congruence.
    - destruct (N.eqb_spec (wordToN bm) (wordToN bm0)); intuition; rewrite ?andb_true_r, ?andb_false_r in *; try congruence.
  * (* Tip left, Bin right *)
    simpl; subst.
    repeat (match goal with [ |- (match ?scrut with _ => _ end) = Eq <-> _ ] => destruct scrut end;
            try intuition congruence).
  * (* Bin right, Tip left *)
    simpl; subst.
    intuition congruence.
  * (* Bin both sides *)
    simpl; subst; unfold shorter; unfoldMethods.
    repeat rewrite andb_true_iff.
    repeat rewrite !N.eqb_eq.
    repeat rewrite !N.eqb_eq.
    unfold op_zg__, Ord__Word, op_zg____, wordFromInt. Int_Word_N.
    destruct (N.ltb_spec (rMask r4) (rMask r));
      only 2: destruct (N.ltb_spec (rMask r) (rMask r4)).
    - (* left is bigger than right *)
      intuition try (congruence||lia).
      admit. (* Injectivity of NToInt on small values *)
    - (* right is bigger than left *)
      repeat (match goal with [ |- (match ?scrut with _ => _ end) = Eq <-> _ ] => destruct scrut end);
      intuition try (congruence||lia).
      all:admit.  (* Injectivity of NToInt on small values *)
    - (* same sized bins *)
      unfoldMethods.
      rewrite <- IH by ((simpl; lia) || eassumption).
      rewrite <- IH by ((simpl; lia) || eassumption).
      destruct (N.eqb_spec (rPrefix r) (rPrefix r4));
      repeat (match goal with [ |- (match ?scrut with _ => _ end) = Eq <-> _ ] => destruct scrut eqn:? end);
        intuition try (congruence || lia).
      all:admit.  (* Injectivity of NToInt on small values *)
Admitted.

Program Fixpoint subsetCmp_isSubsetOf
  s1 r1 f1 s2 r2 f2
  { measure (size_nat s1 + size_nat s2) } :
  Desc s1 r1 f1 ->
  Desc s2 r2 f2 ->
  negb (eq_comparison (subsetCmp s1 s2) Gt) = isSubsetOf s1 s2 := _.
Next Obligation.
  revert subsetCmp_isSubsetOf H H0.
  intros IH HD1 HD2.
  destruct HD1, HD2.
  * (* Both are tips *)
    simpl; subst. unfoldMethods. Int_Word_N.
    rewrite if_negb.
    destruct (N.eqb_spec (rPrefix r) (rPrefix r0)).
    - destruct (N.eqb_spec (wordToN bm) (wordToN bm0)); try intuition congruence.
      + subst.
        admit.
        (* rewrite N.land_diag, N.lxor_nilpotent, N.eqb_refl. intuition congruence. *)
      + destruct (N.land (wordToN bm) (N.lnot (wordToN bm0) IntWord.WIDTH) =? 0)%N;
        intuition; rewrite ?andb_false_r in *; try congruence.
    - destruct (N.land (wordToN bm) (N.lnot (wordToN bm0) IntWord.WIDTH)  =? 0)%N;
      intuition; rewrite ?andb_false_r in *; try congruence.
  * (* Tip left, Bin right *)
    simpl; subst.
    do 2 erewrite <- IH by (first [ simpl; omega
                                  | apply DescTip; try eassumption; reflexivity
                                  | eassumption ]).
    repeat (match goal with [ |- context [match ?scrut with _ => _ end] ] => destruct scrut end;
            try intuition congruence).
  * (* Bin right, Tip left *)
    simpl; subst.
    intuition congruence.
  * (* Bin both sides *)
    simpl; subst; unfold shorter; unfoldMethods. Int_Word_N.
    repeat rewrite andb_true_iff.
    repeat rewrite !N.eqb_eq.
    repeat rewrite !N.eqb_eq.
    destruct (N.ltb_spec (rMask r4) (rMask r));
      only 2: destruct (N.ltb_spec (rMask r) (rMask r4)).
    - (* left is bigger than right *)
      reflexivity.
    - (* right is bigger than left *)
      unfold match_, nomatch. unfoldMethods.
      rewrite if_negb.
      do 2 erewrite <- IH by (first [ simpl; omega
                                    | eapply DescBin; try beassumption; reflexivity
                                    | eassumption ]).
      destruct (intToN (mask _ _) =? _), (zero _ _);
      repeat (match goal with [ |- context [match ?scrut with _ => _ end] ] => destruct scrut eqn:? end); intuition.
    - (* same sized bins *)
      unfoldMethods.
      do 2 erewrite <- IH by (first [ simpl; omega
                                    | eapply DescBin; try beassumption; reflexivity
                                    | eassumption ]).
      destruct (N.eqb_spec (rPrefix r) (rPrefix r4));
        repeat (match goal with [ |- context [match ?scrut with _ => _ end] ] => destruct scrut eqn:? end); intuition.
Admitted.

Lemma isProperSubsetOf_Sem:
  forall s1 f1 s2 f2,
  Sem s1 f1 -> Sem s2 f2 ->
  isProperSubsetOf s1 s2 = true <-> ((forall i, f1 i = true -> f2 i = true) /\ (exists i, f1 i <> f2 i)).
Proof.
  intros ???? HSem1 HSem2.
  rewrite <- Sem_differ_witness by eassumption.
  rewrite <- isSubsetOf_Sem by eassumption.
  destruct HSem1, HSem2.
  * replace (isProperSubsetOf _ _) with false by reflexivity.
    replace (isSubsetOf _ _) with true by reflexivity.
    intuition try congruence.
  * replace (isProperSubsetOf Nil s) with true by (destruct HD; reflexivity).
    replace (isSubsetOf Nil s) with true by (destruct s; reflexivity).
    intuition try congruence.
    subst; inversion HD.
  * replace (isProperSubsetOf s Nil) with false by (destruct s; reflexivity).
    replace (isSubsetOf s Nil) with false by (destruct HD; reflexivity).
    intuition try congruence.
  * pose proof (subsetCmp_isSubsetOf _ _ _ _ _ _ HD HD0).
    rewrite eq_iff_eq_true in H.
    pose proof (subsetCmp_equal _ _ _ _ _ _ HD HD0).
    rewrite equal_spec in H0.
    unfold isProperSubsetOf.
    destruct (subsetCmp s s0) eqn:Hssc; simpl in *;
    intuition try congruence.
Qed.

(** *** Verification of [map] *)

Lemma map_Sem: forall g s f1,
  Sem s f1 -> Sem (map g s) (fun i => existsb (fun j => intToN (g j) =? i) (toList s)).
Proof.
  intros.
  unfold map.
  change (Sem (fromList (List.map g (toList s))) (fun i : N => existsb (fun j : Key => intToN (g j) =? i) (toList s))).
  destruct (fromList_Sem (List.map g (toList s))) as [f [HSem Hf]].
  eapply Sem_change_f; only 1: eassumption.
  intro i.
  apply eq_iff_eq_true.
  admit.
(*
  rewrite Hf.
  rewrite existsb_exists, in_map_iff.
  split; intros [x Hx]; exists x; try rewrite N.eqb_eq in *; intuition.
Qed.
*)

(** *** Verification of [valid] *)

(** The [valid] function is used in the test suite to detect whether
   functions return valid trees. It should be equivalent to our [WF].
   
   For now it is not complete (see https://github.com/haskell/containers/issues/522)
   and even with that fixed we might have a problem due to too wide types.
*)

(* Need to re-export with fixed width ints *)

(*
Require Import IntSetValidity.

Definition noNilInSet : IntSet -> bool :=
    (fix noNilInSet (t' : IntSet) : bool :=
        match t' with
        | Bin _ _ l' r' => noNilInSet l' && noNilInSet r'
        | Tip _ _ => true
        | Nil => false
        end).

Lemma valid_noNilInSet: forall s r f, Desc s r f -> noNilInSet s = true.
Proof.
  intros.
  induction H.
  * reflexivity.
  * simpl. rewrite IHDesc1, IHDesc2. reflexivity.
Qed.

Lemma valid_nilNeverChildOfBin: forall s, WF s -> nilNeverChildOfBin s = true.
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * reflexivity.
  * pose proof (valid_noNilInSet _ _ _ HD).
    destruct HD; apply H.
Qed.

Lemma valid_maskPowerOfTwo: forall s, WF s -> maskPowerOfTwo s = true.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * reflexivity.
  * induction HD.
    - reflexivity.
    - simpl. unfold bitcount. unfoldMethods.
      rewrite IHHD1, IHHD2.
      subst. simpl.
      rewrite andb_true_r.
      rewrite N.eqb_eq.
      destruct r as [p b].
      unfold rMask, rBits, snd in *.
      unfold id.
      rewrite N_popcount_pow2.
      reflexivity.
Qed.

Lemma Foldable_all_forallb:
  forall {a} p (l : list a), Foldable.all p l = forallb p l.
Proof.
  intros.
  induction l.
  * reflexivity.
  * simpl. rewrite <- IHl.
    compute.
    match goal with [ |- _ = match ?x with _ => _ end ] => destruct x end.
    match goal with [ |- _ = match ?x with _ => _ end ] => destruct x end.
    reflexivity.
    reflexivity.
Qed.

Lemma valid_commonPrefix: forall s, WF s -> commonPrefix s = true.
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * reflexivity.
  * destruct HD.
    - reflexivity.
    - unfold commonPrefix.
      unfoldMethods.
      set (s := Bin p msk s1 s2).
      assert (Desc s r f) by (eapply DescBin; eassumption).
      
      replace elems with toList by reflexivity.
      rewrite Foldable_all_forallb.
      rewrite forallb_forall.
      intros i Hi.
      rewrite <- toList_In in Hi by (eapply DescSem; eassumption).
      eapply Desc_inside in Hi; try eassumption.
      rewrite N.eqb_eq.
      symmetry.
      apply N.lxor_eq_0_iff.
      subst p.
      clear - Hi.
      destruct r as [p b].
      unfold inRange, rPrefix in *.
      rewrite N.eqb_eq in Hi.
      subst.
      apply N.bits_inj_iff.
      intros j.
      rewrite N.land_spec.
      destruct (N.ltb_spec j b).
      + rewrite N.shiftl_spec_low by assumption.
        reflexivity.
      + rewrite N.shiftl_spec_high' by assumption.
        rewrite !N.shiftr_spec by Nomega.
        replace (j - b + b) with j by Nomega.
        rewrite andb_diag.
        reflexivity.
Qed.

Lemma valid_maskRespected: forall s, WF s -> maskRespected s = true.
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * reflexivity.
  * destruct HD.
    - reflexivity.
    - unfold maskRespected.
      unfoldMethods.
      replace elems with toList by reflexivity.
      rewrite !Foldable_all_forallb.
      rewrite andb_true_iff; split.
      + rewrite forallb_forall.
        intros i Hi.
        rewrite <- toList_In in Hi by (eapply DescSem; eassumption).
        eapply Desc_inside in Hi; try eassumption.
        subst msk.
        rewrite zero_spec by assumption.
        rewrite negb_true_iff.
        apply testbit_halfRange_true_false; try assumption.
        eapply inRange_isSubrange_true; [|eassumption]; isSubrange_true.
        inRange_false; fail.
      + rewrite forallb_forall.
        intros i Hi.
        rewrite <- toList_In in Hi by (eapply DescSem; eassumption).
        eapply Desc_inside in Hi; try eassumption.
        subst msk.
        rewrite zero_spec by assumption.
        rewrite negb_involutive.
        apply testbit_halfRange_false_false; try assumption.
        eapply inRange_isSubrange_true; [|eassumption]; isSubrange_true.
        inRange_false; fail.
Qed.

Lemma valid_tipsValid: forall s, WF s -> tipsValid s = true.
Proof.
  intros.
  destruct H as [f HSem].
  destruct HSem.
  * reflexivity.
  * induction HD.
    + simpl.
      unfold validTipPrefix.
      unfoldMethods.
      destruct r as [p' b]. unfold rPrefix, rBits, snd in *. subst.
      rewrite N.eqb_eq.
      apply N.bits_inj_iff. intros i.
      rewrite N.bits_0.
      rewrite N.land_spec.
      destruct (N.ltb_spec i (N.log2 WIDTH)).
      - rewrite N.shiftl_spec_low by assumption.
        apply andb_false_r.
      - rewrite N.shiftl_spec_high' by assumption.
        rewrite N.bits_above_log2.
        apply andb_false_l.
        unfold WIDTH in *.
        simpl N.log2 in *.
        lia.
    + simpl.
      rewrite IHHD1, IHHD2.
      reflexivity.
Qed.

Lemma valid_correct: forall s, WF s -> valid s = true.
Proof.
  intros.
  unfold valid.
  rewrite valid_nilNeverChildOfBin by assumption.
  rewrite valid_maskPowerOfTwo by assumption.
  rewrite valid_commonPrefix by assumption.
  rewrite valid_maskRespected by assumption.
  rewrite valid_tipsValid by assumption.
  reflexivity.
Qed.
*)

(** ** [IntSet]s with [WF] *)

Definition WFIntSet : Type := {s : IntSet | WF s}.
Definition pack      : forall s : IntSet, WF s -> WFIntSet      := exist _.
Definition unpack    : WFIntSet                -> IntSet        := @proj1_sig _ _.
Definition unpack_WF : forall s : WFIntSet,       WF (unpack s) := @proj2_sig _ _.

(** ** Type classes *)

(** *** Verification of [Eq] *)

Require Import Proofs.GHC.Base.

Theorem Eq_eq_IntSet (x y : IntSet) : reflect (x = y) (x == y).
Proof.
  change (reflect (x = y) (equal x y)).
  apply iff_reflect.
  rewrite equal_spec.
  reflexivity.
Qed.

Instance EqLaws_IntSet : EqLaws IntSet.
Proof.
  EqLaws_from_reflect Eq_eq_IntSet.
  intros x y; unfoldMethods; unfold InternalWord.Eq___IntSet_op_zsze__.
  rewrite nequal_spec, negb_involutive.
  reflexivity.
Qed.

Instance EqExact_IntSet : EqExact IntSet.
Proof.  constructor; apply Eq_eq_IntSet. Qed.

Instance Eq__WFIntSet : Eq_ WFIntSet := fun _ k => k
  {| op_zeze____ := fun s1 s2 => unpack s1 == unpack s2
   ; op_zsze____ := fun s1 s2 => unpack s1 /= unpack s2
  |}.

Instance EqLaws_WFIntSet : EqLaws WFIntSet :=
  {| Eq_refl  := fun s        => Eq_refl  (unpack s)
   ; Eq_sym   := fun s1 s2    => Eq_sym   (unpack s1) (unpack s2)
   ; Eq_trans := fun s1 s2 s3 => Eq_trans (unpack s1) (unpack s2) (unpack s3)
   ; Eq_inv   := fun s1 s2    => Eq_inv   (unpack s1) (unpack s2)
  |}.

(** *** Verification of [Ord] *)

Local Close Scope N_scope.

Instance Ord_WFIntSet : Ord WFIntSet := fun _ k => k
  {| op_zlze____ := fun s1 s2 => unpack s1 <= unpack s2
   ; op_zgze____ := fun s1 s2 => unpack s1 >= unpack s2
   ; op_zl____   := fun s1 s2 => unpack s1 <  unpack s2
   ; op_zg____   := fun s1 s2 => unpack s1 >  unpack s2
   ; compare__   := fun s1 s2 => compare (unpack s1) (unpack s2)
   ; min__       := fun s1 s2 => if unpack s1 > unpack s2 then s2 else s1
   ; max__       := fun s1 s2 => if unpack s1 < unpack s2 then s1 else s2
  |}.

Ltac unfold_applied t :=
  let rec hd t' := match t' with
                   | ?f _ => hd f
                   | ?x   => x 
                   end in
  let f := hd t      in
  let x := fresh "x" in
  let E := fresh "E" in
  (remember t as x eqn:E; unfold f in E; subst x) || fail "nothing to unfold".

Ltac fold_is_true :=
  repeat match goal with
  | |- context[?x = true] => let H := fresh in
                             assert ((x = true) <-> is_true x) as H by reflexivity;
                             rewrite H; clear H
  end.

Local Ltac unfold_WFIntSet_Eq :=
  repeat first [ progress simpl
               | unfold_applied (@op_zeze__ WFIntSet)
               | unfold_applied (@op_zsze__ WFIntSet)
               | unfold_applied Eq__WFIntSet ].

Local Ltac unfold_WFIntSet_Ord :=
  unfold_WFIntSet_Eq;
  repeat first [ progress simpl
               | unfold_applied (@op_zl__   WFIntSet) | unfold_applied (@op_zl__   IntSet)
               | unfold_applied (@op_zlze__ WFIntSet) | unfold_applied (@op_zlze__ IntSet)
               | unfold_applied (@op_zg__   WFIntSet) | unfold_applied (@op_zg__   IntSet)
               | unfold_applied (@op_zgze__ WFIntSet) | unfold_applied (@op_zgze__ IntSet)
               | unfold_applied (@compare   WFIntSet) | unfold_applied (@compare   IntSet)
               | unfold_applied (@max       WFIntSet) | unfold_applied (@max       IntSet)
               | unfold_applied (@min       WFIntSet) | unfold_applied (@min       IntSet)
               | unfold_applied Ord_WFIntSet          | unfold_applied Ord__IntSet
               | unfold_applied Data.IntSet.InternalWord.Ord__IntSet_op_zl__
               | unfold_applied Data.IntSet.InternalWord.Ord__IntSet_op_zlze__
               | unfold_applied Data.IntSet.InternalWord.Ord__IntSet_op_zg__
               | unfold_applied Data.IntSet.InternalWord.Ord__IntSet_op_zgze__
               | unfold_applied Data.IntSet.InternalWord.Ord__IntSet_compare
               | unfold_applied Data.IntSet.InternalWord.Ord__IntSet_max
               | unfold_applied Data.IntSet.InternalWord.Ord__IntSet_min ].

Lemma compare_not_Gt_le {A} `{OrdLaws A} (x y : A) :
  (compare x y /= Gt) = (x <= y).
Proof. destruct (compare x y) eqn:C; order A. Qed.

Local Ltac to_Ord_list :=
  repeat match goal with
  | |- forall s : WFIntSet, _ => intros [? ?]; simpl
  end;
  rewrite ?compare_not_Gt_le;
  repeat match goal with
  | |- context[toAscList ?s]  => let x := fresh in
                                 let E := fresh in
                                 (remember (toAscList s) as x eqn:E; clear E)
  end;
  unfold Key in *.

(* Needs OrdLaws on Int *)

(*
Instance OrdLaws_WFIntSet : OrdLaws WFIntSet.
Proof.
  constructor; unfold_WFIntSet_Ord; try now to_Ord_list; order (list N).
  
  - intros [s1 WF1] [s2 WF2]; simpl.
    rewrite !compare_not_Gt_le => LE1 LE2.
    apply equal_spec, toAscList_exact; trivial.
    apply (reflect_iff _ _ (Eq_eq _ _)); generalize dependent LE1; generalize dependent LE2;
      to_Ord_list; order (list N).
  
  - intros [s1 WF1] [s2 WF2]; simpl.
    destruct (Ord_total (toAscList s1) (toAscList s2)); to_Ord_list; order (list N).
  
  - intros [s1 WF1] [s2 WF2]; simpl.
    unfold "==", Eq___IntSet, Data.IntSet.Internal.Eq___IntSet_op_zeze__; simpl.
    rewrite equal_spec, toAscList_exact, Ord_compare_Eq; trivial.
    symmetry; apply (ssrbool.rwP (Eq_eq _ _)).
  
  - intros [s1 WF1] [s2 WF2]; simpl.
    apply eq_iff_eq_true;
      rewrite !compare_not_Gt_le; fold_is_true;
      rewrite <-(ssrbool.rwP (Eq_eq _ _)), Ord_compare_Lt;
      order (list N).
  
  - intros [s1 WF1] [s2 WF2]; simpl.
    apply eq_iff_eq_true;
      rewrite !compare_not_Gt_le; fold_is_true;
      rewrite <-(ssrbool.rwP (Eq_eq _ _)), Ord_compare_Gt;
      order (list N).
Qed.
*)

(** *** Verification of [Semigroup] *)

Instance Semigroup_WFIntSet : Semigroup WFIntSet := fun _ k => k
  {| op_zlzlzgzg____ := fun s1 s2 => pack (unpack s1 <<>> unpack s2)
                                      (union_WF _ _ (unpack_WF s1) (unpack_WF s2)) |}.

Instance SemigroupLaws_WFIntSet : SemigroupLaws WFIntSet.
Proof.
  constructor; intros [s1 [f1 SEM1]] [s2 [f2 SEM2]] [s3 [f3 SEM3]].
  unfold_WFIntSet_Eq; fold_is_true; rewrite <-(ssrbool.rwP (Eq_eq _ _)).
  repeat match goal with
         | SEMs : Sem ?s ?fs, SEMt : Sem ?t ?ft |- context[?s <<>> ?t] =>
           match goal with
           | _ : Sem (s <> t)    _ |- _ => fail 1
           | _ : Sem (union s t) _ |- _ => fail 1
           |                          _ => specialize (union_Sem s fs t ft SEMs SEMt) as ?
           end
         end.
  eapply Sem_unique; try eassumption.
  now intros i; simpl; rewrite orb_assoc.
Qed.

(** *** Verification of [Monoid] *)

Require Import Data.Monoid.

Lemma WFIntSet_unpack_mconcat_WF (ss : list WFIntSet) :
  WF (mconcat (GHC.Base.map unpack ss)).
Admitted.
(* needs unions
Proof.
  apply unions_WF, Forall_forall; intros s; rewrite in_map_iff.
  intros [? [? ?]]; subst; apply unpack_WF.
Qed.
*)

Instance Monoid_WFIntSet : Monoid WFIntSet := fun _ k => k
  {| mempty__  := pack mempty empty_WF
   ; mappend__ := _<<>>_
   ; mconcat__ := fun ss => pack (mconcat (GHC.Base.map unpack ss)) (WFIntSet_unpack_mconcat_WF ss) |}.

Local Ltac WFIntSet_Eq_eq := unfold_WFIntSet_Eq; fold_is_true; rewrite <-(ssrbool.rwP (Eq_eq _ _)).

Lemma MonoidLaws_WFIntSet_mconcat_swing (ss : list WFIntSet) (s' z : IntSet) :
  WF s' ->
  WF z  ->
  fold_left union (List.map unpack ss) (union z s') = union s' (fold_left union (List.map unpack ss) z).
Proof.
  generalize dependent z; generalize dependent s'; induction ss as [|s ss IH]; simpl; intros s' z WFs' WFz.
  - now rewrite union_comm.
  - assert (WF (unpack s))                               as WFs by apply unpack_WF.
    assert (WF (union z s'))                             as WFzs' by now apply union_WF.
    assert (WF (fold_left union (List.map unpack ss) z)) as WFssz. {
      clear - WFz.
      rewrite <-fold_left_rev_right, <-hs_coq_map, <-map_rev.
      induction (rev ss) as [|s rss IH]; simpl; trivial.
      apply union_WF; [apply IH | apply unpack_WF].
    }
    rewrite !IH, !union_assoc; trivial.
    now rewrite (union_comm s').
    (* TODO: This Qed takes 40 seconds on my machine for some reason?! —ASZ *)
    (* Here too, and this is annoying while working on the file, so I just admit it.*)
    all:fail. (* ensure that no subgoals are left *)
Admitted.

Instance MonoidLaws_WFIntSet : MonoidLaws WFIntSet.
Proof.
  constructor.
  - intros [s WFs]; WFIntSet_Eq_eq. 
    now destruct s.
  - intros [s WFs]; WFIntSet_Eq_eq. 
    now destruct s.
  - intros [s1 WF1] [s2 WF2]; WFIntSet_Eq_eq. 
    reflexivity.
  - intros ss; WFIntSet_Eq_eq. 
    unfold mconcat, Monoid__IntSet, Data.IntSet.InternalWord.Monoid__IntSet_mconcat; simpl.
    unfold unions; rewrite hs_coq_foldl_list, hs_coq_foldr_base, hs_coq_map.
    induction ss as [|s ss IH]; simpl.
    + reflexivity.
    + rewrite MonoidLaws_WFIntSet_mconcat_swing, IH; auto using unpack_WF.
Qed.

(** ** Instantiating the [FSetInterface] *)

Require Import Coq.FSets.FSetInterface.
Require Import Coq.Structures.OrderedTypeEx.
Require Import SortedUtil.

Module Int_as_OT <: UsualOrderedType.

  Definition t := Int.

  Definition eq := @eq Int.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition lt x y := Z.lt (intToZ x) (intToZ y).

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Admitted.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Admitted.

  Definition compare x y : Compare lt eq x y.
  Admitted.

  Definition eq_dec (x y : t) : { eq x y } + { ~ eq x y }.
  Admitted.
End Int_as_OT.

Module IntSetFSet <: WSfun(Int_as_OT) <: WS <: Sfun(Int_as_OT) <: S.
  Module E := Int_as_OT.

  Module OrdFacts := OrderedTypeFacts(Int_as_OT).

  Definition elt := Int.

  (* Well-formedness *)
  
  Definition t := WFIntSet.
  
  Notation "x <-- f ;; P" :=
    (match f with
     | exist x _ => P
     end) (at level 99, f at next level, right associativity).

  (* Membership, equality, etc. *)

  Definition In_set x (s : IntSet) :=
    member x s = true.
  
  Definition In x (s' : t) :=
    s <-- s' ;;
    In_set x s.

  Definition Equal_set s s' := forall a : Int, In_set a s <-> In_set a s'.
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.

  Definition eq : t -> t -> Prop := Equal.
  
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.

  Definition empty : t.
    eexists. eexists. apply SemNil. intro. reflexivity.
  Defined.
  
  Definition is_empty : t -> bool := fun s' => 
    s <-- s' ;; null s.

  (* IntSet comparison predicate *)
  
  Definition lt (s s' : t) : Prop := (s < s') = true.
  
  (* More information later, after we've proved theorems *)

  (* Minimal and maximal elements *)
  
  (* Definition min_elt : t -> option elt := fmap fst ∘ minView ∘ unpack. *)
  
  (* Definition max_elt : t -> option elt := fmap fst ∘ maxView ∘ unpack. *)
  
  (* The bit-twiddling to prove `minView` and `maxView` correct is quite
     difficult.  In the meantime: *)
  
  Definition min_elt : t -> option elt := @hd_error _ ∘ toAscList ∘ unpack.
  
  Definition max_elt : t -> option elt := @hd_error _ ∘ toDescList ∘ unpack.
  
  (* Theorems *)

  Lemma empty_1 : Empty empty.
  Proof. unfold Empty; intros a H. inversion H. Qed.

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    intros. unfold Empty, In, In_set, is_empty in *. destruct s.
    destruct w as [s HSem].
    erewrite null_Sem by eassumption.
    intro i.
    specialize (H (NToInt i)).
    rewrite not_true_iff_false in H.
    erewrite member_Sem in H by eassumption.
    Int_Word_N.
    assumption.
  Qed.

  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof.
    intros ????.
    unfold In, In_set in *. destruct s. simpl in *.
    destruct x; try inversion H. inversion H0.
  Qed.

  Definition singleton : elt -> t.
    refine (fun e => pack (singleton e) _).
    apply singleton_WF; nonneg.
  Defined.

  Definition add (e: elt) (s': t) : t.
    refine (s <-- s' ;;
            pack (insert e s) _).
    apply insert_WF; nonneg.
  Defined.

  Definition remove  (e: elt) (s': t) : t.
    refine (s <-- s' ;;
            pack (delete e s) _).
    apply delete_WF; nonneg.
  Defined.

  Definition union (s1' s2' : t) : t.
    refine (s1 <-- s1' ;;
            s2 <-- s2' ;;
            pack (union s1 s2) _).
    apply union_WF; assumption.
  Defined.

  Definition inter (s1' s2' : t) : t.
    refine (s1 <-- s1' ;;
            s2 <-- s2' ;;
            pack (intersection s1 s2) _).
    apply intersection_WF; assumption.
  Defined.

  Definition diff (s1' s2' : t) : t.
    refine (s1 <-- s1' ;;
          s2 <-- s2' ;;
          pack (difference s1 s2) _).
  apply difference_WF; assumption.
  Defined.


  Definition equal : t -> t -> bool :=
    fun ws ws' => s <-- ws ;;
               s' <-- ws' ;;
               s == s'.
  
  Definition subset : t -> t -> bool :=
    fun ws ws' => s <-- ws ;;
               s' <-- ws' ;;
               isSubsetOf s s'.

  Definition eq_dec : forall s s' : t, {eq s s'} + {~ eq s s'}.
  Proof.
    intros.
    destruct s as [s1 Hwf1].
    destruct s' as [s2 Hwf2].
    destruct (InternalWord.equal s1 s2) eqn:?.
    * left.
      rewrite equal_spec in Heqb.
      subst.
      intro. unfold In. reflexivity.
    * right.
      apply not_true_iff_false in Heqb.
      contradict Heqb.
      rewrite equal_spec.
      destruct Hwf1 as [f1 HSem1].
      destruct Hwf2 as [f2 HSem2].
      eapply Sem_unique; try eassumption.
      intro i.
      apply eq_iff_eq_true.
      specialize (Heqb (NToInt i)).
      unfold eq, In, In_set in Heqb.
      erewrite (member_Sem HSem1) in Heqb.
      erewrite (member_Sem HSem2) in Heqb.
      Int_Word_N.
      assumption.
  Defined.

  Lemma eq_refl : forall s : t, eq s s.
  Proof. destruct s. unfold eq. unfold Equal. intro. reflexivity. Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. destruct s; destruct s'; 
    unfold eq, Equal in *. intros. rewrite H. intuition. Qed.

  Lemma eq_trans :
    forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
    destruct s; destruct s'; destruct s''; simpl.
    unfold eq, Equal. intros ???. rewrite H, H0. reflexivity.
  Qed.

  Definition fold (A : Type) (f : elt -> A -> A) (ws : t) (x : A) : A :=
    s <-- ws;;
    foldl (fun x a => f a x) x s.

  Definition filter : (elt -> bool) -> t -> t.
    refine (fun p ws =>
       s <-- ws;;
       pack (filter p s) _).
    apply filter_WF; assumption.
  Defined.


  Program Definition partition : (elt -> bool) -> t -> t * t :=
     (fun p ws => Data.IntSet.InternalWord.partition p ws).
  Next Obligation.
    rewrite partition_snd.
    apply filter_WF.
    destruct ws; auto.
  Qed.
  Next Obligation.
    rewrite partition_fst.
    apply filter_WF.
    destruct ws; auto.
  Qed.

  Definition cardinal : t -> nat :=
    fun ws => s <-- ws;;
              Z.to_nat (intToZ (size s)).

  Definition elements (ws : t) : list elt :=
    s <-- ws;;
    toList s.

  Lemma In_1 :
    forall (s : t) (x y : elt), Int_as_OT.eq x y -> In x s -> In y s.
  Proof. intros. destruct H. assumption. Qed.
  
  Definition mem : elt -> t -> bool := fun e s' =>
   s <-- s' ;; member e s.


  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
  
  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true.
  Proof.
    intros.
    destruct s as [s1 [f1 HSem1]].
    destruct s' as [s2 [f2 HSem2]].
    apply equal_spec.
    eapply Sem_unique; try eassumption.
    intro i.
    apply eq_iff_eq_true.
    specialize (H (NToInt i)).
    unfold eq, In, In_set in H.
    erewrite (member_Sem HSem1) in H.
    erewrite (member_Sem HSem2) in H.
    Int_Word_N.
    assumption.
  Qed.

  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
  Proof.
    intros.
    destruct s as [s1 [f1 HSem1]].
    destruct s' as [s2 [f2 HSem2]].
    apply equal_spec in H.
    subst.
    intro i; intuition.
  Qed.

  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true.
  Proof.
    intros.
    destruct s as [s1 [f1 HSem1]].
    destruct s' as [s2 [f2 HSem2]].
    unfold Subset, subset, In, In_set in *.
    rewrite isSubsetOf_Sem by eassumption.
    intro i. specialize (H (NToInt i)).
    do 2 erewrite member_Sem in H by eassumption.
    Int_Word_N.
    assumption.
  Qed.

  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
  Proof.
    intros.
    destruct s as [s1 [f1 HSem1]].
    destruct s' as [s2 [f2 HSem2]].
    unfold Subset, subset, In, In_set in *.
    rewrite isSubsetOf_Sem in H by eassumption.
    intro i. specialize (H (intToN i)).
    do 2 erewrite member_Sem by eassumption.
    assumption.
  Qed.

  Lemma add_1 :
    forall (s : t) (x y : elt), Int_as_OT.eq x y -> In y (add x s).
  Proof.
    intros.
    inversion_clear H; subst.
    unfold In, add, pack, In_set; intros; destruct s as [s].
    destruct w as [f HSem].
    erewrite member_Sem.
      Focus 2.
      eapply insert_Sem; try nonneg; try eassumption.
      intro. reflexivity.
    simpl. rewrite N.eqb_refl. reflexivity.
  Qed.

  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s).
  Proof.
    intros.
    unfold In, add, pack, In_set in *; intros; destruct s as [s].
    destruct w as [f HSem].
    erewrite member_Sem.
      Focus 2.
      eapply insert_Sem; try nonneg; try eassumption.
      intro. reflexivity.
      simpl. rewrite orb_true_iff. right.
    erewrite <- member_Sem. eassumption. eassumption.
  Qed.

  Lemma add_3 :
    forall (s : t) (x y : elt), ~ Int_as_OT.eq x y -> In y (add x s) -> In y s.
  Proof.
    intros.
    unfold In, add, pack, In_set in *; intros; destruct s as [s].
    destruct w as [f HSem].
    erewrite member_Sem in H0.
      Focus 2.
      eapply insert_Sem; try nonneg; try eassumption.
      intro. reflexivity. simpl in *.
    rewrite -> orb_true_iff in H0.
    rewrite -> N.eqb_eq in H0.
    Int_Word_N.
    destruct H0. congruence.

    erewrite member_Sem.
      Focus 2.
      eassumption.
    assumption.
  Qed.

  Lemma remove_1 :
    forall (s : t) (x y : elt), Int_as_OT.eq x y -> ~ In y (remove x s).
  Proof.
    intros.
    unfold In, remove, pack, In_set in *; intros; destruct s as [s].
    destruct H.
    destruct w as [f HSem].
    erewrite member_Sem.
      Focus 2.
      eapply delete_Sem; try nonneg.
      eassumption.
      intro i. reflexivity.
    simpl.
    rewrite N.eqb_refl; simpl.
    congruence.
  Qed.

  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ Int_as_OT.eq x y -> In y s -> In y (remove x s).
  Proof.
    intros.
    unfold In, remove, pack, In_set in *; intros; destruct s as [s].
    apply not_false_iff_true.
    contradict H.
    destruct w as [f HSem].
    erewrite member_Sem in H.
        Focus 2.
        eapply delete_Sem; try nonneg.
        eassumption.
      intro i. reflexivity.
    erewrite member_Sem in H0 by eassumption.
    simpl in *.
    destruct (N.eqb_spec (intToN y) (intToN x)); simpl in *; Int_Word_N; try congruence.
  Qed.

  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s.
  Proof.
    intros.
    unfold In, remove, pack, In_set in *; intros; destruct s as [s].
    destruct w as [f HSem].
    erewrite member_Sem in H.
        Focus 2.
        eapply delete_Sem; try nonneg.
        eassumption.
      intro i. reflexivity.
    erewrite member_Sem by eassumption.
    simpl in *.
    rewrite andb_true_iff in H. intuition.
  Qed.

  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> Int_as_OT.eq x y.
  Proof.
    intros.
    unfold In, In_set, singleton, pack in *.
    erewrite member_Sem in H.
    Focus 2. apply singleton_Sem; nonneg.
    simpl in H.
    rewrite -> N.eqb_eq in H.
    symmetry.
    Int_Word_N.
    assumption.
  Qed.

  Lemma singleton_2 :
    forall x y : elt, Int_as_OT.eq x y -> In y (singleton x).
  Proof.
    intros.
    unfold In, In_set, singleton, pack in *.
    erewrite member_Sem.
    Focus 2. apply singleton_Sem; nonneg.
    simpl.
    rewrite -> N.eqb_eq.
    congruence.
  Qed.

  Lemma union_1 :
    forall (s s' : t) (x : elt), In x (union s s') -> In x s \/ In x s'.
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, union, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem by eassumption.
    erewrite member_Sem in H
     by (eapply union_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite orb_true_iff in H.
    assumption.
  Qed.

  Lemma union_2 :
    forall (s s' : t) (x : elt), In x s -> In x (union s s').
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, union, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem in H by eassumption.
    erewrite member_Sem
     by (eapply union_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite orb_true_iff.
    intuition.
  Qed.

  Lemma union_3 :
    forall (s s' : t) (x : elt), In x s' -> In x (union s s').
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, union, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem in H by eassumption.
    erewrite member_Sem
     by (eapply union_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite orb_true_iff.
    intuition.
  Qed.

  Lemma inter_1 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s.
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, inter, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem by eassumption.
    erewrite member_Sem in H
     by (eapply intersection_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff in H.
    intuition.
  Qed.

  Lemma inter_2 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s'.
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, inter, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem by eassumption.
    erewrite member_Sem in H
     by (eapply intersection_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff in H.
    intuition.
  Qed.
  
  Lemma inter_3 :
    forall (s s' : t) (x : elt), In x s -> In x s' -> In x (inter s s').
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, inter, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem in H by eassumption.
    erewrite !member_Sem in H0 by eassumption.
    erewrite member_Sem
     by (eapply intersection_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff.
    intuition.
  Qed.

  Lemma diff_1 :
    forall (s s' : t) (x : elt), In x (diff s s') -> In x s.
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, diff, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem by eassumption.
    erewrite member_Sem in H
     by (eapply difference_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff in H.
    intuition.
  Qed.

  Lemma diff_2 :
    forall (s s' : t) (x : elt), In x (diff s s') -> ~ In x s'.
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, diff, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem by eassumption.
    erewrite member_Sem in H
     by (eapply difference_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff in H.
    rewrite negb_true_iff in H.
    intuition congruence.
  Qed.

  Lemma diff_3 :
    forall (s s' : t) (x : elt), In x s -> ~ In x s' -> In x (diff s s').
  Proof.
    intros.
    destruct s, s'.
    unfold In, In_set, diff, pack in *.
    destruct w as [f1 HSem1], w0 as [f2 HSem2].
    erewrite !member_Sem in H by eassumption.
    erewrite !member_Sem in H0 by eassumption.
    erewrite member_Sem
     by (eapply difference_Sem; try eassumption; intro; reflexivity).
    simpl in *.
    rewrite andb_true_iff.
    intuition.
  Qed.

  Lemma fold_left_map:
    forall {a b c} f (g : a -> b) (x : c) xs,
    fold_left (fun a e => f a e) (List.map g xs) x
      = fold_left (fun a e => f a (g e)) xs x.
  Proof.
    intros.
    revert x.
    induction xs; intros.
    * reflexivity.
    * simpl. rewrite IHxs. reflexivity.
  Qed.

  Lemma fold_1 :
    forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
    fold A f s i =
    fold_left (fun (a : A) (e : elt) => f e a) (elements s) i.
  Proof.
    intros.
    destruct s as [s Hwf].
    simpl.
    apply foldl_spec; assumption.
  Qed.

  Lemma cardinal_1 : forall s : t, cardinal s = length (elements s).
  Proof.
    intros.
    destruct s as [s Hwf].
    simpl.
    rewrite size_spec by assumption.
    Int_Word_N.
    rewrite Nat2Z.id.
    reflexivity.
  Qed.

  Lemma filter_1 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool Int_as_OT.eq f -> In x (filter f s) -> In x s.
  Proof.
    intros s x P Heq Hin.
    destruct s as [s [f HSem]].
    unfold filter, In, In_set in *.
    simpl in *.
    erewrite member_Sem by eassumption.
    erewrite member_Sem in Hin
      by (eapply filter_Sem; try eassumption; intro i; reflexivity).
    simpl in *.
    rewrite andb_true_iff in Hin.
    intuition.
  Qed.

  Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool Int_as_OT.eq f -> In x (filter f s) -> f x = true.
  Proof.
    intros s x P Heq Hin.
    destruct s as [s [f HSem]].
    unfold filter, In, In_set in *.
    simpl in *.
    erewrite member_Sem in Hin
      by (eapply filter_Sem; try eassumption; intro i; reflexivity).
    simpl in *.
    rewrite andb_true_iff in Hin.
    Int_Word_N.
    intuition.
  Qed.

  Lemma filter_3 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool Int_as_OT.eq f -> In x s -> f x = true -> In x (filter f s).
  Proof.
    intros s x P Heq Hin HP.
    destruct s as [s [f HSem]].
    unfold filter, In, In_set in *.
    simpl in *.
    erewrite member_Sem in Hin by eassumption.
    erewrite member_Sem
      by (eapply filter_Sem; try eassumption; intro i; reflexivity).
    simpl in *.
    rewrite andb_true_iff.
    Int_Word_N.
    intuition.
  Qed.

  Lemma partition_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool Int_as_OT.eq f -> Equal (fst (partition f s)) (filter f s).
  Proof.
    intros.
    destruct s.
    unfold Equal, partition; simpl.
    rewrite partition_fst.
    reflexivity.
  Qed.

  Lemma partition_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool Int_as_OT.eq f ->
    Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s).
  Proof.
    intros.
    destruct s.
    unfold Equal, partition; simpl.
    rewrite partition_snd by assumption.
    reflexivity.
  Qed.

  Lemma elements_1 :
    forall (s : t) (x : elt), In x s -> InA Int_as_OT.eq x (elements s).
  Proof.
    intros.
    destruct s as [s Hwf].
    destruct Hwf as [f HSem].
    simpl in *.
    unfold In_set in *.
    erewrite member_Sem in H by eassumption.
    apply OrdFacts.ListIn_In.
    rewrite <- toList_In by eassumption.
    assumption.
  Qed.

  Lemma elements_2 :
    forall (s : t) (x : elt), InA Int_as_OT.eq x (elements s) -> In x s.
  Proof.
    intros.
    destruct s as [s Hwf].
    destruct Hwf as [f HSem].
    simpl in *.
    unfold In_set in *.
    erewrite member_Sem by eassumption.
    rewrite InA_alt in H.
    destruct H as [_[[]?]].
    rewrite <- toList_In in H by eassumption.
    assumption.
  Qed.
  
  Lemma elements_3 (s : t) : Sorted E.lt (elements s).
  Proof.
    unfold E.lt; destruct s as [s WFs]; simpl.
    apply StronglySorted_Sorted.
    now apply to_List_sorted.
  Qed.
  
  Lemma elements_3w (s : t) : NoDupA Int_as_OT.eq (elements s).
  Proof. apply OrdFacts.Sort_NoDup, elements_3. Qed.
  
  (* Ordering theorems *)
  
  Definition compare (s s' : t) : Compare lt eq s s'.
  Admitted.
  (* Needs OrdLaws *)
  (*
  Proof.
    destruct (compare s s') eqn:CMP.
    - apply EQ; abstract now apply equal_2; destruct s, s'; generalize dependent CMP;
                             rewrite Ord_compare_Eq; unfold "==", Eq__WFIntSet; simpl.
    - apply LT; abstract order t.
    - apply GT; abstract order t.
  Defined.
  *)
  
  Theorem lt_trans (s1 s2 s3 : t) :
    lt s1 s2 -> lt s2 s3 -> lt s1 s3.
  Admitted.
  (*
  Proof. unfold lt; order t. Qed. 
  *)
  
  Theorem lt_not_eq (s1 s2 : t) :
    lt s1 s2 -> ~ eq s1 s2.
  Admitted.
  (*
  Proof.
    destruct s1 as [s1 WF1], s2 as [s2 WF2].
    unfold lt, "<", Ord_WFIntSet; simpl.
    intros LT EQ; apply equal_1, (reflect_iff _ _ (Eq_eq _ _)) in EQ.
    subst s2; clear WF2.
    assert (pack s1 WF1 < pack s1 WF1 = true) by now unfold "<", Ord_WFIntSet; simpl.
    order WFIntSet.
  Qed.
  *)
  
  Lemma min_elt_1 (s : t) (x : elt) : min_elt s = Some x -> In x s.
  Proof.
    destruct s as [s [fs SEM_s]]; unfold min_elt, "∘"; simpl; unfold In_set.
    destruct (toAscList s) as [|e xs] eqn:ASC; simpl; [easy | intros EQ; inversion EQ; subst e; clear EQ].
    erewrite member_Sem by eassumption.
    eapply toList_In; [eassumption|].
    now unfold toList; rewrite ASC; left.
  Qed.
  
  Lemma min_elt_2 (s : t) (x y : elt) : min_elt s = Some x -> In y s -> ~ E.lt y x.
  Proof.
    destruct s as [s WFs]; destruct (WFs) as [fs SEM_s]; unfold min_elt, "∘", E.lt; simpl; unfold In_set.
    destruct (toAscList s) as [|e xs] eqn:ASC; simpl; [easy | intros EQ; inversion EQ; subst e; clear EQ].
    erewrite member_Sem, toList_In by eassumption.
    specialize (to_List_sorted s WFs); unfold toList; rewrite ASC; simpl.
    intros SS' IN_y LT.
    inversion SS' as [|x_ xs_ SS min_x]; subst x_ xs_.
    rewrite Forall_forall in min_x.
    destruct IN_y as [|IN_y]; [subst y|].
    - now apply Z.lt_irrefl in LT.
    - specialize (min_x _ IN_y).
      specialize (Z.lt_trans _ _ _ LT min_x); apply Z.lt_irrefl.
  Qed.
  
  Lemma min_elt_3 (s : t) : min_elt s = None -> Empty s.
  Proof.
    destruct s as [s [fs SEM_s]]; unfold min_elt, "∘", Empty; simpl; unfold In_set.
    destruct (toAscList s) as [|e xs] eqn:ASC; simpl; [intros _ | easy].
    intros x.
    erewrite member_Sem, toList_In by eassumption.
    now unfold toList; rewrite ASC.
  Qed.

  Lemma max_elt_1 (s : t) (x : elt) : max_elt s = Some x -> In x s.
  Proof.
    destruct s as [s WFs]; destruct (WFs) as [fs SEM_s]; unfold max_elt, "∘"; simpl; unfold In_set.
    rewrite toDescList_spec by easy.
    destruct (rev (toList s)) as [|e xs] eqn:DESC; simpl; [easy | intros EQ; inversion EQ; subst e; clear EQ].
    erewrite member_Sem by eassumption.
    eapply toList_In, in_rev; [eassumption|].
    now fold Key; rewrite DESC; left.
  Qed.
  
  Lemma max_elt_2 (s : t) (x y : elt) : max_elt s = Some x -> In y s -> ~ E.lt x y.
  Proof.
    destruct s as [s WFs]; destruct (WFs) as [fs SEM_s]; unfold max_elt, "∘", E.lt; simpl; unfold In_set.
    rewrite toDescList_spec by easy.
    destruct (rev (toList s)) as [|e xs] eqn:DESC; simpl; [easy | intros EQ; inversion EQ; subst e; clear EQ].
    erewrite member_Sem, toList_In, in_rev by eassumption.
    specialize (to_List_sorted s WFs); fold Key; rewrite StronglySorted_rev, DESC; simpl.
    intros SS' IN_y LT.
    inversion SS' as [|x_ xs_ SS max_x]; subst x_ xs_.
    rewrite Forall_forall in max_x.
    destruct IN_y as [|IN_y]; [subst y|].
    - now apply Z.lt_irrefl in LT.
    - specialize (max_x _ IN_y).
      specialize (Z.lt_trans _ _ _ LT max_x); apply Z.lt_irrefl.
  Qed.
  
  Lemma max_elt_3 (s : t) : max_elt s = None -> Empty s.
  Proof.
    destruct s as [s WFs]; destruct (WFs) as [fs SEM_s]; unfold max_elt, "∘", Empty; simpl; unfold In_set.
    rewrite toDescList_spec by easy.
    destruct (rev (toList s)) as [|e xs] eqn:DESC; simpl; [intros _ | easy].
    intros x.
    erewrite member_Sem, toList_In, in_rev by eassumption.
    now fold Key; rewrite DESC.
  Qed.
  
  (**
  These (non-ordering) portions of the [FSetInterface]s have no counterpart in the [IntSet] interface.
  We implement them generically.
  *)

  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Definition for_all : (elt -> bool) -> t -> bool :=
    fun P s => forallb P (elements s).
  Definition exists_ : (elt -> bool) -> t -> bool :=
    fun P s => existsb P (elements s).

  Lemma for_all_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool Int_as_OT.eq f ->
    For_all (fun x : elt => f x = true) s -> for_all f s = true.
  Proof.
    intros.
    unfold For_all, for_all in *.
    rewrite forallb_forall.
    intros. apply H0.
    apply elements_2.
    apply OrdFacts.ListIn_In.
    assumption.
  Qed.

  Lemma for_all_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool Int_as_OT.eq f ->
    for_all f s = true -> For_all (fun x : elt => f x = true) s.
  Proof.
    intros.
    unfold For_all, for_all in *.
    rewrite forallb_forall in H0.
    intros. apply H0.
    apply elements_1 in H1.
    rewrite InA_alt in H1.
    destruct H1 as [?[[]?]].
    assumption.
  Qed.

  Lemma exists_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool Int_as_OT.eq f ->
    Exists (fun x : elt => f x = true) s -> exists_ f s = true.
  Proof.
    intros.
    unfold Exists, exists_ in *.
    rewrite existsb_exists.
    destruct H0 as [x[??]].
    exists x.
    split; auto.
    apply elements_1 in H0.
    rewrite InA_alt in H0.
    destruct H0 as [?[[]?]].
    assumption.
  Qed.

  Lemma exists_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool Int_as_OT.eq f ->
    exists_ f s = true -> Exists (fun x : elt => f x = true) s.
  Proof.
    intros.
    unfold Exists, exists_ in *.
    rewrite existsb_exists in H0.
    destruct H0 as [x[??]].
    exists x.
    split; auto.
    apply elements_2.
    apply OrdFacts.ListIn_In.
    assumption.
  Qed.

  (** One could implement [choose] with [minView]. We currenlty do not
  translate [minView], because of a call to [error] in a branch that is inaccessible
  in well-formed trees. Stretch goal: translate that and use it here.
  *)

  Definition choose : t -> option elt :=
    fun s => match elements s with
                | nil => None
                | x :: _ => Some x
              end.


  Lemma choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s.
  Proof.
    intros.
    unfold choose in *.
    destruct (elements s) eqn:?; try congruence.
    inversion H; subst.
    apply elements_2.
    rewrite Heql.
    left.
    reflexivity.
  Qed.

  Lemma choose_2 : forall s : t, choose s = None -> Empty s.
  Proof.
    intros.
    unfold choose in *.
    destruct (elements s) eqn:?; try congruence.
    intros x ?.
    apply elements_1 in H0.
    rewrite Heql in H0.
    inversion H0.
  Qed.

  Lemma choose_3 (s1 s2 : t) (x1 x2 : elt) :
    choose s1 = Some x1 -> 
    choose s2 = Some x2 ->
    Equal s1 s2         ->
    E.eq  x1 x2.
  Proof.
    destruct s1 as [s1 WF1], s2 as [s2 WF2].
    intros C1 C2 EQ.
    apply equal_1 in EQ; unfold equal in EQ; eapply reflect_iff in EQ; [|apply Eq_eq]; subst s2.
    enough (Some x1 = Some x2) as E by now inversion E.
    etransitivity; first symmetry; eassumption.
  Qed.

End IntSetFSet.

(** * Rewrite rules *)


(**
@
{-# RULES "IntSet.toAscList" [~1] forall s . toAscList s = build (\c n -> foldrFB c n s) #-}
{-# RULES "IntSet.toAscListBack" [1] foldrFB (:) [] = toAscList #-}
{-# RULES "IntSet.toDescList" [~1] forall s . toDescList s = build (\c n -> foldlFB (\xs x -> c x xs) n s) #-}
{-# RULES "IntSet.toDescListBack" [1] foldlFB (\xs x -> x : xs) [] = toDescList #-}
@
*)

Lemma rule_toAscList: forall (s : IntSet), toAscList s = build (fun _ c n => foldrFB c n s).
Proof. intros.  reflexivity. Qed.

Lemma rule_toAscListBack: foldrFB cons nil = toAscList.
Proof. intros.  reflexivity. Qed.

Lemma rule_toDescList: forall (s : IntSet), toDescList s = build (fun _ c n => foldlFB (fun xs x => c x xs) n s).
Proof. intros.  reflexivity. Qed.

Lemma rule_toDescListBack: forall (s : IntSet), foldlFB (fun xs x => x :: xs) nil = toDescList.
Proof. intros.  reflexivity. Qed.
