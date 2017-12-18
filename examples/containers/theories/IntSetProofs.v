Require Import GHC.Base.
Import Notations.
Require Import GHC.Num.
Import Notations.
Require Import Data.Bits.


Require Import Data.IntSet.Base.
Require Import Coq.FSets.FSetInterface.

Require Import Omega.

From mathcomp Require Import ssrbool ssreflect.

Local Open Scope Z_scope.

(** This should be in a separate file, but let's keep it here for
    convenience for now. *)
Section Int_And_Z.
  Variables a b : Int.

  Lemma Int_plus_is_Z_plus :
    a GHC.Num.+ b = (a + b).
  Proof. rewrite /_GHC.Num.+_. reflexivity. Qed.

  Lemma Int_minus_is_Z_minus :
    a GHC.Num.- b = (a - b).
  Proof. rewrite /_GHC.Num.-_. reflexivity. Qed.

  Lemma Int_mult_is_Z_mult :
    a GHC.Num.* b = (a * b).
  Proof. rewrite /_GHC.Num.*_. reflexivity. Qed.

  Lemma Int_lt_is_Z_lt :
    a GHC.Base.< b = (a <? b).
  Proof. rewrite /_GHC.Base.<_. reflexivity. Qed.

  Lemma Int_le_is_Z_le : 
    a GHC.Base.<= b = (a <=? b).
  Proof. rewrite /_GHC.Base.<=_. reflexivity. Qed.

  Lemma Int_gt_is_Z_gt :
    a GHC.Base.> b = (b <? a).
  Proof. rewrite /_GHC.Base.>_. reflexivity. Qed.

  Lemma Int_ge_is_Z_ge : 
    a GHC.Base.>= b = (b <=? a).
  Proof. rewrite /_GHC.Base.>=_. reflexivity. Qed.

  Lemma Int_eq_is_Z_eq : 
    a GHC.Base.== b = (Z.eqb a b).
  Proof. rewrite /_GHC.Base.==_. reflexivity. Qed.

  Lemma Int_neq_is_Z_neq : 
    a GHC.Base./= b = negb (Z.eqb a b).
  Proof. rewrite /_GHC.Base.==_. reflexivity. Qed.

  Lemma Int_is_Z : forall a : Z,
      # a = a.
  Proof. reflexivity. Qed.
  
End Int_And_Z.

Ltac rewrite_Int :=
  repeat (rewrite ?Int_plus_is_Z_plus ?Int_minus_is_Z_minus
                  ?Int_mult_is_Z_mult
                  ?Int_lt_is_Z_lt ?Int_le_is_Z_le
                  ?Int_ge_is_Z_ge ?Int_gt_is_Z_gt
                  ?Int_eq_is_Z_eq ?Int_neq_is_Z_neq 
                  ?Int_is_Z).


Lemma pos_nonneg: forall p, (0 <= N.pos p)%N. 
Proof.
  compute; congruence.
Qed.

Lemma pos_pos: forall p, (0 < N.pos p)%N. 
Proof.
  compute; congruence.
Qed.


(* exists for Z, but not for N? *)
Lemma N_pow_pos_nonneg: forall a b : N, (0 < a -> 0 < a ^ b)%N.
Proof.
  intros.
  apply N.peano_ind with (n := b); intros.
  * simpl. reflexivity.
  * rewrite N.pow_succ_r; [|apply N.le_0_l].
    eapply N.lt_le_trans. apply H0.
    replace (a ^ n)%N  with (1 * a^n)%N at 1 by (apply N.mul_1_l).
    apply N.mul_le_mono_pos_r; auto.
    rewrite <- N.le_succ_l in H.
    apply H.
Qed.

Require Import Coq.Structures.OrderedTypeEx.

Module Foo: WSfun(N_as_OT).
  Module OrdFacts := OrderedTypeFacts(N_as_OT).

  Definition isPrefix (p : Z) := Z.land p suffixBitMask = 0.

  Lemma isPrefix_suffixMask: forall p, isPrefix p -> Z.land p suffixBitMask = 0.
  Proof. intros.  apply H. Qed.

  Lemma isPrefix_prefixMask: forall p, isPrefix p -> Z.land p prefixBitMask = p.
  Proof.
    intros.
    unfold isPrefix, prefixBitMask, Bits.complement, instance_Bits_Int, complement_Int in *.
    enough (Z.lor (Z.land p suffixBitMask)  (Z.land p (Z.lnot suffixBitMask)) = p).
    + rewrite H Z.lor_0_l in H0. assumption.
    + rewrite <- Z.land_lor_distr_r.
      rewrite Z.lor_lnot_diag Z.land_m1_r. reflexivity.
  Qed.
  
  Lemma isPrefix_prefixOf: forall e, isPrefix (prefixOf e).
  Proof.
    intros.
    unfold isPrefix, prefixOf, prefixBitMask, suffixBitMask.
    rewrite /_.&._ /Bits.complement /Bits__N /instance_Bits_Int /complement_Int.
    rewrite Z.land_ones. rewrite <- Z.ldiff_land.
    rewrite Z.ldiff_ones_r.
    rewrite Z.shiftl_mul_pow2.
    apply Z_mod_mult.
    all: compute; congruence.
  Qed.
  
  Lemma prefixOf_nonneg: forall p,
    0 <= p -> 0 <= prefixOf p.
  Proof.
    intros.
    unfold isPrefix, prefixOf, prefixBitMask, suffixBitMask.
    rewrite /_.&._ /Bits.complement /Bits__N /instance_Bits_Int /complement_Int.
    rewrite Z.land_nonneg; intuition.
  Qed.

  Definition WIDTH := 64%N.
  
  Lemma suffixOf_lt_WIDTH: forall e, suffixOf e < Z.of_N WIDTH.
    intros.
    unfold suffixOf, suffixBitMask.
    rewrite /_.&._ /Bits__N /instance_Bits_Int.
    rewrite Z.land_ones.
    change (e mod 64 < 64).
    apply Z.mod_pos_bound.
    reflexivity.
    compute. congruence.
  Qed.
    
  Lemma suffixOf_noneg:  forall e, 0 <= suffixOf e.
    intros.
    unfold suffixOf, suffixBitMask.
    rewrite /_.&._ /Bits__N /instance_Bits_Int.
    rewrite Z.land_ones.
    apply Z_mod_lt.
    reflexivity.
    compute. congruence.
  Qed.

  (* We very often have to resolve non-negativity constraints *)

  Create HintDb nonneg.
  Hint Immediate N2Z.is_nonneg : nonneg.
  Hint Immediate pos_nonneg : nonneg.
  Hint Resolve prefixOf_nonneg : nonneg.
  Hint Resolve <- Z.shiftr_nonneg : nonneg.

  Ltac nonneg := auto with nonneg.

  Definition isBitMask (bm : N) :=
    (0 < bm /\ bm < 2^WIDTH)%N.
  
  Definition isBitMask_testbit:
    forall bm, isBitMask bm -> (exists i, i < WIDTH /\ N.testbit bm i = true)%N.
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
         (rewrite N.lor_spec H2; auto).
       enough (0 <> N.lor bm1 bm2)%N by 
         (destruct (N.lor bm1 bm2); auto; try congruence; apply pos_pos).
       contradict H3; rewrite <- H3.
       rewrite N.bits_0. congruence.
     split; try assumption.
     * unfold isBitMask in *; destruct H, H0.
       rewrite N.log2_lt_pow2; auto.
       rewrite N.log2_lor.
       apply N.max_lub_lt; rewrite <- N.log2_lt_pow2; auto.
   Qed.

  
  Lemma isBitMask_suffixOf: forall e, isBitMask (bitmapOf e).
    intros.
    unfold isBitMask, bitmapOf, suffixOf, suffixBitMask, bitmapOfSuffix, shiftLL.
    rewrite /_.&._ /Bits__N /instance_Bits_Int.
    unfold fromInteger, Num_Word__.
    rewrite N.shiftl_mul_pow2 N.mul_1_l.
    rewrite Z.land_ones; [|compute; congruence].
    constructor.
    * apply N_pow_pos_nonneg. reflexivity.
    * apply N.pow_lt_mono_r. reflexivity.
      change (Z.to_N (e mod 64) < Z.to_N 64)%N.
      apply Z2N.inj_lt.
      apply Z.mod_pos_bound; compute; congruence.
      compute;congruence.
      apply Z.mod_pos_bound; compute; congruence.
  Qed.

  Definition prefixed p b f g :=
    (forall i, f i = if Z.shiftr i (Z.of_N b) =? p then g i else false).
  
  Definition testBitZ p b bm i :=
    if Z.shiftr i (Z.of_N b) =? p then N.testbit bm (Z.to_N (Z.land i (Z.ones (Z.of_N b))))else false.

  Inductive Desc : IntSet -> Z -> N -> (Z -> bool) -> Prop :=
    | DescTip : forall p bm p' b f,
      0 <= p ->
      p' = Z.shiftl p (Z.of_N b) -> b = N.log2 WIDTH ->
      prefixed p b f (fun i => N.testbit bm (Z.to_N (Z.land i (Z.ones (Z.of_N b))))) ->
      isBitMask bm ->
      Desc (Tip p' bm) p b f
    | DescBin : forall s1 p1 b1 f1 s2 p2 b2 f2 p msk p' b f,
      Desc s1 p1 b1 f1 ->
      Desc s2 p2 b2 f2 ->
      (b1 < b)%N ->
      (b2 < b)%N ->
      Z.testbit p1 (Z.pred (Z.of_N b) - Z.of_N b1) = false ->
      Z.testbit p2 (Z.pred (Z.of_N b) - Z.of_N b2) = true ->
      Z.shiftr p1 (Z.of_N b - Z.of_N b1) = Z.shiftr p2 (Z.of_N b - Z.of_N b2) ->
      p = Z.shiftr p1 (Z.of_N b - Z.of_N b1) ->
      p = Z.shiftr p2 (Z.of_N b - Z.of_N b2) ->
      p' = Z.shiftl p (Z.of_N b) ->
      msk = (2^Z.pred (Z.of_N b)) -> 
      (forall i, f i = f1 i || f2 i) ->
      Desc (Bin p' msk s1 s2) p b f.
  
  Inductive WF : IntSet -> Prop :=
    | WFEmpty : WF Nil
    | WFNonEmpty : forall s p b f (HD : Desc s p b f), WF s.

  (* We are saying [N] instead of [Z] to force the invariant that
     all elements have a finite number of bits. The code actually
     works with [Z]. *)
  Definition elt := N.

  (* Well-formedness *)
  
  Definition t := {s : IntSet | WF s}.
  Definition pack (s : IntSet) (H : WF s): t := exist _ s H.

  Notation "x <-- f ;; P" :=
    (match f with
     | exist x _ => P
     end) (at level 99, f at next level, right associativity).

  Definition In_set x (s : IntSet) :=
    member x s = true.
  
  Definition In x (s' : t) :=
    s <-- s' ;;
    In_set (Z.of_N x) s.

  Definition Equal_set s s' := forall a : Z, In_set a s <-> In_set a s'.
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Definition empty : t := pack empty WFEmpty.
  Definition is_empty : t -> bool := fun s' => 
    s <-- s' ;; null s.
  
  Lemma empty_1 : Empty empty.
  Proof. unfold Empty; intros a H. inversion H. Qed.
  
  Lemma to_N_log2: forall i, Z.to_N (Z.log2 i) = N.log2 (Z.to_N i).
  Proof.
    intros.
    destruct i; try reflexivity.
    destruct p; try reflexivity.
  Qed.

  Lemma of_N_log2: forall n, Z.of_N (N.log2 n) = Z.log2 (Z.of_N n).
  Proof.
    intros.
    destruct n; try reflexivity.
    destruct p; try reflexivity.
  Qed.
  

  
  (* This is a stronger version than what’s in the standard library *)
  Lemma log2_le_lin': forall a : N, (* (0 <= a)%N -> *) (N.log2 a <= a)%N.
  Proof. intros.
    destruct a.
    reflexivity.
    apply N.log2_le_lin.
    nonneg.
  Qed.
  
  Lemma N_land_pow2_testbit:
    forall n i, negb (N.land (2 ^ i) n =? 0)%N = N.testbit n i.
  Admitted.
  
  Lemma land_pow2_eq:
    forall i b, (Z.land i (2 ^ b) =? 0) = (negb (Z.testbit i b)).
  Admitted.
  
  Lemma prefixOf_le : forall i,  prefixOf i <= i.
  Admitted.
  
  Lemma prefixOf_lt : forall i,  i < prefixOf i + 64.
  Admitted.
  
  Lemma Z_shiftl_inj:
    forall x y n,
      Z.shiftl x n = Z.shiftl y n <-> x = y.
  Admitted.
  
   Lemma land_shiftl_ones:
     forall i n,  Z.land (Z.shiftl i n) (Z.ones n) = 0.
   Admitted.
  
  Lemma Z_shiftl_injb:
    forall x y n, (Z.shiftl x n =? Z.shiftl y n) = (x =? y).
  Proof.
    intros.
    destruct (Z.eqb_spec (Z.shiftl x n) (Z.shiftl y n)),
             (Z.eqb_spec x y); auto; try congruence; exfalso.
    apply Z_shiftl_inj in e. congruence.
  Qed.


  Lemma prefixOf_eq_shiftr:
    forall i p, 
      (prefixOf i =? Z.shiftl p (Z.of_N (N.log2 WIDTH))) =
      (Z.shiftr i (Z.of_N (N.log2 WIDTH)) =? p).
   Proof.
     intros.
     unfold prefixOf, prefixBitMask, suffixBitMask.
     unfold Bits.complement, instance_Bits_Int, complement_Int.
     rewrite /_.&._ /Bits__N /instance_Bits_Int.
     rewrite <- Z.ldiff_land.
     rewrite Z.ldiff_ones_r.
     replace (Z.of_N (N.log2 WIDTH)) with 6 by reflexivity.

     rewrite Z_shiftl_injb.
     reflexivity.
     compute; congruence.
   Qed.
   

   Lemma Desc_outside:
     forall {s p b f i}, Desc s p b f -> Z.shiftr i (Z.of_N b) =? p = false -> f i = false.
   Proof.
     intros ????? HD Houtside.
     induction HD;subst.
     * rewrite H2.
       rewrite Houtside.
       reflexivity.
     * rewrite H8.
       rewrite orb_false_iff. split.
       + apply IHHD1. clear IHHD1 IHHD2.
         apply Z.eqb_neq in Houtside.
         apply Z.eqb_neq.
         contradict Houtside.
         replace (Z.of_N b) with ((Z.of_N b1) + (Z.of_N b - Z.of_N b1)) at 1 by omega.
         rewrite <- Z.shiftr_shiftr.
         rewrite Houtside. reflexivity.
         enough (Z.of_N b1 < Z.of_N b) by omega.
         apply N2Z.inj_lt. assumption.
       + apply IHHD2. clear IHHD1 IHHD2.
         apply Z.eqb_neq in Houtside.
         apply Z.eqb_neq.
         contradict Houtside.
         replace (Z.of_N b) with ((Z.of_N b2) + (Z.of_N b - Z.of_N b2)) at 1 by omega.
         rewrite <- Z.shiftr_shiftr.
         rewrite Houtside. congruence.
         enough (Z.of_N b2 < Z.of_N b) by omega.
         apply N2Z.inj_lt. assumption.
   Qed.

    Lemma Desc_prefix_nonneg:
      forall {s p b f}, Desc s p b f -> 0 <= p.
    Admitted.
    
    Hint Extern 1 (0 <= ?p) => 
       (try match goal with [ H : Desc _ p _ _  |- _ ] => apply (Desc_prefix_nonneg H) end)
       : nonneg.


    Lemma Desc_neg_false:
     forall {s p b f i}, Desc s p b f -> ~ (0 <= i) -> f i = false.
    Proof.
      intros.
      apply (Desc_outside H).
      rewrite Z.eqb_neq.
      contradict H0.
      rewrite <- (Z.shiftr_nonneg i (Z.of_N b)).
      rewrite H0.
      nonneg.
    Qed.
   
   Lemma nomatch_spec:
      forall i p b,
      (0 < b)%N ->
      nomatch i (Z.shiftl p (Z.of_N b)) (2 ^ Z.pred (Z.of_N b)) =
      negb (Z.shiftr i (Z.of_N b) =? p).
   Proof.
     intros.
     unfold nomatch, zero.
     rewrite /_GHC.Base./=_ /_GHC.Base.==_ /Eq_Char___ /Eq_Integer___ /op_zsze____ /op_zeze____.
     rewrite /_.&._ /Bits__N /instance_Bits_Int.
     unfold mask.
     rewrite Z.log2_pow2.
     rewrite Z.succ_pred.
     f_equal.
     rewrite Z.ldiff_ones_r.
     rewrite Z_shiftl_injb.
     reflexivity.
     nonneg.
     enough (0 < Z.of_N b) by omega.
     replace 0 with (Z.of_N 0%N) by reflexivity.
     apply N2Z.inj_lt. assumption.
   Qed.
   
   Lemma zero_spec:
     forall i b,
      zero i (2 ^ Z.pred (Z.of_N b)) = negb (Z.testbit i (Z.pred (Z.of_N b))).
   Proof.
     intros.
     apply land_pow2_eq.
   Qed.

   Lemma member_spec:
     forall {s p b f i}, Desc s p b f -> member i s = f i.
   Proof.
     intros ????? HD.
     induction HD; subst.
     * simpl.
       set (p' := Z.shiftl p (Z.of_N (N.log2 WIDTH))).
       change (((prefixOf i == p') && ((bitmapOf i .&.bm) /= #0)) = f i).

       rewrite /_GHC.Base.==_ /Eq_Integer___ /op_zeze____.
       rewrite /_GHC.Base./=_ /Eq_Char___ /op_zsze____.
       unfold bitmapOf, bitmapOfSuffix, suffixOf, suffixBitMask, shiftLL.
       rewrite /_.&._ /Bits__N /instance_Bits_Int.
       unfold fromInteger, Num_Word__.
       rewrite N.shiftl_mul_pow2 N.mul_1_l.
       rewrite N_land_pow2_testbit.
       
       subst p'; rewrite prefixOf_eq_shiftr.
       specialize (H2 i); rewrite H2; clear H2.
       destruct (Z.eqb_spec (Z.shiftr i (Z.of_N (N.log2 WIDTH))) p); simpl; auto.
     * simpl.
       rewrite H8. clear H8.
       rewrite nomatch_spec.
       rewrite zero_spec.
       match goal with [ |- context [?x =? ?y]] => destruct (Z.eqb_spec x y) end; simpl.
       * destruct (Z.testbit i (Z.pred (Z.of_N b))) eqn:Htestbit; simpl.
         * enough (f1 i = false) as Hf1 by (rewrite Hf1 IHHD2; reflexivity).
           apply (Desc_outside HD1).
           rewrite Z.eqb_neq.
           rewrite <- Z.bits_inj_iff.
           intro Htb; specialize (Htb (Z.pred (Z.of_N b) - Z.of_N b1)).
           rewrite Z.shiftr_spec in Htb.
           replace (Z.pred (Z.of_N b) - Z.of_N b1 + Z.of_N b1) with (Z.pred (Z.of_N b)) in Htb by omega.
           rewrite Htestbit in Htb.
           congruence.
           enough (Z.of_N b1 < Z.of_N b) by omega.
           apply N2Z.inj_lt. assumption.

         * enough (f2 i = false) as Hf2 by (rewrite Hf2 IHHD1 orb_false_r; reflexivity).
           apply (Desc_outside HD2).
           rewrite Z.eqb_neq.
           rewrite <- Z.bits_inj_iff.
           intro Htb; specialize (Htb (Z.pred (Z.of_N b) - Z.of_N b2)).
           rewrite Z.shiftr_spec in Htb.
           replace (Z.pred (Z.of_N b) - Z.of_N b2 + Z.of_N b2) with (Z.pred (Z.of_N b)) in Htb by omega.
           rewrite Htestbit in Htb.
           congruence.
           enough (Z.of_N b2 < Z.of_N b) by omega.
           apply N2Z.inj_lt. assumption.

       * enough (f1 i = false /\ f2 i = false); try split.
         destruct H4 as [Hf1 Hf2]; rewrite Hf1 Hf2; reflexivity.
         + apply (Desc_outside HD1).
           rewrite Z.eqb_neq.
           contradict n.
           replace (Z.of_N b) with ((Z.of_N b1) + (Z.of_N b - Z.of_N b1)) at 1 by omega.
           rewrite <- Z.shiftr_shiftr.
           rewrite n. reflexivity.
           enough (Z.of_N b1 < Z.of_N b) by omega.
           apply N2Z.inj_lt. assumption.

         + apply (Desc_outside HD2).
           rewrite Z.eqb_neq.
           contradict n.
           replace (Z.of_N b) with ((Z.of_N b2) + (Z.of_N b - Z.of_N b2)) at 1 by omega.
           rewrite <- Z.shiftr_shiftr.
           rewrite n. congruence.
           enough (Z.of_N b2 < Z.of_N b) by omega.
           apply N2Z.inj_lt. assumption.

     apply (N.le_lt_trans _ b1); auto. destruct b1; compute; congruence.
   Qed.


   Lemma Desc_some_f:
     forall {s p b f}, Desc s p b f -> exists i, f i = true.
   Proof.
   intros ???? HD.
   induction HD; subst.
   + destruct (isBitMask_testbit _ H3) as [j[??]].
     set (i := (Z.lor (Z.shiftl p 6) (Z.of_N j))).
     exists i.

     assert (Z.log2 (Z.of_N j) < 6).
     - rewrite <- of_N_log2.
       change (Z.of_N (N.log2 j) < Z.of_N 6%N).
       apply N2Z.inj_lt.
       destruct (N.lt_decidable 0%N j).
       + apply N.log2_lt_pow2; assumption.
       + enough (j = 0)%N by (subst; compute; congruence).
         destruct j; auto; contradict H4. apply pos_pos.

    rewrite  H2; clear H2.
    replace ((Z.of_N (N.log2 WIDTH))) with 6 by reflexivity.
    replace (Z.shiftr i 6) with p.
    rewrite (Z.eqb_refl).
    replace (Z.land i (Z.ones 6)) with (Z.of_N j).
    rewrite N2Z.id.
    assumption.
    
    * subst i.
      rewrite Z.land_lor_distr_l.
      rewrite land_shiftl_ones.
      rewrite Z.lor_0_l.
      rewrite Z.land_ones_low. reflexivity.
      nonneg.
      assumption.
    * symmetry.
      subst i.
      rewrite Z.shiftr_lor.
      replace ((Z.shiftr (Z.of_N j) 6)) with 0.
      rewrite Z.lor_0_r.
      rewrite Z.shiftr_shiftl_l.
      reflexivity.
      compute; congruence.
      symmetry.
      apply Z.shiftr_eq_0; auto.
      nonneg.
  + destruct IHHD1  as [j?].
    exists j.
    rewrite H8.
    rewrite H4.
    reflexivity.
   Qed.

   Lemma Desc_has_member: 
     forall {s p b f}, Desc s p b f -> exists i, 0 <= i /\ member i s = true.
   Proof.
     intros ???? HD.
     destruct (Desc_some_f HD) as [j?].
     exists j.
     rewrite (member_spec HD). intuition.
     destruct (Z.leb_spec 0 j); auto.
     contradict H.
     rewrite  (Desc_neg_false HD); try congruence.
     apply Zlt_not_le. assumption.
   Qed.

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    intros. unfold Empty, In, In_set, is_empty in *. destruct s. simpl.
    induction w.
    * auto.
    * destruct (Desc_has_member  HD).
      specialize (H (Z.to_N x)).
      rewrite Z2N.id in H; try assumption; intuition.
  Qed.
  
  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof. move=>s. rewrite /Empty /In. elim s=>[s']. elim s'=>//. Qed.

  Lemma Tip_Desc:
    forall p p' bm, isBitMask bm ->
      0 <= p ->
      p' = (Z.shiftl p 6) ->
      Desc (Tip p' bm) p (N.log2 WIDTH)
           (fun i => testBitZ p 6%N bm i).
  Proof.
    intros; subst.
    apply DescTip; auto.
    intro i. unfold testBitZ.
    reflexivity.
  Qed.
  
  Lemma Tip_WF:
    forall p bm, 0 <= p -> isPrefix p -> isBitMask bm -> WF (Tip p bm).
  Proof.
    intros ?? Hnonneg Hp Hbm.
    eapply WFNonEmpty.
    apply Tip_Desc with (p := Z.shiftr p 6); auto. 
    nonneg.
    clear Hbm bm.
    unfold isPrefix in *.
    rewrite <- Z.ldiff_ones_r.
    unfold suffixBitMask in *.
    symmetry.
    rewrite Z.ldiff_land.
    enough (Z.lor (Z.land p (Z.lnot (Z.ones 6))) (Z.land p (Z.ones 6)) = p).
    rewrite Hp in H.
    rewrite Z.lor_0_r in H.
    assumption.
    rewrite <- Z.land_lor_distr_r.
    rewrite Z.lor_lnot_diag.
    apply Z.land_m1_r.
    compute; congruence.
  Qed.

  Definition singleton : elt -> t.
    refine (fun e => pack (singleton (Z.of_N e)) _).
    unfold singleton, Prim.seq.
    apply Tip_WF.
    * nonneg.
    * apply isPrefix_prefixOf.
    * apply isBitMask_suffixOf.
  Qed.

  Lemma link_Desc:
      forall p1' s1 p1 b1 f1 s2 p2' p2 b2 f2 b f,
      Desc s1 p1 b1 f1 ->
      Desc s2 p2 b2 f2 ->
      (b1 < b)%N ->
      (b2 < b)%N ->
      p1' = Z.shiftl p1 (Z.of_N b1) ->
      p2' = Z.shiftl p2 (Z.of_N b2) ->
      b = Z.to_N (Z.succ (Z.log2 (Z.lxor (Z.shiftl p1 (Z.of_N b1)) (Z.shiftl p2 (Z.of_N b2))))) ->
      Z.testbit p1 (Z.pred (Z.of_N b) - Z.of_N b1) <> Z.testbit p2 (Z.pred (Z.of_N b) - Z.of_N b2) ->
      Z.shiftr p1 (Z.of_N b - Z.of_N b1) = Z.shiftr p2 (Z.of_N b - Z.of_N b2) ->
      (forall i, f i = f1 i || f2 i) ->
    Desc (link p1' s1 p2' s2)
         (Z.shiftr p1 (Z.of_N b - Z.of_N b1)) b f.
  Proof.
    intros.
    
    assert (0 <= Z.pred (Z.of_N b)).
    + enough (0 < Z.of_N b) by omega.
      enough (0 <= Z.of_N b1 /\ Z.of_N b1 < Z.of_N b) by omega.
      split.
      apply N2Z.is_nonneg.
      apply N2Z.inj_lt. assumption.


    unfold link.
    subst p1' p2'.
    unfold zero, branchMask, mask.
    rewrite land_pow2_eq.
    replace (Z.log2 (Z.lxor (Z.shiftl p1 (Z.of_N b1)) (Z.shiftl p2 (Z.of_N b2))))
        with (Z.pred (Z.of_N b)).
    rewrite Z.shiftl_spec.

    destruct (Z.testbit p1 (Z.pred (Z.of_N b) - Z.of_N b1)) eqn:Htb; simpl.
    * eapply DescBin.
      apply H0. apply H.
      all:try congruence.
      destruct (Z.testbit p2 (Z.pred (Z.of_N b) - Z.of_N b2)); congruence.
      rewrite Z.log2_pow2.
      rewrite Z.ldiff_ones_r.
      rewrite Z.shiftr_shiftl_r. f_equal. f_equal. omega. omega.
      apply N2Z.is_nonneg.
      rewrite Z.succ_pred. apply N2Z.is_nonneg.
      assumption.
      intro i. rewrite H8. apply orb_comm.
    * eapply DescBin.
      apply H. apply H0.
      all:try congruence.
      destruct (Z.testbit p2 (Z.pred (Z.of_N b) - Z.of_N b2)); congruence.
      rewrite Z.log2_pow2.
      rewrite Z.ldiff_ones_r.
      rewrite Z.shiftr_shiftl_r. f_equal. f_equal. omega. omega.
      apply N2Z.is_nonneg.
      rewrite Z.succ_pred. apply N2Z.is_nonneg.
      assumption.

    (* Have to show that b is actually the right one *)
    symmetry.
    subst b.
    rewrite Z2N.id. rewrite Z.pred_succ. reflexivity.
    apply  Z.le_le_succ_r; apply Z.log2_nonneg.
  Qed.
 
  Lemma isPrefix_shiftl_shiftr:
     forall p, isPrefix p -> p = Z.shiftl (Z.shiftr p 6) 6.
  Proof.
    intros.
    rewrite <- Z.ldiff_ones_r.
    rewrite Z.ldiff_land.
    symmetry.
    apply isPrefix_prefixMask. assumption.
    omega.
  Qed.


  Hint Resolve OMEGA2 : nonneg.
  Hint Resolve Z.log2_nonneg : nonneg.
  Hint Extern 0 => try omega : nonneg.

  Lemma insertBM_WF:
    forall p bm s,
    0 <= p -> isPrefix p -> isBitMask bm -> WF s -> WF (insertBM p bm s).
  Proof.
    intros ??? Hnonneg Hp Hbm HWF.
    destruct HWF.
    * simpl. unfold Prim.seq.
      apply Tip_WF; auto.
    * induction HD; subst.
      + unfold insertBM, Prim.seq.
        unfold GHC.Base.op_zeze__, Eq_Integer___, op_zeze____.
        destruct (Z.eqb_spec (Z.shiftl p0 (Z.of_N (N.log2 WIDTH))) p); subst.
        * apply Tip_WF; auto.
          apply isBitMask_lor; auto.
        * (* calling link now *)
          eapply WFNonEmpty.
          eapply link_Desc. 7:reflexivity.
          - apply Tip_Desc with (p := Z.shiftr p 6); auto.
            nonneg.
            apply isPrefix_shiftl_shiftr; assumption.
          - apply Tip_Desc with (p := p0); auto.
            rewrite <- Z.shiftl_lxor.
            rewrite Z.log2_shiftl.
            replace (N.log2 WIDTH) with (Z.to_N (Z.of_N (N.log2 WIDTH))) at 1 by reflexivity.
            apply Z2N.inj_lt.
            nonneg.
            auto 8 with nonneg.
            apply OMEGA2. nonneg. nonneg.
            rewrite (isPrefix_shiftl_shiftr _ Hp) in n.
            replace (Z.of_N (N.log2 WIDTH)) with 6 in * by reflexivity.
            rewrite -> Z_shiftl_inj in n.
            enough (0 <= Z.log2 (Z.lxor (Z.shiftr p 6) p0)) by omega.
            apply Z.log2_nonneg.
            admit. (* This cannot be shown *)
            admit.
            admit.
            apply isPrefix_shiftl_shiftr; assumption.
            reflexivity.
            admit.
            admit.
            intro i. reflexivity.
      + simpl. unfold Prim.seq.
        admit.
  Admitted.
  
  Definition add (e: elt) (s': t) : t.
    refine (s <-- s' ;;
            pack (insert (Z.of_N e) s) _).
    unfold insert, Prim.seq.
    apply insertBM_WF.
    nonneg.
    apply isPrefix_prefixOf.
    apply isBitMask_suffixOf.
    assumption.
  Qed.   
  
  Definition remove : elt -> t -> t. Admitted.
  Definition union : t -> t -> t. Admitted.
  Definition inter : t -> t -> t. Admitted.
  Definition diff : t -> t -> t. Admitted.
    
  Definition equal : t -> t -> bool :=
    fun ws ws' => s <-- ws ;;
               s' <-- ws' ;;
               s == s'.
  
  Definition subset : t -> t -> bool :=
    fun ws ws' => s <-- ws ;;
               s' <-- ws' ;;
               isSubsetOf s s'.

  Definition eq_set : IntSet -> IntSet -> Prop := Equal_set.
  Definition eq : t -> t -> Prop := Equal.
  Definition eq_dec : forall s s' : t, {eq s s'} + {~ eq s s'}. Admitted.

  Lemma eq_set_refl : forall s, eq_set s s.
  Proof. intros; constructor; auto. Qed.
    
  Lemma eq_refl : forall s : t, eq s s.
  Proof. destruct s. unfold eq. unfold Equal. intro. apply eq_set_refl. Qed.

  Lemma eq_set_sym : forall s s', eq_set s s' -> eq_set s' s.
  Proof. rewrite /eq_set /Equal_set; symmetry; auto. Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. destruct s; destruct s'; 
    unfold eq, Equal in *. intros. rewrite H. intuition. Qed.
    
  Lemma eq_set_trans :
    forall s s' s'', eq_set s s' -> eq_set s' s'' -> eq_set s s''.
  Proof.
    rewrite /eq_set /Equal_set; intros s s' s'' H1 H2 a.
    apply (iff_trans (H1 a) (H2 a)).
  Qed.
  
  Lemma eq_trans :
    forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
    destruct s; destruct s'; destruct s''; simpl.
    unfold eq, Equal. intros ???. rewrite H H0. reflexivity.
  Qed.


  Definition fold : forall A : Type, (elt -> A -> A) -> t -> A -> A. Admitted.
  Definition for_all : (elt -> bool) -> t -> bool. Admitted.
  Definition exists_ : (elt -> bool) -> t -> bool. Admitted.
  Definition filter : (elt -> bool) -> t -> t. Admitted.
  Definition partition : (elt -> bool) -> t -> t * t. Admitted.
  Definition cardinal : t -> nat. Admitted.
  Definition elements : t -> list elt. Admitted.
  Definition choose : t -> option elt. Admitted.
  
  Lemma In_1 :
    forall (s : t) (x y : elt), N.eq x y -> In x s -> In y s.
  Admitted.
  
  Definition mem : elt -> t -> bool := fun e s' =>
   s <-- s' ;; member (Z.of_N e) s.


  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
    
  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
  
  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true. Admitted.
  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'. Admitted.
  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true. Admitted.
  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'. Admitted.
  
  Lemma add_1 :
    forall (s : t) (x y : elt), N.eq x y -> In y (add x s). Admitted.
  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s). Admitted.
  Lemma add_3 :
    forall (s : t) (x y : elt), ~ N.eq x y -> In y (add x s) -> In y s. Admitted.
  Lemma remove_1 :
    forall (s : t) (x y : elt), N.eq x y -> ~ In y (remove x s). Admitted.
  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ N.eq x y -> In y s -> In y (remove x s). Admitted.
  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s. Admitted.

  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> N.eq x y.
  Admitted.
        
  Lemma singleton_2 :
    forall x y : elt, N.eq x y -> In y (singleton x).
  Admitted.
      
  Lemma union_1 :
    forall (s s' : t) (x : elt), In x (union s s') -> In x s \/ In x s'. Admitted.
  Lemma union_2 :
    forall (s s' : t) (x : elt), In x s -> In x (union s s'). Admitted.
  Lemma union_3 :
    forall (s s' : t) (x : elt), In x s' -> In x (union s s'). Admitted.
  Lemma inter_1 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s. Admitted.
  Lemma inter_2 :
    forall (s s' : t) (x : elt), In x (inter s s') -> In x s'. Admitted.
  Lemma inter_3 :
    forall (s s' : t) (x : elt), In x s -> In x s' -> In x (inter s s'). Admitted.
  Lemma diff_1 :
    forall (s s' : t) (x : elt), In x (diff s s') -> In x s. Admitted.
  Lemma diff_2 :
    forall (s s' : t) (x : elt), In x (diff s s') -> ~ In x s'. Admitted.
  Lemma diff_3 :
    forall (s s' : t) (x : elt), In x s -> ~ In x s' -> In x (diff s s'). Admitted.
  Lemma fold_1 :
    forall (s : t) (A : Type) (i : A) (f : elt -> A -> A),
    fold A f s i =
    fold_left (fun (a : A) (e : elt) => f e a) (elements s) i. Admitted.
  Lemma cardinal_1 : forall s : t, cardinal s = length (elements s). Admitted.
  Lemma filter_1 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool N.eq f -> In x (filter f s) -> In x s. Admitted.
  Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool N.eq f -> In x (filter f s) -> f x = true. Admitted.
  Lemma filter_3 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool N.eq f -> In x s -> f x = true -> In x (filter f s). Admitted.
  Lemma for_all_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    For_all (fun x : elt => f x = true) s -> for_all f s = true. Admitted.
  Lemma for_all_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    for_all f s = true -> For_all (fun x : elt => f x = true) s. Admitted.
  Lemma exists_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    Exists (fun x : elt => f x = true) s -> exists_ f s = true. Admitted.
  Lemma exists_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    exists_ f s = true -> Exists (fun x : elt => f x = true) s. Admitted.
  Lemma partition_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f -> Equal (fst (partition f s)) (filter f s). Admitted.
  Lemma partition_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool N.eq f ->
    Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s). Admitted.
  Lemma elements_1 :
    forall (s : t) (x : elt), In x s -> InA N.eq x (elements s). Admitted.
  Lemma elements_2 :
    forall (s : t) (x : elt), InA N.eq x (elements s) -> In x s. Admitted.
  Lemma elements_3w : forall s : t, NoDupA N.eq (elements s). Admitted.
  Lemma choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s. Admitted.
  Lemma choose_2 : forall s : t, choose s = None -> Empty s. Admitted.

End Foo.