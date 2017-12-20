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


  
Lemma lor_ones_ones: forall b1 b2, Z.lor (Z.ones b1) (Z.ones b2) = Z.ones (Z.max b1 b2).
Admitted.
  

(* We very often have to resolve non-negativity constraints *)

Lemma succ_nonneg: forall n, 0 <= n -> 0 <= Z.succ n.
Proof. intros. omega. Qed.

    
Lemma ones_nonneg: forall n, 0 <= n -> 0 <= Z.ones n.
Proof.
  intros.
  unfold Z.ones.
  rewrite -> Z.shiftl_mul_pow2 by assumption.
  rewrite Z.mul_1_l.
  rewrite <- Z.lt_le_pred.
  apply Z.pow_pos_nonneg; auto.
  omega.
Qed.

Lemma log2_ones: forall n, 0 < n -> Z.log2 (Z.ones n) = Z.pred n.
  intros.
  unfold Z.ones.
  rewrite -> Z.shiftl_mul_pow2 by omega.
  rewrite Z.mul_1_l.
  apply Z.log2_pred_pow2.
  assumption.
Qed.

Create HintDb nonneg.
Hint Immediate N2Z.is_nonneg : nonneg.
Hint Immediate pos_nonneg : nonneg.
Hint Resolve N.le_0_l : nonneg.
Hint Resolve Z.log2_nonneg : nonneg.
Hint Resolve ones_nonneg : nonneg.
Hint Resolve succ_nonneg : nonneg.
Hint Resolve <- Z.shiftl_nonneg : nonneg.
Hint Resolve <- Z.shiftr_nonneg : nonneg.
Hint Extern 1 (0 <= Z.succ (Z.pred (Z.of_N _))) => rewrite Z.succ_pred : nonneg.
Hint Resolve <- Z.lxor_nonneg : nonneg.
Hint Extern 0 => omega : nonneg.

Ltac nonneg := solve [auto with nonneg].

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
Proof.
  intros.
  destruct (N.testbit n i) eqn:Htb.
  * rewrite negb_true_iff.
    rewrite N.eqb_neq.
    contradict Htb.
    assert (N.testbit (N.land (2^i)%N n) i = false).
     by (rewrite Htb; apply N.bits_0).
    rewrite N.land_spec in H. rewrite N.pow2_bits_true in H.
    simpl in H. congruence.
  * rewrite negb_false_iff.
    rewrite N.eqb_eq.
    apply N.bits_inj.
    intro j.
    rewrite N.land_spec.
    rewrite N.pow2_bits_eqb.
    destruct (N.eqb_spec i j); subst; intuition.
Qed.

Lemma land_pow2_eq:
  forall i b, 0 <= b -> (Z.land i (2 ^ b) =? 0) = (negb (Z.testbit i b)).
Proof.
  intros ?? Hnonneg.
  destruct (Z.testbit i b) eqn:Htb; simpl.
  * rewrite Z.eqb_neq.
    contradict Htb.
    assert (Z.testbit (Z.land i (2^b)) b = false)
     by (rewrite Htb; apply Z.bits_0).
    rewrite Z.land_spec in H. rewrite Z.pow2_bits_true in H.
    rewrite andb_true_r in H.
    simpl in H. congruence.
    nonneg.
  * rewrite Z.eqb_eq.
    apply Z.bits_inj'.
    intros j ?.
    rewrite  Z.bits_0.
    rewrite Z.land_spec.
    rewrite Z.pow2_bits_eqb.
    destruct (Z.eqb_spec b j).
    * subst. rewrite Htb. reflexivity.
    * rewrite andb_false_r.  reflexivity.
    nonneg.
Qed.

Lemma shiftr_eq_ldiff :
forall n m b,
    0 <= b ->
    Z.ldiff n (Z.ones b) = Z.ldiff m (Z.ones b) ->
    Z.shiftr n b = Z.shiftr m b.
Proof.
  intros.
    * apply Z.bits_inj'.
      intros i ?.
      rewrite -> !Z.shiftr_spec by assumption.
      apply Z.bits_inj_iff in H0.
      specialize (H0 (i + b)).
      rewrite -> !Z.ldiff_spec in H0.
      rewrite -> !Z.ones_spec_high in H0.
      simpl in *.
      rewrite -> ! andb_true_r in H0.
      assumption.
      omega.
Qed.


Lemma Z_shiftl_inj:
  forall x y n,
    0 <= n ->
    Z.shiftl x n = Z.shiftl y n <-> x = y.
Proof.
  intros; split; intro.
  * apply Z.bits_inj'.
    intros i ?.
    apply Z.bits_inj_iff in H0.
    specialize (H0 (i + n)).
    do 2 rewrite -> Z.shiftl_spec in H0 by omega.
    replace (i + n - n) with i in H0 by omega.
    assumption.
  * apply Z.bits_inj'.
    intros i ?.
    apply Z.bits_inj_iff in H0.
    specialize (H0 (i - n)).
    do 2 rewrite -> Z.shiftl_spec by omega.
    assumption.
 Qed.
 
Lemma Z_shiftl_injb:
  forall x y n, 0 <= n -> (Z.shiftl x n =? Z.shiftl y n) = (x =? y).
Proof.
  intros.
  destruct (Z.eqb_spec (Z.shiftl x n) (Z.shiftl y n)),
           (Z.eqb_spec x y); auto; try congruence; exfalso.
  apply Z_shiftl_inj in e; auto.
Qed.

 Lemma land_shiftl_ones:
   forall i n, 0 <= n -> Z.land (Z.shiftl i n) (Z.ones n) = 0.
 Proof.
   intros.
   apply Z.bits_inj'.
   intros j ?.
   rewrite Z.land_spec.
   rewrite -> Z.shiftl_spec by nonneg.
   rewrite Z.bits_0. rewrite andb_false_iff.
   destruct (Z.ltb_spec j n).
   * left. apply Z.testbit_neg_r. omega.
   * right. apply Z.ones_spec_high. omega.
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
  Hint Resolve prefixOf_nonneg : nonneg.

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

    
  (* A range is described by a prefix and a shift width *)
  Definition range := (Z * N)%type.
  Definition rBits : range -> N := snd.
  
  (* Operatons on ranges: We can get its prefix and it mask
     (this is what we actually find in the data type) *)
  Definition rPrefix : range -> Z :=
     fun '(p,b) => Z.shiftl p (Z.of_N b).
  Definition rMask   : range -> Z :=
     fun '(p,b) => 2^(Z.of_N b).
  
  (* This is only needed because we restrict ourselves
     to positive numbers *)
  Definition rNonneg : range -> Prop :=
    fun '(p,b) =>  0 <= p.
    
  (* We can do various queries on segments *)
  Definition inRange : Z -> range -> bool :=
    fun n '(p,b) => Z.shiftr n (Z.of_N b) =? p.
  (* Segments either disjoint or contained in each other *)
  Definition isSubrange : range -> range -> bool :=
    fun r1 r2 => inRange (rPrefix r2) r1 && (rBits r2 <=? rBits r1)%N.
  Definition rangeDisjoint : range -> range -> bool :=
    fun r1 r2 => negb (isSubrange r1 r2 || isSubrange r2 r1).
  
  (* most signifiant differing bit *)
  Definition msDiffBit : Z -> Z -> N :=
    fun n m => Z.to_N (Z.succ (Z.log2 (Z.lxor n m))).
  
  (* The smallest range that encompasses two (disjoint) ranges *)
  Definition commonRangeDisj : range -> range -> range :=
    fun r1 r2 =>
      let b := msDiffBit (rPrefix r1) (rPrefix r2) in
      (Z.shiftr (rPrefix r1) (Z.of_N b) , b).

  Definition eqOnRange r f g :=
    (forall i, f i = if inRange i r then g i else false).
  
  Definition bitmapInRange r bm i :=
    if inRange i r then N.testbit bm (Z.to_N (Z.land i (Z.ones (Z.of_N (rBits r)))))
                   else false.
    
  (* Lemmas about range *)
  
  Lemma rangeDisjoint_sym: forall r1 r2,
    rangeDisjoint r1 r2 = rangeDisjoint r2 r1.
  Proof.
    intros.
    unfold rangeDisjoint.
    rewrite orb_comm.
    reflexivity.
  Qed.
   
 Lemma msDiffBit_sym: forall p1 p2,
    msDiffBit p1 p2 = msDiffBit p2 p1.
  Proof.
    intros.
    unfold msDiffBit.
    rewrite Z.lxor_comm.
    reflexivity.
  Qed.

  Section msDiffBit.
    Variable p1 p2 : Z.
    Variable (Hnonneg1 : 0 <= p1).
    Variable (Hnonneg2 : 0 <= p2).
    Variable (Hne : p1 <> p2).
    
    Local Lemma lxor_pos: 0 < Z.lxor p1 p2.
    Proof.
      assert (0 <= Z.lxor p1 p2) by nonneg.
      enough (Z.lxor p1 p2 <> 0) by omega.
      rewrite Z.lxor_eq_0_iff.
      assumption.
    Qed.
    
    Lemma msDiffBit_Different:
          Z.testbit p1 (Z.pred (Z.of_N (msDiffBit p1 p2)))
       <> Z.testbit p2 (Z.pred (Z.of_N (msDiffBit p1 p2))).
    Proof.
      match goal with [ |- Z.testbit ?x ?b <> Z.testbit ?y ?b] =>
        enough (xorb (Z.testbit x b) (Z.testbit y b))
        by (destruct (Z.testbit x b), (Z.testbit y b); simpl in *; congruence) end.
      rewrite <- Z.lxor_spec.
      unfold msDiffBit.
      rewrite -> Z2N.id by nonneg.
      rewrite -> Z.pred_succ.
      apply Z.bit_log2.
      apply lxor_pos.
    Qed.

    Lemma msDiffBit_Same:
      forall j,  Z.of_N (msDiffBit p1 p2) <= j ->
      Z.testbit p1 j = Z.testbit p2 j.
    Proof.
      intros.
      match goal with [ |- Z.testbit ?x ?b = Z.testbit ?y ?b] =>
        enough (xorb (Z.testbit x b) (Z.testbit y b) = false)
        by (destruct (Z.testbit x b), (Z.testbit y b); simpl in *; congruence) end.
      rewrite <- Z.lxor_spec.
      unfold msDiffBit in H.
      rewrite -> Z2N.id in H by nonneg.
      apply Z.bits_above_log2; try nonneg.
    Qed.

    Lemma msDiffBit_shiftr_same:
          Z.shiftr p1 (Z.of_N (msDiffBit p1 p2))
       =  Z.shiftr p2 (Z.of_N (msDiffBit p1 p2)).
    Proof.
      apply Z.bits_inj_iff'. intros j ?.
      rewrite -> !Z.shiftr_spec by nonneg.
      apply msDiffBit_Same.
      omega.
    Qed.
  End msDiffBit.
   
  Lemma msDiffBit_larger_tmp:
    forall r1 r2,
      rNonneg r1 -> rNonneg r2 -> 
      rangeDisjoint r1 r2 ->
      (rBits r2 <= rBits r1)%N ->
      (msDiffBit (rPrefix r1) (rPrefix r2) <= rBits r1)%N ->
      False.
  Proof.
    intros.
    * assert (inRange (rPrefix r2) r1 = true).
        destruct r1 as [p1 b1], r2 as [p2 b2].
        unfold inRange, rPrefix, rBits, rNonneg,  snd in *.
        rewrite -> N2Z.inj_le in H2, H3.
        apply Z.eqb_eq.
        symmetry.
        apply Z.bits_inj_iff'. intros j ?.
        replace j with ((j + Z.of_N b1) - Z.of_N b1) by omega.
        rewrite <- Z.shiftl_spec by (apply OMEGA2; nonneg).
        rewrite -> msDiffBit_Same with (p2 := (Z.shiftl p2 (Z.of_N b2))) by nonneg.
        rewrite -> !Z.shiftl_spec by (apply OMEGA2; nonneg).
        rewrite -> !Z.shiftr_spec by nonneg.
        rewrite -> !Z.shiftl_spec by (apply OMEGA2; nonneg).
        f_equal. omega.

      unfold rangeDisjoint in H1.
      apply negb_true_iff in H1.
      rewrite -> orb_false_iff in H1.
      unfold isSubrange in *.
      rewrite -> !andb_false_iff in H1.
      rewrite -> !N.leb_nle in H1.
      intuition try congruence.
  Qed.
  
    Lemma msDiffBit_larger:
    forall r1 r2,
      rNonneg r1 -> rNonneg r2 -> 
      rangeDisjoint r1 r2 ->
      (N.max (rBits r1) (rBits r2) < msDiffBit (rPrefix r1) (rPrefix r2))%N.
    Proof.
      intros.
      destruct (N.leb_spec (rBits r1) (rBits r2)).
      * rewrite -> N.max_r by assumption.
        apply N.nle_gt.
        intro.
        rewrite rangeDisjoint_sym in H1.
        rewrite msDiffBit_sym in H3.
        apply (msDiffBit_larger_tmp r2 r1 H0 H H1 H2 H3).
      * apply N.lt_le_incl in H2.
        rewrite -> N.max_l by assumption.
        apply N.nle_gt.
        intro.
        apply (msDiffBit_larger_tmp r1 r2 H H0 H1 H2 H3).
  Qed.
 
  Lemma msDiffBit_larger_l:
     forall r1 r2,
      rNonneg r1 -> rNonneg r2 -> 
      rangeDisjoint r1 r2 ->
      (rBits r1 < msDiffBit (rPrefix r1) (rPrefix r2))%N.
  Proof.
    intros.
    apply N.le_lt_trans with (m := N.max (rBits r1) (rBits r2)).
    apply N.le_max_l.
    apply msDiffBit_larger; auto.
  Qed.

  Lemma msDiffBit_larger_r:
     forall r1 r2,
      rNonneg r1 -> rNonneg r2 -> 
      rangeDisjoint r1 r2 ->
      (rBits r2 < msDiffBit (rPrefix r1) (rPrefix r2))%N.
  Proof.
    intros.
    apply N.le_lt_trans with (m := N.max (rBits r1) (rBits r2)).
    apply N.le_max_r.
    apply msDiffBit_larger; auto.
  Qed.
  
  Lemma commonRangeDis_larger_l:
    forall r1 r2,
    rNonneg r1 -> rNonneg r2 ->
    rangeDisjoint r1 r2 ->
    (rBits r1 < rBits (commonRangeDisj r1 r2))%N.
  Proof.
    intros.
    unfold commonRangeDisj. simpl.
    apply (msDiffBit_larger_l); auto.
  Qed.
  
  Lemma commonRangeDis_larger_r:
    forall r1 r2,
    rNonneg r1 -> rNonneg r2 ->
    rangeDisjoint r1 r2 ->
    (rBits r2 < rBits (commonRangeDisj r1 r2))%N.
  Proof.
    intros.
    unfold commonRangeDisj. simpl.
    apply (msDiffBit_larger_r); auto.
  Qed. 

  Lemma outside_commonRangeDis_l:
    forall r1 r2 i,
    rNonneg r1 -> rNonneg r2 ->
    rangeDisjoint r1 r2 ->
    inRange i (commonRangeDisj r1 r2) = false ->
    inRange i r1 = false.
  Proof.
    intros.
    assert (rBits r1 <= rBits (commonRangeDisj r1 r2))%N
      by (apply N.lt_le_incl; apply commonRangeDis_larger_l; auto).
    refine (contraFF _ H2 ); intro; clear H2.
    clear H1.
    
    rewrite -> N2Z.inj_le in H3.

    destruct r1 as [p1 b1], r2 as [p2 b2]. simpl in *.
    set (b := msDiffBit _ _) in *.
    apply Z.eqb_eq in H4.
    apply Z.eqb_eq.
    
    rewrite -> Z.shiftr_shiftl_r by nonneg.
    replace (Z.of_N b) with (Z.of_N b1 + (Z.of_N b - Z.of_N b1)) at 1 by omega.
    rewrite <- Z.shiftr_shiftr by omega.
    rewrite -> H4 by omega.
    reflexivity.
  Qed.

  Lemma outside_commonRangeDis_r:
    forall r1 r2 i,
    rNonneg r1 -> rNonneg r2 ->
    rangeDisjoint r1 r2 ->
    inRange i (commonRangeDisj r1 r2) = false ->
    inRange i r2 = false.
  Proof.
    intros.
    assert (rBits r2 <= rBits (commonRangeDisj r1 r2))%N
      by (apply N.lt_le_incl; apply commonRangeDis_larger_r; auto).
    refine (contraFF _ H2 ); intro; clear H2.
    clear H1.
    
    rewrite -> N2Z.inj_le in H3.

    destruct r1 as [p1 b1], r2 as [p2 b2]. simpl in *.
    set (b := msDiffBit _ _) in *.
    apply Z.eqb_eq in H4.
    apply Z.eqb_eq.
    
    subst b.
    rewrite -> msDiffBit_shiftr_same by nonneg.
    set (b := msDiffBit _ _) in *.
    
    rewrite -> Z.shiftr_shiftl_r by nonneg.
    replace (Z.of_N b) with (Z.of_N b2 + (Z.of_N b - Z.of_N b2)) at 1 by omega.
    rewrite <- Z.shiftr_shiftr by omega.
    rewrite -> H4 by omega.
    reflexivity.
  Qed.


  Inductive Desc : IntSet -> range -> (Z -> bool) -> Prop :=
    | DescTip : forall p bm r f,
      0 <= p ->
      p = rPrefix r ->
      rBits r = N.log2 WIDTH ->
      (forall i, f i = bitmapInRange r bm i) ->
      isBitMask bm ->
      Desc (Tip p bm) r f
    | DescBin : forall s1 r1 f1 s2 r2 f2 p msk r f,
      Desc s1 r1 f1 ->
      Desc s2 r2 f2 ->
      rangeDisjoint r1 r2 ->
      r = commonRangeDisj r1 r2 -> 
      Z.testbit (rPrefix r1) (Z.pred (Z.of_N (rBits r))) = false ->
      Z.testbit (rPrefix r2) (Z.pred (Z.of_N (rBits r))) = true ->
      p = rPrefix r ->
      msk = rMask r -> 
      (forall i, f i = f1 i || f2 i) ->
      Desc (Bin p msk s1 s2) r f.
  
  Inductive WF : IntSet -> Prop :=
    | WFEmpty : WF Nil
    | WFNonEmpty : forall s r f (HD : Desc s r f), WF s.

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
     rewrite -> Z.ldiff_ones_r by omega.
     replace (Z.of_N (N.log2 WIDTH)) with 6 by reflexivity.

     rewrite -> Z_shiftl_injb by omega.
     reflexivity.
   Qed.
   

   Lemma Desc_outside:
     forall {s r f i}, Desc s r f -> inRange i r = false -> f i = false.
   Proof.
     intros ???? HD Houtside.
     induction HD;subst.
     * rewrite H2.
       unfold bitmapInRange.
       rewrite Houtside.
       reflexivity.
     * rewrite H5.
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
     rewrite -> Z.ldiff_ones_r by nonneg.
     rewrite -> Z_shiftl_injb by nonneg.
     reflexivity.
     enough (0 < Z.of_N b) by omega.
     replace 0 with (Z.of_N 0%N) by reflexivity.
     apply N2Z.inj_lt. assumption.
   Qed.
   
   Lemma zero_spec:
     forall i b,
      (0 < b)%N ->
      zero i (2 ^ Z.pred (Z.of_N b)) = negb (Z.testbit i (Z.pred (Z.of_N b))).
   Proof.
     intros.
     apply land_pow2_eq.
     apply Z.lt_le_pred.
     change (Z.of_N 0%N < Z.of_N b).
     apply N2Z.inj_lt.
     assumption.
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
       assert (Hp_pos : (0 < b)%N) by (apply N.le_lt_trans with (m := b1); nonneg).
       rewrite -> nomatch_spec by apply Hp_pos.
       rewrite -> zero_spec by apply Hp_pos.
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
      rewrite -> land_shiftl_ones by omega.
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
      apply Z.shiftr_eq_0; nonneg.
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
    rewrite -> land_pow2_eq by nonneg.
    replace (Z.log2 (Z.lxor (Z.shiftl p1 (Z.of_N b1)) (Z.shiftl p2 (Z.of_N b2))))
        with (Z.pred (Z.of_N b)).
    rewrite -> Z.shiftl_spec by nonneg.

    destruct (Z.testbit p1 (Z.pred (Z.of_N b) - Z.of_N b1)) eqn:Htb; simpl.
    * eapply DescBin.
      apply H0. apply H.
      all:try congruence.
      destruct (Z.testbit p2 (Z.pred (Z.of_N b) - Z.of_N b2)); congruence.
      rewrite -> Z.log2_pow2 by assumption.
      rewrite -> Z.ldiff_ones_r by nonneg.
      rewrite -> Z.shiftr_shiftl_r by nonneg. f_equal. f_equal. omega. omega.
      intro i. rewrite H8. apply orb_comm.
    * eapply DescBin.
      apply H. apply H0.
      all:try congruence.
      destruct (Z.testbit p2 (Z.pred (Z.of_N b) - Z.of_N b2)); congruence.
      rewrite -> Z.log2_pow2 by assumption.
      rewrite -> Z.ldiff_ones_r by nonneg.
      rewrite -> Z.shiftr_shiftl_r by nonneg. f_equal. f_equal. omega. omega.

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

  Lemma lxor_pos:
    forall a b, 0 <= a -> 0 <= b -> a <> b -> 0 < Z.lxor a b.
   Admitted.

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
        * assert (Hxor_pos : 0 < Z.lxor (Z.shiftr p 6) p0).
            apply lxor_pos; try nonneg.
            rewrite (isPrefix_shiftl_shiftr _ Hp) in n.
            rewrite -> Z_shiftl_inj in n by nonneg.
            congruence.

          (* calling link now *)
          eapply WFNonEmpty.
          eapply link_Desc. 7:reflexivity.
          - apply Tip_Desc with (p := Z.shiftr p 6); auto.
            nonneg.
            apply isPrefix_shiftl_shiftr; assumption.
          - apply Tip_Desc with (p := p0); auto.
          all: replace (Z.of_N (N.log2 WIDTH)) with 6 in * by reflexivity.
          all: replace (N.log2 WIDTH) with (Z.to_N 6) in * by reflexivity.
          - rewrite <- Z.shiftl_lxor.
            rewrite -> Z.log2_shiftl; try assumption.
            apply Z2N.inj_lt; [nonneg|nonneg|].
            rewrite (isPrefix_shiftl_shiftr _ Hp) in n.
            rewrite -> Z_shiftl_inj in n by nonneg.
            enough (0 <= Z.log2 (Z.lxor (Z.shiftr p 6) p0)) by omega; nonneg.
            nonneg.
          - apply Z2N.inj_lt; try nonneg.
              rewrite <- Z.shiftl_lxor.
              rewrite Z.log2_shiftl; try nonneg.
              enough (0 <= Z.log2 (Z.lxor (Z.shiftr p 6) p0)) by omega; nonneg.
           - apply isPrefix_shiftl_shiftr; assumption.
           - reflexivity.
           - rewrite -> Z2N.id by nonneg.
             rewrite Z.pred_succ.
             rewrite <- Z.shiftl_lxor.
             rewrite  Z.log2_shiftl; try nonneg.
             replace (Z.log2 (Z.lxor (Z.shiftr p 6) p0) + 6 - 6) with (Z.log2 (Z.lxor (Z.shiftr p 6) p0)) by omega.
             (* log2 finds the difference *)
             admit.
           - rewrite -> Z2N.id by nonneg.
             rewrite <- Z.shiftl_lxor.
             rewrite  Z.log2_shiftl; try nonneg.
             replace (Z.succ (Z.log2 (Z.lxor (Z.shiftr p 6) p0) + 6) - 6) with (Z.succ (Z.log2 (Z.lxor (Z.shiftr p 6) p0))) by omega.
             (* log2 finds the largest difference *)
             admit.
           - intro i. reflexivity.
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