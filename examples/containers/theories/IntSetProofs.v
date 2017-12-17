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


Require Import Coq.Structures.OrderedTypeEx.

Module Foo: WSfun(Z_as_OT).
  Module OrdFacts := OrderedTypeFacts(Z_as_OT).

  Definition elt := Z.

  (* Well-formedness *)
  
  Definition isPrefix (p : Z)  := Z.land p suffixBitMask = 0.
  
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

  (* exists for Z, but not for N? *)
  Lemma N_pow_pos_nonneg: forall a b : N, (0 < a -> 0 < a ^ b)%N.
  Proof.
    intros.
    SearchAbout N "ind".
    apply N.peano_ind with (n := b); intros.
    * simpl. reflexivity.
    * rewrite N.pow_succ_r; [|apply N.le_0_l].
      SearchAbout N.lt "trans".
      eapply N.lt_le_trans. apply H0.
      replace (a ^ n)%N  with (1 * a^n)%N at 1 by (apply N.mul_1_l).
      apply N.mul_le_mono_pos_r; auto.
      rewrite <- N.le_succ_l in H.
      apply H.
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

  Definition between l f u g :=
    (forall i, f i = if i <? l then false else if i <? u then g i else false).
  
  Definition testBitZ bm i :=
    if i <? 0 then false else N.testbit bm (Z.to_N i).
  
  Inductive Desc : IntSet -> Z -> (Z -> bool) -> Z -> Prop :=
    | DescTip : forall p bm l f u,
      l = p -> u = l + Z.of_N WIDTH ->
      between l f u (fun i => N.testbit bm (Z.to_N (i - l))) ->
      isBitMask bm ->
      isPrefix p ->
      Desc (Tip p bm) l f u.
  
  Inductive WF : IntSet -> Prop :=
    | WFEmpty : WF Nil
    | WFNonEmpty : forall s l f u (HD : Desc s l f u), WF s.
    
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
    In_set x s.

  Definition Equal_set s s' := forall a : elt, In_set a s <-> In_set a s'.
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
    apply pos_nonneg.
  Qed.

   Lemma Desc_has_member: 
    forall {s l f u}, Desc s l f u -> exists i, member i s.
   Proof.
   intros ???? HD.
   induction HD; subst.
   + destruct (isBitMask_testbit _ H2) as [j[??]].
     set (i := (Z.lor p (Z.of_N j))).
     exists i.

     assert (Z.log2 (Z.of_N j) < 6).
     - rewrite <- of_N_log2.
       change (Z.of_N (N.log2 j) < Z.of_N 6%N).
       apply N2Z.inj_lt.
       destruct (N.lt_decidable 0%N j).
       + apply N.log2_lt_pow2; assumption.
       + enough (j = 0)%N by (subst; compute; congruence).
         destruct j; auto; contradict H4. apply pos_pos.

     simpl.
     change ((prefixOf i == p) && ((bitmapOf i .&.bm) /= #0)).
     apply/andP; constructor.
     - rewrite /_GHC.Base.==_ /Eq_Integer___ /op_zeze____.
       apply <- Z.eqb_eq.
       change (Z.land i prefixBitMask = p).
       rewrite Z.land_lor_distr_l.
       rewrite (isPrefix_prefixMask p H3).
       enough (Z.land (Z.of_N j) prefixBitMask = 0) as H'
         by (rewrite H' Z.lor_0_r; reflexivity).
         unfold prefixBitMask, Bits.complement, instance_Bits_Int, complement_Int in *.
         unfold suffixBitMask.
         rewrite <- Z.ldiff_land.
         apply Z.ldiff_ones_r_low.
         (apply Z.pow_nonneg; omega) || apply Z.log2_nonneg || apply N2Z.is_nonneg.
         assumption.
     - rewrite /_GHC.Base./=_ /Eq_Char___ /op_zsze____.
       rewrite /_.&._ /Bits__N.
       apply negb_true_iff.
       apply N.eqb_neq.
       unfold bitmapOf.
       replace (suffixOf i) with (Z.of_N j).
       ** unfold bitmapOfSuffix, shiftLL. rewrite N2Z.id.
          rewrite N.shiftl_mul_pow2 N.mul_1_l.
          unfold fromInteger, Num_Word__.
          replace (Z.to_N 0) with 0%N by reflexivity.
          intro Hneq.
          apply N.bits_inj_iff in Hneq.
          specialize (Hneq j).
          rewrite N.land_spec N.pow2_bits_true H0 N.bits_0 in Hneq.
          simpl in Hneq. congruence.
       ** symmetry.
          unfold suffixOf.
          rewrite /_.&._ /Bits__N /instance_Bits_Int.
          rewrite Z.land_lor_distr_l.
          rewrite (isPrefix_suffixMask p H3).
          rewrite Z.lor_0_l.
          apply Z.land_ones_low.
          (apply Z.pow_nonneg; omega) || apply Z.log2_nonneg || apply N2Z.is_nonneg.
          assumption.
  Qed.


  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    intros. unfold Empty, In, In_set, is_empty in *. destruct s. simpl.
    induction w.
    * auto.
    * destruct (Desc_has_member  HD).
      specialize (H x). intuition.
  Qed.
  
  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof. move=>s. rewrite /Empty /In. elim s=>[s']. elim s'=>//. Qed.

  Lemma Tip_Desc:
    forall p bm, isPrefix p -> isBitMask bm ->
      Desc (Tip p bm) p (fun i => testBitZ bm (i - p))  (p + Z.of_N WIDTH).
  Proof.
    intros ?? Hp Hbm.
    apply DescTip; auto.
    intro i. unfold testBitZ.
    replace (i <? p) with (i - p <? 0).
    replace (i <? p + Z.of_N WIDTH ) with (i - p <? Z.of_N WIDTH).
    generalize (i - p) as j. intro.
    destruct (Z.ltb_spec0 j 0); auto.
    destruct (Z.ltb_spec0 j (Z.of_N WIDTH)); auto.
    unfold bitmapOf, bitmapOfSuffix, shiftLL.
    unfold fromInteger, Num_Word__. replace (Z.to_N 1) with (1%N) by reflexivity.
    apply N.bits_above_log2.
    apply N.log2_lt_pow2;[ unfold isBitMask in *; intuition|].
    unfold isBitMask in *.
    eapply N.lt_le_trans; [ unfold isBitMask in *; intuition; eassumption|].
    apply N.pow_le_mono_r. compute; congruence.
    assert (Z.of_N WIDTH <= j) by intuition; clear n0.
    assert (0 <= j)  by intuition; clear n.
    change (Z.to_N 64 <= Z.to_N j)%N.
    apply Z2N.inj_le; auto.
    compute; congruence.
    
    destruct (Z.ltb_spec0 (i - p) (Z.of_N WIDTH)),
             (Z.ltb_spec0 i (p + Z.of_N WIDTH)); auto; try omega.
    destruct (Z.ltb_spec0 (i - p) 0),
             (Z.ltb_spec0 i p); auto; try omega.
  Qed.

  Lemma Tip_WF:
    forall p bm, isPrefix p -> isBitMask bm -> WF (Tip p bm).
  Proof.
    intros ?? Hp Hbm.
    eapply WFNonEmpty.
    apply Tip_Desc; assumption.
  Qed.

  Definition singleton : elt -> t.
    refine (fun e => pack (singleton e) _).
    unfold singleton, Prim.seq.
    apply Tip_WF.
    * apply isPrefix_prefixOf.
    * apply isBitMask_suffixOf.
  Qed.
  
  Lemma insertBM_WF:
    forall p bm s,
    isPrefix p -> isBitMask bm -> WF s -> WF (insertBM p bm s).
  Proof.
    intros ??? Hp Hbm HWF.
    destruct HWF.
    * simpl. unfold Prim.seq.
      apply Tip_WF; auto.
    * induction HD.
      + simpl; unfold Prim.seq.
        unfold GHC.Base.op_zeze__, Eq_Integer___, op_zeze____.
        destruct (Z.eqb_spec p0 p); subst.
        * apply Tip_WF; auto.
          apply isBitMask_lor; auto.
        * (* calling link now *)          
  Admitted.
  
  Definition add (e: elt) (s': t) : t.
    refine (s <-- s' ;;
            pack (insert e s) _).
    unfold insert, Prim.seq.
    apply insertBM_WF.
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
  Proof. destruct s. simpl. apply eq_set_refl. Qed.

  Lemma eq_set_sym : forall s s', eq_set s s' -> eq_set s' s.
  Proof. rewrite /eq_set /Equal_set; symmetry; auto. Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. destruct s; destruct s'; simpl. apply eq_set_sym. Qed.
    
  Lemma eq_set_trans :
    forall s s' s'', eq_set s s' -> eq_set s' s'' -> eq_set s s''.
  Proof.
    rewrite /eq_set /Equal_set; intros s s' s'' H1 H2 a.
    apply (iff_trans (H1 a) (H2 a)).
  Qed.
  
  Lemma eq_trans :
    forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
    destruct s; destruct s'; destruct s''; simpl. apply eq_set_trans.
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
    forall (s : t) (x y : elt), Z.eq x y -> In x s -> In y s.
  Admitted.
  
  Definition mem : elt -> t -> bool := fun e s' =>
   s <-- s' ;; member e s.


  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
    
  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
  
  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true. Admitted.
  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'. Admitted.
  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true. Admitted.
  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'. Admitted.
  
  Lemma add_1 :
    forall (s : t) (x y : elt), Z.eq x y -> In y (add x s). Admitted.
  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s). Admitted.
  Lemma add_3 :
    forall (s : t) (x y : elt), ~ Z.eq x y -> In y (add x s) -> In y s. Admitted.
  Lemma remove_1 :
    forall (s : t) (x y : elt), Z.eq x y -> ~ In y (remove x s). Admitted.
  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ Z.eq x y -> In y s -> In y (remove x s). Admitted.
  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s. Admitted.

  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> Z.eq x y.
  Admitted.
        
  Lemma singleton_2 :
    forall x y : elt, Z.eq x y -> In y (singleton x).
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
    compat_bool Z.eq f -> In x (filter f s) -> In x s. Admitted.
  Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool Z.eq f -> In x (filter f s) -> f x = true. Admitted.
  Lemma filter_3 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool Z.eq f -> In x s -> f x = true -> In x (filter f s). Admitted.
  Lemma for_all_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool Z.eq f ->
    For_all (fun x : elt => f x = true) s -> for_all f s = true. Admitted.
  Lemma for_all_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool Z.eq f ->
    for_all f s = true -> For_all (fun x : elt => f x = true) s. Admitted.
  Lemma exists_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool Z.eq f ->
    Exists (fun x : elt => f x = true) s -> exists_ f s = true. Admitted.
  Lemma exists_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool Z.eq f ->
    exists_ f s = true -> Exists (fun x : elt => f x = true) s. Admitted.
  Lemma partition_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool Z.eq f -> Equal (fst (partition f s)) (filter f s). Admitted.
  Lemma partition_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool Z.eq f ->
    Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s). Admitted.
  Lemma elements_1 :
    forall (s : t) (x : elt), In x s -> InA Z.eq x (elements s). Admitted.
  Lemma elements_2 :
    forall (s : t) (x : elt), InA Z.eq x (elements s) -> In x s. Admitted.
  Lemma elements_3w : forall s : t, NoDupA Z.eq (elements s). Admitted.
  Lemma choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s. Admitted.
  Lemma choose_2 : forall s : t, choose s = None -> Empty s. Admitted.

End Foo.