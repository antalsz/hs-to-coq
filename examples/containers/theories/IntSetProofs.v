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

  Definition isBitMask (bm : N) :=
    (0 < bm /\ bm < 2 ^ 64)%N.
  Definition between l f u g :=
    (forall i, f i = if i <? l then false else if i >=? u then false else g i).
  
  Inductive Desc : IntSet -> Z -> (Z -> bool) -> Z -> Prop :=
    | DescTip : forall p bm l f u,
      l = p -> u = l + 64 ->
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
  
  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    intros. unfold Empty, In, In_set, is_empty in *. destruct s. simpl.
    induction w.
    * auto.
    * induction HD.
      + set (i := Z.lor p (Z.log2 (Z.of_N bm))).
        specialize (H i). contradict H.
        assert (Z.log2 (Z.log2 (Z.of_N bm)) < 64).
        destruct (Z_lt_dec 0 (Z.log2 (Z.of_N bm))).
        - apply Z.log2_lt_pow2; try assumption.
          unfold isBitMask in *.
          transitivity (Z.of_N bm).
          apply Z.log2_lt_lin.
          change (Z.of_N 0%N < Z.of_N bm). 
          apply N2Z.inj_lt. intuition.
          change (Z.of_N bm < Z.of_N (2 ^ 64)%N). 
          apply N2Z.inj_lt. intuition.
          replace bm with 1%N. reflexivity.
          unfold isBitMask in *.
          destruct bm; simpl in *; intuition; destruct p0; intuition.
        change ((prefixOf i == p) && ((bitmapOf i .&.bm) /= #0)).
        apply/andP; constructor.
        - rewrite /_GHC.Base.==_ /Eq_Integer___ /op_zeze____.
          apply <- Z.eqb_eq.
          change (Z.land i prefixBitMask = p).
          rewrite Z.land_lor_distr_l.
          rewrite (isPrefix_prefixMask p H4).
          enough (Z.land (Z.log2 (Z.of_N bm)) prefixBitMask = 0) as H'
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
          replace (suffixOf i) with (Z.log2 (Z.of_N bm)).
          ** unfold bitmapOfSuffix, shiftLL.
             rewrite N.shiftl_mul_pow2 N.mul_1_l to_N_log2. rewrite N2Z.id.
             unfold fromInteger, Num_Word__.
             replace (Z.to_N 0) with 0%N by reflexivity.
             intro.
             apply N.bits_inj_iff in H5.
             specialize (H5 (N.log2 bm)).
             rewrite N.land_spec N.pow2_bits_true N.bit_log2 in H5.
             rewrite N.bits_0 in H5. simpl in H5. congruence.
             unfold isBitMask in *; intuition; subst; apply (N.lt_irrefl _ H6).
          ** symmetry.
             unfold suffixOf.
             rewrite /_.&._ /Bits__N /instance_Bits_Int.
             rewrite Z.land_lor_distr_l.
             rewrite (isPrefix_suffixMask p H4).
             rewrite Z.lor_0_l.
             apply Z.land_ones_low.
             (apply Z.pow_nonneg; omega) || apply Z.log2_nonneg || apply N2Z.is_nonneg.
             assumption.
  Qed.
      
  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof. move=>s. rewrite /Empty /In. elim s=>[s']. elim s'=>//. Qed.


  Definition singleton : elt -> t.
    refine (fun e => pack (singleton e) _).
    unfold singleton, Prim.seq.
    eapply WFNonEmpty.
  Admitted.

  Definition add (e: elt) (s': t) : t.
    refine (s <-- s' ;;
            pack (insert e s) _).
    unfold insert, Prim.seq.
    (* now about [insertBM], move to own lemma *)
  Admitted.
  
  
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