Require Import GHC.Base.
Import Notations.
Require Import GHC.Num.
Import Notations.

Require Import Data.Set.Base.
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

  Lemma Int_is_Z : forall a : Z,
      # a = a.
  Proof. reflexivity. Qed.
  
End Int_And_Z.

Ltac rewrite_Int :=
  repeat (rewrite ?Int_plus_is_Z_plus ?Int_minus_is_Z_minus
                  ?Int_mult_is_Z_mult
                  ?Int_lt_is_Z_lt ?Int_le_is_Z_le
                  ?Int_ge_is_Z_ge ?Int_gt_is_Z_gt
                  ?Int_eq_is_Z_eq ?Int_is_Z).

Module Foo (E : OrderedType) : WSfun(E).
  Local Instance Eq_t : GHC.Base.Eq_ E.t :=
    fun _ k => k {|
                op_zeze____ := fun x y => E.eq_dec x y;
                op_zsze____ := fun x y => negb (E.eq_dec x y);
              |}.

  Local Definition compare (x y: E.t) : comparison :=
    match E.compare x y with
    | EQ _ => Eq
    | LT _ => Lt
    | GT _ => Gt
    end.
  
  Local Instance Ord_t : GHC.Base.Ord E.t := GHC.Base.ord_default compare.
  
  Module OrdFacts := OrderedTypeFacts(E).

  Ltac rewrite_option_eq :=
    rewrite /op_zeze__ /Eq___option //= /op_zeze__ /Eq_Integer___ //=.
  
  Ltac rewrite_compare_e :=
    rewrite /Base.compare /Ord_t /ord_default; simpl; rewrite /compare.

  Ltac destruct_match :=
    match goal with
    | [ H :context[match ?a with _ => _ end] |- _] =>
      let Heq := fresh "Heq" in
      destruct a eqn:Heq=>//
    | [ |- context[match ?a with _ => _ end]] =>
      let Heq := fresh "Heq" in
      destruct a eqn:Heq=>//
    end.

  Definition elt := E.t.
  
  (* Well-formedness *)
  Definition WF (s : Set_ elt) := valid s.
  (* Will it be easier for proof if [WF] is an inductive definition? *)
  Definition t := {s : Set_ elt | WF s}.
  Definition pack (s : Set_ elt) (H : WF s): t := exist _ s H.

  Notation "x <-- f ;; P" :=
    (match f with
     | exist x _ => P
     end) (at level 99, f at next level, right associativity).

  Lemma balanced_children : forall {a} (s1 s2 : Set_ a) l e,
      balanced (Bin l e s1 s2) -> balanced s1 /\ balanced s2.
  Proof. split; simpl in H; move: H; case: and3P=>//; elim; done. Qed.

  Lemma ordered_children : forall {a} `{Eq_ a} `{Ord a} (s1 s2 : Set_ a) l e,
      ordered (Bin l e s1 s2) -> ordered s1 /\ ordered s2.
  Proof.
    split; unfold ordered in *; move: H2; case: and4P=>//; elim; intros.
    - remember (const true) as ct. rewrite {2}[ct] Heqct.
      clear H5; clear Heqct; clear H2; clear H3. generalize dependent ct.
      induction s1=>//. intros. move: H4; case: and4P=>//; elim.
      intros. apply /and4P; split=>//. apply IHs1_2; auto.
    - remember (const true) as ct. rewrite {1}[ct] Heqct.
      clear H4; clear Heqct; clear H2; clear H3. generalize dependent ct.
      induction s2=>//. intros. move: H5; case: and4P=>//; elim.
      intros. apply /and4P; split=>//. apply IHs2_1; auto.
  Qed.

  Lemma validsize_children : forall {a} (s1 s2 : Set_ a) l e,
      validsize (Bin l e s1 s2) -> validsize s1 /\ validsize s2.
  Proof.
    intros; move: H; rewrite /validsize=>H;
      remember (fix realsize (t' : Set_ a) : option Size :=
                  match t' with
                  | Bin sz _ l r =>
                    match realsize l with
                    | Some n =>
                      match realsize r with
                      | Some m =>
                        if _GHC.Base.==_ (n + m + 1)%Z sz
                        then Some sz
                        else None
                      | None => None
                      end
                    | None => None
                    end
                  | Tip => Some 0%Z
                  end) as f; move: H; rewrite -Heqf.
    split; generalize dependent e; generalize dependent l.
    - generalize dependent s2.
      destruct s1; intros.
      + move: H. rewrite Heqf; simpl; rewrite -Heqf.
        destruct (f s1_1) eqn:Heqs1; destruct (f s1_2) eqn:Heqs2=>//.
        destruct (_GHC.Base.==_ (s0 + s1 + 1)%Z s) eqn:Heq=>//.
        intros. rewrite_option_eq. apply Z.eqb_refl.
      + rewrite Heqf. simpl. rewrite_option_eq. auto.
    - generalize dependent s1.
      destruct s2; intros.
      + move: H. rewrite Heqf; simpl; rewrite -Heqf.
        destruct (f s1) eqn:Heqs;
          destruct (f s2_1) eqn:Heqs1;
          destruct (f s2_2) eqn:Heqs2=>//.
        destruct (_GHC.Base.==_ (s2 + s3 + 1)%Z s) eqn:Heq=>//.
        intros. rewrite_option_eq. apply Z.eqb_refl.
      + rewrite Heqf. simpl. rewrite_option_eq. 
  Qed.
      
  Lemma WF_children : forall s1 s2 l e, WF (Bin l e s1 s2) -> WF s1 /\ WF s2.
  Proof.
    rewrite /WF /valid. move=>s1 s2 l e. case: and3P=>//.
    elim; move=>Hb Ho Hv H; clear H. 
    split; apply /and3P; split;
      apply balanced_children in Hb;
      apply ordered_children in Ho;
      apply validsize_children in Hv; intuition.
  Qed.

  Lemma WF_size_children : forall s1 s2 l e,
      WF (Bin l e s1 s2) -> size s1 + size s2 + 1 = l.
  Proof.
    rewrite /WF /valid. move=>s1 s2 l e. case: and3P=>//.
    elim; move=>Hb Ho Hv H; clear H.
    apply validsize_children in Hv as Hv2. destruct Hv2.
    move: H0 H Hv. rewrite /validsize.
    remember (fix realsize (t' : Set_ elt) : option Size :=
             match t' with
             | Bin sz _ l0 r =>
                 match realsize l0 with
                 | Some n0 =>
                     match realsize r with
                     | Some m =>
                         if _GHC.Base.==_ (_GHC.Num.+_ (_GHC.Num.+_ n0 m) #1) sz
                         then Some sz
                         else None
                     | None => None
                     end
                 | None => None
                 end
             | Tip => Some #0
             end) as f. rewrite -Heqf.
    destruct s1; destruct s2=>//.
    - rewrite /size; rewrite_Int; intros. repeat destruct_match.
      move: H0 H Heq1; rewrite_option_eq.
      rewrite /is_true !Z.eqb_eq. intros; subst; auto.
    - rewrite /size; rewrite_Int; intros. repeat destruct_match.
      move: H0 H Heq1; rewrite_option_eq.
      rewrite /is_true !Z.eqb_eq. intros; subst; auto.
    - rewrite /size; rewrite_Int; intros. repeat destruct_match.
      move: H0 H Heq1; rewrite_option_eq.
      rewrite /is_true !Z.eqb_eq. intros; subst; auto.
    - rewrite /size; rewrite_Int; intros. repeat destruct_match.
      move: H0 H Heq0; rewrite_option_eq.
      rewrite /is_true !Z.eqb_eq. intros; subst; auto.
  Qed.

  Lemma WF_size_nonneg : forall s, WF s -> size s >= 0.
  Proof.
    induction s; intros.
    - apply WF_size_children in H as H2.
      apply WF_children in H. destruct H.
      rewrite /size. subst. apply IHs1 in H. apply IHs2 in H0. omega.
    - simpl; omega.
  Qed.

  Lemma WF_size_pos : forall s1 s2 e l,
      WF (Bin l e s1 s2) -> size (Bin l e s1 s2) >= 1.
  Proof.
    intros. have: WF (Bin l e s1 s2) by done.
    apply WF_children in H; destruct H.
    move=>Hwf. apply WF_size_children in Hwf.
    rewrite /size -Hwf.
    apply WF_size_nonneg in H; apply WF_size_nonneg in H0.
    omega.
  Qed.

  Lemma WF_balanced : forall s1 s2 e l,
      WF (Bin l e s1 s2) -> balanced (Bin l e s1 s2).
  Proof. move=>s1 s2 e l; rewrite /WF /valid; case /and3P=>//. Qed.

  Lemma WF_ordered : forall s1 s2 e l,
      WF (Bin l e s1 s2) -> ordered (Bin l e s1 s2).
  Proof. move=>s1 s2 e l; rewrite /WF /valid; case /and3P=>//. Qed.

  Lemma WF_validsize : forall s1 s2 e l,
      WF (Bin l e s1 s2) -> validsize (Bin l e s1 s2).
  Proof. move=>s1 s2 e l; rewrite /WF /valid; case /and3P=>//. Qed.
        
  Definition In x (s' : t) :=
    s <-- s' ;;
    member x s = true.
  
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Ltac rewrite_size :=
    repeat match goal with
           | [ |- _ ] => rewrite ![size (Bin _ _ _ _)]/size
           | [ |- _ ] => rewrite ![size Tip]/size
           | [H: context[size (Bin _ _ _ _)] |- _ ] =>
             rewrite ![size (Bin _ _ _ _)]/size in H
           end.

  Ltac prepare_for_omega :=
    repeat match goal with
                          | [H: context[_ <? _] |- _ ] => move: H
                          | [H: context[_ <=? _] |- _ ] => move: H
                          | [H: context[_ =? _] |- _ ] => move: H
                          end; rewrite_Int; rewrite_size;
    rewrite /is_true ?Z.ltb_lt ?Z.ltb_ge ?Z.leb_le ?Z.eqb_eq.

  Ltac rewrite_for_omega :=
    repeat match goal with
                          | [H: context[delta] |- _ ] => move: H
                          | [H: context[ratio] |- _ ] => move: H
           end; rewrite /delta /ratio;
    rewrite_Int; rewrite_size; prepare_for_omega.


  Lemma balanced_size_constraints : forall (s1 s2 : Set_ elt) e l,
      balanced (Bin l e s1 s2) ->
      size s1 + size s2 <= 1 \/
      (size s1 <= delta * size s2 /\ size s2 <= delta * size s1).
  Proof.
    move=>s1 s2 e l. rewrite /balanced.
    case and3P=>//; elim; rewrite_Int.
    case orP=>//; elim;
      [rewrite /is_true !Z.leb_le; left; auto |
       case andP=>//; elim; rewrite /is_true !Z.leb_le;
       right; split; auto].
  Qed.
  
  Ltac derive_constraints :=
    repeat match goal with
           | [Hwf: context[WF (Bin ?s ?x ?a ?b)] |- _ ] =>
             let Hsum := fresh "Hsum" in
             have: WF (Bin s x a b) by [done];
             move /WF_size_children; rewrite_size; move=>Hsum;
             let Hpos := fresh "Hpos" in
             have: WF (Bin s x a b) by [done];
             move /WF_size_pos; rewrite_size; move=>Hpos;
             let Hwfc := fresh "Hwfc" in
             let Hwfl := fresh "Hwfl" in
             let Hwfr := fresh "Hwfr" in
             have Hwfc : WF a /\ WF b by
                 [move: Hwf; move /WF_children];
             destruct Hwfc as [Hwfl Hwfr];
             let Hbalanced := fresh "Hbalanced" in
             have Hbalanced: (size a + size b <= 1) \/
                                 (size a <= delta * size b /\
                                  size b <= delta * size a) by
                 [ move: Hwf; move /WF_balanced /balanced_size_constraints];
             clear Hwf
           | [Hwf: context[WF ?t] |- _ ] =>
             let Hnonneg := fresh "Hnonneg" in
             have: WF t by [done];
             move /WF_size_nonneg; move=>Hnonneg; clear Hwf
           end.

  Ltac brute_force_solve :=
    (repeat match goal with
            | [H: _ \/ _ |- _ ] => destruct H
            | [H: _ /\ _ |- _ ] => destruct H
            end); try omega; rewrite_for_omega; omega.
                                    
  (** The balancing condition is that [ls <= delta*rs] and [rs <=
      delta*ls].  The moment that balancing is broken because of
      insertion/deletion of one single element, we know exactly one
      constraint will be broken. [belanceL] is called when the left
      child is bigger, so we know what happened is that now [ls =
      delta * rs + 1].

      To prove ordering, here should be another constraint, that [x]
      is greater than any value in [l], and smaller than any value in
      [r]. *)
  Definition before_balancedL (x: elt) (l r : Set_ elt) : Prop :=
    size l == delta * size r + 1.
  
  Lemma balanceL_balanced: forall (x: elt) (l r : Set_ elt),
    WF l -> WF r ->
    before_balancedL x l r -> balanced (balanceL x l r).
  Proof.
    intros x l r Hwfl Hwfr.
    have: WF l by done. have: WF r by done.
    rewrite /WF /valid. 
    case: and3P=>//; elim; move=>Hbr Hor Hvr; elim.
    case: and3P=>//; elim; move=>Hbl Hol Hvl; elim.
    destruct r as [sr xr rl rr | ]; destruct l as [sl xl ll lr | ];
      rewrite /before_balancedL /balanceL; rewrite_Int; move=>Hbefore.
    - (** [l] and [r] are both [Bin]s. *)
      rewrite_Int. destruct_match.
      + (** The [ls > delta*rs] branch in Haskell code. *)
        destruct ll as [sll xll lll llr | ];
          destruct lr as [slr xlr lrl lrr | ]; rewrite_Int.
        * (** [ll] and [lr] are both Bins *)
          destruct_match.
          -- (** [lrs < ratio*lls] branch (single rotation): We need
                 to prove that [Bin (1+ls+rs) lx ll (Bin (1+rs+lrs) x
                 lr r)] is balanced. *)
            rewrite /balanced. rewrite_Int.
            apply /and3P=>//. split.
            ++ (** Top level is balanced. That is, size of [ll] and of
                   [Bin (1+rs+lrs) x lr r] are balanced. This should
                   be proved by arithmetics. *)
              apply /orP=>//. right.
              apply /andP=>//. split; derive_constraints; subst.
              ** destruct Hbalanced0; rewrite_for_omega; intros; omega.
              ** rewrite_for_omega. omega.
            ++ (** Left child [ll] is balanced. We already know this
                   from the precondition. All we need to do here is
                   derive that fact from precondition. No arithmetics
                   involved. *)
              apply balanced_children in Hbl; destruct Hbl.
              move: H. rewrite /balanced. auto.
            ++ (** Right child [Bin (1+rs+lrs) x lr r] is
                   balanced. Arithmetics. *)
              apply /and5P=>//; split.
              ** derive_constraints; subst. 
                 apply /orP=>//. right.
                 apply /andP=>//; split; rewrite_for_omega; omega.
              ** apply balanced_children in Hbl; destruct Hbl.
                 move: H0. rewrite /balanced. auto.
              ** move: Hbr. rewrite /balanced.
                 case and3P=>//; elim. auto.
              ** apply balanced_children in Hbr. destruct Hbr.
                 move: H. rewrite /balanced =>//.
              ** apply balanced_children in Hbr. destruct Hbr.
                 move: H0. rewrite /balanced =>//.
          -- (** The [otherwise] branch, i.e. [lr >= ratio * ll]
                 (double rotation). *)
            rewrite /balanced. apply /and3P=>//; split.
            ++ (** Left child [Bin (1+lls+size lrl) lx ll lrl] and
                   right child [Bin (1+rs+size lrr) x lrr r] are
                   balanced wrt. to each other. *)
              apply /orP=>//. right.
              apply /andP=>//. derive_constraints; subst; rewrite_for_omega.
              split; omega.
            ++ (** [Bin (1+lls+size lrl) lx ll lrl] is balanced. *)
              apply /and3P=>//; split.
              ** apply /orP=>//. destruct lrl.
                 { right. apply /andP=>//. derive_constraints; subst.
                   split; brute_force_solve. }
                 { derive_constraints; subst; rewrite_size; rewrite_Int.
                   left. rewrite_for_omega. omega. }
              ** apply balanced_children in Hbl; destruct Hbl.
                 move: H. rewrite /balanced. auto.
              ** apply balanced_children in Hbl; destruct Hbl.
                 apply balanced_children in H0; destruct H0.
                 move: H0. rewrite /balanced. auto.
            ++ (** [Bin (1+rs+size lrr) x lrr r] is balanced. *)
              apply /and3P; split.
              ** apply /orP=>//. destruct lrr.
                 { right. apply /andP=>//. derive_constraints; subst.
                   split; brute_force_solve. }
                 { derive_constraints; subst; rewrite_size; rewrite_Int.
                   left. rewrite_for_omega. omega. }
              ** apply balanced_children in Hbl; destruct Hbl.
                 apply balanced_children in H0; destruct H0.
                 move: H1. rewrite /balanced. auto.
              ** move: Hbr. rewrite /balanced. auto.
        * (** [lr] is [Tip] *) admit.
        * (** [ll] is [Tip] *) admit.
        * (** [ll] and [lr] are both [Tip]s. *) admit.
      + (** The [otherwise] branch, i.e. [ls >= delta*rs]. *) admit.
    - (** [l] is [Tip] *) admit.
    - (** [r] is [Tip] *) admit.
    - (** Both [l] and [r] and [Tip]s. *) admit.
  Admitted.

  Lemma balanceL_ordered: forall (x: elt) (l r : Set_ elt),
      WF l -> WF r ->
      before_balancedL x l r -> ordered (balanceL x l r).
  Admitted.
    
  Lemma balanceL_validsize: forall (x: elt) (l r : Set_ elt),
      WF l -> WF r ->
      before_balancedL x l r -> validsize (balanceL x l r).
  Admitted.

  Lemma balanceL_WF: forall (x: elt) (l r : Set_ elt),
      WF l -> WF r ->
      before_balancedL x l r -> WF (balanceL x l r).
  Proof with auto.
    intros. rewrite /WF /valid.
    apply /and3P=>//; split.
    - apply balanceL_balanced...
    - apply balanceL_ordered...
    - apply balanceL_validsize...
  Qed.
  
  Definition empty : t := pack empty eq_refl.
  Definition is_empty : t -> bool := fun s' => 
     s <-- s' ;; null s.
  Definition mem : elt -> t -> bool := fun e s' =>
     s <-- s' ;; member e s.
  Definition add : elt -> t -> t. Admitted. (* must contain a WF proof *)
  Definition singleton : elt -> t.
    refine (fun e => pack (singleton e) _).
    rewrite /singleton /WF /valid.
    apply /and3P; split; auto.
  Defined.
  Definition remove : elt -> t -> t. Admitted.
  Definition union : t -> t -> t. Admitted.
  Definition inter : t -> t -> t. Admitted.
  Definition diff : t -> t -> t. Admitted.
  Definition eq : t -> t -> Prop := Equal.
  Definition eq_dec : forall s s' : t, {eq s s'} + {~ eq s s'}.
    destruct s as [s]; destruct s' as [s']; simpl.
    destruct (s == s') eqn:Heq; move: Heq;
      rewrite /_GHC.Base.==_ /Eq___Set_; simpl;
        rewrite /Base.Eq___Set__op_zeze__;
        rewrite /_GHC.Base.==_ /Eq_Integer___ /Eq_list; simpl;
          case: andP=>//.
    - elim; intros; left.
      rewrite /eq /Equal; intros. admit.
      (* TODO: need lemmas on [toAscList] *)
  Admitted.
    
  Definition equal : t -> t -> bool :=
    fun ws ws' => s <-- ws ;;
               s' <-- ws' ;;
               s == s'.
  
  Definition subset : t -> t -> bool :=
    fun ws ws' => s <-- ws ;;
               s' <-- ws' ;;
               isSubsetOf s s'.
        
  Definition fold : forall A : Type, (elt -> A -> A) -> t -> A -> A. Admitted.
  Definition for_all : (elt -> bool) -> t -> bool. Admitted.
  Definition exists_ : (elt -> bool) -> t -> bool. Admitted.
  Definition filter : (elt -> bool) -> t -> t. Admitted.
  Definition partition : (elt -> bool) -> t -> t * t. Admitted.
  Definition cardinal : t -> nat. Admitted.
  Definition elements : t -> list elt. Admitted.
  Definition choose : t -> option elt. Admitted.
  Lemma In_1 :
    forall (s : t) (x y : elt), E.eq x y -> In x s -> In y s.
  Proof.
    (* LY: Surely this can be simplified? *)
    unfold In; destruct s as [s']; induction s'; auto. intros.
    simpl in H0; destruct (Base.compare x a) eqn:Hcomp;
      vm_compute in Hcomp; destruct (E.compare x a) as [HL | HE | HG];
        inversion Hcomp; clear Hcomp.
    - apply E.eq_sym in H. apply (E.eq_trans H) in HE.
      apply OrdFacts.elim_compare_eq in HE; destruct HE as [? Heq].
      simpl. vm_compute. rewrite Heq; auto.
    - apply (OrdFacts.eq_lt (E.eq_sym H)) in HL.
      apply OrdFacts.elim_compare_lt in HL; destruct HL as [? Hlt]. simpl.
      assert (Hcomp: Base.compare y a = Lt).
      { vm_compute. rewrite Hlt; auto. }
      rewrite Hcomp. apply WF_children in i; destruct i. eauto.
    - assert (Heq: E.eq x y) by apply H.
      apply (OrdFacts.lt_eq HG) in H.
      apply OrdFacts.elim_compare_gt in H; destruct H as [? Hgt]. simpl.
      assert (Hcomp: Base.compare y a = Gt).
      { vm_compute. rewrite Hgt; auto. }
      rewrite Hcomp. apply WF_children in i; destruct i. eauto.
  Qed.
      
  Lemma eq_refl : forall s : t, eq s s.
  Proof. intros; constructor; auto. Qed.
    
  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. unfold eq; unfold Equal; symmetry; auto. Qed.
    
  Lemma eq_trans :
    forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof.
    unfold eq; unfold Equal; intros s s' s'' H1 H2 a.
    apply (iff_trans (H1 a) (H2 a)).
  Qed.
    
  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
    
  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.
  
  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true. Admitted.
  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'. Admitted.
  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true. Admitted.
  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'. Admitted.
  
  Lemma empty_1 : Empty empty.
  Proof. unfold Empty; intros a H. inversion H. Qed.
  
  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    unfold Empty; unfold In. destruct s; destruct x; auto.
    intros H. specialize (H e). move: H. simpl. rewrite_compare_e.
    assert (Heq: E.eq e e); auto.
    apply OrdFacts.elim_compare_eq in Heq; destruct Heq.
    rewrite H; contradiction.
  Qed.
      
  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof.
    unfold Empty; unfold In. destruct s; destruct x; auto.
  Qed.
      
  Lemma add_1 :
    forall (s : t) (x y : elt), E.eq x y -> In y (add x s). Admitted.
  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s). Admitted.
  Lemma add_3 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y (add x s) -> In y s. Admitted.
  Lemma remove_1 :
    forall (s : t) (x y : elt), E.eq x y -> ~ In y (remove x s). Admitted.
  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y s -> In y (remove x s). Admitted.
  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s. Admitted.

  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> E.eq x y.
  Proof.
    rewrite /singleton /In; simpl.
    rewrite_compare_e. intros.
    destruct (E.compare y x) eqn:Hcomp=>//.
    apply E.eq_sym=>//.
  Qed.
      
  Lemma singleton_2 :
    forall x y : elt, E.eq x y -> In y (singleton x).
  Proof.
    rewrite /singleton /In; simpl.
    rewrite_compare_e. intros.
    destruct (E.compare y x) eqn:Hcomp=>//; exfalso.
    - apply E.eq_sym in H. apply (E.lt_not_eq l)=>//.
    - apply (E.lt_not_eq l)=>//.
  Qed.
      
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
    compat_bool E.eq f -> In x (filter f s) -> In x s. Admitted.
  Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x (filter f s) -> f x = true. Admitted.
  Lemma filter_3 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s). Admitted.
  Lemma for_all_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    For_all (fun x : elt => f x = true) s -> for_all f s = true. Admitted.
  Lemma for_all_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    for_all f s = true -> For_all (fun x : elt => f x = true) s. Admitted.
  Lemma exists_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    Exists (fun x : elt => f x = true) s -> exists_ f s = true. Admitted.
  Lemma exists_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    exists_ f s = true -> Exists (fun x : elt => f x = true) s. Admitted.
  Lemma partition_1 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s). Admitted.
  Lemma partition_2 :
    forall (s : t) (f : elt -> bool),
    compat_bool E.eq f ->
    Equal (snd (partition f s)) (filter (fun x : elt => negb (f x)) s). Admitted.
  Lemma elements_1 :
    forall (s : t) (x : elt), In x s -> InA E.eq x (elements s). Admitted.
  Lemma elements_2 :
    forall (s : t) (x : elt), InA E.eq x (elements s) -> In x s. Admitted.
  Lemma elements_3w : forall s : t, NoDupA E.eq (elements s). Admitted.
  Lemma choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s. Admitted.
  Lemma choose_2 : forall s : t, choose s = None -> Empty s. Admitted.

End Foo.
