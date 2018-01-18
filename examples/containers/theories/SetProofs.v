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

Section ZReflect.
  Variables a b : Z.

  Lemma Z_eqP : reflect (a = b) (a =? b).
  Proof.
    destruct (a =? b) eqn:Hab; constructor; move: Hab.
    - move /Z.eqb_eq  =>//.
    - move /Z.eqb_neq =>//.
  Qed.

  Lemma Z_ltP : reflect (a < b) (a <? b).
  Proof.
    destruct (a <? b) eqn:Hab; constructor; move: Hab.
    - move /Z.ltb_lt =>//.
    - move /Z.ltb_nlt =>//.
  Qed.
End ZReflect.

Arguments Z_eqP {a} {b}.
Arguments Z_ltP {a} {b}.

Lemma Z_gtP { a b }: reflect (b < a) (a >? b).
Proof. rewrite Z.gtb_ltb. apply Z_ltP. Qed.

Section Option_Int.
  Variables a b : option Int.
  
  Ltac rewrite_option_eq :=
    rewrite /op_zeze__ /Eq___option //= /op_zeze__ /Eq_Integer___ //=.

  Lemma option_int_eqP :
    reflect (a = b) (a GHC.Base.== b).
  Proof.
    rewrite /_GHC.Base.==_ /Eq___option /= /Base.Eq___option_op_zeze__.
    destruct a; destruct b.
    - rewrite_Int. eapply iffP.
      + apply Z_eqP.
      + move -> => //.
      + case => //.
    - constructor. discriminate.
    - constructor. discriminate.
    - constructor. reflexivity.
  Qed.
  
  Lemma option_int_eq :
    a = b <-> a GHC.Base.== b.
  Proof. apply rwP. apply option_int_eqP. Qed.
End Option_Int.

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

  Ltac rewrite_compare_e :=
    rewrite /Base.compare /Ord_t /ord_default /= /compare.

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

  Lemma elt_ltP { e1 e2 } : reflect (E.lt e1 e2) (e1 GHC.Base.< e2).
  Proof.
    rewrite /_GHC.Base.<_ /Ord_t /ord_default /=.
    rewrite /_GHC.Base.==_ /Eq_comparison___ /= /eq_comparison /compare.
    do 2 destruct_match; constructor; auto.
  Qed.

  Lemma elt_gtP { e1 e2 } : reflect (E.lt e2 e1) (e1 GHC.Base.> e2).
  Proof.
    rewrite /_GHC.Base.>_ /Ord_t /ord_default /=.
    rewrite /_GHC.Base.==_ /Eq_comparison___ /= /eq_comparison /compare.
    do 2 destruct_match; constructor; auto.
  Qed.

  Lemma elt_compare_ltP {e1 e2} :
    reflect (E.lt e1 e2) (eq_comparison (GHC.Base.compare e1 e2) Lt).
  Proof.
    rewrite_compare_e; destruct_match; constructor; auto.
  Qed.

  Lemma elt_compare_lt'P {e1 e2} :
    reflect (GHC.Base.compare e1 e2 = Lt)
            (eq_comparison (GHC.Base.compare e1 e2) Lt).
  Proof.
    rewrite_compare_e.
    destruct_match; constructor; auto;
      move=>Hcontra; inversion Hcontra.
  Qed.

  Lemma elt_compare_gtP {e1 e2} :
    reflect (E.lt e2 e1) (eq_comparison (GHC.Base.compare e1 e2) Gt).
  Proof.
    rewrite_compare_e; destruct_match; constructor; auto.
  Qed.

  Lemma elt_compare_gt'P {e1 e2} :
    reflect (GHC.Base.compare e1 e2 = Gt)
            (eq_comparison (GHC.Base.compare e1 e2) Gt).
  Proof.
    rewrite_compare_e.
    destruct_match; constructor; auto;
      move=>Hcontra; inversion Hcontra.
  Qed.

  Lemma elt_compare_eqP {e1 e2} :
    reflect (E.eq e1 e2) (eq_comparison (GHC.Base.compare e1 e2) Eq).
  Proof.
    rewrite_compare_e; destruct_match; constructor; auto.
  Qed.

  Lemma elt_compare_eq'P {e1 e2} :
    reflect (GHC.Base.compare e1 e2 = Eq)
            (eq_comparison (GHC.Base.compare e1 e2) Eq).
  Proof.
    rewrite_compare_e.
    destruct_match; constructor; auto;
      move=>Hcontra; inversion Hcontra.
  Qed.

  Hint Resolve elt_ltP.
  Hint Resolve elt_gtP.
  Hint Resolve elt_compare_ltP.
  Hint Resolve elt_compare_lt'P.
  Hint Resolve elt_compare_gtP.
  Hint Resolve elt_compare_gt'P.
  Hint Resolve elt_compare_eqP.
  Hint Resolve elt_compare_eq'P.

  Lemma elt_lt : forall e1 e2, E.lt e1 e2 <-> e1 GHC.Base.< e2.
  Proof. move=>e1 e2. apply rwP =>//. Qed.

  Lemma elt_gt : forall e1 e2, E.lt e2 e1 <-> e1 GHC.Base.> e2.
  Proof. move=>e1 e2. apply rwP =>//. Qed.

  Lemma elt_compare_lt: forall (e1 e2 : elt),
      E.lt e1 e2 <-> GHC.Base.compare e1 e2 = Lt.
  Proof.
    move=>e1 e2.
    apply rwP2 with (b:=eq_comparison (GHC.Base.compare e1 e2) Lt) =>//.
  Qed.

  Lemma elt_compare_gt: forall (e1 e2 : elt),
      E.lt e2 e1 <-> GHC.Base.compare e1 e2 = Gt.
  Proof.
    move=>e1 e2.
    apply rwP2 with (b:=eq_comparison (GHC.Base.compare e1 e2) Gt) =>//.
  Qed.

  Lemma elt_compare_eq: forall (e1 e2 : elt),
       E.eq e1 e2 <-> GHC.Base.compare e1 e2 = Eq.
  Proof.
    move=>e1 e2.
    apply rwP2 with (b:=eq_comparison (GHC.Base.compare e1 e2) Eq) =>//.
  Qed.

  Hint Rewrite <- elt_lt : elt_compare.
  Hint Rewrite <- elt_gt : elt_compare.
  Hint Rewrite <- elt_compare_lt : elt_compare.
  Hint Rewrite <- elt_compare_gt : elt_compare.
  Hint Rewrite <- elt_compare_eq : elt_compare.

  Ltac rewrite_size :=
    repeat match goal with
           | [ |- _ ] => rewrite ![size (Bin _ _ _ _)]/size
           | [ |- _ ] => rewrite ![size Tip]/size
           | [H: context[size (Bin _ _ _ _)] |- _ ] =>
             rewrite ![size (Bin _ _ _ _)]/size in H
           | [H: context[size Tip] |- _ ] =>
             rewrite ![size Tip]/size in H
           end.

  Notation "x <-- f ;; P" :=
    (match f with
     | exist x _ => P
     end) (at level 99, f at next level, right associativity).

  Definition In_set x (s : Set_ elt) :=
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

  Definition empty : t := pack empty Logic.eq_refl.
  Definition is_empty : t -> bool := fun s' =>
    s <-- s' ;; null s.

  Lemma empty_1 : Empty empty.
  Proof. unfold Empty; intros a H. inversion H. Qed.

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
    move=>s. rewrite /Empty /In. case s=>[s'].
    case s'=>[ls x l r | ] => Hwf Hempty=>//.
    specialize (Hempty x). exfalso. apply Hempty.
    rewrite /In_set /member //=. rewrite_compare_e.
    have Heq: E.eq x x by done.
    apply OrdFacts.elim_compare_eq in Heq; destruct Heq.
    rewrite H=>//.
  Qed.

  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s.
  Proof. move=>s. rewrite /Empty /In. elim s=>[s']. elim s'=>//. Qed.

  Lemma empty_not_bin : forall l e (s1 s2 : Set_ elt),
      ~ Equal_set Tip (Bin l e s1 s2).
  Proof.
    intros. rewrite /Equal_set=>Heq.
    specialize (Heq e). destruct Heq.
    move: H0. rewrite {1}/In_set /member /=.
    have Heq: E.eq e e by done.
    apply elt_compare_eq in Heq. rewrite Heq=>Hcontra.
    specialize (Hcontra Logic.eq_refl). inversion Hcontra.
  Qed.

  Lemma bin_not_empty : forall l e (s1 s2 : Set_ elt),
      ~ Equal_set (Bin l e s1 s2) Tip.
  Proof.
    intros. rewrite /Equal_set=>Heq.
    specialize (Heq e). destruct Heq.
    move: H. rewrite {1}/In_set /member /=.
    have Heq: E.eq e e by done.
    apply elt_compare_eq in Heq. rewrite Heq=>Hcontra.
    specialize (Hcontra Logic.eq_refl). inversion Hcontra.
  Qed.

  Definition eq_set : Set_ elt -> Set_ elt -> Prop := Equal_set.
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

  Lemma bin_compat : forall l e,
      forall x x', eq_set x x' ->
              forall y y', eq_set y y' ->
                      eq_set (Bin l e x y) (Bin l e x' y').
  Proof.
    induction x.
    - intros. destruct x'.
      + rewrite /eq_set /Equal_set /In_set /member //=.
        intros. repeat destruct_match; split=>//; admit.
      + apply bin_not_empty in H. inversion H.
    - intros. admit.
  Admitted.

  Add Parametric Relation : (Set_ elt) @eq_set
      reflexivity proved by (eq_set_refl)
      symmetry proved by (eq_set_sym)
      transitivity proved by (eq_set_trans)
        as eq_set_rel.

  Add Parametric Morphism l e : (Bin l e) with
        signature eq_set ==> eq_set ==> eq_set as union_mor.
  Proof. exact (bin_compat l e). Qed.

  Lemma balanced_children : forall {a} (s1 s2 : Set_ a) l e,
      balanced (Bin l e s1 s2) -> balanced s1 /\ balanced s2.
  Proof. split; simpl in H; move: H; case: and3P=>//; elim; done. Qed.

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

  Ltac derive_ordering :=
    match goal with
    | [H: context[ordered _] |- _ ] =>
      move: H; rewrite /ordered=>H
    end;
    repeat match goal with
           | [ H: context[andb _ (andb _ (andb _ _))] |- _ ] =>
             let Hlo := fresh "Hlo" in
             let Hhi := fresh "Hhi" in
             let Hboundl := fresh "Hboundl" in
             let Hboundh := fresh "Hboundh" in
             move: H; case /and4P=>// =>Hlo Hhi Hbouldl Hboundh
           end.

  Ltac step_in_ordered :=
    apply /and4P=>//; split=>//; try solve [derive_ordering].

  Definition partial_lt {a} `{Ord a} (x : a) : a -> bool :=
    (fun arg => arg GHC.Base.< x).
  Definition partial_gt {a} `{Ord a} (x : a) : a -> bool :=
    (fun arg => arg GHC.Base.> x).

  Lemma partial_lt_mono : forall x y z,
      E.lt y x \/ E.eq x y ->
      partial_lt z x -> partial_lt z y.
  Proof.
    move=>x y z [Hlt | Heq]; rewrite /partial_lt;
           autorewrite with elt_compare; intros; eauto.
      apply E.eq_sym in Heq. eauto.
  Qed.

  Lemma partial_lt_relax : forall x y z,
      E.lt x y \/ E.eq x y ->
      partial_lt x z -> partial_lt y z.
  Proof.
    move=>x y z [Hlt | Heq]; rewrite /partial_lt;
           autorewrite with elt_compare; intros; eauto.
  Qed.

  Lemma partial_gt_mono : forall x y z,
      E.lt x y \/ E.eq x y ->
      partial_gt z x -> partial_gt z y.
  Proof.
    move=>x y z [Hlt | Heq]; rewrite /partial_gt;
           autorewrite with elt_compare; intros; eauto.
  Qed.

  Lemma partial_gt_relax : forall x y z,
      E.lt y x \/ E.eq x y ->
      partial_gt x z -> partial_gt y z.
  Proof.
    move=>x y z [Hlt | Heq]; rewrite /partial_gt;
           autorewrite with elt_compare; intros; eauto.
    apply E.eq_sym in Heq; eauto.
  Qed.

  Definition local_bounded {a} `{Ord a} :=
    fix bounded lo hi t'
      := match t' with
         | Tip => true
         | Bin _ x l r => andb (lo x)
                              (andb (hi x)
                                    (andb
                                       (bounded lo (partial_lt x) l)
                                       (bounded (partial_gt x) hi r)))
         end.

  Ltac solve_local_bounded :=
    repeat match goal with
           | [H: is_true (local_bounded _ _ _) |- _ ] =>
             move: H; rewrite /local_bounded=>?
           | [ H: is_true (andb _ (andb _ (andb _ _))) |- _ ] =>
             let Hlo := fresh "Hlo" in
             let Hhi := fresh "Hhi" in
             let Hboundl := fresh "Hboundl" in
             let Hboundh := fresh "Hboundh" in
             move: H; case /and4P=>//; move=>Hlo Hhi Hboundl Hboundh
           | [ |- is_true (andb _ (andb _ (andb _ _))) ] =>
             apply /and4P=>//; split=>//
           | [H: context[partial_lt _ _] |- _ ] =>
             move: H; rewrite /partial_lt; move=>H
           | [H: context[partial_gt _ _] |- _ ] =>
             move: H; rewrite /partial_gt; move=>H
           end; autorewrite with elt_compare in *; eauto.

  Lemma local_bounded_left_relax : forall {a} `{Ord a} (f g f' : a -> bool) s,
      (forall x, f x -> f' x) ->
      local_bounded f g s ->
      local_bounded f' g s.
  Proof.
    move=>a Heq Hord f g f' s. move: f g f'.
    induction s=>//; intros; solve_local_bounded.
  Qed.

  Lemma local_bounded_right_relax : forall {a} `{Ord a} (f g g' : a -> bool) s,
      (forall x, g x -> g' x) ->
      local_bounded f g s ->
      local_bounded f g' s.
  Proof.
    move=>a Heq Hord f g g' s. move: f g g'.
    induction s=>//; intros; solve_local_bounded.
  Qed.

  Lemma bounded_impl_left_const_true : forall {a} `{GHC.Base.Ord a} f g s,
      local_bounded f g s -> local_bounded (const true) g s.
  Proof.
    intros. apply local_bounded_left_relax with (f0:=f); auto.
  Qed.

  Lemma bounded_impl_right_const_true : forall {a} `{Ord a} f g s,
      local_bounded f g s -> local_bounded f (const true) s.
  Proof.
    intros. apply local_bounded_right_relax with (g0:=g); auto.
  Qed.

  Lemma local_bounded_constr : forall {a} `{Ord a} (f g : a -> bool) x l r,
      f x ->
      g x ->
      local_bounded f (fun arg_0__ => arg_0__ GHC.Base.< x) l ->
      local_bounded (fun arg_1__ => arg_1__ GHC.Base.> x) g r ->
      local_bounded f g (Bin 0 x l r).
  Proof.
    intros. rewrite /local_bounded.
    apply /and4P=>//; split=>//.
  Qed.

  Lemma local_bounded_size_irrelevance :
    forall {a} `{Ord a} (f g : a -> bool) s1 s2 x l r,
      local_bounded f g (Bin s1 x l r) ->
      local_bounded f g (Bin s2 x l r).
  Proof. auto. Qed.

  Lemma ordered_children : forall {a} `{Ord a} (s1 s2 : Set_ a) l e,
      ordered (Bin l e s1 s2) -> ordered s1 /\ ordered s2.
  Proof.
    split; unfold ordered in *; move: H1; case: and4P=>//; elim; intros.
    - eapply (@bounded_impl_right_const_true a H H0). apply H3.
    - eapply (@bounded_impl_left_const_true a H H0). apply H4.
  Qed.

  Lemma ordered_rewrite : forall (s1 s2: Set_ elt) l e1 e2,
      E.eq e1 e2 -> ordered (Bin l e1 s1 s2) -> ordered (Bin l e2 s1 s2).
  Proof.
    move=>s1 s2 l e1 e2 Heq. rewrite /ordered -/local_bounded.
    case /and4P=>//; intros. apply /and4P=>//; split=>//.
    - apply local_bounded_right_relax
        with (g:=fun arg_0__ : E.t => _GHC.Base.<_ arg_0__ e1); auto.
      move=>x. autorewrite with elt_compare. move=>Hlt. eauto.
    - apply local_bounded_left_relax
        with (f:=fun arg_1__ : E.t => _GHC.Base.>_ arg_1__ e1); auto.
      move=>x. autorewrite with elt_compare. move=>Hlt.
      apply E.eq_sym in Heq. eauto.
  Qed.

  Definition local_realsize {a} :=
    fix realsize (t' : Set_ a) : option Size :=
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
      end.

  Lemma validsize_children : forall {a} (s1 s2 : Set_ a) l e,
      validsize (Bin l e s1 s2) -> validsize s1 /\ validsize s2.
  Proof.
    intros; move: H; rewrite /validsize=>H;
      move: H; rewrite -/local_realsize.
    split; generalize dependent e; generalize dependent l.
    - generalize dependent s2.
      destruct s1; intros.
      + move: H. rewrite /local_realsize /= -/local_realsize.
        repeat destruct_match. intro.
        apply /option_int_eqP =>//.
      + rewrite /local_realsize /=. apply /option_int_eqP =>//.
    - generalize dependent s1.
      destruct s2; intros.
      + move: H. rewrite /local_realsize /= -/local_realsize.
        repeat destruct_match. intros. apply /option_int_eqP =>//.
      + rewrite /local_realsize /=. apply /option_int_eqP =>//.
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
    rewrite /WF /valid. move=>s1 s2 l e.
    case: and3P=>//. elim; move=>Hb Ho Hv _.
    apply validsize_children in Hv as Hv2. destruct Hv2.
    move: H0 H Hv. rewrite /validsize -/local_realsize.
    do 2 move /option_int_eq ->. move /option_int_eq.
    destruct_match; move: Heq. rewrite_Int. move /Z_eqP -> =>//.
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

  Lemma WF_balanced : forall t,
      WF t -> balanced t.
  Proof. move=>t; rewrite /WF /valid; case /and3P=>//. Qed.

  Lemma WF_ordered : forall t,
      WF t -> ordered t.
  Proof. move=>t; rewrite /WF /valid; case /and3P=>//. Qed.

  Lemma WF_validsize : forall t,
      WF t -> validsize t.
  Proof. move=>t; rewrite /WF /valid; case /and3P=>//. Qed.

  Lemma WF_singleton : forall e, WF (singleton e).
  Proof. intros. rewrite /WF /valid. apply /and3P=>//. Qed.

  Ltac prepare_for_omega :=
    repeat match goal with
           | [H: context[_ <? _] |- _ ] => move: H
           | [H: context[_ <=? _] |- _ ] => move: H
           | [H: _ < _ |- _ ] => move: H
           | [H: _ <= _ |- _ ] => move: H
           | [H: _ > _ |- _ ] => move: H
           | [H: _ >= _ |- _ ] => move: H
           | [H: context[_ =? _] |- _ ] => move: H
           end; rewrite_size; rewrite_Int;
    rewrite /is_true ?Z.ltb_lt ?Z.ltb_ge ?Z.leb_le ?Z.leb_gt ?Z.eqb_eq.

  Ltac rewrite_for_omega :=
    repeat match goal with
           | [H: context[delta] |- _ ] => move: H
           | [H: context[ratio] |- _ ] => move: H
           end; rewrite /delta /ratio; prepare_for_omega.

  Ltac derive_constraints :=
    repeat match goal with
           | [Hwf: is_true (WF (Bin ?s ?x ?a ?b)) |- _ ] =>
             let Hsum := fresh "Hsum" in
             have: WF (Bin s x a b) by [done];
             move /WF_size_children; rewrite_size;
             move=>Hsum;
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
             let Hvs := fresh "Hvs" in
             have Hvs: validsize (Bin s x a b) by
                 [apply WF_validsize in Hwf];
             let Hbl := fresh "Hbl" in
             have Hbl: balanced (Bin s x a b) by
                 [apply WF_balanced in Hwf];
             clear Hwf
           | [Hwf: is_true (WF ?t) |- _ ] =>
             let Hnonneg := fresh "Hnonneg" in
             have: WF t by [done];
             move /WF_size_nonneg; move=>Hnonneg;
             let Hvs := fresh "Hvs" in
             have Hvs: validsize t by
                 [apply WF_validsize in Hwf];
             clear Hwf
           | [H: is_true (validsize (Bin ?s ?x ?l ?r)) |- _ ] =>
             have: validsize (Bin s x l r) by [done];
             apply validsize_children in H; destruct H;
             rewrite /validsize -/local_realsize;
             move /option_int_eqP ->
           | [H: is_true (validsize ?t) |- _ ] =>
             move: H; rewrite /validsize -/local_realsize;
             move /option_int_eqP ->
           end.

  Ltac lucky_balanced_solve :=
    derive_constraints; subst; rewrite_for_omega; intros; omega.

  Ltac solve_balanced_trivial :=
    solve [auto; repeat (match goal with
                         | [H: is_true (WF (Bin _ _ _ _)) |- _] =>
                           apply WF_balanced in H;
                           apply balanced_children in H;
                           destruct H
                         end; auto)].

  Ltac step_in_balanced :=
    rewrite /balanced; apply /and3P=>//; split=>//;
      try solve_balanced_trivial.

  Ltac solve_balanced :=
    repeat match goal with
           | [ |- is_true (balanced _)] =>
             step_in_balanced
           | [ |- is_true (andb _ (andb _ _))] =>
             step_in_balanced
           | [ |- is_true (orb _ (andb _ _)) ] =>
             apply /orP=>//;
                   ((right; apply /andP=>//) + left);
                    solve [derive_constraints; subst;
                           rewrite_for_omega; intros; omega]
           end;
    try solve [derive_constraints; subst;
           repeat match goal with
                  | [ H: is_true (balanced _) |- _ ] =>
                    move: H; rewrite /balanced;
                    case /and3P=>//; move=>? ? ?
                  end].

  Lemma balanceL_add_size : forall (x : elt) (l r : Set_ elt),
      WF l -> WF r ->
      size (balanceL x l r) = size l + size r + 1.
  Proof.
    destruct r as [sr xr rl rr | ];
      destruct l as [sl xl ll lr | ].
    - rewrite /balanceL; destruct_match.
      + destruct ll as [sll xll lll llr | ];
          destruct lr as [slr xlr lrl lrr | ];
          try solve [intros; derive_constraints; subst;
                     rewrite_for_omega; intros; omega].
        destruct_match; intros;
          rewrite_size; rewrite_Int; (* why can't [omega] solve it? *)
            rewrite -Z.add_assoc [1 + _]Z.add_comm //.
      + intros. rewrite_size; rewrite_Int.
        rewrite -Z.add_assoc [1 + _]Z.add_comm //.
    - intros. rewrite_size; rewrite_Int.
      rewrite Z.add_0_l Z.add_comm //.
    - rewrite /balanceL;
        destruct ll as [sll xll lll llr | ];
        destruct lr as [slr xlr lrl lrr | ].
      + destruct_match; intros; rewrite_size; rewrite_Int;
          rewrite -Z.add_assoc Z.add_0_l Z.add_comm //.
      + intros. derive_constraints; subst.
        destruct Hbalanced; rewrite_for_omega.
        * intros. have Hs: (size lll + size llr = 0) by omega. rewrite Hs //.
        * intros. omega.
      + intros. derive_constraints; subst.
        destruct Hbalanced; rewrite_for_omega.
        * intros. have Hs: (size lrl + size lrr = 0) by omega. rewrite Hs //.
        * intros. omega.
      + intros; derive_constraints. move: Hsum.
        rewrite_for_omega. intros. rewrite -Hsum. reflexivity.
    - rewrite_size. do 2 elim. rewrite_Int. reflexivity.
  Qed.

  Lemma balanceR_add_size : forall (x : elt) (l r : Set_ elt),
      WF l -> WF r ->
      size (balanceR x l r) = size l + size r + 1.
  Proof.
    destruct l as [sl xl ll lr | ];
      destruct r as [sr xr rl rr | ].
    - rewrite /balanceR; destruct_match.
      + destruct rl as [srl xrl rll rlr | ];
          destruct rr as [srr xrr rrl rrr | ];
          try solve [intros; derive_constraints; subst;
                     rewrite_for_omega; intros; omega].
        destruct_match; intros;
          rewrite_size; rewrite_Int; (* why can't [omega] solve it? *)
            rewrite -Z.add_assoc [1 + _]Z.add_comm //.
      + intros. rewrite_size; rewrite_Int.
        rewrite -Z.add_assoc [1 + _]Z.add_comm //.
    - intros. rewrite_size; rewrite_Int.
      rewrite Z.add_0_r Z.add_comm //.
    - rewrite /balanceR;
        destruct rl as [srl xrl rll rlr | ];
        destruct rr as [srr xrr rrl rrr | ].
      + destruct_match; intros; rewrite_size; rewrite_Int;
          rewrite -Z.add_assoc Z.add_0_l Z.add_comm //.
      + intros. derive_constraints; subst.
        destruct Hbalanced; rewrite_for_omega.
        * intros. have Hs: (size rll + size rlr = 0) by omega. rewrite Hs //.
        * intros. omega.
      + intros. derive_constraints; subst.
        destruct Hbalanced; rewrite_for_omega.
        * intros. have Hs: (size rrl + size rrr = 0) by omega. rewrite Hs //.
        * intros. omega.
      + intros; derive_constraints. move: Hsum.
        rewrite_for_omega. intros. rewrite -Hsum. reflexivity.
    - rewrite_size. do 2 elim. rewrite_Int. reflexivity.
  Qed.

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
    (size l + size r <= 2 /\ size r <= 1) \/
    (size l <= delta * size r + 1 /\ size r <= delta * size l).

  Lemma balanceL_balanced: forall (x: elt) (l r : Set_ elt),
      WF l -> WF r ->
      before_balancedL x l r -> balanced (balanceL x l r).
  Proof.
    intros x l r Hwfl Hwfr.
    destruct r as [sr xr rl rr | ]; destruct l as [sl xl ll lr | ];
      rewrite /before_balancedL /balanceL; rewrite_Int; move=>Hbefore.
    - (** [l] and [r] are both [Bin]s. *)
      destruct_match.
      + (** The [ls > delta*rs] branch in Haskell code. *)
        destruct ll as [sll xll lll llr | ];
          destruct lr as [slr xlr lrl lrr | ]; rewrite_Int;
            try solve [lucky_balanced_solve].
        * (** [ll] and [lr] are both Bins *)
          destruct_match; solve_balanced.
          -- (** [Bin (1+lls+size lrl) lx ll lrl] is balanced. *)
            destruct lrl; solve_balanced.
          -- (** [Bin (1+rs+size lrr) x lrr r] is balanced. *)
            destruct lrr; solve_balanced.
      + (** The [otherwise] branch, i.e. [ls <= delta*rs]. *)
        solve_balanced.
    - (** [l] is [Tip] *)
      destruct rl; destruct rr; solve_balanced.
    - (** [r] is [Tip] *)
      destruct ll as [sll xll lll llr | ];
        destruct lr as [slr xlr lrl lrr | ];
        solve_balanced.
      (** [ll] is [Bin sll xll lll llr] *)
      destruct_match; solve_balanced.
    - (** Both [l] and [r] and [Tip]s. *)
      step_in_balanced.
      Time Qed. (* Finished transaction in 20.068 secs (19.946u,0.053s) (successful) *)

    Definition before_balancedR (x: elt) (l r : Set_ elt) : Prop :=
    (size l + size r <= 2 /\ size l <= 1) \/
    (size r <= delta * size l + 1 /\ size l <= delta * size r).

  Lemma balanceR_balanced: forall (x: elt) (l r : Set_ elt),
      WF l -> WF r ->
      before_balancedR x l r -> balanced (balanceR x l r).
  Proof.
    intros x l r Hwfl Hwfr.
    destruct l as [sl xl ll lr | ]; destruct r as [sr xr rl rr | ];
      rewrite /before_balancedR /balanceR; rewrite_Int; move=>Hbefore.
    - (** [l] and [r] are both [Bin]s. *)
      destruct_match.
      + (** The [rs > delta*ls] branch in Haskell code. *)
        destruct rl as [srl xrl rll rlr | ];
          destruct rr as [srr xrr rrl rrr | ]; rewrite_Int;
            try solve [lucky_balanced_solve].
        * (** [rl] and [rr] are both Bins *)
          destruct_match; solve_balanced.
          -- (** [Bin (1+ls+size rll) x l rll] is balanced. *)
            destruct rll; solve_balanced.
          -- (** [Bin (1+rrs+size rlr) rx rlr rr] is balanced. *)
            destruct rlr; solve_balanced.
      + (** The [otherwise] branch, i.e. [ls <= delta*rs]. *)
        solve_balanced.
    - (** [r] is [Tip] *)
      destruct ll; destruct lr; solve_balanced.
    - (** [l] is [Tip] *)
        destruct rl as [srl xrl rll rlr | ];
          destruct rr as [srr xrr rrl rrr | ];
          solve_balanced.
      (** [rr] is [Bin srr xrr rrl rrr] *)
      destruct_match; solve_balanced.
    - (** Both [l] and [r] and [Tip]s. *)
      step_in_balanced.
      Time Qed. (* Finished transaction in 20.24 secs (20.106u,0.059s) (successful) *)

  Definition before_ordered (x : elt) (l r : Set_ elt) (f g : elt -> bool) :=
    f x /\ (forall x y, E.lt x y \/ E.eq x y -> f x -> f y) /\
    g x /\ (forall x y, E.lt y x \/ E.eq x y -> g x -> g y) /\
    local_bounded f (fun arg_1__ => arg_1__ GHC.Base.< x) l /\
    local_bounded (fun arg_0__ => arg_0__ GHC.Base.> x) g r.

  Ltac derive_compare :=
    repeat match goal with
           | [H: is_true
                   (andb _ (andb _ (andb (local_bounded _ _ _)
                                         (local_bounded _ _ _)))) |- _] =>
             let Hc1 := fresh "Hcomp" in
             let Hc2 := fresh "Hcomp" in
             let Hl1 := fresh "Hlb" in
             let Hl2 := fresh "Hlb" in
             move: H; case /and4P=>//;
             rewrite -/local_bounded /partial_gt /partial_lt;
             move=> Hc1 Hc2 Hl1 Hl2
           | [H: is_true (local_bounded _ _ _) |- _ ] =>
             let Hc1 := fresh "Hcomp" in
             let Hc2 := fresh "Hcomp" in
             let Hl1 := fresh "Hlb" in
             let Hl2 := fresh "Hlb" in
             move: H; rewrite /local_bounded;
             case /and4P=>//;
             rewrite -/local_bounded /partial_gt /partial_lt;
             move=> Hc1 Hc2 Hl1 Hl2
           end; autorewrite with elt_compare in *.

  Ltac rel_deriver := eauto 2.
  
  Ltac solve_relations_single_step :=
    match goal with
    | [ |- E.lt ?a ?b -> _ ] =>
      do [move /elt_compare_gt -> =>//
         | move /elt_compare_lt -> =>//]
    | [ |- E.eq ?a ?b -> _ ] =>
      move /elt_compare_eq -> =>//
    | [ |- context[Base.compare ?a ?b]] =>
      do [have: E.lt a b by [rel_deriver]
         | have: E.eq a b by [rel_deriver]
         | have: E.lt b a by [rel_deriver]]
    end.

  Ltac solve_relations :=
    repeat solve_relations_single_step.

  Ltac prepare_relations :=
    try multimatch goal with
        | [H: E.eq ?a ?b |- _ ] =>
          first [(match goal with
                  | [H': E.eq b a |- _ ] =>
                    idtac
                  end)
                | (have: E.eq b a by [apply E.eq_sym; apply H];
                   move=>?)]
        end.

  Ltac rewrite_relations :=
    repeat (autorewrite with elt_compare in *;
            prepare_relations;
            solve_relations;
            try match goal with
                | [ |- context[Base.compare ?a ?b]] =>
                  destruct_match
                end).
  
  Ltac solve_membership :=
    solve [derive_compare; rewrite_relations].
    
  Lemma membership_prop : forall s y x l r,
      member y (Bin s x l r) ->
      (E.eq y x \/ member y l \/ member y r).
  Proof.
    move=>s y x l r. rewrite /member.
    destruct_match;
      try (right; (left + right); solve [auto]).
    left. apply /elt_compare_eq =>//.
  Qed.

  Ltac prepare_bst :=
    intros;
    repeat match goal with
           | [H: context[member _ _] |- _] => move: H
           | [H: context[In_set _ _] |- _] => move: H
           end;
    rewrite /In_set /balanceL /balanceR /member;
    repeat match goal with
           | [H: before_ordered _ _ _ _ _ |- _ ] =>
             move: H; rewrite /before_ordered; move=>[? [? [? [? [? ?]]]]]
           end;
    repeat match goal with
           | [H: before_balancedL _ _ _ |- _ ] =>
             move: H; rewrite /before_balancedL; move=>H
           | [H: before_balancedR _ _ _ |- _ ] =>
             move: H; rewrite /before_balancedR; move=>H
           end.

  Ltac solve_bst :=
    repeat (destruct_match; rewrite_relations;
            try solve [lucky_balanced_solve]);
    try solve [derive_compare; OrdFacts.order].

  Lemma size_zero : forall (s : Set_ elt),
      WF s -> size s <= 0 -> s = Tip.
  Proof.
    destruct s; intros.
    - derive_constraints. omega.
    - reflexivity.
  Qed.

  Lemma balanceL_preserves_membership : forall s y x l r,
      WF l ->
      WF r ->
      before_balancedL x l r ->
      before_ordered x l r (const true) (const true) ->
      (In_set y (Bin s x l r) <-> In_set y (balanceL x l r)).
  Proof.
    prepare_bst. split; solve_bst.
    - have Hs0: size s1_1 <= 0.
      { derive_constraints; rewrite_for_omega; intros; omega. }
      apply WF_children in H; destruct H.
      apply WF_children in H2; destruct H2.
      apply (size_zero _ H2) in Hs0; subst; auto.
    - have Hs0: size s1_2 <= 0.
      { derive_constraints; rewrite_for_omega; intros; omega. }
      apply WF_children in H; destruct H.
      apply WF_children in H2; destruct H2.
      apply (size_zero _ H3) in Hs0; subst; auto.
  Qed.

  Lemma balanceR_preserves_membership : forall s y x l r,
      WF l ->
      WF r ->
      before_balancedR x l r ->
      before_ordered x l r (const true) (const true) ->
      (In_set y (Bin s x l r) <-> In_set y (balanceR x l r)).
  Proof.
    prepare_bst. split; solve_bst.
    - have Hs0: size s1_1 <= 0.
      { derive_constraints; rewrite_for_omega; intros; omega. }
      apply WF_children in H0; destruct H0.
      apply WF_children in H0; destruct H0.
      apply (size_zero _ H0) in Hs0; subst; auto.
    - have Hs0: size s1_2 <= 0.
      { derive_constraints; rewrite_for_omega; intros; omega. }
      apply WF_children in H0; destruct H0.
      apply WF_children in H0; destruct H0.
      apply (size_zero _ H3) in Hs0; subst; auto.
  Qed.

  Lemma size_irrelevance_in_ordered : forall s1 s2 x (l r : Set_ elt),
      ordered (Bin s1 x l r) -> ordered (Bin s2 x l r).
  Proof. move=>s1 s2 x l r. rewrite /ordered; auto. Qed.

  Lemma balanceL_ordered : forall (x: elt) (l r : Set_ elt) f g,
      (** We need [before_balancedL] as preconditions to eliminate the
          impossible cases. *)
      WF l ->
      WF r ->
      before_balancedL x l r ->
      before_ordered x l r f g ->
      local_bounded f g (balanceL x l r).
  Proof.
    move=>x l r f g Hwfl Hwfr.
    destruct r as [sr xr rl rr | ]; destruct l as [sl xl ll lr | ];
      rewrite /before_ordered /balanceL; rewrite_Int;
        move=>Hbefore_balance Hbefore_ordered;
               destruct Hbefore_ordered as [? [? [? [? [? ?]]]]];
               try solve [solve_local_bounded].
    - (** Both [r] and [l] are [Bin]s *)
      destruct_match; try solve [solve_local_bounded].
      destruct ll as [sll xll lll llr | ];
        destruct lr as [slr xlr lrl lrr | ];
        try solve [lucky_balanced_solve].
      destruct_match; rewrite_Int; solve_local_bounded.
    - (** [r] is a [Tip] *)
      destruct ll as [sll xll lll llr | ];
        destruct lr as [slr xlr lrl lrr | ];
        try solve [solve_local_bounded].
      destruct_match; solve_local_bounded.
  Time Qed. (* Finished transaction in 0.67 secs (0.668u,0.001s) (successful) *)

  Lemma balanceR_ordered : forall (x: elt) (l r : Set_ elt) f g,
      WF l ->
      WF r ->
      before_balancedR x l r ->
      before_ordered x l r f g ->
      local_bounded f g (balanceR x l r).
  Proof.
    move=>x l r f g Hwfl Hwfr.
    destruct l as [sl xl ll lr | ]; destruct r as [sr xr rl rr | ];
      rewrite /before_ordered /balanceR; rewrite_Int;
        move=>Hbefore_balance Hbefore_ordered;
               destruct Hbefore_ordered as [? [? [? [? [? ?]]]]];
               try solve [solve_local_bounded].
    - (** Both [r] and [l] are [Bin]s *)
      destruct_match; try solve [solve_local_bounded].
        destruct rl as [srl xrl rll rlr | ];
          destruct rr as [srr xrr rrl rrr | ];
          try solve [lucky_balanced_solve].
      destruct_match; rewrite_Int; solve_local_bounded.
    - (** [l] is a [Tip] *)
      destruct rl as [srl xrl rll rlr | ];
        destruct rr as [srr xrr rrl rrr | ];
        try solve [solve_local_bounded].
      destruct_match; solve_local_bounded.
  Time Qed. (* Finished transaction in 0.644 secs (0.642u,0.001s) (successful) *)

  Ltac solve_realsize :=
    apply /option_int_eqP;
    rewrite /local_realsize;
    derive_constraints; rewrite_size; rewrite_Int;
    repeat match goal with
           | [ |- context[if ?c then _ else _] ] =>
             let Heq := fresh "Heq" in
             have Heq: c by [ rewrite_for_omega; omega];
             rewrite Heq=>//
           end.

  Lemma balanceL_validsize: forall (x: elt) (l r : Set_ elt),
      WF l -> WF r ->
      before_balancedL x l r -> validsize (balanceL x l r).
  Proof.
    move=>x l r Hwfl Hwfr.
    rewrite /validsize -/local_realsize.
    destruct r as [sr xr rl rr | ]; destruct l as [sl xl ll lr | ];
      rewrite /before_balancedL /balanceL; intros; try solve [solve_realsize].
    - rewrite_Int. destruct_match; try solve [solve_realsize].
      destruct ll as [sll xll lll llr | ];
        destruct lr as [slr xlr lrl lrr | ];
        try solve [lucky_balanced_solve].
      destruct_match; solve_realsize.
    - destruct ll as [sll xll lll llr | ];
        destruct lr as [slr xlr lrl lrr | ];
        try solve [lucky_balanced_solve || solve_realsize].
  Time Qed. (* Finished transaction in 2.83 secs (2.822u,0.004s) (successful) *)

  Lemma balanceR_validsize: forall (x: elt) (l r : Set_ elt),
      WF l -> WF r ->
      before_balancedR x l r -> validsize (balanceR x l r).
  Proof.
    move=>x l r Hwfl Hwfr.
    rewrite /validsize -/local_realsize.
    destruct l as [sl xl ll lr | ]; destruct r as [sr xr rl rr | ];
      rewrite /before_ordered /balanceR; intros; try solve [solve_realsize].
    - rewrite_Int. destruct_match; try solve [solve_realsize].
      destruct rl as [srl xrl rll rlr | ];
        destruct rr as [srr xrr rrl rrr | ];
        try solve [lucky_balanced_solve].
      destruct_match; solve_realsize.
    - destruct rl as [srl xrl rll rlr | ];
        destruct rr as [srr xrr rrl rrr | ];
        try solve [lucky_balanced_solve || solve_realsize].
      destruct_match; solve_realsize.
  Time Qed. (* Finished transaction in 2.29 secs (2.284u,0.002s) (successful) *)

  Lemma balanceL_WF: forall (x: elt) (l r : Set_ elt),
      WF l -> WF r ->
      before_balancedL x l r ->
      before_ordered x l r (const true) (const true) ->
      WF (balanceL x l r).
  Proof with auto.
    intros. rewrite /WF /valid.
    apply /and3P=>//; split.
    - apply balanceL_balanced...
    - apply balanceL_ordered...
    - apply balanceL_validsize...
  Qed.

  Lemma balanceR_WF: forall (x: elt) (l r : Set_ elt),
      WF l -> WF r ->
      before_balancedR x l r ->
      before_ordered x l r (const true) (const true) ->
      WF (balanceR x l r).
  Proof with auto.
    intros. rewrite /WF /valid.
    apply /and3P=>//; split.
    - apply balanceR_balanced...
    - apply balanceR_ordered...
    - apply balanceR_validsize...
  Qed.


  Lemma inset_balanceL : forall (x y : elt) (l r : Set_ elt),
      WF l ->
      WF r ->
      before_balancedL x l r ->
      before_ordered x l r (const true) (const true) ->
      E.eq x y \/ (E.lt y x /\ In_set y l) \/ (E.lt x y /\ In_set y r) ->
      In_set y (balanceL x l r).
  Proof.
    prepare_bst. move=>[? | [[? ?] | [? ?]]]; solve_bst.
    - have Hs0: size s5 <= 0.
      { derive_constraints; rewrite_for_omega; intros; omega. }
      apply WF_children in H; destruct H.
      apply WF_children in H2; destruct H2.
      apply (size_zero _ H2) in Hs0; subst; auto.
    - have Hs0: size s6 <= 0.
      { derive_constraints; rewrite_for_omega; intros; omega. }
      apply WF_children in H; destruct H.
      apply WF_children in H2; destruct H2.
      apply (size_zero _ H3) in Hs0; subst; auto.
  Time Qed. (* Finished transaction in 5.667 secs (5.626u,0.035s) (successful) *)
  
  Lemma inset_balanceR : forall (x y : elt) (l r : Set_ elt),
      WF l ->
      WF r ->
      before_balancedR x l r ->
      before_ordered x l r (const true) (const true) ->
      E.eq x y \/ (E.lt y x /\ In_set y l) \/ (E.lt x y /\ In_set y r) ->
      In_set y (balanceR x l r).
  Proof.
    prepare_bst. move=>[? | [[? ?] | [? ?]]]; solve_bst.
    - have Hs0: size s5 <= 0.
      { derive_constraints; rewrite_for_omega; intros; omega. }
      apply WF_children in H0; destruct H0.
      apply WF_children in H0; destruct H0.
      apply (size_zero _ H0) in Hs0; subst; auto.
    - have Hs0: size s6 <= 0.
      { derive_constraints; rewrite_for_omega; intros; omega. }
      apply WF_children in H0; destruct H0.
      apply WF_children in H0; destruct H0.
      apply (size_zero _ H3) in Hs0; subst; auto.
  Time Qed. (* Finished transaction in 5.877 secs (5.847u,0.014s) (successful) *)
  
  Definition mem : elt -> t -> bool := fun e s' =>
    s <-- s' ;; member e s.

  Ltac split3 := split; [| split].

  Ltac solve_local_bounded_with_relax :=
    solve_local_bounded; rewrite -/local_bounded;
    ((eapply local_bounded_right_relax; [| eassumption];
      intros; eapply partial_lt_relax;
      (idtac + (multimatch goal with
                | [H: E.eq _ _ |- _] => apply E.eq_sym in H
                end))) +
     (eapply local_bounded_left_relax; [| eassumption];
      intros; eapply partial_gt_relax;
      (idtac + (multimatch goal with
                | [H: E.eq _ _ |- _] => apply E.eq_sym in H
                end)))); solve [eauto].

  Lemma insert_prop : forall e s,
      WF s ->
      WF (insert e s) /\
      (size (insert e s) = size s + 1 \/ size (insert e s) = size s) /\
      (forall a,
          (forall (f : elt -> bool),
              E.lt e a -> f e ->
              (forall x y, E.lt x y \/ E.eq x y -> f x -> f y) ->
              local_bounded f (fun arg => arg GHC.Base.< a) s ->
              local_bounded f (fun arg => arg GHC.Base.< a) (insert e s)) /\
          (forall (g : elt -> bool),
              E.lt a e -> g e ->
              (forall x y, E.lt y x \/ E.eq x y -> g x -> g y) ->
              local_bounded (fun arg => arg GHC.Base.> a) g s ->
              local_bounded (fun arg => arg GHC.Base.> a) g (insert e s))).
  Proof.
    induction s.
    - intros. rewrite /insert/=. destruct_match; split3.
      + (** s is Bin, e = a, prove: WF (insert e s) *)
        apply elt_compare_eq in Heq. move: H.
        rewrite /WF /valid. case /and3P=>//; intros.
        apply /and3P=>//; split=>//. apply E.eq_sym in Heq.
        eapply ordered_rewrite; eauto.
      + (** prove [size (insert e s) = size s] *)
        right. rewrite /size=>//.
      + intros. split; intros; solve_local_bounded_with_relax.
      + (** s is Bin, e < a, prove: WF (insert e s) *)
        intros. apply balanceL_WF.
        * (** WF (insert e s2) *)
          apply WF_children in H. apply IHs1. tauto.
        * (** WF s3 *)
          apply WF_children in H. tauto.
        * (** (insert e s2) and s3 satisfy [before_balancedL]'s
              pre-condbitions. *)
          rewrite -/insert /before_balancedL.
          have Hs1: WF s2 by [apply WF_children in H; tauto].
          apply IHs1 in Hs1; destruct Hs1.
          (** cases analysis: did we insert an element to s2?  *)
          destruct H1 as [[H1 | H1] _].
          -- (** we did *)
            destruct s2; destruct s3; derive_constraints; subst;
              repeat match goal with
                     | [H: _ \/ _ |- _ ] => destruct H
                     | [H: _ /\ _ |- _ ] => destruct H
                     end; rewrite_for_omega; rewrite ?H1;
                try solve [(right + left); omega].
          -- (** we didn't *) derive_constraints; subst.
             rewrite H1. destruct Hbalanced; (left + right); omega.
        * (** prove [before_ordered] pre-conditions *)
          rewrite -/insert /before_ordered.
          have Hord: ordered (Bin 0 a s2 s3).
          { apply WF_ordered in H.
            eapply size_irrelevance_in_ordered. eauto. }
          move: Hord. rewrite /ordered. rewrite -/local_bounded.
          case /and4P=>// => _ _ Hlo Hhi.
          split; [| split; [| split; [| split; [| split]]]]=>//.
          apply WF_children in H; destruct H.
          apply IHs1 in H. destruct H as [ _ [_ Hord']].
          specialize (Hord' a); destruct Hord'.
          apply H=>//. autorewrite with elt_compare in *. auto.
      + (** prove [size (insert e s) = size s + 1] *)
        rewrite -/insert.
        have Hs1: WF s2 by [apply WF_children in H; tauto].
        rewrite balanceL_add_size=>//.
        * apply IHs1 in Hs1.
          destruct Hs1 as [_ [[Hs | Hs] _]];
            derive_constraints; subst; rewrite Hs.
          -- left.
             rewrite [size s2 + 1]Z.add_comm [(_ + 1) + 1]Z.add_comm !Z.add_assoc //.
          -- right. reflexivity.
        * apply IHs1 in Hs1. tauto.
        * apply WF_children in H. tauto.
      + intros; split; intros;
          apply balanceL_ordered=>//;
          try solve [rewrite -/insert; apply WF_children in H; destruct H;
                     apply IHs1 in H; tauto];
          try solve [apply WF_children in H; tauto];
          try solve [rewrite -/insert /before_balancedL;
                     have Hwf: WF (Bin s1 a s2 s3) by [done];
                     apply WF_children in H; destruct H;
                     apply IHs1 in H; destruct H as [? [Hs _]];
                     destruct Hs; derive_constraints;
                     subst; rewrite_for_omega;
                     rewrite H5; intros; omega].
        * move: H3. case /and4P=>// => Hf Hlt Hlo Hhi.
          rewrite -/insert /before_ordered.
          split; [| split; [| split; [| split; [| split]]]]=>//.
          -- intros. autorewrite with elt_compare in *.
             intuition; eauto. apply E.eq_sym in H5; eauto.
          -- apply WF_children in H; destruct H.
             apply IHs1 in H. destruct H as [ _ [_ Hord']].
             specialize (Hord' a); destruct Hord'.
             apply H=>//. autorewrite with elt_compare in *. auto.
        * move: H3. case /and4P=>// => Hf Hlt Hlo Hhi.
          rewrite -/insert /before_ordered.
          split; [| split; [| split; [| split; [| split]]]]=>//.
          -- intros. autorewrite with elt_compare in *.
             intuition; eauto. 
          -- apply WF_children in H; destruct H.
             apply IHs1 in H. destruct H as [ _ [_ Hord']].
             specialize (Hord' a0); destruct Hord'.
             apply H4=>//; try intros;
               autorewrite with elt_compare in *; auto.
             destruct H5; eauto. apply E.eq_sym in H5. eauto.
      + (** s is Bin, e > a, prove: WF (insert e s) *)
        intros. apply balanceR_WF.
        * (** WF s2 *)
          apply WF_children in H. tauto.
        * (** WF (insert e s3) *)
          apply WF_children in H. apply IHs2. tauto.
        * (** s2 and (insert e s3) satisfy [before_balancedR]'s
              pre-condbitions. *)
          rewrite -/insert /before_balancedR.
          have Hs2: WF s3 by [apply WF_children in H; tauto].
          apply IHs2 in Hs2; destruct Hs2.
          (** cases analysis: did we insert an element to s3?  *)
          destruct H1 as [[H1 | H1] _].
          -- (** we did *)
            destruct s2; destruct s3; derive_constraints; subst;
              rewrite_for_omega; rewrite ?H1; intros; omega.
          -- (** we didn't *) derive_constraints; subst.
             rewrite H1. destruct Hbalanced; (left + right); omega.
        * (** prove [before_ordered] pre-conditions *)
          rewrite -/insert /before_ordered.
          have Hord: ordered (Bin 0 a s2 s3).
          { apply WF_ordered in H.
            eapply size_irrelevance_in_ordered. eauto. }
          move: Hord. rewrite /ordered. rewrite -/local_bounded.
          case /and4P=>// => _ _ Hlo Hhi.
          split; [| split; [| split; [| split; [| split]]]]=>//.
          apply WF_children in H; destruct H.
          apply IHs2 in H0. destruct H0 as [ _ [_ Hord']].
          specialize (Hord' a); destruct Hord'.
          apply H1=>//. autorewrite with elt_compare in *. auto.
      + rewrite -/insert.
        have Hs2: WF s3 by [apply WF_children in H; tauto].
        rewrite balanceR_add_size=>//.
        * apply IHs2 in Hs2.
          destruct Hs2 as [_ [[Hs | Hs] _]];
            derive_constraints; subst; rewrite Hs.
          -- left. rewrite Z.add_assoc //.
          -- right. reflexivity.
        * apply WF_children in H. tauto.
        * apply IHs2 in Hs2. tauto.
      + intros; split; intros;
          apply balanceR_ordered=>//;
          try solve [rewrite -/insert; apply WF_children in H; destruct H;
                     apply IHs1 in H; tauto];
          try solve [apply WF_children in H; tauto];
          try solve [rewrite -/insert /before_balancedR;
                     have Hwf: WF (Bin s1 a s2 s3) by [done];
                     apply WF_children in H; destruct H as [_ H];
                     apply IHs2 in H; destruct H as [? [Hs _]];
                     destruct Hs as [Hs | Hs]; derive_constraints;
                       subst; rewrite_for_omega;
                         rewrite Hs; intros; omega].
        * move: H3. case /and4P=>// => Hf Hlt Hlo Hhi.
          rewrite -/insert /before_ordered.
          split; [| split; [| split; [| split; [| split]]]]=>//.
          -- intros. autorewrite with elt_compare in *.
             intuition; eauto. apply E.eq_sym in H5; eauto.
          -- apply WF_children in H; destruct H.
             apply IHs2 in H3. destruct H3 as [ _ [_ Hord']].
             specialize (Hord' a0); destruct Hord'.
             apply H3=>//; try intros; autorewrite with elt_compare in *; auto.
             destruct H5; eauto.
        * move: H3. case /and4P=>// => Hf Hlt Hlo Hhi.
          rewrite -/insert /before_ordered.
          split; [| split; [| split; [| split; [| split]]]]=>//.
          -- intros. autorewrite with elt_compare in *.
             intuition; eauto. 
          -- apply WF_children in H; destruct H.
             apply IHs2 in H3. destruct H3 as [ _ [_ Hord']].
             specialize (Hord' a); destruct Hord'.
             apply H4=>//; autorewrite with elt_compare in *; auto.
    - simpl. elim. rewrite /singleton. split3.
      + apply WF_singleton.
      + left; reflexivity.
      + intros; split; intros; apply /and3P=>//; split=>//.
        * autorewrite with elt_compare. auto.
        * autorewrite with elt_compare. auto.
  Time Qed. (* Finished transaction in 1.354 secs (1.301u,0.045s) (successful) *)

  Lemma left_insert_before_balancedL : forall e s l r x,
      WF (Bin s e l r) ->
      E.lt x e ->
      before_balancedL e (insert x l) r.
  Proof.
    intros; rewrite -/insert /before_balancedL.
    have Hs: size (insert x l) = size l + 1 \/ size (insert x l) = size l
      by [ apply WF_children in H; destruct H;
           apply insert_prop with (e:=x) in H; tauto ].
    derive_constraints.
    destruct Hs; rewrite H; destruct Hbalanced;
      solve [(left + right); split; rewrite_for_omega; intros; omega].
  Qed.

  Lemma right_insert_before_balancedR : forall e s l r x,
      WF (Bin s e l r) ->
      E.lt e x ->
      before_balancedR e l (insert x r).
  Proof.
    intros; rewrite -/insert /before_balancedR.
    have Hs: size (insert x r) = size r + 1 \/ size (insert x r) = size r
      by [ apply WF_children in H; destruct H;
           apply insert_prop with (e:=x) in H1; tauto ].
    derive_constraints.
    destruct Hs; rewrite H; destruct Hbalanced;
      solve [(left + right); split; rewrite_for_omega; intros; omega].
  Qed.

  Definition add (e: elt) (s': t) : t.
    refine (s <-- s' ;;
              pack (insert e s) _).
    move: i=>H. eapply insert_prop in H. destruct H. eauto.
  Defined.

  Definition singleton : elt -> t.
    refine (fun e => pack (singleton e) _).
    apply WF_singleton.
  Defined.

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
    move=>s x y. rewrite /In /In_set. elim s=>[s'].
    elim s'=>[sl sx l IHl r IHr | ]=>Hwf Heq.
    - simpl. destruct_match.
      + move: Heq0. move /elt_compare_eq => Heq'.
        prepare_relations. solve_relations.
      + move: Heq0. move /elt_compare_lt => Heq'.
        prepare_relations. solve_relations.
        move: Hwf. move /WF_children. elim. move=>? _.
        apply IHl=>//.
      + move: Heq0. move /elt_compare_gt => Heq'.
        prepare_relations. solve_relations.
        move: Hwf. move /WF_children. elim. move=>_ ?.
        apply IHr=>//.
    - elim. rewrite /member //.
  Qed.

  Lemma mem_1 : forall (s : t) (x : elt), In x s -> mem x s = true.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof. unfold In; intros; destruct s as [s]; auto. Qed.

  Lemma equal_1 : forall s s' : t, Equal s s' -> equal s s' = true. Admitted.
  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'. Admitted.
  Lemma subset_1 : forall s s' : t, Subset s s' -> subset s s' = true. Admitted.
  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'. Admitted.

  Lemma singleton_1 :
    forall x y : elt, In y (singleton x) -> E.eq x y.
  Proof.
    rewrite /singleton /In /In_set //.
    intros. simpl in H.
    destruct (Base.compare y x) eqn:Hcomp;
      move: Hcomp =>//; move /elt_compare_eq; auto.
  Qed.

  Lemma singleton_2 :
    forall x y : elt, E.eq x y -> In y (singleton x).
  Proof.
    rewrite /singleton /In /In_set //.
    rewrite_compare_e. intros.
    destruct (Base.compare y x) eqn:Hcomp=>//; exfalso; move: Hcomp;
      prepare_relations; solve_relations.
  Qed.

  Lemma WF_prop_l1 :
    forall (l r : Set_ elt) (x y : elt) s,
      WF (Bin s x l r) ->
      E.lt y x ->
      WF (insert y l).
  Proof.
    intros; apply WF_children in H; destruct H.
    apply insert_prop with (e:=y) in H. destruct H as [? _]. auto.
  Qed.

  Lemma WF_prop_r1 :
    forall (l r : Set_ elt) (x y : elt) s,
      WF (Bin s x l r) ->
      E.lt x y ->
      WF (insert y r).
  Proof.
    intros; apply WF_children in H; destruct H.
    apply insert_prop with (e:=y) in H1. destruct H1 as [? _]. auto.
  Qed.

  Lemma WF_prop_l2 :
    forall (l r : Set_ elt) (x y : elt) s,
      WF (Bin s x l r) ->
      E.lt y x ->
      before_balancedL x (insert y l) r.
  Proof.
    intros. have Hwf: WF (Bin s x l r) by [done].
    apply WF_children in H; destruct H.
    apply insert_prop with (e:=y) in H. destruct H as [_ [? _]].
    rewrite /before_balancedL. derive_constraints; subst.
    destruct H as [Hs | Hs]; rewrite_for_omega;
      rewrite Hs; intros; omega.
  Qed.

  Lemma WF_prop_r2 :
    forall (l r : Set_ elt) (x y : elt) s,
      WF (Bin s x l r) ->
      E.lt x y ->
      before_balancedR x l (insert y r).
  Proof.
    intros. have Hwf: WF (Bin s x l r) by [done].
    apply WF_children in H; destruct H.
    apply insert_prop with (e:=y) in H1. destruct H1 as [_ [? _]].
    rewrite /before_balancedR. derive_constraints; subst.
    destruct H1 as [Hs | Hs]; rewrite_for_omega;
      rewrite Hs; intros; omega.
  Qed.

  Lemma WF_prop_l3:
    forall (l r : Set_ elt) (x y : elt) s,
      WF (Bin s x l r) ->
      E.lt y x ->
      before_ordered x (insert y l) r (const true) (const true).
  Proof.
    intros. have Hord: ordered (Bin 0 x l r).
    { apply WF_ordered in H.
      eapply size_irrelevance_in_ordered. eauto. }
    move: Hord. rewrite /ordered. rewrite -/local_bounded.
    case /and4P=>//. move=>_ _ Hlo Hhi.
    rewrite /before_ordered.
    apply WF_children in H; destruct H.
    apply insert_prop with (e:=y) in H. destruct H as [_ [_ ?]].
    specialize (H x). destruct H as [Hf Hg]. repeat split=>//.
    apply Hf=>//.
  Qed.

  Lemma WF_prop_r3:
    forall (l r : Set_ elt) (x y : elt) s,
      WF (Bin s x l r) ->
      E.lt x y ->
      before_ordered x l (insert y r) (const true) (const true).
  Proof.
    intros. have Hord: ordered (Bin 0 x l r).
    { apply WF_ordered in H.
      eapply size_irrelevance_in_ordered. eauto. }
    move: Hord. rewrite /ordered. rewrite -/local_bounded.
    case /and4P=>//. move=>_ _ Hlo Hhi.
    rewrite /before_ordered.
    apply WF_children in H; destruct H.
    apply insert_prop with (e:=y) in H1. destruct H1 as [_ [_ ?]].
    specialize (H1 x). destruct H1 as [Hf Hg]. repeat split=>//.
    apply Hg=>//.
  Qed.

  Hint Resolve WF_prop_l1.
  Hint Resolve WF_prop_l2.
  Hint Resolve WF_prop_l3.
  Hint Resolve WF_prop_r1.
  Hint Resolve WF_prop_r2.
  Hint Resolve WF_prop_r3.

  Lemma inset_destruct :
    forall (l r : Set_ elt) (x y : elt) s,
      In_set y (Bin s x l r) ->
      E.eq x y \/ (E.lt y x /\ In_set y l) \/ (E.lt x y /\ In_set y r).
  Proof.
    move=>l r x y s. rewrite /In_set /member /= -/member.
    destruct_match; autorewrite with elt_compare in *.
    - left. apply E.eq_sym. done.
    - right; left. intuition.
    - right; right; intuition.
  Qed.
  
  Lemma add_1 :
    forall (s : t) (x y : elt), E.eq x y -> In y (add x s).
  Proof with eauto.
    intros. destruct s as [s]. simpl. induction s.
    - rewrite /insert /= -/insert. destruct_match.
      + rewrite /In_set /member /= -/member.
        move: H. move /E.eq_sym /elt_compare_eq -> =>//.
      + autorewrite with elt_compare in *; apply inset_balanceL...
        * apply WF_children in i; tauto.
        * right; left. split.
          -- apply E.eq_sym in H...
          -- apply WF_children in i. destruct i. apply IHs1 in H0...
      + autorewrite with elt_compare in *; apply inset_balanceR...
        * apply WF_children in i; tauto.
        * right; right. split...
          -- apply WF_children in i. destruct i. apply IHs2 in H1...
    - rewrite /insert /= /Base.singleton /In_set /member /=.
      move: H. move /E.eq_sym /elt_compare_eq -> =>//.
  Qed.
        
  Lemma add_2 : forall (s : t) (x y : elt), In y s -> In y (add x s).
  Proof with eauto.
    destruct s as [s]. simpl. intros; induction s.
    - rewrite /insert /= -/insert. destruct_match.
      + move: H. rewrite /In_set /member /= -/member.
        have Heq': (Base.compare y x = Base.compare y a).
        {destruct (Base.compare y a) eqn:Hcomp;
            autorewrite with elt_compare in *; eauto.
          apply E.eq_sym in Heq. eauto. }
        destruct_match; rewrite Heq' //.
      + autorewrite with elt_compare in *; apply inset_balanceL...
        * apply WF_children in i. tauto.
        * apply inset_destruct in H. intuition.
          apply WF_children in i; destruct i.
          apply (IHs1 H) in H1. intuition.
      + autorewrite with elt_compare in *; apply inset_balanceR...
        * apply WF_children in i. tauto.
        * apply inset_destruct in H. intuition.
          apply WF_children in i; destruct i.
          apply (IHs2 H2) in H1. intuition.
    - inversion H.
  Qed.
    
  Lemma add_3 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y (add x s) -> In y s.
  Proof.
    destruct s as [s]. simpl. intros; induction s.
    - move: H0. rewrite /insert /= -/insert. destruct_match.
      + have Heq': (Base.compare y x = Base.compare y a).
        { destruct (Base.compare y a) eqn:Hcomp;
            autorewrite with elt_compare in *; eauto.
          apply E.eq_sym in Heq. eauto. }
        rewrite /In_set /member /= -/member.
        destruct_match; rewrite -Heq' //.
      + move=>Hb. apply balanceL_preserves_membership with (s:=0) in Hb.
        * move: Hb. rewrite /In_set /=.
          destruct_match; auto. apply IHs1.
          apply WF_children in i; tauto.
        * apply insert_prop. apply WF_children in i; tauto.
        * apply WF_children in i. tauto.
        * rewrite_relations. eapply left_insert_before_balancedL; eauto.
        * rewrite_relations. rewrite /before_ordered. repeat split; auto.
          -- apply insert_prop; auto.
             ++ apply WF_children in i; tauto.
             ++ move: i. rewrite /WF /valid. case /and3P => _ Hord _.
                move: Hord. rewrite /ordered. case /and4P => _ _ ? ?. auto.
          -- move: i. rewrite /WF /valid. case /and3P => _ Hord _.
             move: Hord. rewrite /ordered. case /and4P => _ _ ? ?. auto.
      + move=>Hb. apply balanceR_preserves_membership with (s:=0) in Hb.
        * move: Hb. rewrite /In_set /=.
          destruct_match; auto. apply IHs2.
          apply WF_children in i; tauto.
        * apply WF_children in i. tauto.
        * apply insert_prop. apply WF_children in i; tauto.
        * rewrite_relations. eapply right_insert_before_balancedR; eauto.
        * rewrite_relations. rewrite /before_ordered. repeat split; auto.
          -- move: i. rewrite /WF /valid. case /and3P => _ Hord _.
             move: Hord. rewrite /ordered. case /and4P => _ _ ? ?. auto.
          -- apply insert_prop; auto.
             ++ apply WF_children in i; tauto.
             ++ move: i. rewrite /WF /valid. case /and3P => _ Hord _.
                move: Hord. rewrite /ordered. case /and4P => _ _ ? ?. auto.
    - inversion H0. move: H2.
      destruct_match; autorewrite with elt_compare in *.
      apply E.eq_sym in Heq. contradiction.
  Qed.

  Lemma remove_1 :
    forall (s : t) (x y : elt), E.eq x y -> ~ In y (remove x s). Admitted.
  Lemma remove_2 :
    forall (s : t) (x y : elt), ~ E.eq x y -> In y s -> In y (remove x s). Admitted.
  Lemma remove_3 :
    forall (s : t) (x y : elt), In y (remove x s) -> In y s. Admitted.

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
