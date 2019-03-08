Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.
Require Import Data.Map.Internal.
Import GHC.Num.Notations.
Require Import OrdTactic.
Require Import Psatz.
Require Import Tactics.
Set Bullet Behavior "Strict Subproofs".

(** ** Tactics for pointer equality *)

Ltac destruct_ptrEq := lazymatch goal with
  | |- context [if PtrEquality.ptrEq ?x ?y && PtrEquality.ptrEq ?x2 ?y2 then _ else _]
  => let Hpe := fresh "Hpe" in
     let Hpe1 := fresh "Hpe1" in
     let Hpe2 := fresh "Hpe2" in
     destruct (PtrEquality.ptrEq x y && PtrEquality.ptrEq x2 y2) eqn:Hpe;
     [ rewrite andb_true_iff in Hpe;
       destruct Hpe as [Hpe1 Hpe2];
       apply PtrEquality.ptrEq_eq in Hpe1;
       apply PtrEquality.ptrEq_eq in Hpe2;
       subst
     | clear Hpe]
  | |- context [if PtrEquality.ptrEq ?x ?y then _ else _]
  => let Hpe := fresh "Hpe" in
     destruct (PtrEquality.ptrEq x y) eqn:Hpe;
     [ apply PtrEquality.ptrEq_eq in Hpe; subst
     | clear Hpe] 
end.

(** * Tactics for option-valued functions *)

Section oro.
Context {a : Type}.

Definition oro : option a -> option a -> option a :=
  fun x y => match x with
    | Some v => Some v
    | None => y
    end.

Infix "|||" := oro.

Definition ando : option a -> option a -> option a :=
  fun x y =>  match y with None => None | _ => x end.

Infix "&&&" := ando.

Definition diffo : option a -> option a -> option a :=
  fun x y => match y with
    | Some v => None
    | None => x
    end.

Lemma oro_None_l : forall x, None ||| x = x.
Proof. intros. destruct x; reflexivity. Qed.

Lemma oro_None_r : forall x, x ||| None = x.
Proof. intros. destruct x; reflexivity. Qed.

Lemma oro_Some_l : forall x y, Some x ||| y = Some x.
Proof. intros. reflexivity. Qed.

Lemma oro_Some_iff: forall x y v, x ||| y = Some v <-> (x = Some v \/ (x = None /\ y = Some v)).
Proof. intros. destruct x, y; simpl; intuition congruence. Qed.

Lemma ando_None_l : forall x, None &&& x = None.
Proof. intros. destruct x; reflexivity. Qed.

Lemma ando_None_r : forall x, x &&& None = None.
Proof. intros. destruct x; reflexivity. Qed.

Lemma ando_Some_r : forall x y, x &&& Some y = x.
Proof. intros. reflexivity. Qed.

Definition SomeIf (b : bool) (x : a) : option a :=
  if b then Some x else None.

Lemma SomeIf_eq_Some : forall b x y,
  SomeIf b x = Some y <-> b = true /\ x = y.
Proof. intros. destruct b; simpl in *; intuition try congruence. Qed.

Lemma SomeIf_eq_None : forall b x,
  SomeIf b x = None <-> b = false.
Proof. intros. destruct b; simpl in *; intuition try congruence. Qed.

Definition isSome (x : option a) : bool := if x then true else false.

Lemma isSome_oro : forall x y, isSome (x ||| y) = isSome x || isSome y.
Proof. intros. destruct x, y; reflexivity. Qed.

Lemma isSome_ando : forall x y, isSome (x &&& y) = isSome x && isSome y.
Proof. intros. destruct x, y; reflexivity. Qed.

Lemma isSome_SomeIf : forall b x, isSome (SomeIf b x) = b.
Proof. intros. destruct b; reflexivity. Qed.


End oro.
Infix "|||" := oro.
Infix "&&&" := ando.

Ltac simpl_options := repeat lazymatch goal with
  | |- context [true    ||  ?x]              => rewrite (orb_true_l x)
  | H: context [true    ||  ?x]         |- _ => rewrite (orb_true_l x) in H
  | |- context [?x      ||  true]            => rewrite (orb_true_r x)
  | H: context [?x      ||  true]       |- _ => rewrite (orb_true_r x) in H
  | |- context [false   ||  ?x]              => rewrite (orb_false_l x)
  | H: context [false   ||  ?x]         |- _ => rewrite (orb_false_l x) in H
  | |- context [?x      ||  false]           => rewrite (orb_false_r x)
  | H: context [?x      ||  false]      |- _ => rewrite (orb_false_r x) in H
  | |- context [None    ||| ?x]              => rewrite (oro_None_l x)
  | H: context [None    ||| ?x]         |- _ => rewrite (oro_None_l x) in H
  | |- context [?x      ||| None]            => rewrite (oro_None_r x)
  | H: context [?x      ||| None]       |- _ => rewrite (oro_None_r x) in H
  | |- context [Some ?x ||| ?y]              => rewrite (oro_Some_l x y)
  | H: context [Some ?x ||| ?y]         |- _ => rewrite (oro_Some_l x y) in H
  | |- context [None    &&& ?x]              => rewrite (ando_None_l x)
  | H: context [None    &&& ?x]         |- _ => rewrite (ando_None_l x) in H
  | |- context [?x      &&& None]            => rewrite (ando_None_r x)
  | H: context [?x      &&& None]       |- _ => rewrite (ando_None_r x) in H
  | |- context [?x      &&& Some ?y]         => rewrite (ando_Some_r x y)
  | H: context [?x      &&& Some ?y]    |- _ => rewrite (ando_Some_r x y) in H
  | |- context [isSome (?x &&& ?y)]          => rewrite (isSome_ando x y)
  | H: context [isSome (?x &&& ?y)]     |- _ => rewrite (isSome_ando x y) in H
  | |- context [isSome (?x ||| ?y)]          => rewrite (isSome_oro x y)
  | H: context [isSome (?x ||| ?y)]     |- _ => rewrite (isSome_oro x y) in H
  | |- context [isSome (Some ?x)]            => simpl (isSome (Some x))
  | H: context [isSome (Some ?x)]       |- _ => simpl (isSome (Some x)) in H
  | |- context [isSome None]                 => simpl (isSome None)
  | H: context [isSome None]            |- _ => simpl (isSome None) in H
  | |- context [isSome (SomeIf ?b ?x)]       => rewrite (isSome_SomeIf b x)
  | H: context [isSome (SomeIf ?b ?x)]  |- _ => rewrite (isSome_SomeIf b x) in H
  | |- context [SomeIf false ?x]             => simpl (SomeIf false x)
  | H: context [SomeIf false ?x]        |- _ => simpl (SomeIf false x) in H
  | |- context [SomeIf true ?x]              => simpl (SomeIf true  x)
  | H: context [SomeIf true ?x]         |- _ => simpl (SomeIf true  x) in H
  | |- context [SomeIf ?b ?x = Some ?y]      => rewrite (SomeIf_eq_Some b x y)
  | H: context [SomeIf ?b ?x = Some ?y] |- _ => rewrite (SomeIf_eq_Some b x y) in H; destruct H; subst
  | |- context [SomeIf ?b ?x = None]         => rewrite (SomeIf_eq_None b x)
  | H: context [SomeIf ?b ?x = None]    |- _ => rewrite (SomeIf_eq_None b x) in H; subst
end; lazy match in *.

Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(** ** Utilities for working with [Ord] *)

(* We don’t have a OrdLawful class yet. We need to introduce that,
   add it to the context, and derive all axioms from that.
 *)
Lemma compare_Eq : forall (x y : e),
  compare x y = Eq <-> x == y = true.
Proof. order e. Qed.
Lemma compare_Lt : forall (x y : e),
  compare x y = Lt <-> x < y = true.
Proof. order e. Qed.
Lemma compare_Gt : forall (x y : e),
  compare x y = Gt <-> x > y = true.
Proof. order e. Qed.

Lemma lt_eq_r : forall x y z,
  x < y = true ->
  z == y = true ->
  x < z = true.
Proof. order e. Qed.

Lemma lt_eq_l : forall x y z,
  x < y = true ->
  z == x = true ->
  z < y = true.
Proof. order e. Qed.

Lemma lt_not_eq : forall (x y : e),
  x < y = true -> x == y = false.
Proof. order e. Qed.

Lemma gt_not_eq : forall (x y : e),
 x > y = true -> x == y = false.
Proof. order e. Qed.


Lemma lt_gt : forall (x y : e), (x > y) = (y < x).
Proof. order e. Qed.

Lemma lt_trans : forall (x y z : e),
  x < y = true -> y < z = true -> x < z = true.
Proof. order e. Qed.


(** This is just like size, but with a type signature that does not confuse [lia] *)
Definition size (s : Map e a) : Z :=
  match s with | Bin sz _ _ _ _ => sz
               | Tip => 0 end.

Lemma size_size: Internal.size = size.
Proof. reflexivity. Qed.

(** * Well-formedness *)

(* Bounds may be absent (infinity) *)
Definition bound := (option e)%type.

(** A suitable comparision operator for bounds.
   If someone feels like it, then you may introduce nice notation. *)
Definition isLB : bound -> e -> bool :=
  fun lb e => match lb with
    | Some lb => lb < e
    | None => true
  end.

Definition isUB : bound -> e -> bool :=
  fun ub e => match ub with
    | Some ub => e < ub
    | None => true
  end.

Ltac order_Bounds :=
  intros;
  simpl isUB in *;
  simpl isLB in *;
  repeat (congruence || lazymatch goal with
    | H : isUB ?ub _ = false |- _ => destruct ub; simpl isUB in *
    | |-  isUB ?ub _ = _          => destruct ub; simpl isUB in *
    | H : isLB ?lb _ = false |- _ => destruct lb; simpl isLB in *
    | |-  isLB ?lb _ = _          => destruct lb; simpl isLB in *
   end);
   order e.

Lemma isLB_lt:
  forall lb x y,
  isLB lb x = true->
  x < y = true ->
  isLB lb y = true.
Proof. order_Bounds. Qed.

Lemma isUB_lt:
  forall ub x y,
  isUB ub x = true->
  y < x = true ->
  isUB ub y = true.
Proof. order_Bounds. Qed.

(** The balancing property of a binary node *)
Definition balance_prop sz1 sz2 :=
  (sz1 + sz2 <= 1 \/ sz1 <= delta * sz2 /\ sz2 <= delta * sz1)%Z.

(** One precondition for [balanceL]: The left tree has been inserted to (but not by too much).
    This is mechanically derived from the context in the call to [balanceL] in [link], and
    unfortunately not very educational.
 *)
Definition balance_prop_inserted sz1 sz2 :=
  (delta * sz1 <= delta*delta*sz2 + delta*sz2 + sz2 /\ sz2 <= sz1)%Z.

(* NB: this does not work: 
Definition balance_prop_inserted sz1 sz2 := balance_prop sz1 sz2.
*)

Fixpoint sem (s : Map e a) (i : e) : option a :=
  match s with | Bin _ x v s1 s2 => sem s1 i ||| SomeIf (i == x) v ||| sem s2 i
               | Tip => None end.

Lemma sem_resp_eq : forall s i j,
  i == j = true -> sem s i = sem s j.
Proof.
  intros.
  induction s.
  * simpl.
    rewrite IHs1, IHs2.
    replace (j == k) with (i == k) by order e.
    reflexivity.
  * reflexivity.
Qed.

(** This inductive predicate describes when sets are well-formed within 
  (exclusive) bounds.
*)


Inductive Bounded : Map e a -> bound -> bound -> Prop :=
  | BoundedTip : forall lb ub,
    Bounded Tip lb ub
  | BoundedBin :
    forall lb ub,
    forall s1,
    forall s2,
    forall x v sz,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true ->
    sz = (1 + size s1 + size s2)%Z ->
    balance_prop (size s1) (size s2) ->
    Bounded (Bin sz x v s1 s2) lb ub.

(** ** Lemmas related to well-formedness *)

(** There are no values outside the bounds *)
Lemma sem_outside_below:
  forall {s lb ub i},
  Bounded s lb ub ->
  isLB lb i = false ->
  sem s i = None.
Proof.
  intros ???? HD ?.
  induction HD; intros; subst; simpl in *; intuition.
  rewrite H2.
  rewrite IHHD2 by order_Bounds.
  simpl_options.
  order_Bounds.
Qed.

Lemma sem_outside_above:
  forall {s lb ub i},
  Bounded s lb ub ->
  isUB ub i = false ->
  sem s i = None.
Proof.
  intros ???? HD ?.
  induction HD; intros; subst; simpl in *; intuition.
  rewrite H2.
  rewrite IHHD1 by order_Bounds.
  simpl_options.
  order_Bounds.
Qed.

Lemma sem_inside:
  forall {s lb ub i v},
  Bounded s lb ub ->
  sem s i = Some v ->
  isLB lb i = true /\ isUB ub i = true.
Proof.
  intros ????? HD ?.
  induction HD; intros; subst; simpl in *; rewrite ?oro_Some_iff in H; intuition; try congruence;
  simpl_options;
  order_Bounds.
Qed.

Lemma sem_inside_isSome:
  forall {s lb ub i},
  Bounded s lb ub ->
  isSome (sem s i) = true ->
  isLB lb i = true /\ isUB ub i = true.
Proof.
  intros ???? HD ?.
  destruct (sem s i) eqn:H1; simpl in *; try congruence.
  eapply sem_inside; eassumption.
Qed.

(* We use this as a rewrite rule because
   [simpl (size (Bin _ _ _ _ ))]
   simplifies the [ 1 + _ ] which is annoying. *)
Lemma size_Bin: forall sz x v (s1 s2 : Map e a),
  size (Bin sz x v s1 s2) = sz.
Proof. intros. reflexivity. Qed.

(* Pose the proof [prf], unless it already exists. *)
Ltac pose_new prf :=
  let prop := type of prf in
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => pose proof prf
  end.

(* Pose the [prop], using [prf], unless it already exists. *)
Ltac assert_new prop prf :=
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => assert prop by prf
  end.

Lemma size_nonneg:
  forall {s lb ub},
  Bounded s lb ub -> (0 <= size s)%Z.
Proof.
  intros ??? HD.
  induction HD.
  * simpl. lia.
  * simpl. lia.
Qed.


Ltac postive_sizes :=
  repeat match goal with [ H : Bounded ?s _ _ |- _ ] => pose_new (size_nonneg H) end.

Lemma size_0_iff_tip:
  forall {s lb ub},
  Bounded s lb ub -> (size s = 0)%Z <-> s = Tip.
Proof.
  induction 1.
  * intuition.
  * postive_sizes;
    rewrite ?size_Bin in *.
    intuition try (congruence || lia).
Qed.

(** The main point of the balancing condition: Logarithmic height (Same as SetProofs)*)

Fixpoint height (s :Map e a) : Z := match s with
  | Tip => 0%Z
  | Bin _ _ _ s1 s2 => (1 + max (height s1) (height s2))%Z
  end.

Lemma height_nonneg:
  forall m, (0 <= height m)%Z.
Proof. induction m; cbn -[Z.add]; lia. Qed.

Ltac postive_heights :=
  repeat match goal with [ m : Map e a |- _ ] => pose_new (height_nonneg m) end.

Lemma size_height_1:
  forall {m lb ub},
  Bounded m lb ub -> (size m = 1)%Z -> height m = 1%Z.
Proof.
  intros.
  destruct H.
  + inversion H0.
  + destruct H, H1; cbn -[Z.add] in *; postive_sizes; try lia; try reflexivity.
Qed.

Lemma Bounded_size_bound : forall m lb ub,
  Bounded m lb ub -> (4^(height m - 1) <= size m*3^(height m - 1))%Z.
Proof.
  intros ??? HB. induction HB.
  * simpl. reflexivity.
  * cbn -[Z.add].
    postive_sizes.
    postive_heights.
    + unfold balance_prop, delta, fromInteger, Num_Integer__ in H2.
      apply Z.max_case_strong; intro Hle.
      - destruct (Z.leb_spec (size s1 + size s2) 1).
         ** assert (size s1 = 0 \/ size s1 = 1)%Z as Hsmall by lia.
            destruct Hsmall.
            ++ rewrite (size_0_iff_tip HB1) in *. subst. cbn -[N.add Z.add Z.mul] in *.
               simpl Z.sub.
               lia.
            ++ assert (size s2 = 0)%Z by lia. 
               rewrite (size_0_iff_tip HB2) in *. subst. cbn -[N.add Z.add Z.mul] in *.
               replace (height s1) with 1%Z in *
                 by (symmetry; eapply size_height_1; eassumption).
               simpl Z.sub.
               lia.
         ** destruct H2; only 1: lia.
            assert (height s1 <> 0%Z)
              by (destruct s1; cbn -[Z.add]; postive_heights; simpl size in *; try lia).
            replace (((1 + height s1) - 1))%Z with (Z.succ (height s1 - 1)) by lia.
            rewrite !Z.pow_succ_r by lia.
            etransitivity; only 1: (apply Z.mul_le_mono_nonneg_l; [lia | eassumption]).
            rewrite !Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; only 1: (apply Z.pow_nonneg; lia).
            lia.
      - destruct (Z.leb_spec (size s1 + size s2) 1).
         ** assert (size s2 = 0 \/ size s2 = 1)%Z as Hsmall by lia.
            destruct Hsmall.
            ++ rewrite (size_0_iff_tip HB2) in *. subst. cbn -[N.add Z.add Z.mul] in *.
               simpl Z.sub.
               lia.
            ++ assert (size s1 = 0)%Z by lia. 
               rewrite (size_0_iff_tip HB1) in *. subst. cbn -[N.add Z.add Z.mul] in *.
               replace (height s2) with 1%Z in *
                 by (symmetry; eapply size_height_1; eassumption).
               simpl Z.sub.
               lia.
         ** destruct H2; only 1: lia.
            assert (height s1 <> 0%Z)
              by (destruct s1; cbn -[Z.add]; postive_heights; simpl size in *; try lia).
            replace (((1 + height s2) - 1))%Z with (Z.succ (height s2 - 1)) by lia.
            rewrite !Z.pow_succ_r by lia.
            etransitivity; only 1: (apply Z.mul_le_mono_nonneg_l; [lia | eassumption]).
            rewrite !Z.mul_assoc.
            apply Z.mul_le_mono_nonneg_r; only 1: (apply Z.pow_nonneg; lia).
            lia.
Qed.

Lemma Z_log2_pow2:
  forall y,
  (0 <= y)%Z ->
  (Z.log2 (y ^ 2) <= 2 * Z.log2 y + 1)%Z.
Proof.
  intros.
  replace (y ^ 2)%Z with (y * y)%Z by lia.
  etransitivity; only 1: (apply Z.log2_mul_above; assumption).
  lia.
Qed.

Lemma Z_log2_pow3:
  forall y,
  (0 <= y)%Z ->
  (Z.log2 (y ^ 3) <= 3 * Z.log2 y + 2)%Z.
Proof.
  intros.
  replace (y ^ 3)%Z with (y^2 * y)%Z by lia.
  assert (0 <= y^2)%Z by (apply Z.pow_nonneg; assumption).
  etransitivity; only 1: (apply Z.log2_mul_above; assumption).
  enough ((Z.log2 (y^2) <= 2 * Z.log2 y + 1)%Z) by lia.
  apply Z_log2_pow2.
  assumption.
Qed.

(* Frustratingly, concluding this lemma from the one above took more time
   than proving that. *)
Lemma Bounded_logarithmic_height : forall m lb ub,
  Bounded m lb ub -> (height m <= 3 * Z.log2 (size m) + 3)%Z.
Proof.
  intros ??? HB.
  pose proof (Bounded_size_bound m lb ub HB).
  postive_heights.
  postive_sizes.
  assert (size m = 0 \/ 0 < size m)%Z by lia. destruct H2.
  * apply (size_0_iff_tip HB) in H2.
    subst. simpl. intro Htmp. inversion Htmp.
  * clear H1.
    enough (height m - 1 <= 3 * Z.log2 (size m) + 2)%Z by lia.
    assert (0 < height m)%Z by (induction HB; cbn -[Z.add] in *; postive_heights; try lia).
    assert (0 <= height m - 1)%Z by lia.
    generalize  dependent (height m - 1)%Z; intros h ??.
    generalize dependent (size m); intros sz ??.
    clear dependent m. clear lb ub. clear dependent e.
    assert (0 < 3 ^ h)%Z by (apply Z.pow_pos_nonneg; lia).
    assert (0 < 4 ^ h)%Z by (apply Z.pow_pos_nonneg; lia).
    assert (0 < sz ^ 3)%Z by (apply Z.pow_pos_nonneg; lia).

    etransitivity; only 2: (apply Z_log2_pow3; lia).
    apply Z.log2_le_pow2; only 1: assumption.

    eapply Zmult_lt_0_le_reg_r. apply H0.
    eapply Zmult_lt_0_le_reg_r. apply H0.
    eapply Zmult_lt_0_le_reg_r. apply H0.
    rewrite <- !Z.pow_mul_l.
    simpl (2 * 3 * 3 * 3)%Z.
    etransitivity. apply Z.pow_le_mono_l with (b := (4^3)%Z). lia.
    rewrite <- Z.pow_mul_r by lia.
    rewrite Z.mul_comm.
    rewrite -> Z.pow_mul_r by lia.
    etransitivity. apply Z.pow_le_mono_l. split. lia. eapply H.
    lia.
Qed.

Lemma Bounded_change_ub:
  forall s lb ub ub',
  Bounded s lb (Some ub) ->
  ub <= ub' = true ->
  Bounded s lb (Some ub').
Proof.
  intros ???? HD Heq.
  remember (Some ub) as ubo.
  induction HD; subst.
  * apply BoundedTip; auto.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    order_Bounds.
Qed.

Lemma Bounded_change_lb:
  forall s lb lb' ub,
  Bounded s (Some lb) ub ->
  lb' <= lb = true ->
  Bounded s (Some lb') ub.
Proof.
  intros ???? HD Heq.
  remember (Some lb) as lbo.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    order_Bounds.
Qed.

(* Bounded_change_ub and Bounded_relax_ub could be united with
   a isNonStrictUB predicate *)
Lemma Bounded_relax_ub:
  forall s lb ub ub',
  Bounded s lb (Some ub) ->
  isUB ub' ub = true ->
  Bounded s lb ub'.
Proof.
  intros ???? HD Heq.
  remember (Some ub) as ubo.
  induction HD; subst.
  * apply BoundedTip; auto.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    order_Bounds.
Qed.

Lemma Bounded_relax_lb:
  forall s lb lb' ub,
  Bounded s (Some lb) ub ->
  isLB lb' lb = true ->
  Bounded s lb' ub.
Proof.
  intros ???? HD Heq.
  remember (Some lb) as lbo.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    order_Bounds.
Qed.

Lemma Bounded_relax_ub_None:
  forall s lb ub,
  Bounded s lb ub ->
  Bounded s lb None.
Proof.
  intros ??? HD.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * eapply BoundedBin; try eassumption; try reflexivity.
Qed.

Lemma Bounded_relax_lb_None:
  forall s lb ub,
  Bounded s lb ub ->
  Bounded s None ub.
Proof.
  intros ??? HD.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * eapply BoundedBin; try eassumption; try reflexivity.
Qed.


(** ** Tactics for Boundedness etc. *)


(** Learns bounds of values found in some set in the context *)
Ltac inside_bounds :=
  repeat lazymatch goal with
    | H : Bounded ?s _ _, H2 : sem ?s ?i = Some _ |- _ =>
       apply (sem_inside H) in H2; destruct H2
    | H : Bounded ?s _ _, H2 : isSome (sem ?s ?i) = true |- _ =>
       apply (sem_inside_isSome H) in H2; destruct H2
  end.

(** Solve [isLB] and [isUB] goals.  *)
Ltac solve_Bounds := first
  [ eassumption
  | solve [inside_bounds; order_Bounds]
  | idtac "solve_Bounds gave up"
  ].

(* Solve equations of the form
     forall i, f i = f0 i || f1 i
   possibly using equations from the context.
   Fails if it does not start with [forall i,], but may leave a partially solve goal.
    *)
Ltac f_solver_simple  :=
  let i := fresh "i" in 
  intro i;
  try reflexivity; (* for when we have an existential variable *)
  repeat multimatch goal with [ H : (forall i, _) |- _] => specialize (H i) end;
  repeat match goal with [ H : ?f = _ |- context [?f i] ] => rewrite H in *; clear H end;
  simpl sem in *; simpl_options;
  try reflexivity.


(** This auxillary tactic destructs one boolean or option atom in the argument *)

Ltac split_bool_go expr :=
  lazymatch expr with 
    | true       => fail
    | false      => fail
    | Some _     => fail
    | None       => fail
    | match ?x with _ => _ end => split_bool_go x || (simpl x; cbv match)
    | negb ?x      => split_bool_go x
    | ?x && ?y     => split_bool_go x || split_bool_go y
    | ?x || ?y     => split_bool_go x || split_bool_go y
    | xorb ?x ?y   => split_bool_go x || split_bool_go y
    | ?x ||| ?y    => split_bool_go x || split_bool_go y
    | ?x &&& ?y    => split_bool_go x || split_bool_go y
    | diffo ?x ?y  => split_bool_go y || split_bool_go x
    | SomeIf ?b ?x => split_bool_go b
    | ?bexpr       => destruct bexpr eqn:?
  end.

(** This auxillary tactic destructs one boolean or option atom in the goal *)


Ltac split_bool :=
  match goal with 
    | |- ?lhs = ?rhs        => split_bool_go lhs || split_bool_go rhs
    (* A bit ad-hoc, could be improved: *)
    | H : ?x ||| ?y = Some _   |- _ => split_bool_go x
    | H : ?x ||| ?y = None     |- _ => split_bool_go x
    | H : context [?x &&& ?y]  |- _ => split_bool_go y
    | H : context [?x &&& ?y]  |- _ => split_bool_go y
    | H : diffo ?x ?y = Some _ |- _ => split_bool_go y
    | H : diffo ?x ?y = None   |- _ => split_bool_go y
    | H : ?x || ?y = true      |- _ => split_bool_go x
    | H : ?x || ?y = false     |- _ => split_bool_go x
    | H : ?x && ?y = true      |- _ => split_bool_go x
    | H : ?x && ?y = false     |- _ => split_bool_go x
  end.


Ltac f_solver_cleanup :=
  simpl negb in *;
  simpl_options;
  try congruence;
  repeat lazymatch goal with
    |  H1 : true   = true   |- _ => clear H1
    |  H1 : true   = _      |- _ => symmetry in H1
    |  H1 : false  = false  |- _ => clear H1
    |  H1 : false  = _      |- _ => symmetry in H1
    |  H1 : Some _ = Some _ |- _ => inversion H1; subst; clear H1
    |  H1 : Some _ = _      |- _ => symmetry in H1
    |  H1 : None   = None   |- _ => clear H1
    |  H1 : None   = _      |- _ => symmetry in H1
  end;
  (* Find equalities *)
  repeat lazymatch goal with
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = Some ?a, H3 : sem ?s ?j = Some ?b |- _
      => rewrite (sem_resp_eq s i j H1) in H2; rewrite H2 in H3; inversion H3; subst; clear H3
  end;
  (* Try to solve it *)
  try solve [exfalso; inside_bounds; order_Bounds];
  try reflexivity;
  (* Find conradiction *)   
  try lazymatch goal with
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = Some _, H3 : sem ?s ?j = None |- _
      => exfalso; rewrite (sem_resp_eq s i j H1) in H2; congruence
    |  H1 : (?i == ?j) = true , H2 : isSome (sem ?s ?i) = true, H3 : sem ?s ?j = None |- _
      => exfalso; rewrite <- (sem_resp_eq s i j H1) in H3; rewrite H3 in H2; simpl in H2; congruence
    |  H1 : (?i == ?j) = true , H2 : isSome (sem ?s ?i) = false, H3 : sem ?s ?j = Some _ |- _
      => exfalso; rewrite <- (sem_resp_eq s i j H1) in H3; rewrite H3 in H2; simpl in H2; congruence
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = None, H3 : sem ?s ?j = Some _ |- _
      => exfalso; rewrite (sem_resp_eq s i j H1) in H2; congruence
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = None, H3 : isSome (sem ?s ?j) = true |- _
      => exfalso; rewrite  (sem_resp_eq s i j H1) in H2; rewrite H2 in H3; simpl in H3; congruence
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = Some _, H3 : isSome (sem ?s ?j) = false |- _
      => exfalso; rewrite  (sem_resp_eq s i j H1) in H2; rewrite H2 in H3; simpl in H3; congruence
  end.

Ltac f_solver_step := first
  [ split_bool
  | lazymatch goal with H : context [if ?x == ?y then _ else _] |- _
      => destruct (x == y) eqn:?
    end
(*   | exfalso *)
  ].

Ltac f_solver := f_solver_simple; f_solver_cleanup; repeat (f_solver_step; f_solver_cleanup).

(** A variant of [lia] that unfolds a few specific things and knows that
   the size of a well-formed tree is positive. *)
Ltac lia_sizes :=
  postive_sizes;
  unfold balance_prop_inserted, balance_prop, delta, ratio in *;
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__,
                      Num_Integer__, Ord_Integer___,
                      op_zg____, op_zl____ in *;
  rewrite ?size_size in *;
  rewrite ?size_Bin in *; simpl (size Tip) in *;
  lia.

(** A tactic to solve questions about size. *)
Ltac solve_size := first
  [ assumption
  | reflexivity
  | lia_sizes
  | idtac "solve_size gave up"
  ].

(** Solve goals of Bounded. Should be back-tracking free, I think. *)
Ltac solve_Bounded := eassumption || lazymatch goal with
  | [ |- Bounded Tip _ _ ]
    => apply BoundedTip
  | [ H : Bounded ?s ?lb (Some ?ub) |- Bounded ?s ?lb (Some ?ub') ]
    => apply (Bounded_change_ub _ _ _ _ H); solve_Bounds
  | [ H : Bounded ?s (Some ?lb) ?ub  |- Bounded ?s (Some ?lb') ?ub ]
    => apply (Bounded_change_lb _ _ _ _ H); solve_Bounds
  | [ H : Bounded ?s ?lb (Some ?ub) |- Bounded ?s ?lb ?ub' ]
    => apply (Bounded_relax_ub _ _ _ _ H); solve_Bounds
  | [ H : Bounded ?s (Some ?lb) ?ub  |- Bounded ?s ?lb' ?ub ]
    => apply (Bounded_relax_lb _ _ _ _ H); solve_Bounds
  | [ |- Bounded (Bin _ _ _ _ _) _ _ ]
    => apply BoundedBin;
        [ solve_Bounded
        | solve_Bounded
        | solve_Bounds
        | solve_Bounds
        | solve_size
        | solve_size
        ]
  | |- ?H => fail "solve_Bounded gave up on" H
  end.

(** We now have special tactics for the three kinds of preconditions most
    our lemmas below have. So we can write a tactic that correctly chooses the
    right tactic.
    Why not simply use [first [solve_Bounded|solve_Bounds|solve_size]]?
    Because that would involve backtracking which hides error messages from us,
    and is possibly too slow.
  *)

Ltac solve_Precondition := lazymatch goal with
  | |- Bounded _ _ _          => solve_Bounded
  | |- isLB _ _ = true        => solve_Bounds
  | |- isUB _ _ = true        => solve_Bounds
  | |- context [map_size]     => simpl; lia    (* in well-founded recursion *)
  | |- _ = _                  => solve_size
  | |- context [balance_prop] => solve_size
  | |- ?H                     => fail "solve_Precondition does not recognize this goal: " H
  end.

(** ** A setup for complete specification *)



(** A proposition of the form [Desc s lb ub sz f] tells us
  everything we need to know about [s].

  Therefore, it is phrased as an induction lemma which replaces
  the concrete Set (e.g. [insert y s]) with a fresh variable [s'],
  and adds all interesting bits about it to the context.

  To prove a [Desc] statement, use [apply showDesc].

  To use a [Desc] statement, use [applyDesc HD] or [apply foo_Desc].
  *)

Definition Desc s lb ub sz f : Prop :=
  forall (P : Map e a -> Prop),
  (forall s,
    Bounded s lb ub ->
    size s = sz ->
    (forall i, sem s i = f i) ->
    P s) ->
  P s.

Local Inductive HIDE (P : Prop) := unhide : P -> HIDE P.
Local Lemma hide : forall {P : Prop},  HIDE P -> P. Proof. intros. inversion H. assumption. Qed.

Ltac applyDesc lem :=
  apply hide;
  eapply lem;
  [ solve_Precondition ..
  | let s := fresh "s" in 
    let HB := fresh "HB" in
    let Hsz := fresh "Hsz" in
    let Hsem := fresh "Hsem" in
    intros s HB Hsz Hsem;
    apply unhide;
    try replace (size s) in *;
    try replace (sem s) in *;
    try assumption
  ].

Lemma showDesc :
  forall s lb ub sz f,
  Bounded s lb ub /\ size s = sz /\ (forall i, sem s i = f i) ->
  Desc s lb ub sz f.
Proof.
  intros. intros P HP. apply HP; intuition.
Qed.

Lemma Desc_change_f:
  forall s lb ub sz f f',
  (forall i, f' i = f i) ->
  Desc s lb ub sz f' <-> Desc s lb ub sz f.
Proof.
  intros.
  split; intro HD; applyDesc HD;
  (apply showDesc; split; [solve_Bounded | split; [solve_size | simpl sem; try solve [f_solver]]]);
  intuition.
Qed.

(** A variant that does not indicate anything about [size]. *)

Definition Desc' s lb ub f : Prop :=
  forall (P : Map e a -> Prop),
  (forall s,
    Bounded s lb ub ->
    True ->             (* So that we can still use [applyDesc] here *)
    (forall i, sem s i = f i) ->
    P s) ->
  P s.

Lemma showDesc' :
  forall s lb ub f,
  Bounded s lb ub /\ (forall i, sem s i = f i) ->
  Desc' s lb ub f.
Proof.
  intros. intros P HP. apply HP; intuition.
Qed.

Ltac solve_Desc :=
 lazymatch goal with
 | |- (Desc _ _ _ _ _)
 => apply showDesc; split; [solve_Bounded | split; [solve_size | simpl sem; try solve [f_solver]]]
 | |- (Desc' _ _ _ _)
 => apply showDesc'; split; [solve_Bounded | simpl sem; try solve [f_solver]]
 | |- ?P
 => fail "solve_Desc: Goal not a Desc or Desc' proposition: " P
 end.

(** ** The actual [WF] predicate *)


(** And any set that has a bounds is well-formed *)
Definition WF (s : Map e a) : Prop := Bounded s None None.

Lemma Desc_WF:
  forall s sz f,
  Desc s None None sz f -> WF s.
Proof.
  intros ??? HD.
  unfold WF.
  (* Unfortunately, [apply HD] does not work unless we have [size s] and [sem s]
     in the context. *)
  assert (Bounded s None None /\ size s = size s /\ sem s = sem s) by (apply HD; auto).
  intuition.
Qed.

Lemma Desc_WF':
  forall m sz f lb ub,
  Desc m lb ub sz f -> WF m.
Proof.
  intros m sz f lb ub HD.
  unfold WF.
  (* Unfortunately, [apply HD] does not work unless we have [size s] and [sem s]
     in the context. *)
  assert (Bounded m lb ub /\ size m = size m /\ sem m = sem m) by (apply HD; auto).
  intuition.
  destruct ub; destruct lb.
  - eapply Bounded_relax_lb; eauto;
      eapply Bounded_relax_ub; eauto.
  - eapply Bounded_relax_ub; eauto.
  - eapply Bounded_relax_lb; eauto.
  - auto.
Qed.


(** For every set in the context, try to see if [lia] knows it is empty. *)
Ltac find_Tip :=
  match goal with [ H : Bounded ?s _ _ |- _ ] =>
    assert_new (size s = 0)%Z lia_sizes;
    rewrite (size_0_iff_tip H) in *;
    subst s;
    inversion H;
    clear H;
    subst
  end.

Require Import Coq.Program.Tactics.

Open Scope Z_scope.

(** ** Verification of [empty] *)

Lemma empty_Desc:
  forall lb ub,
  Desc empty lb ub 0 (fun _ => None).
Proof. intros. unfold empty. solve_Desc. Qed.

Lemma empty_WF: WF empty.
Proof. intros. unfold empty. eapply Desc_WF. apply empty_Desc. Qed.


(** ** Verification of [null] *)

Lemma null_spec:
  forall s, WF s -> null s = true <-> s = Tip.
Proof. intros. unfold null. inversion H; simpl; intuition (congruence || lia_sizes). Qed.


(** ** Verification of [singleton] *)

Lemma singleton_Desc:
  forall x v lb ub,
  isLB lb x = true ->
  isUB ub x = true ->
  Desc (singleton x v) lb ub 1 (fun i => SomeIf (i == x) v).
Proof.
  intros.

  unfold singleton.
  unfold fromInteger, Num_Integer__.
  solve_Desc.
Qed.


Lemma singleton_WF:
  forall x v, WF (singleton x v).
Proof. intros. eapply Desc_WF. eapply singleton_Desc; reflexivity. Qed.

(** ** Verifying the various balancing operations *)

(** *** Verification of [balanceL] *)

Lemma balanceL_Desc:
    forall x v s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub  ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) \/
    balance_prop_inserted (size s1 - 1) (size s2) /\ (1 <= size s1)%Z \/
    balance_prop (size s1) (size s2 + 1) ->
    Desc (balanceL x v s1 s2) lb ub (1 + size s1 + size s2) (fun i => sem s1 i ||| SomeIf (i == x) v ||| sem s2 i).
Proof.
  intros.

  unfold balanceL.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try solve [solve_Desc].
Qed.

Lemma balanceL_noop :
    forall x y s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) ->
    balanceL x y s1 s2 = Bin (1 + size s1 + size s2) x y s1 s2.
Proof.
  intros.

  unfold balanceL.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try reflexivity.
Qed.


(** *** Verification of [balanceR] *)

Lemma balanceR_Desc:
    forall x v s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) \/
    balance_prop_inserted (size s2 - 1) (size s1) /\ (1 <= size s2)%Z  \/
    balance_prop (size s1 + 1) (size s2) ->
    Desc (balanceR x v s1 s2) lb ub (1 + size s1 + size s2) (fun i => sem s1 i ||| SomeIf (i == x) v ||| sem s2 i).
Proof.
  intros.

  unfold balanceR.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try solve [solve_Desc].
Qed.

Lemma balanceR_noop :
    forall x y s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) ->
    balanceR x y s1 s2 = Bin (1 + size s1 + size s2) x y s1 s2.
Proof.
  intros.

  unfold balanceR.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try reflexivity.
Qed.

(** *** Verification of [insertMax] *)

Lemma insertMax_Desc:
    forall x v s1 lb ub,
    Bounded s1 lb (Some x) ->
    isLB lb x = true ->
    isUB ub x = true->
    Desc (insertMax x v s1) lb ub (1 + size s1) (fun i => sem s1 i ||| SomeIf (i == x) v).
Proof.
  intros.
  
  remember (Some x) as ub'. revert dependent x.
  induction H; intros; subst; cbn - [Z.add SomeIf].
  * applyDesc singleton_Desc.
    solve_Desc.
  * clear IHBounded1.
    applyDesc IHBounded2.
    applyDesc balanceR_Desc.
    solve_Desc.
Qed.

(** *** Verification of [insertMin] *)

Lemma insertMin_Desc:
    forall x v s2 lb ub,
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    Desc (insertMin x v s2) lb ub (1 + size s2) (fun i => SomeIf (i == x) v ||| sem s2 i).
Proof.
  intros.
  remember (Some x) as ub'. revert dependent x.
  induction H; intros; subst; cbn - [Z.add].
  * applyDesc singleton_Desc.
    solve_Desc.
  * clear IHBounded2.
    applyDesc IHBounded1.
    applyDesc balanceL_Desc.
    solve_Desc.
Qed.

(** *** Verification of [link] *)

Lemma link_eq (x : e) (v : a) (s1: Map e a)  (s2: Map e a) :
  link x v s1 s2 =
       match s1, s2 with
          | Tip , r => insertMin x v r
          | l , Tip => insertMax x v l
          | (Bin sizeL y vy ly ry as l) , (Bin sizeR z vz lz rz as r) =>
            if Sumbool.sumbool_of_bool ((delta GHC.Num.* sizeL) GHC.Base.< sizeR)
            then balanceL z vz (link x v l lz) rz
            else if Sumbool.sumbool_of_bool  ((delta GHC.Num.* sizeR) GHC.Base.< sizeL)
                 then balanceR y vy ly (link x v ry r)
                 else bin x v l r
        end.
Proof.
  destruct s1; [|reflexivity].
  destruct s2; [|reflexivity].
  unfold link at 1, link_func at 1.
  lazymatch goal with 
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs => 
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.

(* [program_simpl] calls [simpl], which is very confusing due to [1 + _]. So
ask [Next Obligation] to use this only when it solves the goal completely. *)
Local Obligation Tactic := try solve [program_simpl].

Program Fixpoint link_Desc (x : e) (v : a) (s1: Map e a) (s2: Map e a)
  {measure (map_size s1 + map_size s2)} :
    forall lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub  ->
    isLB lb x = true ->
    isUB ub x = true->
    Desc (link x v s1 s2) lb ub (1 + size s1 + size s2)
        (fun i => sem s1 i ||| SomeIf (i == x) v ||| sem s2 i)
    := _.
Next Obligation.
  intros.
  rewrite link_eq. 
  inversion H; subst; clear H;
  inversion H0; subst; clear H0.
  * simpl insertMin.
    applyDesc singleton_Desc.
    solve_Desc.
  * applyDesc insertMin_Desc.
    solve_Desc.
  * applyDesc insertMax_Desc.
    solve_Desc.
  * destruct (Sumbool.sumbool_of_bool _);
    only 2: destruct (Sumbool.sumbool_of_bool _);
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
    - applyDesc link_Desc.
      applyDesc balanceL_Desc.
      solve_Desc.
    - applyDesc link_Desc.
      applyDesc balanceR_Desc.
      solve_Desc.
    - clear link_Desc.
      unfold bin.
      solve_Desc.
Qed.

(** ** Verification of [lookup] *)

Lemma lookup_spec:
 forall {s lb ub i}, Bounded s lb ub -> lookup i s = sem s i.
Proof.
  intros ???? HB.
  induction HB.
  * simpl. reflexivity.
  * subst; simpl.
    destruct (compare i x) eqn:?.
    + replace (i == x) with true by order_Bounds.
      rewrite (sem_outside_above HB1) by order_Bounds.
      reflexivity.
    + replace (i == x) with false by order_Bounds.
      rewrite IHHB1.
      rewrite (sem_outside_below HB2) by order_Bounds.
      simpl_options.
      reflexivity.
    + replace (i == x) with false by order_Bounds.
      rewrite IHHB2.
      rewrite (sem_outside_above HB1) by order_Bounds.
      simpl_options.
      reflexivity.
Qed.

(** ** Verification of [member] *)

Lemma member_spec:
 forall {s lb ub i}, Bounded s lb ub -> member i s = true <-> exists v, sem s i = Some v.
Proof.
  intros. induction H.
  - simpl. split. intros. discriminate H. intros. destruct H. discriminate H. 
  - subst. simpl. destruct (compare i x) eqn: ?; split; intros.
    + replace (i==x) with true by order_Bounds.
      rewrite (sem_outside_above H) by order_Bounds.
      simpl. exists v. reflexivity.
    + reflexivity.
    + replace (i==x) with false by order_Bounds.
      rewrite (sem_outside_below H0) by order_Bounds.
      simpl_options. apply IHBounded1 in H3. destruct H3. exists x0. assumption.
    + assert (sem s2 i = None). { eapply sem_outside_below. apply H0. unfold isLB.
      order_Bounds. }
      rewrite H5 in H3. assert (i == x = false). { rewrite compare_Lt in Heqc.
      apply lt_not_eq. assumption. } rewrite H6 in H3. simpl in H3. simpl_options. 
      apply IHBounded1. destruct H3. exists x0. assumption. 
    + replace (i==x) with false by order_Bounds.
      rewrite (sem_outside_above H) by order_Bounds.
      simpl. apply IHBounded2 in H3. destruct H3. exists x0. assumption.
    + assert (sem s1 i = None). { eapply sem_outside_above. apply H. order_Bounds. }
      rewrite H5 in H3. rewrite compare_Gt in Heqc. apply gt_not_eq in Heqc. rewrite Heqc in H3.
      simpl_options. destruct H3. apply IHBounded2. exists x0. assumption.
Qed.

(** ** Verification of [notMember] *)

Lemma contrapositive : forall (P : Prop) (Q: Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. intro. apply H in H1. contradiction.
Qed.

Lemma notMember_spec:
 forall {s lb ub i}, Bounded s lb ub -> notMember i s = true <-> sem s i = None.
Proof.
  intros ???? HB.
  unfold notMember, op_zd__. split; intros.
  pose proof (@member_spec s lb ub i). apply H0 in HB. destruct HB. apply contrapositive in H2.
  unfold not in H2. destruct (sem s i). destruct H2. exists a0. reflexivity. reflexivity.
  rewrite negb_true_iff in H. intro. rewrite H3 in H. inversion H.
  pose proof (@member_spec s lb ub i). apply H0 in HB. destruct HB. apply contrapositive in H1.
  rewrite negb_true_iff. destruct (member i s). contradiction. reflexivity. intro.
  destruct H3. rewrite H3 in H. inversion H.
Qed.


(** ** Verification of [insert] *)

(* The [orig] passing and the local fixpoint in insert is plain ugly, so let’s to this instead *)

Fixpoint insert' (x : e) (v : a) (s : Map e a) : Map e a :=
  match s with 
    | Tip => singleton x v
    | Bin sz y vy l r => match compare x y with
      | Lt =>
        let l' := insert' x v l in
        if PtrEquality.ptrEq l' l then s else balanceL y vy l' r
      | Gt =>
        let r' := insert' x v r in 
        if PtrEquality.ptrEq r' r then s else balanceR y vy l r'
      | Eq =>
        if PtrEquality.ptrEq v vy && PtrEquality.ptrEq x y then s else Bin sz x v l r
     end
  end.

Lemma insert_insert' : forall x v s, insert x v s = insert' x v s.
Proof.
  intros.
  unfold insert.
  induction s; simpl.
  * destruct (compare x k).
    - reflexivity.
    - rewrite IHs1. reflexivity.
    - rewrite IHs2. reflexivity.
  * reflexivity.
Qed.

Lemma insert_Desc:
  forall y v s lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insert y v s) lb ub (if isSome (sem s y) then size s else (1 + size s)%Z)
      (fun i => (if i == y then Some v else None) ||| sem s i).
Proof.
  intros ????? HB HLB HUB.
  rewrite insert_insert'.
  induction HB; intros.
  * simpl.
    applyDesc singleton_Desc; try eassumption; solve_Desc.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in *.
      rewrite Heqc.
      rewrite ?isSome_oro, ?isSome_Some, ?orb_true_r, ?orb_true_l.
      destruct_ptrEq.
      - solve_Desc.
      - unfold Datatypes.id.
        solve_Desc.
    + clear IHHB2.
      applyDesc IHHB1.

      rewrite (sem_outside_below HB2) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      simpl_options.

      destruct_ptrEq.
      - destruct (sem s1 y) eqn:?; simpl isSome in *; try lia.
        solve_Desc.
      - destruct (sem s1 y); simpl isSome in *;
        applyDesc balanceL_Desc;
        cbv match in *;
        solve_Desc.
    + (* more or less a copy-n-paste from above *)
      clear IHHB1.
      applyDesc IHHB2.

      rewrite (sem_outside_above HB1) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      simpl_options.

      destruct_ptrEq.
      - destruct (sem s2 y) eqn:?; simpl_options; try lia.
        solve_Desc.
      - destruct (sem s2 y); simpl_options;
        applyDesc balanceR_Desc;
        solve_Desc.
Qed.

(** ** Verification of [insertR] *)

Fixpoint insertR' (x : e) (v : a) (s : Map e a) : Map e a :=
  match s with 
    | Tip => singleton x v
    | Bin sz y vy l r => match compare x y with
      | Lt =>
        let l' := insertR' x v l in
        if PtrEquality.ptrEq l' l then s else balanceL y vy l' r
      | Gt =>
        let r' := insertR' x v r in 
        if PtrEquality.ptrEq r' r then s else balanceR y vy l r'
      | Eq => Bin sz y vy l r
     end
  end.

Lemma insertR_insertR' : forall x v s, insertR x v s = insertR' x v s.
Proof.
  intros.
  unfold insertR.
  induction s; simpl.
  * destruct (compare x k).
    - reflexivity.
    - rewrite IHs1. reflexivity.
    - rewrite IHs2. reflexivity.
  * reflexivity.
Qed.


Lemma insertR_Desc:
  forall y v s lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insertR y v s) lb ub (if isSome (sem s y) then size s else (1 + size s)%Z)
    (fun i => sem s i ||| (if i == y then Some v else None)).
Proof.
  intros ????? HB HLB HUB.

  rewrite insertR_insertR'.
  induction HB; intros.
  * simpl.
    applyDesc singleton_Desc; try eassumption; solve_Desc.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in *.
      rewrite Heqc.
      rewrite ?isSome_oro, ?isSome_Some, ?orb_true_r, ?orb_true_l.
      solve_Desc.
    + clear IHHB2.
      applyDesc IHHB1.

      rewrite (sem_outside_below HB2) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      simpl_options.

      destruct_ptrEq.
      - destruct (sem s1 y) eqn:?; simpl_options; try lia.
        solve_Desc.
      - destruct (sem s1 y); simpl_options;
        applyDesc balanceL_Desc;
        solve_Desc.
    + (* more or less a copy-n-paste from above *)
      clear IHHB1.
      applyDesc IHHB2.

      rewrite (sem_outside_above HB1) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      simpl_options.
      
      destruct_ptrEq.
      - destruct (sem s2 y) eqn:?; simpl_options; try lia.
        solve_Desc.
      - destruct (sem s2 y); simpl_options;
        applyDesc balanceR_Desc;
        solve_Desc.
Qed.


Lemma insert_WF:
  forall y v s, WF s -> WF (insert y v s).
Proof. intros. eapply Desc_WF. eapply insert_Desc; try reflexivity; try assumption. Qed.

(** ** Verification of [maxViewSure] *)

Lemma maxViewSure_Desc:
  forall sz' x v s1 s2 lb ub,
    Bounded (Bin sz' x v s1 s2) lb ub ->
    forall P,
    (forall y vy r,
      (y = x /\ vy = v \/ sem s2 y = Some vy) /\
      Desc r lb (Some y) (size s1 + size s2)
                         (fun i => if i == y then None else (sem s1 i ||| (if i == x then Some v else None) ||| sem s2 i)) ->
      P (Mk_MaxView y vy r)) ->
    P (maxViewSure x v s1 s2).
    (* we know that y is in the input, and we actually know more: it is x or in s2 *)
Proof.
  intros ??????? HB.
  revert sz' x v s1 lb ub HB.
  induction s2; intros sz' x v s1 lb ub HB;subst.
  - clear IHs2_1.
    simpl.
    intros X HX.
    destruct (maxViewSure k a0 s2_1 s2_2) eqn:HmaxView.
    apply HX. clear X HX.

    inversion HB; subst; clear HB.
    inversion H5; subst.

    revert HmaxView.
    eapply IHs2_2; only 1: solve_Bounded.
    intros y vy r H; destruct H as [Hthere IHD]; clear IHs2_2.
    cbn -[Z.add size] in *; rewrite size_Bin in *.

    intro HmaxView; inversion HmaxView; subst; clear HmaxView.

    applyDesc IHD; clear IHD.

    split.
    + right.
      destruct Hthere as [[H H2]|H]; rewrite H in *.
      * subst. rewrite Eq_refl.
        erewrite sem_outside_above by solve_Bounds.
        reflexivity.
      * erewrite sem_outside_above by solve_Bounds.
        replace (e0 == k) with false by solve_Bounds.
        reflexivity.
    + destruct Hthere as [[Heq Heq1]|Hthere].
      * subst; applyDesc balanceL_Desc; solve_Desc.
      * applyDesc balanceL_Desc.
        solve_Desc.
  - intros X HX.
    destruct (maxViewSure _ _ _ _) eqn:HmaxView.
    apply HX. clear X HX.
    cbn -[Z.add size] in *.
    inversion HB; subst; clear HB.
    inversion HmaxView; subst; clear HmaxView.
    split; [left; (split;reflexivity) | solve_Desc].
Qed.

(** ** Verification of [lookupMin] *)

Lemma empty_no_elts : forall m,
  (forall i, sem m i = None) <-> m = empty.
Proof.
  intros. split; intros.
  destruct m. specialize (H e0). simpl in H. destruct (sem m1 e0); simpl in H.
  inversion H. rewrite Eq_Reflexive in H. inversion H. reflexivity. rewrite H. reflexivity.
Qed.

Lemma lookupMin_in_bin: forall (m: Map e a),
  m <> Tip -> forall k1 k2 v1 v2, lookupMinSure k1 v1 m = lookupMinSure k2 v2 m.
Proof.
  intros. destruct m; intros.
  - simpl. reflexivity.
  - contradiction.
Qed. 

Lemma lookupMax_in_bin: forall (m: Map e a),
  m <> Tip -> forall k1 k2 v1 v2, lookupMaxSure k1 v1 m = lookupMaxSure k2 v2 m.
Proof.
  intros. destruct m; intros.
  - simpl. reflexivity.
  - contradiction.
Qed. 
 

Lemma lookupMinSure_Desc:
  forall m x v0 lb ub,
    Bounded m lb ub ->
    let (y, v) := lookupMinSure x v0 m in
    ((forall i, sem m i = None) /\ y = x /\ v = v0 \/
      sem m y = Some v /\ (forall i v1, sem m i = Some v1 -> (y GHC.Base.<= i) = true)).
Proof.
  intros.  revert x v0. induction H; intros.
  - left. simpl. intuition.
  - destruct (lookupMinSure x0 v0 (Bin sz x v s1 s2)) eqn : ?. right. simpl.
    specialize (IHBounded1 x0 v0). destruct (lookupMinSure x0 v0 s1) eqn : ?. destruct IHBounded1.
    + destruct H5. destruct H6. assert (sem s1 e0 = None) by (apply H5). rewrite H8; simpl. subst.
      simpl in Heqp. apply empty_no_elts in H5. subst. inversion Heqp. subst.
      rewrite Eq_Reflexive. simpl. split. reflexivity. intros.
      destruct (e0 == i) eqn : ?. order e. assert (i == e0 = false) by order e. rewrite H5 in H3.
      simpl in H3. solve_Bounds.
    + destruct H5. simpl in Heqp. assert (s1 <> Tip). { destruct s1. intro. discriminate H7.
      simpl in H5. inversion H5. } 
      eapply lookupMin_in_bin in H7. rewrite Heqp in H7. rewrite Heqp0 in H7. inversion H7; subst.
      rewrite H5. simpl. split. reflexivity. intros.
      destruct (sem s1 i) eqn : ?. simpl in H3. inversion H3; subst. 
      apply H6 in Heqo. assumption.
      simpl in H3. assert (_GHC.Base.<=_  e1 x = true) by solve_Bounds.
      destruct (i == x) eqn : ?. order e. simpl in H3. solve_Bounds. 
Qed. 

Lemma lookupMin_Desc:
  forall m lb ub,
    Bounded m lb ub ->
    match lookupMin m with 
      | None => (forall i, sem m i = None)
      | Some (y, v) => sem m y = Some v /\ (forall i v1, sem m i = Some v1 -> (y GHC.Base.<= i) = true)
    end.
Proof.
  intros.
  unfold lookupMin.
  inversion H; subst; clear H.
  * reflexivity.
  * simpl.
    pose proof (lookupMinSure_Desc s1 x v lb (Some x) H0). destruct (lookupMinSure x v s1) eqn : ?.
    destruct H.
    - destruct H; subst. apply empty_no_elts in H; subst. simpl. simpl in Heqp. inversion Heqp; subst.
      rewrite Eq_Reflexive. simpl. split. reflexivity. intros. destruct (i == e0) eqn : ?.
      order e. simpl in H. solve_Bounds.
    - destruct H. rewrite H. simpl; split. reflexivity. intros. destruct (sem s1 i) eqn : ?.
      apply H4 in Heqo. assumption. simpl in H6. destruct (i == x) eqn : ?.
      solve_Bounds. simpl in H6. solve_Bounds.
Qed. 


(** ** Verification of [lookupMax] *)

Lemma lookupMaxSure_Desc:
  forall m x v0 lb ub,
    Bounded m lb ub ->
    let (y, v) := lookupMaxSure x v0 m in
    ((forall i, sem m i = None) /\ y = x /\ v = v0 \/
      sem m y = Some v /\ (forall i v1, sem m i = Some v1 -> (i GHC.Base.<= y) = true)).
Proof.
  intros.  revert x v0. induction H; intros.
  - left. simpl. intuition.
  - destruct (lookupMaxSure x0 v0 (Bin sz x v s1 s2)) eqn : ?. right. simpl.
    specialize (IHBounded2 x0 v0). destruct (lookupMaxSure x0 v0 s2) eqn : ?. destruct IHBounded2.
    + destruct H5. destruct H6. assert (sem s2 e0 = None) by (apply H5). rewrite H8; simpl. subst.
      simpl in Heqp. apply empty_no_elts in H5. subst. inversion Heqp. subst.
      rewrite Eq_Reflexive. simpl.  assert (sem s1 e0 = None). { eapply sem_outside_above.
      apply H. unfold isUB. order e. } split. rewrite H3. reflexivity. intros.
      destruct (e0 == i) eqn : ?. order e. assert (i == e0 = false) by order e. rewrite H6 in H5.
      simpl in H5. rewrite oro_None_r in H5. rewrite oro_None_r in H5. solve_Bounds.
    + destruct H5. simpl in Heqp. assert (s2 <> Tip). { destruct s2. intro. discriminate H7.
      simpl in H5. inversion H5. } 
      eapply lookupMax_in_bin in H7. rewrite Heqp in H7. rewrite Heqp0 in H7. inversion H7; subst.
      rewrite H5. assert (sem s1 e1 = None). { eapply (sem_inside H0) in H5. destruct H5.
      eapply sem_outside_above. apply H. solve_Bounds. } rewrite H3. simpl.
      destruct (e1 == x) eqn : ?. solve_Bounds. simpl. split. reflexivity. intros.
      destruct (sem s1 i) eqn : ?. solve_Bounds. simpl in H8. destruct (i == x) eqn : ?.
      solve_Bounds. simpl in H8. apply H6 in H8. assumption.
Qed. 

Lemma lookupMax_Desc:
  forall m lb ub,
    Bounded m lb ub ->
    match lookupMax m with 
      | None => (forall i, sem m i = None)
      | Some (y, v) => sem m y = Some v /\ (forall i v1, sem m i = Some v1 -> (i GHC.Base.<= y) = true)
    end.
Proof.
  intros.
  unfold lookupMax.
  inversion H; subst; clear H.
  * reflexivity.
  * simpl.
    pose proof (lookupMaxSure_Desc s2 x v (Some x) ub H1). destruct (lookupMaxSure x v s2) eqn : ?.
    destruct H.
    - destruct H; subst. apply empty_no_elts in H; subst. simpl. simpl in Heqp. inversion Heqp; subst.
      rewrite Eq_Reflexive. simpl. split. assert (sem s1 e0 = None). { eapply sem_outside_above.
      apply H0. solve_Bounds. } rewrite H. reflexivity.
      intros. destruct (i == e0) eqn : ?.
      order e. simpl in H. rewrite oro_None_r in H. rewrite oro_None_r in H. solve_Bounds.
    - destruct H. rewrite H. simpl; split. assert (sem s1 e0 = None). { eapply sem_outside_above.
      apply H0. apply (sem_inside H1) in H. solve_Bounds. } rewrite H6.
      destruct (e0 == x) eqn : ?. solve_Bounds. simpl. reflexivity.
      intros. destruct (sem s1 i) eqn : ?. solve_Bounds. simpl in H6. destruct (i == x) eqn : ?.
      solve_Bounds. simpl in H6. eapply H4. apply H6.
Qed.


(** ** Verification of [minViewSure] *)

Lemma minViewSure_Desc:
  forall sz' x v s1 s2 lb ub,
    Bounded (Bin sz' x v s1 s2) lb ub ->
    forall P,
    (forall y vy r,
      (y = x /\ vy = v \/ sem s1 y = Some vy) /\
      Desc r (Some y) ub (size s1 + size s2)
                         (fun i => if i == y then None else (sem s1 i ||| (if i == x then Some v else None) ||| sem s2 i)) ->
      P (Mk_MinView y vy r)) ->
    P (minViewSure x v s1 s2).
    (* we know that y is in the input, and we actually know more: it is x or in s2 *)
Proof.
  intros ??????? HB.
  revert sz' x v s2 lb ub HB.
  induction s1; intros sz' x v s2 lb ub HB;subst.
  - clear IHs1_2.
    simpl.
    intros X HX.
    destruct (minViewSure _ _ _ _ ) eqn:HmaxView.
    apply HX. clear X HX.

    inversion HB; subst; clear HB.
    inversion H4; subst.

    revert HmaxView.
    eapply IHs1_1; only 1: solve_Bounded.
    intros y vy r H; destruct H as [Hthere IHD]; clear IHs1_1.
    cbn -[Z.add size] in *; rewrite size_Bin in *.

    intro HmaxView; inversion HmaxView; subst; clear HmaxView.

    applyDesc IHD; clear IHD.

    split.
    + right.
      destruct Hthere as [[H H2]|H]; rewrite H in *.
      * subst. rewrite Eq_refl.
        erewrite sem_outside_above by solve_Bounds.
        reflexivity.
      * reflexivity.
    + destruct Hthere as [[Heq Heq1]|Hthere].
      * subst; applyDesc balanceR_Desc; solve_Desc.
      * applyDesc balanceR_Desc; solve_Desc.
  - intros X HX.
    destruct (minViewSure _ _ _ _) eqn:Hview.
    apply HX. clear X HX.
    cbn -[Z.add size] in *.
    inversion HB; subst; clear HB.
    inversion Hview; subst; clear Hview.
    split; [left; (split;reflexivity) | solve_Desc].
Qed.

(** ** Verification of [maxView] *)

Lemma maxViewWithKey_Desc:
  forall m lb ub,
    Bounded m lb ub ->
    forall (P : option ((e * a) * Map e a) -> Prop),
    (forall y r v,
      (sem m y = Some v) /\
      Desc r lb (Some y) (size m - 1) (fun i => if (i == y) then None else sem m i) ->
      P (Some ((y, v), r))) ->
    ((forall i, sem m i = None) -> P None) ->
    P (maxViewWithKey m).
Proof.
  intros ??? HB P HSome HNone.
  unfold maxViewWithKey.
  inversion HB; subst.
  * apply HNone. intro; reflexivity.
  * unfold op_zdzn__, Datatypes.id, op_zd__.
    eapply maxViewSure_Desc; only 1: eassumption.
    intros.
    apply HSome.
    split.
    - simpl. destruct H3. destruct H3. destruct H3. subst. rewrite Eq_Reflexive.
      assert (sem s1 x = None). { eapply sem_outside_above. apply H. solve_Bounds. }
      rewrite H3. simpl. reflexivity. rewrite H3. 
      assert (sem s1 y = None). { eapply sem_outside_above. apply H. solve_Bounds. }
      rewrite H6. simpl. destruct (y == x) eqn : ?. solve_Bounds. reflexivity. 
    - applyDesc H3. solve_Desc.
Qed.

Lemma maxViewDesc:
  forall m lb ub,
  Bounded m lb ub ->
  maxView m = match maxViewWithKey m with
            |None => None
            | Some ((x,y), m) => Some (y, m)
            end.
Proof.
  intros. unfold maxView. reflexivity.
Qed.

(** ** Verification of [minView] *)

Lemma minViewWithKey_Desc:
  forall m lb ub,
    Bounded m lb ub ->
    forall (P : option ((e * a) * Map e a) -> Prop),
    (forall y r v,
      (sem m y = Some v) /\
      Desc r (Some y) ub  (size m - 1) (fun i => if (i == y) then None else sem m i) ->
      P (Some ((y, v), r))) ->
    ((forall i, sem m i = None) -> P None) ->
    P (minViewWithKey m).
Proof.
  intros ??? HB P HSome HNone.
  unfold minViewWithKey.
  inversion HB; subst.
  * apply HNone. intro; reflexivity.
  * unfold op_zdzn__, Datatypes.id, op_zd__.
    eapply minViewSure_Desc; only 1: eassumption.
    intros.
    apply HSome.
    split.
    - simpl. destruct H3. destruct H3. destruct H3. subst. rewrite Eq_Reflexive.
      assert (sem s1 x = None). { eapply sem_outside_above. apply H. solve_Bounds. }
      rewrite H3. simpl. reflexivity. rewrite H3. simpl. reflexivity. 
    - applyDesc H3. solve_Desc.
Qed.

Lemma minViewDesc:
  forall m lb ub,
  Bounded m lb ub ->
  minView m = match minViewWithKey m with
            |None => None
            | Some ((x,y), m) => Some (y, m)
            end.
Proof.
  intros. unfold minView. reflexivity.
Qed.


(** ** Verification of [glue] *)

Lemma glue_Desc:
  forall s1 s2 lb ub x,
  Bounded s1 lb (Some x) ->
  Bounded s2 (Some x) ub ->
  isLB lb x = true ->
  isUB ub x = true ->
  balance_prop (size s1) (size s2) ->
  Desc (glue s1 s2) lb ub ((size s1 + size s2)%Z) (fun i => sem s1 i ||| sem s2 i).
Proof.
  intros ????? HB1 HB2 ???.

  inversion HB1; inversion HB2; subst; cbn -[Z.add]; clear HB1 HB2.
  1-3: solve [solve_Desc|solve_size].
  destruct (Z.ltb_spec (1 + size s4 + size s5) (1 + size s0 + size s3)).
  - eapply maxViewSure_Desc; only 1: solve_Bounded.
    intros y vy r [Hthere HD].
    applyDesc HD.
    destruct Hthere as [[??]|Hthere].
    * subst; applyDesc balanceR_Desc; solve_Desc.
    * subst; applyDesc balanceR_Desc; solve_Desc.
  - eapply minViewSure_Desc; only 1: solve_Bounded.
    intros y vy r [Hthere HD].
    applyDesc HD.
    destruct Hthere as [[??]|Hthere]; subst; applyDesc balanceL_Desc; solve_Desc.
Qed.

(** ** Verification of [delete] *)

Lemma delete_Desc :
  forall x s lb ub,
  Bounded s lb ub ->
  Desc (delete x s) lb ub (if isSome (sem s x) then (size s - 1) else size s) (fun i => if i == x then None else sem s i).
Proof.
  intros ???? HB.
  induction HB; intros; subst.
  - simpl. solve_Desc.
  - cbn -[Z.add].
    destruct (compare x x0) eqn:Heq.
    + replace (x == x0) with true by solve_Bounds.
      simpl_options.
      applyDesc glue_Desc.
      solve_Desc.
    + applyDesc IHHB1; clear IHHB1 IHHB2.
      replace (x == x0) with false by solve_Bounds.
      rewrite -> (sem_outside_below HB2) by solve_Bounds.
      simpl_options.
      destruct_ptrEq.
      * replace (isSome (sem s1 x)) with false in *
          by (destruct (sem s1 x); simpl in *;  try congruence; lia).
        solve_Desc.
      * destruct (sem s1 x); cbn -[Z.add] in *; applyDesc balanceR_Desc; solve_Desc.
    + applyDesc IHHB2; clear IHHB1 IHHB2.
      replace (x == x0) with false by solve_Bounds.
      rewrite -> (sem_outside_above HB1) by solve_Bounds.
      simpl_options.
      destruct_ptrEq.
      * replace (isSome (sem s2 x)) with false by (destruct (sem s2 x); simpl in *; try congruence; lia).
        solve_Desc.
      * destruct (sem s2 x); cbn -[Z.add] in *; applyDesc balanceL_Desc; solve_Desc.
Qed.

(** ** Verification of [deleteMin] *)

(** It is hard to phrase this without refering to [lookupMin] *)

Lemma deleteMin_Desc :
  forall m lb ub,
  Bounded m lb ub ->
  deleteMin m = match lookupMin m with | None => m
                                       | Some (x, y) => delete x m end.
Proof.
  intros ??? HD.
  induction HD.
  * reflexivity.
  * clear IHHD2.
    cbn [deleteMin].
    rewrite IHHD1; clear IHHD1.

    destruct s1 eqn:?.
    + replace (lookupMin (Bin sz x v (Bin s e0 a0 m1 m2) s2)) with (lookupMin (Bin s e0 a0 m1 m2)) by reflexivity.
      rewrite <- Heqm in *. clear  s e0 a0 m1 m1 Heqm.

      pose proof (lookupMin_Desc s1 lb (Some x) HD1) as Hlookup.
      destruct (lookupMin s1) as [ex|].
      - destruct ex. destruct Hlookup as [Hthere Hextrem].
        simpl.
        apply (sem_inside HD1) in Hthere. destruct Hthere.
        replace (compare e0 x) with Lt by (symmetry; solve_Bounds).
        ** destruct_ptrEq.
           ++ rewrite Hpe. clear Hpe.
              eapply balanceR_noop; try eassumption.
           ++ reflexivity.
       - rewrite H1.
          eapply balanceR_noop; try eassumption.
   + simpl.
     replace (compare x x) with Eq by (symmetry; order e).
     reflexivity.
Qed.

(** ** Verification of [deleteMax] *)

(** It is hard to phrase this without refering to [lookupMax] *)

Lemma deleteMax_Desc :
  forall m lb ub,
  Bounded m lb ub ->
  deleteMax m = match lookupMax m with | None => m
                                       | Some (x, y) => delete x m end.
Proof.
  intros ??? HD.
  induction HD.
  * reflexivity.
  * clear IHHD1.
    cbn [deleteMax].
    rewrite IHHD2; clear IHHD2.

    destruct s2 eqn:?.
    + replace (lookupMax (Bin sz x v s1 (Bin s e0 a0 m1 m2))) with (lookupMax (Bin s e0 a0 m1 m2)) by reflexivity.
      rewrite <- Heqm in *. clear s e0 a0 m1 m2 Heqm.

      pose proof (lookupMax_Desc s2 (Some x) ub HD2) as Hlookup.
      destruct (lookupMax s2) as [ex|].
      - destruct ex. destruct Hlookup as [Hthere Hextrem].
        simpl.
        apply (sem_inside HD2) in Hthere. destruct Hthere.
        replace (compare e0 x) with Gt by (symmetry; solve_Bounds).
        ** destruct_ptrEq.
           ++ rewrite Hpe. clear Hpe.
              eapply balanceL_noop; try eassumption.
           ++ reflexivity.
       - rewrite H1.
          eapply balanceL_noop; try eassumption.
   + simpl.
     replace (compare x x) with Eq by (symmetry; order e).
     destruct s1; reflexivity.
Qed.

(** ** Verification of [split] *)

Lemma split_Desc :
  forall x s lb ub,
  Bounded s lb ub ->
  forall (P : Map e a * Map e a -> Prop),
  (forall s1 s2,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    size s = size s1 + size s2 + (if isSome (sem s x) then 1 else 0) ->
    (forall i, sem s i = (if i == x then sem s i else sem s1 i ||| sem s2 i)) ->
    P (s1, s2)) ->
  P (split x s) : Prop.
Proof.
  intros ?? ?? HB.
  Ltac solveThis := intros X HX; apply HX; clear X HX; [solve_Bounded|solve_Bounded| |f_solver].
  induction HB.
  - solveThis. reflexivity.
  - simpl.
    destruct (compare x x0) eqn:?.
  + solveThis. replace (x == x0) with true by order e.
    simpl_options. lia.
  + apply IHHB1; intros s1_2 s1_3 HB1_2 HB1_3 Hsz Hsems1; clear IHHB1 IHHB2.
    applyDesc link_Desc.
    solveThis. destruct (sem s1 x); cbn -[Z.add] in *.
    * simpl. lia.
    * replace (x == x0) with false by order e. simpl.
      rewrite (sem_outside_below HB2) by solve_Bounds. simpl. lia.
  + apply IHHB2; intros s2_2 s2_3 HB2_2 HB2_3 Hsz Hsems2; clear IHHB1 IHHB2.
    applyDesc link_Desc.
    solveThis. destruct (sem s2 x); cbn -[Z.add] in *.
    * simpl_options. lia.
    * replace (x == x0) with false by order e. simpl.
      rewrite (sem_outside_above HB1) by solve_Bounds. simpl. lia.
Qed.

(** ** Verification of [union] *)

(* The [union] uses some nested pattern match that expand to a very large
   number of patterns in Coq. So let’s take them apart here *)
Lemma union_destruct :
  forall (P : Map e a -> Prop),
  forall s1 s2,
  (s2 = Tip -> P s1) ->
  (s1 = Tip -> P s2) ->
  (forall sz2 x vx, (s2 = Bin sz2 x vx Tip Tip) -> P (insertR x vx s1)) ->
  (forall sz1 x vx, (s1 = Bin sz1 x vx Tip Tip) -> P (insert x vx s2)) ->
  (forall sz1 x vx l1 r1, (s1 = Bin sz1 x vx l1 r1) -> 
    P (
      match split x s2 with
      | pair l2 r2 =>
      match union r1 r2 with
      | r1r2 =>
      match union l1 l2 with
      | l1l2 => if andb  (PtrEquality.ptrEq l1l2 l1)
                         (PtrEquality.ptrEq r1r2 r1) : bool
                then s1 else link x vx l1l2 r1r2
      end end end)) ->
  P (union s1 s2).
Proof.
  intros P s1 s2 HTipR HTipL HSingletonR HSingletonL HBins.
  destruct s1, s2; simpl union;
  try destruct s1_1, s1_2;
  try destruct s2_1, s2_2;
  first [ eapply HBins; reflexivity
        | eapply HSingletonL; reflexivity
        | eapply HSingletonR; reflexivity
        | eapply HTipL; reflexivity
        | eapply HTipR; reflexivity
        | idtac
        ].
Qed. 

Lemma union_Desc :
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Desc' (union s1 s2) lb ub (fun i => sem s1 i ||| sem s2 i).
(* We use [Desc'] here, because the result of [union] is passed to [link], which
   does a full rebalance, and hence does not need to know anything about the size.
   If it turns out we need [size (union s1 s2)], we can still add it.
*)
Proof.
  intros ???? HB1 HB2.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  * apply union_destruct; intros; subst; try congruence.
    + solve_Desc.
    + solve_Desc.
    + inversion HB3; subst; clear HB3.
      clear H4 H5.
      (* We need to give [applyDesc] a hint about the bounds that we care about: *)
      assert (Bounded Tip lb ub) by constructor.
      applyDesc insertR_Desc.
      solve_Desc.
  * apply union_destruct; intros; subst; try congruence.
    + solve_Desc.
    + inversion HB3; subst; clear HB3.
      applyDesc insertR_Desc.
      solve_Desc.
    + inversion H3; subst; clear H3.
      applyDesc insert_Desc. solve_Desc.
    + inversion H3; subst; clear H3.
      eapply split_Desc; try eassumption.
      intros.
      applyDesc IHHB1_1.
      applyDesc IHHB1_2.
      destruct_ptrEq.
      - solve_Desc.
      - applyDesc link_Desc.
        solve_Desc.
Qed.

(** ** Verification of [unions] *)

(* This is a bit of a lazy specification, but goes a long way *)

Lemma Forall_rev:
  forall A P (l : list A), Forall P (rev l) <-> Forall P l.
Proof. intros. rewrite !Forall_forall. setoid_rewrite <- in_rev. reflexivity. Qed.

Lemma oro_assoc : forall {a} (o1 o2 o3: option a),
  (o1 ||| o2) ||| o3 = o1 ||| (o2 ||| o3).
Proof.
  intros. destruct o1. simpl. reflexivity. simpl. reflexivity.
Qed.

Lemma oro_app: forall o l1 l2 i,
  (fold_right (fun h t => sem h i ||| t) o (l1 ++ l2)) =
  (fold_right (fun h t => sem h i ||| t) None l1) |||
  (fold_right (fun h t => sem h i ||| t) o l2).
Proof.
  intros. generalize dependent o. generalize dependent l2. induction l1; intros.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. rewrite oro_assoc. reflexivity.
Qed.

Require Proofs.Data.Foldable.

Lemma unions_Desc:
  forall ss lb ub,
  Forall (fun s => Bounded s lb ub) ss ->
  Desc' (unions ss) lb ub (fun i => fold_right (fun h t => sem h i ||| t) None ss).
Proof.
  intros.
  unfold unions.
  (* Switch to a fold right *)
  rewrite Proofs.Data.Foldable.hs_coq_foldl'_list.
  rewrite <- fold_left_rev_right.
  rewrite <- (rev_involutive ss).
  rewrite <- (rev_involutive ss), Forall_rev in H.
  generalize dependent (rev ss). intros.
  rewrite rev_involutive.

  induction H.
  * simpl. applyDesc empty_Desc. solve_Desc.
  * simpl fold_right.
    applyDesc IHForall.
    applyDesc union_Desc.
    solve_Desc.
    intro i.
    rewrite Hsem0, Hsem. rewrite oro_app. simpl. rewrite oro_None_r. reflexivity.
Qed.
(** ** Verification of [link2] *)

(** This is called  [merge] for Set *)

Lemma link2_eq: forall (l r: Map e a), link2 l r = 
  match l, r with 
  | Tip, r => r
  | l, Tip => l
  | (Bin sizeL x vx lx rx as l), (Bin sizeR y vy ly ry as r) =>
    if Sumbool.sumbool_of_bool
         ((delta GHC.Num.* sizeL) GHC.Base.< sizeR)
    then balanceL y vy (link2 l ly) ry           
    else if Sumbool.sumbool_of_bool
              ((delta GHC.Num.* sizeR) GHC.Base.< sizeL)
         then balanceR x vx lx (link2 rx r)
         else glue l r
  end.
Proof.
  intros l r.
  destruct l; [|auto].
  destruct r; [|auto].
  unfold link2 at 1, link2_func at 1;
  lazymatch goal with 
    |- Wf.Fix_sub ?A ?R ?Rwf ?P ?F_sub ?x = ?rhs => 
    apply (@Wf.WfExtensionality.fix_sub_eq_ext A R Rwf P F_sub x)
  end.
Qed.


Program Fixpoint link2_Desc (s1: Map e a)  (s2: Map e a)
  {measure (map_size s1 + map_size s2)} :
    forall x lb ub,
      Bounded s1 lb (Some x) ->
      Bounded s2 (Some x) ub  ->
      isLB lb x = true ->
      isUB ub x = true->
      Desc (link2 s1 s2) lb ub (size s1 + size s2)
           (fun i => sem s1 i ||| sem s2 i)
  := _.
Next Obligation.
  intros.
  rewrite link2_eq. 
  inversion H; subst; clear H;
    inversion H0; subst; clear H0;
      try solve [solve_Desc].
  destruct (Sumbool.sumbool_of_bool _);
    only 2: destruct (Sumbool.sumbool_of_bool _);
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
  - applyDesc link2_Desc.
    applyDesc balanceL_Desc.
    solve_Desc.
  - applyDesc link2_Desc.
    applyDesc balanceR_Desc.
    solve_Desc.
  - applyDesc glue_Desc.
    solve_Desc.
Qed.


(** ** Verification of [splitMember] *)

(* Rewrite to avoid local [go] and StrictTriple *)
Fixpoint splitMember' (k : e) (s : Map e a) : (Map e a * bool * Map e a)%type :=
  match s with
   | Tip => (Tip, false, Tip)
   | Bin _ kx x l r => match GHC.Base.compare k kx with
     | Lt => match splitMember' k l with
               | (lt, z, gt) => match link kx x gt r with
                                              | gt' => (lt, z, gt')
                                            end
             end
     | Gt => match splitMember' k r with
               | (lt, z, gt) => match link kx x l lt with
                                              | lt' => (lt', z, gt)
                                            end
             end
     | Eq => (l, true, r)
    end
 end.

Lemma splitMember_splitMember' : forall x s, splitMember x s  = splitMember' x s.
Proof.
  intros.
  unfold splitMember.
  induction s.
  * simpl.
    rewrite <- IHs1. clear IHs1.
    rewrite <- IHs2. clear IHs2.
    destruct (compare x k).
    + reflexivity.
    + destruct (_ x s2); reflexivity.
    + destruct (_ x s3); reflexivity.
  * reflexivity.
Qed.

Lemma splitMember_Desc:
  forall x s lb ub,
  Bounded s lb ub ->
  forall (P : Map e a * bool * Map e a -> Prop),
  (forall s1 b s2,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    b = isSome (sem s x) ->
    (forall i, sem s i =
          (if i == x then sem s i
           else  (sem s1 i ||| sem s2 i))) ->
    P (s1, b, s2)) ->
  P (splitMember x s) : Prop.
Proof.
  intros ?? ?? HB.
  rewrite splitMember_splitMember'.
  induction HB.
  Ltac solveThis ::= intros X HX; apply HX; clear X HX; [solve_Bounded|solve_Bounded|try reflexivity |f_solver].
  * solveThis.
  * simpl.
    destruct (compare x x0) eqn:?.
    + solveThis.
      replace (x == x0) with true by order_Bounds.
      simpl_options.
      reflexivity.
    + apply IHHB1.
      intros s1_2 b s1_3 HB1_2 HB1_3 Hb Hsems1.
      clear IHHB1 IHHB2.
      applyDesc link_Desc.
      solveThis.
      replace (x == x0) with false by order_Bounds.
      rewrite (sem_outside_below HB2) by order_Bounds.
      simpl_options. assumption.
    + apply IHHB2.
      intros s2_2 b s2_3 HB2_2 HB2_3 Hb Hsems2.
      clear IHHB1 IHHB2.
      applyDesc link_Desc.
      solveThis.
      replace (x == x0) with false by order_Bounds.
      rewrite (sem_outside_above HB1) by order_Bounds.
      simpl_options. assumption.
Qed.

(** ** Verification of [intersection] *)

Lemma intersection_Desc:
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  Desc' (intersection s1 s2) lb ub
        (fun i => sem s1 i &&& sem s2 i).
Proof.
  intros ???? HB1 HB2.
  revert s2 HB2.
  induction HB1; intros s3 HB3.
  - simpl. solve_Desc.
  - simpl.
    destruct s3 eqn:Hs3.
    + rewrite <- Hs3 in *.
      clear Hs3 s e0 a0 m1 m2.
      eapply splitMember_Desc;
        only 1: eassumption.
      intros s4' b s5' HB1 HB2 Hb Hi.
      applyDesc IHHB1_1.
      applyDesc IHHB1_2.
      destruct b.
      * destruct_ptrEq.
        -- solve_Desc.
        -- applyDesc link_Desc.
           solve_Desc.
      * applyDesc link2_Desc.
        solve_Desc.
    + solve_Desc.
Qed.

(** ** Verification of [difference] *)

(** A wart: Because we are in a section that fixes [a], 
we get this proof only for invocations of [difference] where
boths maps have the same element type. This does not
affect the proof, but requires some Coq proof structure engineering
to fix. *)

Lemma difference_destruct :
  forall (P : Map e a -> Prop),
  forall s1 s2,
  (s1 = Tip -> P Tip) ->
  (s2 = Tip -> P s1) ->
  (forall sz2 x vx l2 r2, (s2 = Bin sz2 x vx l2 r2) -> 
    P (
      match split x s1 with
      | pair l1 r1 =>
      match difference r1 r2 with
      | r1r2 =>
      match difference l1 l2 with
      | l1l2 => if size l1l2 + size r1r2 == size s1
                then s1 else link2 l1l2 r1r2
      end end end)) ->
  P (@difference e a a _ _ s1 s2).
Proof.
  intros P s1 s2 HTipL HTipR HBins.
  destruct s1, s2; simpl difference;
  try destruct s1_1, s1_2;
  try destruct s2_1, s2_2;
  first [ eapply HBins; reflexivity
        | eapply HTipL; reflexivity
        | eapply HTipR; reflexivity
        | idtac
        ].
Qed.

Lemma difference_Desc :
  forall s1 s2 lb ub,
  Bounded s1 lb ub ->
  Bounded s2 lb ub ->
  forall (P : Map e a -> Prop),
  (forall s,
    Bounded s lb ub ->
    size s <= size s1 ->
    (size s = size s1 -> forall i, sem s i = sem s1 i) ->
    (forall i, sem s i = diffo (sem s1 i) (sem s2 i)) ->
    P s) ->
  P (difference s1 s2).
Proof.
  intros s1 s2 lb ub Hb1 Hb2.
  revert s1 Hb1. induction Hb2; intros sl Hb1; apply hide.
  Ltac showP := apply unhide; intros X HX; apply HX; clear X HX; only 3: intro.
  - simpl.
    destruct sl; (showP; [assumption | reflexivity | reflexivity | f_solver]).
  - apply difference_destruct; intros; subst.
    + (showP; [assumption | reflexivity | reflexivity | f_solver]).
    + (showP; [assumption | reflexivity | reflexivity | f_solver]). 
    + eapply split_Desc; try eassumption. 
      intros sl1 sl2 HBsl1 HBsl2 Hsz Hsem. inversion H3; subst; clear H3.
      eapply IHHb2_1. solve_Bounded. intros sil ????. clear IHHb2_1.
      eapply IHHb2_2. solve_Bounded. intros sir ????. clear IHHb2_2.
      destruct (_ == _) eqn:Hcomp.
      * showP; [assumption | reflexivity | reflexivity | ].
        assert (size sl1 + size sl2 <= size sl) by (destruct (sem sl x0); simpl in *; lia).
        change (size sil + size sir =? size sl = true) in Hcomp.
        rewrite Z.eqb_eq in Hcomp.
        lapply H4; [intro; subst; clear H4|lia].
        lapply H8; [intro; subst; clear H8|lia].
        assert (sem sl x0 = None) by (destruct (sem sl x0); simpl in *; try reflexivity; lia).
        f_solver. (* TODO: More stuff that [f_solver] should do *)
      * applyDesc link2_Desc.
        showP.
        -- assumption.
        -- destruct (sem sl x0); simpl in *; lia.
        -- assert (sem sl x0 = None) by (destruct (sem sl x0); simpl in *; try reflexivity; lia).
           rewrite H11 in Hsz.
           simpl in Hsz.
           lapply H4; [intro; subst|lia].
           lapply H8; [intro; subst|lia].
           clear H4 H8.
           f_solver.
        -- f_solver.
Qed.

(** ** Verification of [foldrWithKey] *)

Lemma fold_right_toList_go:
  forall f (n : a) map (xs : list (e * a)),
  fold_right f n (foldrWithKey (fun x y t  => (x,y) :: t) xs map) = 
  foldrWithKey (fun x y t => f (x,y) t) (fold_right f n xs) map.
Proof.
  intros. generalize dependent xs. induction map.
  - intros. simpl. rewrite IHmap1. simpl. rewrite IHmap2. reflexivity.
  - simpl. intros. reflexivity.
Qed.

Lemma foldrWithKey_spec:
  forall f (n : a) map,
  foldrWithKey f n map = fold_right (fun (x : e * a) t => let (a0, b0) := x in f a0 b0 t) n (toList map).
Proof.
  intros. unfold toList. unfold toAscList. rewrite fold_right_toList_go. simpl. reflexivity.
Qed.

(** ** Verification of [foldr] *)
Lemma foldr_spec:
  forall f (n: a) (map : Map e a),
  foldr f n map = foldrWithKey (fun x y t => f y t) n map.
Proof.
  intros. generalize dependent n. induction map.
  - intros. simpl. rewrite IHmap1. rewrite IHmap2. reflexivity.
  - intros. simpl. reflexivity.
Qed.

(** ** Verification of [foldr'] *)
Lemma foldr'_spec:
  forall {k : Type} (f : a -> k -> k) (n : k) (m : Map e a),
  foldr' f n m = foldr f n m.
Proof. reflexivity. Qed.

(** ** Verification of [toList] *)

Lemma foldrWithKey_const_append:
  forall xs (map : Map e a),
  foldrWithKey (fun x y t => (x,y) :: t) xs map = toList map ++ xs.
Proof.
  intros. generalize dependent xs. induction map; intros.
  - unfold toList, toAscList in *. simpl. rewrite IHmap1. rewrite IHmap2. 
    rewrite (IHmap1 ((k, a0) :: foldrWithKey (fun (k0 : e) (x : a) (xs0 : list (e * a)) => (k0, x) :: xs0) nil map2)).
    rewrite <- app_assoc. reflexivity.
  - simpl. reflexivity.
Qed.

(*Allows us to decompose toList*)
Lemma toList_Bin:
  forall sz key value (m1 m2 : Map e a),
  toList (Bin sz key value m1 m2) = toList m1 ++ (key, value) :: nil ++ toList m2.
Proof.
  intros.
  unfold toList. unfold toAscList. simpl.
  rewrite foldrWithKey_const_append. rewrite foldrWithKey_const_append.
  rewrite foldrWithKey_const_append. rewrite app_nil_r. rewrite app_nil_r.
  reflexivity.
Qed.

(*We have two different versions of toList_sem for use in proving [Eq], preceded by several helper lemmas*)

(*This function imposes a stronger condition than List.elem - the values must be equal according to Coq.
This is used in proving strong equality*)
Fixpoint In {e} {a} `{EqLaws e} (key : e) (value : a) (l : list (e * a)) : Prop :=
  match l with
  | nil => False
  | a :: tl => (let (x,y):= a in x == key = true /\ y = value) \/ In key value tl
  end.

(*Helper methods for logic*)

Lemma or_assoc: forall b1 b2 b3,
  (b1 \/ b2) \/ b3 <-> b1 \/ ( b2 \/ b3).
Proof.
  intros. split; intros.
  - destruct H. destruct H. left. assumption. right. left. assumption. right.
    right. assumption.
  - destruct H. left. left. assumption. destruct H. left. right. assumption. right.
    assumption.
Qed.

Lemma false_or: forall (P : Prop),
  False \/ P <-> P.
Proof.
  intros. split; intros.
  - destruct H. destruct H. apply H.
  - right. apply H.
Qed. 

(*Key property of In for lists - if we append to 2 lists, an item is in the whole list
iff it is in one of them*)
Lemma elem_or : forall {e} {a} `{EqLaws e} (key : e) (value : a) l1 l2,
  In key value (l1 ++ l2) <-> In key value l1 \/ In key value l2.
Proof.
  intros. generalize dependent l2. induction l1.
  - intros. simpl. split; intros.
    + right. assumption.
    + destruct H1. destruct H1. assumption.
  - intros. simpl. rewrite IHl1. rewrite or_assoc. apply iff_refl.
Qed.

(*The first toList_sem:
This says that sem m key returns a Value iff that key, value pair appears in the 
resulting toList of the map (according to Coq equality for values)*)
Lemma toList_sem :
  forall  `{EqLaws a}  m lb ub, Bounded m lb ub ->
  forall key value, sem m key = Some value <-> In key value (toList m).
Proof.
  intros. generalize dependent value. induction H1.
  - simpl. intros. split; intros. discriminate H1. destruct H1.
  - intros. simpl. rewrite toList_Bin. rewrite elem_or. 
    assert (((x, v) :: nil ++ toList s2) = (((x, v) :: nil) ++ toList s2)).
    simpl. reflexivity. rewrite H5. rewrite elem_or. split; intros.
      + destruct (sem s1 key) eqn : ?; simpl in H6.
      * apply IHBounded1 in H6. left. apply H6. 
      * destruct (key == x) eqn : ?; simpl in H6.
        { right. left. simpl. left. apply Eq_Symmetric in Heqb.
          split. apply Heqb. inversion H6. reflexivity. }
        { apply IHBounded2 in H6. right. right. assumption. }
     + destruct H6.
      * apply IHBounded1 in H6. rewrite H6. simpl. reflexivity.
      * destruct H6. simpl in H6. destruct H6. destruct H6.
        assert (sem s1 key = None). { eapply sem_outside_above.
        apply H1_. order_Bounds. }
        rewrite H8. simpl. apply Eq_Symmetric in H6. rewrite H6. simpl.
        rewrite H7. reflexivity. destruct H6. apply IHBounded2 in H6.
        assert (H1_1:=H1_0). eapply sem_inside in H1_0. destruct H1_0.
        assert (sem s1 key = None). { eapply sem_outside_above. apply H1_.
        assert (isLB (Some x) key = true). { apply H7. }
        order_Bounds. }
        assert (key == x = false). { order_Bounds. }
        rewrite H9. rewrite H10. simpl. assumption. apply H6.
Qed.

(*Helper lemmas for [toList_sem']*)
(*Analogue of [elem_or] for List.elem*)
Lemma list_elem_or : forall `{Eq_ a} `{EqLaws a} l1 l2 (x : e * a),
  List.elem x (l1 ++ l2) = List.elem x l1 || List.elem x l2.
Proof.
  intros. generalize dependent l2. induction l1; intros.
  - destruct l2. simpl. reflexivity. simpl. reflexivity.
  - destruct l2. simpl. rewrite app_nil_r. rewrite orb_false_r .
    reflexivity. simpl. rewrite IHl1. rewrite orb_assoc. simpl. reflexivity.
Qed.

(*It is often easier to prove iff rather than equality (for booleans). This lemma states that either can
be proved *)
Lemma prop_bool: forall (b1: bool) (b2: bool),
  b1 = b2 <-> (b1 = true <-> b2 = true).
Proof.
  intros. split; intros.
  - split; intros.
    + subst. reflexivity.
    + subst. reflexivity.
  - destruct H. destruct b1. symmetry. apply H. reflexivity.
    destruct b2. apply H0. reflexivity. reflexivity.
Qed.

(*Helper lemmas for working with equality of tuples. Because [toList_sem'] uses Haskell rather
than Coq's equality, the equality comparisons get much more tedious*)
Lemma eq_tuple_prop: forall {a} {b} `{Eq_ a} `{EqLaws a} `{Eq_ b} `{EqLaws b}
  (x1 x2 : a) (y1 y2 : b),
  (x1, y1) == (x2, y2) = true <-> x1 == x2 = true /\ y1 == y2 = true.
Proof.
  intros. unfold op_zeze__. unfold Eq_pair___. unfold op_zeze____. unfold eq_pair.
  unfold op_zeze__. unfold op_zeze____. rewrite andb_true_iff. reflexivity.
Qed.

Lemma eq_tuple_eq: forall {a} {b} `{Eq_ a} `{EqLaws a} `{Eq_ b} `{EqLaws b}
  (x1 x2 : a) (y1 y2 : b),
  (x1, y1) == (x2, y2) = (x1 == x2) && (y1 == y2).
Proof. 
  intros. rewrite prop_bool. rewrite andb_true_iff. apply eq_tuple_prop.
Qed.

(*Weaker version of [toList_sem], using Haskell equality instead of Coq's. sem m key == Some value 
iff the (key, value) pair appears in toList*)
Lemma toList_sem' :
  forall `{Eq_ a} `{EqLaws a}  m lb ub, Bounded m lb ub ->
  forall key value, sem m key == Some value = true <->
     List.elem (key, value) (toList m) = true.
Proof.
  intros. generalize dependent value. induction H2.
  - simpl. intros. split; intros.
    + discriminate H2.
    + discriminate H2.
  - intros; split; intros; simpl.
    + rewrite toList_Bin. simpl. rewrite list_elem_or. simpl.
      simpl in H6. destruct (List.elem (key, value) (toList s1)) eqn : ?.
      * simpl. reflexivity.
      * simpl. specialize (IHBounded1 value). destruct IHBounded1.
        apply contrapositive in H7. destruct (sem s1 key) eqn : ?.
        { simpl in H6. contradiction. }
        { simpl in H6. destruct (_GHC.Base.==_ (key, value) (x, v)) eqn : ?.
          { simpl. reflexivity. }
          { simpl. rewrite eq_tuple_eq in Heqb0. 
            rewrite andb_false_iff in Heqb0. destruct Heqb0.
            { rewrite H9 in H6. simpl in H6. apply IHBounded2. apply H6. }
            { destruct (_GHC.Base.==_ key x) eqn : ?.
              { simpl in H6. rewrite simpl_option_some_eq in H6. 
                apply Eq_Symmetric in H6. unfold is_true in H6. 
                rewrite H9 in H6. discriminate H6. }
              { simpl in H6. apply IHBounded2. assumption. }
            }
          }
        }
        { destruct (List.elem (key, value) (toList s1)). discriminate Heqb.
          intro. discriminate H9. }
    + rewrite toList_Bin in H6. simpl in H6. rewrite list_elem_or in H6.
      rewrite orb_true_iff in H6. destruct H6.
      * apply IHBounded1 in H6. destruct (sem s1 key) eqn : ?.
        { simpl. assumption. }
        { discriminate H6. }
      * simpl in H6. rewrite orb_true_iff in H6. destruct H6.
        { assert (forall i, sem s1 key <> Some i). { rewrite eq_tuple_prop in H6.
          destruct H6. intros. intro. solve_Bounds. } 
          assert (sem s1 key = None). { destruct (sem s1 key). specialize (H7 a0).
          contradiction. reflexivity. }
          rewrite H8. simpl. rewrite eq_tuple_prop in H6. destruct H6.
          rewrite H6. simpl. rewrite simpl_option_some_eq. apply Eq_Symmetric.
          apply H9. }
        { apply IHBounded2 in H6. destruct (sem s2 key) eqn : ?.
          assert (sem s1 key = None). { apply (sem_inside H2_0) in Heqo.
          destruct Heqo. eapply sem_outside_above. apply H2_. order_Bounds. }
          rewrite H7. simpl. assert (key == x = false) by solve_Bounds. rewrite H8.
          simpl. assumption. discriminate H6. }
Qed. 

(*Equality based (rather than prop based) version of the above*)
Lemma toList_sem'_eq :
  forall `{Eq_ a} `{EqLaws a}  m lb ub, Bounded m lb ub ->
  forall key value, sem m key == Some value = List.elem (key, value) (toList m).
Proof.
  intros. rewrite prop_bool.  eapply toList_sem'. apply H2.
Qed.

(*The next two lemmas say that every key in toList m is between the bounds of the map*)
Lemma toList_lb : forall m lb ub,
  Bounded m lb ub ->
  Forall (fun (i : e * a) => let (x, _) := i in isLB lb x = true) (toList m).
Proof.
  intros. induction H.
  - apply Forall_nil.
  - rewrite toList_Bin. rewrite Forall_forall in *.
    intros. simpl in H5. rewrite in_app_iff in *.
    destruct H5.
    + apply IHBounded1. assumption.
    +  simpl in H5.  destruct H5. 
      *  subst.  assumption. 
      * apply IHBounded2 in H5. simpl in H5. rename x0 into x2. 
        destruct x2. order_Bounds.
Qed.

Lemma toList_ub : forall m lb ub,
  Bounded m lb ub ->
  Forall (fun (i : e * a) => let (x, _) := i in isUB ub x = true) (toList m).
Proof.
  intros. induction H.
  - apply Forall_nil.
  - rewrite toList_Bin. rewrite Forall_forall in *. intros.
    simpl in H5. rewrite in_app_iff in *. destruct H5.
    + apply IHBounded1 in H5. destruct x0. order_Bounds.
    + simpl in H5. destruct H5. subst. assumption. apply IHBounded2. assumption.
Qed. 

(*The list of the empty tree is empty*)
Lemma toList_Tip: toList (@Tip e a) = nil.
Proof. reflexivity. Qed.

(*The list contains the left subtree, then the current value, then the right subtree
(crucial in showing that the list is sorted)*)
Lemma toList_bin:
  forall key value n (m1 m2 : Map e a),
  toList (Bin n key value m1 m2) = toList m1 ++ ((key, value) :: nil) ++ toList m2.
Proof. intros. apply toList_Bin. Qed.

(*The next two lemmas prove that the list from toList is in the same order even if we balance the tree. The
proofs are very similar to setProofs, only 1 more case at the end*)
Lemma toList_balanceR :
  forall x y m1 m2 lb ub,
  Bounded m1 lb (Some x) ->
  Bounded m2 (Some x) ub ->
  balance_prop (size m1) (size m2) \/
  balance_prop_inserted (size m2 - 1) (size m1) /\ (1 <= size m2)%Z  \/
  balance_prop (size m1 + 1) (size m2) ->
  toList (balanceR x y m1 m2) = toList m1 ++ ((x,y) :: nil) ++ toList m2.
Proof.
  intros.
  unfold balanceR.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: rewrite ?toList_Bin, <- ?app_assoc; try reflexivity.
  simpl. rewrite <- app_assoc. assert (((x2, v1) :: toList s5) ++ (x1, v0) :: toList s0 ++ (x3, v2) :: toList s6
  = (x2, v1) :: toList s5 ++ (x1, v0) :: toList s0 ++ (x3, v2) :: toList s6). simpl. reflexivity.
  rewrite H20. reflexivity.
Qed.

Lemma toList_balanceL:
  forall x y m1 m2 lb ub,
  Bounded m1 lb (Some x) ->
  Bounded m2 (Some x) ub  ->
  balance_prop (size m1) (size m2) \/
  balance_prop_inserted (size m1 - 1) (size m2) /\ (1 <= size m1)%Z \/
  balance_prop (size m1) (size m2 + 1) ->
  toList (balanceL x y m1 m2) = toList m1 ++ ((x, y) :: nil) ++ toList m2.
Proof.
  intros.
  unfold balanceL.
  unfold op_zg__, op_zl__, Ord_Integer___, op_zg____, op_zl____.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: rewrite ?toList_Bin, <- ?app_assoc; try reflexivity.
  - simpl. assert (toList s0 ++ (x3, v2) :: toList s6 ++ (x, y) :: toList s1 ++ (x0, v) :: toList s2
  = (toList s0 ++ (x3, v2) :: toList s6) ++ (x, y) :: toList s1 ++ (x0, v) :: toList s2).
    rewrite <- app_assoc. simpl. reflexivity. rewrite H20. reflexivity.
  - simpl. assert (toList s0 ++ (x3, v2) :: toList s6 ++ (x, y) :: toList s1 ++ (x0, v) :: toList s2 =
    (toList s0 ++ (x3, v2) :: toList s6) ++ (x, y) :: toList s1 ++ (x0, v) :: toList s2). 
    rewrite <- app_assoc. simpl. reflexivity. rewrite H20. reflexivity.
Qed.

(*If we insertMax into a tree, that value is at the end of the list*)
Lemma toList_insertMax:
   forall x y m lb,
   Bounded m lb (Some x) ->
   toList (insertMax x y m) = toList m ++ (x,y) :: nil.
Proof.
  intros. remember (Some x) as ub'. generalize dependent x.
  induction H; intros.
  - simpl. reflexivity.
  - simpl. subst. specialize(IHBounded2 x0 eq_refl). revert IHBounded2.
    assert (isUB None x0 = true) by reflexivity. applyDesc insertMax_Desc.
    intro. erewrite toList_balanceR. rewrite IHBounded2. rewrite toList_bin.
    rewrite <- app_assoc. simpl. reflexivity. apply H. apply HB.
    solve_size.
Qed.

(*If we insertMin into a tree, that value is at the beginning of the list*)
Lemma toList_insertMin:
   forall x y m ub,
   Bounded m (Some x) ub ->
   toList (insertMin x y m) = (x,y) :: nil ++ toList m.
Proof.
  intros. remember (Some x) as ub'. generalize dependent x.
  induction H; intros.
  - simpl. reflexivity.
  - simpl. subst. specialize(IHBounded1 x0 eq_refl). revert IHBounded1.
    assert (isLB None x0 = true) by reflexivity. applyDesc insertMin_Desc.
    intro. erewrite toList_balanceL. rewrite IHBounded1. rewrite toList_bin.
    simpl. reflexivity. apply HB. apply H0. solve_size.
Qed.

(*States that if we link 2 maps together, then the list is in the same order. These
past few lemmas together mean that when balancing the tree, the list does not change*)
Program Fixpoint toList_link (x : e) (y : a) (m1: Map e a)  (m2: Map e a)
  {measure (map_size m1 + map_size m2)} :
    forall lb ub,
    Bounded m1 lb (Some x) ->
    Bounded m2 (Some x) ub  ->
    isLB lb x = true ->
    isUB ub x = true->
    toList (link x y m1 m2) = toList m1 ++ (x,y) :: nil ++ toList m2 := _.
Next Obligation.
  intros.
  rewrite link_eq. 
  inversion H; subst; clear H;
  inversion H0; subst; clear H0.
  * reflexivity.
  * erewrite toList_insertMin by solve_Bounded.
    rewrite toList_Bin.
    reflexivity.
  * erewrite toList_insertMax by solve_Bounded.
    rewrite toList_Bin.
    reflexivity.
  * destruct (Sumbool.sumbool_of_bool _);
    only 2: destruct (Sumbool.sumbool_of_bool _);
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
    - erewrite toList_balanceL; only 3: solve_Precondition.
      erewrite toList_link by solve_Precondition.
      rewrite ?toList_Bin, <- ?app_assoc. reflexivity.
      applyDesc link_Desc; eassumption.
      applyDesc link_Desc; solve_size.
    - erewrite toList_balanceR; only 2: solve_Precondition.
      erewrite toList_link by solve_Precondition.
      rewrite ?toList_Bin, <- ?app_assoc. reflexivity.
      applyDesc link_Desc; eassumption.
      applyDesc link_Desc; solve_size.
    - rewrite ?toList_bin, ?toList_Bin, <- ?app_assoc.
      unfold bin. rewrite toList_bin. rewrite toList_bin.
      rewrite toList_bin. simpl. rewrite <- app_assoc. simpl.
      reflexivity. 
Qed.


(** *** Sortedness of [toList] *)

Require Import Coq.Sorting.Sorted.
Close Scope Z.

(*Maps are sorted only by keys*)
Local Definition lt : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 < e2) = true.

(* States that if two lists are sorted and all values in the first are smaller
than all values in the second, then appending the two lists gives a sorted list. *)
Lemma sorted_append:
  forall (l1 : list (e * a)) (l2 : list (e * a)) (x : e),
  StronglySorted lt l1 ->
  StronglySorted lt l2 ->
  (forall (y : e) (z : a), List.In (y, z) l1 -> (y < x) = true) ->
  (forall y z, List.In (y, z) l2 -> (x <= y) = true) ->
  StronglySorted lt (l1 ++ l2).
Proof.
  intros ??? Hsorted1 Hsorted2 Hlt Hge.
  induction Hsorted1.
  * apply Hsorted2.
  * simpl. apply SSorted_cons.
    + apply IHHsorted1.
      intros y z Hy.
      eapply Hlt.
      right. apply Hy.
    + rewrite Forall_forall.
      intros z Hz.
      rewrite in_app_iff in Hz.
      destruct Hz.
      - rewrite Forall_forall in H.
        apply H; auto.
      - destruct a0.  assert (e0 < x = true). eapply Hlt. left. reflexivity. 
        unfold lt. destruct z. apply Hge in H0. order e.
Qed.

(*Similar to List.elem, but does not require that a be in the Eq typeclass (because it doesn't actually
matter; the a's are not ever compared)*)
Fixpoint list_elem_tuple (x : e * a) (l : list (e * a)) :=
  match l with
  | nil => false
  | h :: t => let (a, b) := h in let (x1, x2) := x in (a == x1) || list_elem_tuple x t
  end.

(*This states that if x is a lower bound for a list and the tuple i is in the list, then x is less than i.
Note: this required a change from toList (using lt rather than < in the conclusion), though this 
is needed because there is no definition of ordering on all tuples*)
Lemma All_lt_elem:
  forall x i xs,
  Forall (lt x) xs ->
  list_elem_tuple i xs = true ->
  lt x i.
Proof.
  intros.
  induction H.
  * simpl in H0. inversion H0.
  * simpl in *. destruct x0. destruct i.
    rewrite orb_true_iff in H0.
    destruct H0.
    - unfold lt in *. destruct x. order e.
    - intuition.
Qed.

(*toList is sorted by key*)
Lemma to_List_sorted:
  forall m lb ub,
  Bounded m lb ub ->
  StronglySorted lt (toList m).
Proof.
  intros. induction H.
  - apply SSorted_nil.
  - rewrite toList_bin. eapply sorted_append. assumption.
    apply SSorted_cons. assumption. apply toList_lb in H0.
    apply H0. apply toList_ub in H.  intros. 
    rewrite Forall_forall in H.
    remember (y,z) as t. 
    apply H in H5. destruct t. inversion Heqt. rewrite <- H7. unfold isUB in H5. apply H5.
    intros. simpl in H5. destruct H5.
    + inversion H5. order e.
    + apply toList_lb in H0. 
      rewrite Forall_forall in H0. apply H0 in H5. order_Bounds.
Qed. 

(** ** Verification of [toAscList] *)

Lemma toAscList_spec: @toAscList = @toList. Proof. reflexivity. Qed.

(** ** Verification of [elems] *)
(*Different than set because elems is toList for set*)

Lemma fold_right_with_assoc:
  forall l1 l2,
    fold_right (fun (x : e * a) acc => let (a,b) := x in b :: acc) l1 l2  = 
  fold_right (fun (x : e * a) acc => let (a,b) := x in b :: acc) nil l2 ++ l1.
Proof.
  intros. generalize dependent l1. induction l2.
  - intros. simpl. reflexivity.
  - intros. simpl. destruct a0. rewrite IHl2. simpl. reflexivity.
Qed. 

Lemma foldr_const_append:
  forall xs (map : Map e a),
  foldr cons xs map = elems map ++ xs.
Proof.
  intros. generalize dependent xs. induction map; intros.
  - simpl. unfold elems. simpl. rewrite IHmap1. rewrite IHmap2. rewrite IHmap1.
    rewrite IHmap2. rewrite <- app_assoc. simpl. rewrite <- app_assoc. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma elems_Bin:
  forall sz key value (m1 m2 : Map e a),
  elems (Bin sz key value m1 m2) = elems m1 ++ (value :: nil) ++ elems m2.
Proof.
  intros. 
  unfold elems at 1. simpl. rewrite foldr_const_append. rewrite foldr_const_append. 
  rewrite app_nil_r. reflexivity.
Qed.

(*For a map, elems means we take the 2nd element of each tuple in toList*)
Lemma elems_spec: forall map,
  elems map = fold_right (fun (x : e * a) acc => let (a,b) := x in  b :: acc) nil (toList map).
Proof.
  intros. induction map.
  - rewrite elems_Bin.  rewrite IHmap1. simpl. rewrite IHmap2. rewrite toList_bin. 
    rewrite fold_right_app. simpl. rewrite <- fold_right_with_assoc. reflexivity.
  - simpl. unfold elems. simpl. reflexivity.
Qed.

(** ** Verification of [toDescList] *)

(*The reverse of a list is empty iff the original list was empty*)
Lemma rev_nil : forall {A : Type} (x : list A),
  rev x = nil <-> x = nil.
Proof.
  intros. split; intros.
  - destruct x. 
    + reflexivity.
    + simpl in H. assert (nil <> rev x ++ a0 :: nil ) by apply app_cons_not_nil.  
      rewrite H in H0. contradiction.
  - rewrite H. reflexivity.
Qed.

(*Reversing a list is injective*)
Lemma rev_inj {A} (x y : list A) :
  rev x = rev y -> x = y.
Proof.
  intros. generalize dependent y. induction x using rev_ind; intros.
  - simpl in H.  symmetry. apply rev_nil. symmetry. assumption.
  - rewrite rev_app_distr in H. simpl in H. destruct y using rev_ind.
    + simpl in H. discriminate H.
    + rewrite rev_app_distr in H. simpl in H. inversion H. subst.
    apply IHx in H2. subst. reflexivity.
Qed.

(*from SetProofs, not actually useful*)
Lemma foldl_acc_app: forall l (m : Map e a),
  foldl (flip cons) l m = foldl (flip cons) nil m ++ l.
Proof.
  intros. generalize dependent l. induction m; intros.
  - simpl. rewrite IHm2. rewrite  IHm1. symmetry. rewrite IHm2. rewrite <- app_assoc.
    simpl. unfold flip. reflexivity.
  - simpl. reflexivity.
Qed.

(*The version we want for toDescList_spec*)
Lemma foldlWithKey_acc_app: forall l (m : Map e a),
  foldlWithKey (fun acc x y => (x, y) :: acc) l m = foldlWithKey (fun acc x y => (x,y) :: acc) nil m ++ l.
Proof.
  intros. generalize dependent l. induction m; intros.
  - simpl. rewrite IHm2. rewrite IHm1. symmetry. rewrite IHm2. rewrite <- app_assoc.
    reflexivity.
  - simpl. reflexivity.
Qed. 

(*reversing a list takes the last element and puts it at the front*)
Lemma rev_cons: forall {A: Type} (l : list A) (x : A),
  rev (l ++ x :: nil) = x :: rev l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. simpl. reflexivity.
Qed. 

(*toDescList returns the reverse of toAscList on a map*)
Lemma toDescList_spec (map : Map e a) :
  toDescList map = rev (toAscList map).
Proof.
  unfold toDescList. unfold toAscList.
  induction map.
  - simpl. rewrite IHmap1. rewrite foldlWithKey_acc_app. rewrite IHmap2.
    assert ((k, a0) :: rev (foldrWithKey (fun (k0 : e) (x : a) (xs : list (e * a)) => (k0, x) :: xs) nil map1)=
      rev (foldrWithKey (fun (k0 : e) (x : a) (xs : list (e * a)) => (k0, x) :: xs) nil map1 ++ (k, a0) :: nil))
      by (symmetry; apply rev_cons).
    rewrite H. rewrite <- rev_app_distr.
    rewrite foldrWithKey_const_append. rewrite app_nil_r. rewrite foldrWithKey_const_append. rewrite app_nil_r.
    rewrite foldrWithKey_const_append. rewrite <- app_assoc. simpl. reflexivity.
  - simpl. reflexivity.
Qed. 

(** ** Verification of [foldl] and [foldlWithKey *)

(** This relates [foldl] and [elems]. *)
Lemma foldl_spec:
  forall k (n : a) (m: Map e a),
  foldl k n m = fold_left k (elems m) n.
Proof.
  intros. generalize dependent n. induction m; intros.
  - simpl. rewrite (elems_Bin s k0 a0 m1 m2) . rewrite IHm1. rewrite IHm2.
    rewrite fold_left_app. simpl. reflexivity.
  - simpl. reflexivity.
Qed. 

(** This relates [foldlWithKey] and [toList]. *)
Lemma foldlWithKey_spec:
  forall f (n : e * a) (m: Map e a),
  foldlWithKey f n m = fold_left (fun xs (x : e * a) => let (a,b) := x in f xs a b)  (toList m) n.
Proof.
  intros. generalize dependent n. induction m; intros.
  - simpl. rewrite toList_Bin. rewrite IHm1. rewrite IHm2.
    rewrite fold_left_app. simpl. reflexivity.
  - reflexivity.
Qed.

(** ** Verification of [foldl'] *)

Lemma foldl'_spec:
  forall k (n : a) (m : Map e a),
  foldl' k n m = foldl k n m.
Proof. reflexivity. Qed.

(** ** Verification of [foldlWithKey'] *)
Lemma foldlWithKey'_spec:
  forall k (n : a) (m : Map e a),
  foldlWithKey' k n m = foldlWithKey k n m.
Proof. reflexivity. Qed.

(** ** Verification of [size] *)

Lemma size_spec:
  forall s lb ub,
  Bounded s lb ub ->
  size s = Z.of_nat (length (toList s)).
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. rewrite toList_Bin. simpl. rewrite app_length. simpl. 
    rewrite Nat2Z.inj_add. rewrite <- IHBounded1.
    rewrite Nat2Z.inj_succ. rewrite <- IHBounded2.
    omega.
Qed.

(** ** Verification of [fromDistinctAscList] *)

Require Import GHC.DeferredFix.

Definition fromDistinctAscList_create_f : (Int -> list (e * a) -> (Map e a) * list (e * a)) -> 
(Int -> list (e * a) -> Map e a * list ( e * a)).
Proof.
  let rhs := eval unfold fromDistinctAscList in (@fromDistinctAscList e a) in
  lazymatch rhs with context [deferredFix2 ?f] => exact f end.
Defined.

Definition fromDistinctAscList_create : Int -> list (e * a) -> (Map e a) * list (e * a)
  := deferredFix2 (fromDistinctAscList_create_f).

Lemma Z_shiftr_pos:
  forall x, (1 < x -> 1 <= Z.shiftr x 1)%Z.
Proof.
  intros.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2^1)%Z with 2%Z by reflexivity.
  assert (2 <= x)%Z by lia. clear H.
  apply Z.div_le_mono with (c := 2%Z) in H0.
  apply H0.
  lia.
Qed.

Lemma Z_shiftl_pos:
  forall x, (1 <= x -> 1 <= Z.shiftl x 1)%Z.
Proof.
  intros.
  rewrite Z.shiftl_mul_pow2 by lia.
  lia.
Qed.

Lemma Z_shiftr_lt:
  forall x, (1 <= x -> Z.shiftr x 1 < x)%Z.
Proof.
  intros.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2^1)%Z with 2%Z by reflexivity.
  apply Z_div_lt; lia.
Qed.

Require Import Coq.Wellfounded.Wellfounded.

Lemma fromDistinctAscList_create_eq:
  forall i xs, (1 <= i)%Z ->
  fromDistinctAscList_create i xs = fromDistinctAscList_create_f fromDistinctAscList_create i xs.
Proof.
  intros.
  change (uncurry fromDistinctAscList_create (i, xs) = uncurry (fromDistinctAscList_create_f fromDistinctAscList_create) (i, xs)).
  apply deferredFix_eq_on with
    (f := fun g => uncurry (fromDistinctAscList_create_f (curry g)))
    (P := fun p => (1 <= fst p)%Z)
    (R := fun x y => (1 <= fst x < fst y)%Z).
  * eapply wf_inverse_image with (R := fun x y => (1 <= x < y)%Z).
    apply Z.lt_wf with (z := 1%Z).
  * clear i xs H.
    intros g h x Px Heq.
    destruct x as [i xs]. simpl in *.
    unfold fromDistinctAscList_create_f.
    destruct_match; try reflexivity.
    repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1); try reflexivity.
    unfold curry.
    assert (1 < i)%Z by lia.
    assert (1 <= Z.shiftr i 1)%Z by (apply Z_shiftr_pos; lia).
    assert (Z.shiftr i 1 < i)%Z by (apply Z_shiftr_lt; lia).
    repeat expand_pairs. simpl.
    rewrite Heq by eauto.
    destruct_match; try reflexivity.
    rewrite Heq by eauto.
    reflexivity.
  * simpl; lia.
Qed.

(* We need to know that [create] returns no longer list than it receives. *)
Program Fixpoint fromDistinctAscList_create_preserves_length
  i xs {measure (Z.to_nat i)} :
  (1 <= i)%Z ->
  forall (P : Map e a * list (e * a) -> Prop),
  ( forall s ys,
    (length ys <= length xs)%nat ->
    P (s, ys)
  ) ->
  P (fromDistinctAscList_create i xs) := _.
Next Obligation.
  intros.
  rename fromDistinctAscList_create_preserves_length into IH.
  rewrite fromDistinctAscList_create_eq by assumption.
  unfold fromDistinctAscList_create_f.
  destruct xs.
  * apply H0. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1).
    + destruct p. apply H0. simpl. lia.
    + assert (Z.to_nat (Bits.shiftR i #1) < Z.to_nat i)%nat. {
        apply Z2Nat.inj_lt.
        apply Z.shiftr_nonneg. lia.
        lia.
        apply Z_shiftr_lt; lia.
      }
      apply IH.
      - assumption. 
      - apply Z_shiftr_pos; lia.
      - intros.
        destruct_match.
        ** apply H0. simpl in *. lia.
        ** apply IH.
           -- assumption.
           -- apply Z_shiftr_pos; lia.
           -- intros.
               destruct p0. apply H0. simpl in *. lia.
Qed.

Definition fromDistinctAscList_go_f : (Int -> Map e a -> list (e * a) -> Map e a) ->
 (Int -> Map e a -> list (e * a) -> Map e a).
Proof.
  let rhs := eval unfold fromDistinctAscList in (@fromDistinctAscList e a) in
  let rhs := eval fold fromDistinctAscList_create_f in rhs in 
  let rhs := eval fold fromDistinctAscList_create in rhs in 
  lazymatch rhs with context [deferredFix3 ?f] => exact f end.
Defined.

Definition fromDistinctAscList_go : Int -> Map e a -> list (e * a) -> Map e a
  := deferredFix3 (fromDistinctAscList_go_f).

Lemma fromDistinctAscList_go_eq:
  forall i s xs, (0 < i)%Z ->
  fromDistinctAscList_go i s xs = fromDistinctAscList_go_f fromDistinctAscList_go i s xs.
Proof.
  intros.
  change (deferredFix (fun g => uncurry (uncurry (fromDistinctAscList_go_f (curry (curry g))))) (i, s, xs) =
    uncurry (uncurry (fromDistinctAscList_go_f fromDistinctAscList_go)) (i, s, xs)).
  rewrite deferredFix_eq_on with
    (P := fun p => (1 <= fst (fst p))%Z)
    (R := fun x y => (length (snd x) < length (snd y))%nat); only 1: reflexivity.
  * apply well_founded_ltof with (f := fun x => length (snd x)).
  * intros g h p Px Heq.
    destruct p as [[x y] z].
    simpl in *.
    unfold fromDistinctAscList_go_f.
    destruct_match; try reflexivity.
    eapply fromDistinctAscList_create_preserves_length; try lia.
    intros s' ys Hlength. destruct p.
    apply Heq.
    + apply Z_shiftl_pos.
      lia.
    + simpl. lia.
  * simpl. lia.
Qed.

Definition safeHd {a} : list (e * a) -> option e := fun xs =>
  match xs with nil => None | ((x, y)::_) => Some x end.

Lemma mul_pow_sub:
  forall sz, (0 < sz)%Z -> (2 * 2 ^ (sz - 1) = 2^sz)%Z.
Proof.
  intros.
  rewrite <- Z.pow_succ_r by lia.
  f_equal.
  lia.
Qed.

Require Import SortedUtil.

Program Fixpoint fromDistinctAscList_create_Desc
  sz lb xs x {measure (Z.to_nat sz)} :
  (0 <= sz)%Z ->
  StronglySorted lt ((lb, x) :: xs) ->
  forall (P : (Map e a) * list (e * a) -> Prop),
  ( forall (s : Map e a) (ys: list (e * a)),
    Bounded s (Some lb) (safeHd ys) ->
    xs = toList s ++ ys ->
    ys = nil \/ size s = (2*2^sz-1)%Z ->
    P (s, ys)
  ) ->
  P (fromDistinctAscList_create (2^sz)%Z xs) := _.
Next Obligation.
  intros ????? Hnonneg HSorted.  
  rename fromDistinctAscList_create_Desc into IH.
  rewrite fromDistinctAscList_create_eq
    by (enough (0 < 2^sz)%Z by lia; apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctAscList_create_f.
  destruct xs.
  * intros X HX. apply HX. clear HX.
    - solve_Bounded.
    - reflexivity.
    - left. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.

    inversion HSorted. subst.
    inversion H2. subst. clear H2.
    inversion H1. subst.
    destruct p.
    assert (isUB (safeHd xs) e0 = true). {
      destruct xs; try reflexivity.
      inversion H5. subst. unfold safeHd. destruct p. assumption. } 
    
    destruct (Z.eqb_spec (2^sz) 1).
    - intros X HX. apply HX. clear HX.
      ++ solve_Bounded.
      ++ rewrite toList_Bin, toList_Tip, app_nil_r. reflexivity.
      ++ right. rewrite size_Bin. lia.
    - assert (~ (sz = 0))%Z by (intro; subst; simpl in n; congruence).
      assert (sz > 0)%Z by lia.
      replace ((Bits.shiftR (2 ^ sz)%Z 1%Z)) with (2^(sz - 1))%Z.
      Focus 2.
        unfold Bits.shiftR, Bits.instance_Bits_Int.
        rewrite Z.shiftr_div_pow2 by lia.
        rewrite Z.pow_sub_r by lia.
        reflexivity.
      assert (Z.to_nat (sz - 1) < Z.to_nat sz)%nat.
      { rewrite Z2Nat.inj_sub by lia. 
        apply Nat.sub_lt.
        apply Z2Nat.inj_le.
        lia.
        lia.
        lia.
        replace (Z.to_nat 1) with 1 by reflexivity.
        lia.
      }
      eapply IH.
      ++ assumption.
      ++ lia.
      ++ eassumption.
      ++ intros l ys HBounded_l Hlist_l Hsize_l.
         destruct ys.
         + intros X HX. apply HX. clear HX.
           ** solve_Bounded.
           ** assumption.
           ** left; reflexivity.
         + simpl in HBounded_l. destruct p.
           destruct Hsize_l; try congruence.
           eapply IH; clear IH.
           ** assumption.
           ** lia.
           ** rewrite Hlist_l in H1. 
              apply StronglySorted_app in H1.
              destruct H1. 
              eassumption.
           ** intros r zs HBounded_r Hlist_r Hsize_r.
              rewrite Hlist_l in HSorted.
              assert (isLB (Some lb) e1 = true). {
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                simpl.
                rewrite Forall_forall in H10. unfold lt in H10.
                specialize (H10 (e1, a1)). 
                apply H10.
                apply in_or_app. right. left. reflexivity.
              }
              rewrite Hlist_r in HSorted.
              assert (isUB (safeHd zs) e1 = true). {
                destruct zs; try reflexivity.
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                apply StronglySorted_app in H10.
                destruct H10.
                apply StronglySorted_inv in H12.
                destruct H12.
                rewrite Forall_forall in H13. specialize (H13 p). unfold isUB. simpl. destruct p.
                unfold lt in H13.
                apply H13.
                apply in_or_app. right. left. reflexivity.
              }
              intros X HX. apply HX. clear HX.
              -- applyDesc link_Desc.
              -- erewrite toList_link by eassumption.
                 rewrite Hlist_l. rewrite Hlist_r.
                 rewrite <- !app_assoc.  reflexivity.
              -- destruct Hsize_r; [left; assumption| right].
                 applyDesc link_Desc.
                 replace (size l). replace (size r).
                 rewrite mul_pow_sub in * by lia.
                 lia.
Qed.

(*The analogue of [sem] for lists - returns the first value associated with
a given key, or None if no such key exists. We will use this to
specify several lemmas in [fromList] rather than List.elem*)
Fixpoint sem_for_lists (l : list (e * a)) (i : e) :=
  match l with
  | nil => None
  | (x,y) :: t => if i == x then Some y else sem_for_lists t i
  end.

Lemma sem_list_app: forall i xs ys,
  sem_for_lists (xs ++ ys) i = sem_for_lists xs i ||| sem_for_lists ys i.
Proof.
  intros. generalize dependent ys. induction xs; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. destruct (i == e0) eqn : ?. reflexivity.
    apply IHxs.
Qed.

Lemma toList_sem'':
  forall s lb ub, Bounded s lb ub ->
  forall i, sem s i = sem_for_lists (toList s) i.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. rewrite IHBounded1. rewrite IHBounded2. rewrite toList_Bin.
    rewrite sem_list_app. rewrite app_comm_cons. rewrite sem_list_app.
    simpl. unfold SomeIf. rewrite oro_assoc. reflexivity.
Qed. 

Program Fixpoint fromDistinctAscList_go_Desc
  sz s xs {measure (length xs)} :
  (0 <= sz)%Z ->
  StronglySorted lt xs ->
  Bounded s None (safeHd xs) ->
  xs = nil \/ size s = (2*2^sz-1)%Z ->
  Desc (fromDistinctAscList_go (2^sz)%Z s xs) None None (size s + List.length xs)
    (fun i => sem s i ||| sem_for_lists xs i) := _. 
Next Obligation.
  intros.
  rename fromDistinctAscList_go_Desc into IH.
  rewrite fromDistinctAscList_go_eq by (apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctAscList_go_f.
  destruct xs.
  * replace (List.length nil) with 0%Z by reflexivity.
    rewrite Z.add_0_r.
    solve_Desc.
  * repeat replace (#1) with 1%Z by reflexivity.
    replace ((Bits.shiftL (2 ^ sz)%Z 1))%Z with (2 ^ (1 + sz))%Z.
    Focus 2.
      unfold Bits.shiftL, Bits.instance_Bits_Int.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.pow_add_r by lia.
      lia. destruct p.

    destruct H2; try congruence.
    eapply fromDistinctAscList_create_Desc.
    - lia.
    - eassumption.
    - intros.
      subst.
      simpl safeHd in *.
      assert (isUB (safeHd ys) e0 = true). {
        destruct ys; try reflexivity.
        apply StronglySorted_inv in H0.
        destruct H0.
        rewrite Forall_forall in H4. specialize (H4 p). unfold isUB. destruct p. simpl.
        unfold lt in H4.
        apply H4. 
        apply in_or_app. right. left. reflexivity.
      }      
      applyDesc link_Desc.
      eapply IH.
      + simpl. rewrite app_length. lia.
      + lia.
      + apply StronglySorted_inv in H0.
        destruct H0.
        apply StronglySorted_app in H0.
        destruct H0.
        assumption.
      + assumption.
      + destruct H5; [left; assumption | right].
        replace (size s1). replace (size s).  replace (size s0).
        rewrite Z.pow_add_r by lia.
        lia.
      + intros.
        solve_Desc.
        ** replace (size s2). replace (size s1). replace (size s).
           rewrite !List.hs_coq_list_length, !Zlength_correct.
           simpl length.
           rewrite app_length, Nat2Z.inj_succ, Nat2Z.inj_add.
           erewrite <- size_spec by eassumption.
           lia.
        ** simpl. 
           setoid_rewrite sem_list_app.
           setoid_rewrite <- toList_sem''; only 2: eassumption.
           f_solver.
Qed.

Lemma fromDistinctAscList_Desc:
  forall xs,
  StronglySorted lt xs ->
  Desc (fromDistinctAscList xs) None None (List.length xs) (fun i => sem_for_lists xs i).
Proof.
  intros.
  unfold fromDistinctAscList.
  fold fromDistinctAscList_create_f.
  fold fromDistinctAscList_create.
  fold fromDistinctAscList_go_f.
  fold fromDistinctAscList_go.
  destruct xs.
  * solve_Desc.
  * replace (#1) with (2^0)%Z by reflexivity. destruct p.
    eapply fromDistinctAscList_go_Desc.
    + lia.
    + apply StronglySorted_inv in H.
      destruct H.
      assumption.
    + assert (isUB (safeHd xs) e0 = true). {
        destruct xs; try reflexivity.
        apply StronglySorted_inv in H.
        destruct H.
        rewrite Forall_forall in H0. destruct p. unfold isUB. simpl.
        unfold lt in H0. specialize (H0 (e1, a1)). 
        apply H0.
        left. reflexivity.
      }
      solve_Bounded.
    + right. reflexivity.
    + intros.
      rewrite List.hs_coq_list_length, Zlength_cons in *.
      rewrite size_Bin in *.
      solve_Desc. simpl. f_solver.
Qed.

(** ** Verification of [fromDistinctDescList] *)

(** Copy’n’paste from [fromDistinctAscList] *)

Local Definition gt : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 > e2) = true.

Definition fromDistinctDescList_create_f : (Int -> list (e * a) -> (Map e a) * list (e * a)) -> 
(Int -> list (e * a) -> Map e a * list ( e * a)).
Proof.
  let rhs := eval unfold fromDistinctDescList in (@fromDistinctDescList e a) in
  lazymatch rhs with context [deferredFix2 ?f] => exact f end.
Defined.

Definition fromDistinctDescList_create : Int -> list (e * a) -> (Map e a) * list (e * a)
  := deferredFix2 (fromDistinctDescList_create_f).

Lemma fromDistinctDescList_create_eq:
  forall i xs, (1 <= i)%Z ->
  fromDistinctDescList_create i xs = fromDistinctDescList_create_f fromDistinctDescList_create i xs.
Proof.
  intros.
  change (uncurry fromDistinctDescList_create (i, xs) = uncurry (fromDistinctDescList_create_f fromDistinctDescList_create) (i, xs)).
  apply deferredFix_eq_on with
    (f := fun g => uncurry (fromDistinctDescList_create_f (curry g)))
    (P := fun p => (1 <= fst p)%Z)
    (R := fun x y => (1 <= fst x < fst y)%Z).
  * eapply wf_inverse_image with (R := fun x y => (1 <= x < y)%Z).
    apply Z.lt_wf with (z := 1%Z).
  * clear i xs H.
    intros g h x Px Heq.
    destruct x as [i xs]. simpl in *.
    unfold fromDistinctDescList_create_f.
    destruct_match; try reflexivity.
    repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1); try reflexivity.
    unfold curry.
    assert (1 < i)%Z by lia.
    assert (1 <= Z.shiftr i 1)%Z by (apply Z_shiftr_pos; lia).
    assert (Z.shiftr i 1 < i)%Z by (apply Z_shiftr_lt; lia).
    repeat expand_pairs. simpl.
    rewrite Heq by eauto.
    destruct_match; try reflexivity.
    rewrite Heq by eauto.
    reflexivity.
  * simpl; lia.
Qed.

(* We need to know that [create] returns no longer list than it receives. *)
Program Fixpoint fromDistinctDescList_create_preserves_length
  i xs {measure (Z.to_nat i)} :
  (1 <= i)%Z ->
  forall (P : Map e a * list (e * a) -> Prop),
  ( forall s ys,
    (length ys <= length xs)%nat ->
    P (s, ys)
  ) ->
  P (fromDistinctDescList_create i xs) := _.
Next Obligation.
  intros.
  rename fromDistinctDescList_create_preserves_length into IH.
  rewrite fromDistinctDescList_create_eq by assumption.
  unfold fromDistinctDescList_create_f.
  destruct xs.
  * apply H0. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1).
    + destruct p. apply H0. simpl. lia.
    + assert (Z.to_nat (Bits.shiftR i #1) < Z.to_nat i)%nat. {
        apply Z2Nat.inj_lt.
        apply Z.shiftr_nonneg. lia.
        lia.
        apply Z_shiftr_lt; lia.
      }
      apply IH.
      - assumption. 
      - apply Z_shiftr_pos; lia.
      - intros.
        destruct_match.
        ** apply H0. simpl in *. lia.
        ** apply IH.
           -- assumption.
           -- apply Z_shiftr_pos; lia.
           -- intros.
               destruct p0. apply H0. simpl in *. lia.
Qed.

Definition fromDistinctDescList_go_f : (Int -> Map e a -> list (e * a) -> Map e a) ->
 (Int -> Map e a -> list (e * a) -> Map e a).
Proof.
  let rhs := eval unfold fromDistinctDescList in (@fromDistinctDescList e a) in
  let rhs := eval fold fromDistinctDescList_create_f in rhs in 
  let rhs := eval fold fromDistinctDescList_create in rhs in 
  lazymatch rhs with context [deferredFix3 ?f] => exact f end.
Defined.

Definition fromDistinctDescList_go : Int -> Map e a -> list (e * a) -> Map e a
  := deferredFix3 (fromDistinctDescList_go_f).

Lemma fromDistinctDescList_go_eq:
  forall i s xs, (0 < i)%Z ->
  fromDistinctDescList_go i s xs = fromDistinctDescList_go_f fromDistinctDescList_go i s xs.
Proof.
  intros.
  change (deferredFix (fun g => uncurry (uncurry (fromDistinctDescList_go_f (curry (curry g))))) (i, s, xs) =
    uncurry (uncurry (fromDistinctDescList_go_f fromDistinctDescList_go)) (i, s, xs)).
  rewrite deferredFix_eq_on with
    (P := fun p => (1 <= fst (fst p))%Z)
    (R := fun x y => (length (snd x) < length (snd y))%nat); only 1: reflexivity.
  * apply well_founded_ltof with (f := fun x => length (snd x)).
  * intros g h p Px Heq.
    destruct p as [[x y] z].
    simpl in *.
    unfold fromDistinctDescList_go_f.
    destruct_match; try reflexivity.
    eapply fromDistinctDescList_create_preserves_length; try lia.
    intros s' ys Hlength. destruct p.
    apply Heq.
    + apply Z_shiftl_pos.
      lia.
    + simpl. lia.
  * simpl. lia.
Qed.

Program Fixpoint fromDistinctDescList_create_Desc
  sz ub xs x {measure (Z.to_nat sz)} :
  (0 <= sz)%Z ->
  StronglySorted (fun x y => gt x y) ((ub, x) :: xs) ->
  forall (P : (Map e a) * list (e * a) -> Prop),
  ( forall (s : Map e a) (ys: list (e * a)),
    Bounded s  (safeHd ys) (Some ub)->
    xs = rev(toList s) ++ ys ->
    ys = nil \/ size s = (2*2^sz-1)%Z ->
    P (s, ys)
  ) ->
  P (fromDistinctDescList_create (2^sz)%Z xs) := _.
Next Obligation.
  intros ????? Hnonneg HSorted.  
  rename fromDistinctDescList_create_Desc into IH.
  rewrite fromDistinctDescList_create_eq
    by (enough (0 < 2^sz)%Z by lia; apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctDescList_create_f.
  destruct xs.
  * intros X HX. apply HX. clear HX.
    - solve_Bounded.
    - reflexivity.
    - left. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.

    inversion HSorted. subst.
    inversion H2. subst. clear H2.
    inversion H1. subst.
    destruct p.
    assert (isLB (safeHd xs) e0 = true). {
      destruct xs; try reflexivity.
      inversion H5. subst. unfold safeHd. destruct p. unfold gt in H6.
      unfold isLB. order e. } 
    
    destruct (Z.eqb_spec (2^sz) 1).
    - intros X HX. apply HX. clear HX.
      ++ solve_Bounded. unfold gt in H3. unfold isUB. order e.
      ++ rewrite toList_Bin, toList_Tip, app_nil_r. reflexivity.
      ++ right. rewrite size_Bin. lia.
    - assert (~ (sz = 0))%Z by (intro; subst; simpl in n; congruence).
      assert (sz > 0)%Z by lia.
      replace ((Bits.shiftR (2 ^ sz)%Z 1%Z)) with (2^(sz - 1))%Z.
      Focus 2.
        unfold Bits.shiftR, Bits.instance_Bits_Int.
        rewrite Z.shiftr_div_pow2 by lia.
        rewrite Z.pow_sub_r by lia.
        reflexivity.
      assert (Z.to_nat (sz - 1) < Z.to_nat sz)%nat.
      { rewrite Z2Nat.inj_sub by lia. 
        apply Nat.sub_lt.
        apply Z2Nat.inj_le.
        lia.
        lia.
        lia.
        replace (Z.to_nat 1) with 1 by reflexivity.
        lia.
      }
      eapply IH.
      ++ assumption.
      ++ lia.
      ++ eassumption.
      ++ intros l ys HBounded_l Hlist_l Hsize_l.
         destruct ys.
         + intros X HX. apply HX. clear HX.
           ** solve_Bounded.
           ** assumption.
           ** left; reflexivity.
         + simpl in HBounded_l. destruct p.
           destruct Hsize_l; try congruence.
           eapply IH; clear IH.
           ** assumption.
           ** lia.
           ** rewrite Hlist_l in H1. 
              apply StronglySorted_app in H1.
              destruct H1. 
              eassumption.
           ** intros r zs HBounded_r Hlist_r Hsize_r.
              rewrite Hlist_l in HSorted.
              assert (isUB (Some ub) e1 = true). {
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                simpl.
                rewrite Forall_forall in H10. unfold gt in H10.
                specialize (H10 (e1, a1)). 
                assert (e1 < ub = true <-> ub > e1 = true) by (order e). rewrite H11.
                apply H10.
                apply in_or_app. right. left. reflexivity.
              }
              rewrite Hlist_r in HSorted.
              assert (isLB (safeHd zs) e1 = true). {
                destruct zs; try reflexivity.
                apply StronglySorted_inv in HSorted.
                destruct HSorted.
                apply StronglySorted_app in H10.
                destruct H10.
                apply StronglySorted_inv in H12.
                destruct H12.
                rewrite Forall_forall in H13. specialize (H13 p). unfold isLB. simpl. destruct p.
                unfold gt in H13. assert (e2 < e1 = true <-> e1 > e2 = true) by (order e).
                rewrite H14.
                apply H13.
                apply in_or_app. right. left. reflexivity.
              }
              intros X HX. apply HX. clear HX.
              -- applyDesc link_Desc.
              -- erewrite toList_link by eassumption.
                 rewrite Hlist_l. rewrite Hlist_r.
                 rewrite !rev_app_distr; simpl.
                 rewrite <- !app_assoc.  simpl. reflexivity.
              -- destruct Hsize_r; [left; assumption| right].
                 applyDesc link_Desc.
                 replace (size l). replace (size r).
                 rewrite mul_pow_sub in * by lia.
                 lia.
Qed.

(*If we look for an element in a map's list, it is the same as looking in the reverse of that list.
This is euivalent to saying that the first key, value pair that matches a given key is the same
as the last pair*)
Lemma sem_list_rev:
  forall m lb ub x,
  Bounded m lb ub ->
  sem_for_lists (toList m) x = sem_for_lists (rev (toList m)) x.
Proof.
  intros. generalize dependent x. induction H; intros.
  - simpl. reflexivity.
  - rewrite toList_Bin. rewrite rev_app_distr.
 simpl. rewrite <- app_assoc. simpl.
    rewrite sem_list_app. rewrite sem_list_app. rewrite <- IHBounded2.
    assert (forall {a} (x : a) l, x :: l = (x :: nil) ++ l). { intros.
    simpl. reflexivity. } rewrite H5. rewrite sem_list_app.
    rewrite (H5 _ _ (rev (toList s1))). rewrite sem_list_app.
    rewrite <- IHBounded1. repeat(erewrite <- toList_sem'').
    destruct (sem s1 x0) eqn : ?. simpl.
    assert (sem s2 x0 = None). { eapply sem_outside_below. apply H0. solve_Bounds. }
    rewrite H6. simpl. assert (x0 == x = false) by solve_Bounds. rewrite H7; reflexivity.
    simpl. destruct (x0 == x) eqn : ?. assert (sem s2 x0 = None). { eapply sem_outside_below.
    apply H0. solve_Bounds. } rewrite H6. reflexivity. simpl. rewrite oro_None_r. reflexivity.
    apply H0. apply H.
Qed.

Program Fixpoint fromDistinctDescList_go_Desc
  sz s xs {measure (length xs)} :
  (0 <= sz)%Z ->
  StronglySorted (fun x y => gt x y) xs ->
  Bounded s (safeHd xs) None  ->
  xs = nil \/ size s = (2*2^sz-1)%Z ->
  Desc (fromDistinctDescList_go (2^sz)%Z s xs) None None (size s + List.length xs)
    (fun i => sem s i ||| sem_for_lists xs i) := _. 
Next Obligation.
  intros.
  rename fromDistinctDescList_go_Desc into IH.
  rewrite fromDistinctDescList_go_eq by (apply Z.pow_pos_nonneg; lia).
  unfold fromDistinctDescList_go_f.
  destruct xs.
  * replace (List.length nil) with 0%Z by reflexivity.
    rewrite Z.add_0_r.
    solve_Desc.
  * repeat replace (#1) with 1%Z by reflexivity.
    replace ((Bits.shiftL (2 ^ sz)%Z 1))%Z with (2 ^ (1 + sz))%Z.
    Focus 2.
      unfold Bits.shiftL, Bits.instance_Bits_Int.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.pow_add_r by lia.
      lia. destruct p.

    destruct H2; try congruence.
    eapply fromDistinctDescList_create_Desc.
    - lia.
    - eassumption.
    - intros.
      subst.
      simpl safeHd in *.
      assert (isLB (safeHd ys) e0 = true). {
        destruct ys; try reflexivity.
        apply StronglySorted_inv in H0.
        destruct H0.
        rewrite Forall_forall in H4. specialize (H4 p). unfold isLB. destruct p. simpl.
        unfold gt in H4. assert (e1 < e0 = true <->e0 > e1 = true) by (order e). rewrite H6.
        apply H4. 
        apply in_or_app. right. left. reflexivity.
      }      
      applyDesc link_Desc.
      eapply IH.
      + simpl. rewrite app_length. lia.
      + lia.
      + apply StronglySorted_inv in H0.
        destruct H0.
        apply StronglySorted_app in H0.
        destruct H0.
        assumption.
      + assumption.
      + destruct H5; [left; assumption | right].
        replace (size s1). replace (size s).  replace (size s0).
        rewrite Z.pow_add_r by lia.
        lia.
      + intros.
        solve_Desc.
        ** replace (size s2). replace (size s1). replace (size s).
           rewrite !List.hs_coq_list_length, !Zlength_correct.
           simpl length.
           rewrite app_length, Nat2Z.inj_succ, Nat2Z.inj_add, rev_length.
           erewrite <- size_spec by eassumption.
           lia.
        ** simpl. setoid_rewrite sem_list_app. 
            assert (forall i, sem_for_lists (rev (toList s0)) i = sem_for_lists (toList s0) i).
            setoid_rewrite (sem_list_rev s0 (safeHd ys) (Some e0) _ H3). intros. reflexivity. 
            setoid_rewrite H9.
            setoid_rewrite <- toList_sem''; only 2: eassumption.
            f_solver.
Qed.



Lemma fromDistinctDescList_Desc:
  forall xs,
  StronglySorted (fun x y => gt x y) xs ->
  Desc (fromDistinctDescList xs) None None (List.length xs) (fun i => sem_for_lists xs i).
Proof.
  intros.
  unfold fromDistinctDescList.
  fold fromDistinctDescList_create_f.
  fold fromDistinctDescList_create.
  fold fromDistinctDescList_go_f.
  fold fromDistinctDescList_go.
  destruct xs.
  * solve_Desc.
  * replace (#1) with (2^0)%Z by reflexivity. destruct p.
    eapply fromDistinctDescList_go_Desc.
    + lia.
    + apply StronglySorted_inv in H.
      destruct H.
      assumption.
    + assert (isLB (safeHd xs) e0 = true). {
        destruct xs; try reflexivity.
        apply StronglySorted_inv in H.
        destruct H.
        rewrite Forall_forall in H0. destruct p. unfold isLB. simpl.
        unfold gt in H0. specialize (H0 (e1, a1)). 
        assert (e1 < e0 = true <-> e0 > e1 = true) by (order e). rewrite H1.
        apply H0.
        left. reflexivity.
      }
      solve_Bounded.
    + right. reflexivity.
    + intros.
      rewrite List.hs_coq_list_length, Zlength_cons in *.
      rewrite size_Bin in *.
      solve_Desc. simpl. f_solver.
Qed.

(** ** Verification of [combineEq] *)

(*Since [combineEq'] and [combineEq] are defined inside [fromAscList] (unlike in Data.Set), we define them here
and then prove equivalence*)

Fixpoint combineEq' {e} {a} `{EqLaws e} (x : e * a) (l : list (e * a) ) :=
  match x, l with
  |z, nil => z :: nil
  |(a, b), (c, d) :: t => if a == c then combineEq' (c, d) t else (a,b) :: combineEq' (c,d) t
  end.

(*The combineEq' from Data.Map (defined here to make combineEq'_equiv nicer*)
Definition old_combineEq' :=(fix combineEq' (arg_0__ : e * a) (arg_1__ : list (e * a)) {struct arg_1__} : list (e * a) :=
   let (kz, _) := arg_0__ in
   match arg_1__ with
   | nil => arg_0__ :: nil
   | (kx, xx) as x :: xs' => if _GHC.Base.==_ kx kz then combineEq' (kx, xx) xs' else arg_0__ :: combineEq' x xs'
   end).

Definition combineEq {e} {a} `{EqLaws e} (l : list (e * a)) :=
  match l with
  | nil => nil
  | x :: nil => x :: nil
  | x :: t => combineEq' x t
  end.

Lemma combineEq'_equiv:
  forall l x, combineEq' x l = old_combineEq' x l.
Proof.
  intros. revert x. induction l; intros.
  - simpl. destruct x. reflexivity.
  - simpl. destruct x. destruct a0. destruct (e0 == e1) eqn : ?.
    assert (e1 == e0 = true) by (order e). rewrite H. apply IHl.
    assert (e1 == e0 = false) by (order e). rewrite H. rewrite IHl.
    reflexivity.
Qed.


Definition fromAscList' (l : list (e * a)) :=
  fromDistinctAscList (combineEq l).


Lemma fromAscList_equiv: forall (l : list (e * a)),
  fromAscList' l = fromAscList l.
Proof.
  intros l. unfold fromAscList', fromAscList. destruct l.
  - simpl. reflexivity.
  -  unfold combineEq. rewrite combineEq'_equiv. unfold old_combineEq'.
     reflexivity.
Qed.

Definition fromDescList' (l : list (e * a)) :=
  fromDistinctDescList (combineEq l).

Lemma fromDescList_equiv: forall (l : list (e * a)),
  fromDescList' l = fromDescList l.
Proof.
  intros l. unfold fromDescList', fromDescList. destruct l.
  - simpl. reflexivity.
  -  unfold combineEq. rewrite combineEq'_equiv. unfold old_combineEq'.
     reflexivity.
Qed.

Definition combineEqGo : (e * a) -> list (e * a) -> list (e * a).
Proof.
  intros.
 apply (@combineEq' e a HEq HEqLaws). apply X.  apply X0.
Defined.

(* Too much duplication here *)

(*See if a key is a (key, value) list*)
Fixpoint key_elem (l : list (e * a)) i :=
  match l with
  | nil => false
  | (x, y) :: t => (x == i) || key_elem t i
  end.

(*This finds the last value associated with a key in a list*)
Fixpoint last_value (l : list (e * a)) i:=
  match l with
  | nil => None
  | (x, y) :: t => if (x == i) then match last_value t i with
                               | None => Some y
                               | Some z => Some z
                               end else last_value t i
  end. 

(*This proves that the last_value does in fact find the last value, since it finds
the first value in the reversed list. It also justifies using either
[sem_for_lists (rev l)] or [last_value l] based on which is more convienent. For 
[combineEq] and [fromDescList] (and similar), I use [last_value l], and in
from_list, I use [sem_for_lists (rev l)]*)
Lemma last_sem_equiv: forall l x,
  sem_for_lists (rev l) x = last_value l x.
Proof.
  intros. revert x; induction l; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. rewrite sem_list_app. rewrite IHl.
    simpl. destruct (e0 == x) eqn : ?. assert (x == e0 = true) by (order e).
    rewrite H. destruct (last_value l x) eqn : ?. simpl. reflexivity. simpl. reflexivity.
    assert (x == e0 = false) by (order e). rewrite H. rewrite oro_None_r. reflexivity.
Qed. 

(*An element has a last occurrence iff it is in the list*)
Lemma last_iff_elem: forall l i,
  (exists v, last_value l i = Some v) <-> key_elem l i = true.
Proof.
  intros. revert  i. induction l; split; intros.
  - simpl in H. inversion H. inversion H0.
  - simpl in H. inversion H. 
  - simpl. destruct a0.  simpl in H. destruct (e0 == i) eqn : ?.
    simpl. reflexivity. simpl. eapply IHl. apply H.
  - simpl. destruct a0. simpl in H. destruct (e0  == i) eqn : ?.
    destruct (last_value l i) eqn : ?. exists a1. reflexivity.
    exists a0. reflexivity. simpl in H. apply IHl. apply H.
Qed.

Local Definition le : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 <= e2) = true.
  
Lemma Forall_le_elem:
  forall x x0 xs,
  Forall (fun y => le (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x <= i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0. 
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold le in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold le. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_le_last:
  forall x x0 xs,
  Forall (fun y => le (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x <= i = true).
Proof.
  intros.
  rewrite Forall_le_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed. 


Local Definition ge : e * a -> e * a -> Prop
  := fun x1 x2 => let (e1, a1) := x1 in let (e2, a2) := x2 in (e1 >= e2) = true.

Lemma Forall_ge_elem:
  forall x x0 xs,
  Forall (fun y => ge (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x >= i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0. 
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold ge in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold ge. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_ge_last:
  forall x x0 xs,
  Forall (fun y => ge (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x >= i = true).
Proof.
  intros.
  rewrite Forall_ge_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed. 

Lemma Forall_lt_elem:
  forall x x0 xs,
  Forall (fun y => lt (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x < i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0. 
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold lt in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold lt. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_lt_last:
  forall x x0 xs,
  Forall (fun y => lt (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x < i = true).
Proof.
  intros.
  rewrite Forall_lt_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed. 


Lemma Forall_gt_elem:
  forall x x0 xs,
  Forall (fun y => gt (x, x0) y) xs <-> (forall i, key_elem xs i = true -> x > i = true).
Proof.
  intros.
  induction xs.
  * split; intro H.
    - intros i Hi; simpl in Hi; congruence.
    - constructor.
  * split; intro H.
    - inversion H; subst; clear H.
      rewrite IHxs in H3; clear IHxs.
      intros i Hi; simpl in Hi. destruct a0. 
      rewrite orb_true_iff in Hi. destruct Hi.
      + unfold gt in *.  order e.
      + apply H3; assumption.
    - constructor.
      + unfold gt. destruct a0. apply H. simpl. rewrite Eq_Reflexive. simpl. reflexivity.
      + rewrite IHxs; clear IHxs.
        intros i Hi. apply H. simpl. rewrite Hi. destruct a0.  apply orb_true_r.
Qed.

Lemma Forall_gt_last:
  forall x x0 xs,
  Forall (fun y => gt (x, x0) y) xs <-> (forall i v, last_value xs i = Some v -> x > i = true).
Proof.
  intros.
  rewrite Forall_gt_elem. split; intros.
  - apply H. apply last_iff_elem. exists v. assumption.
  - apply last_iff_elem in H0. destruct H0. apply H in H0. assumption.
Qed. 


(*Note: This is significatly different than SetProofs. It is not enough that the keys are preserved,
we must show that each key is matched with its last value in the list*)
Lemma combineEqGo_spec:
  forall x xs,
  StronglySorted (fun x y => le x y) (x :: xs) ->
  forall P : list (e * a) -> Prop,
  (forall (ys: list (e * a)),
     StronglySorted (fun x y => lt x y) ys ->
     (forall i, last_value ys i = last_value (x :: xs) i) ->
     P ys) ->
  P (combineEqGo x xs).
Proof.
  intros x xs Hsorted.
  inversion Hsorted; subst; clear Hsorted.
  revert x H2.
  induction H1; intros x Hlt.
  * intros X HX; apply HX; clear X HX.
    + unfold lt. unfold le in Hlt. unfold combineEqGo. simpl. destruct x.
      constructor; constructor.
    + intro. unfold combineEqGo. simpl. destruct x. simpl. reflexivity.
  * inversion Hlt; subst; clear Hlt.  
    simpl. unfold combineEqGo in *. simpl in *. destruct a0. destruct x.
    destruct_match.
    + eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - assumption.
      - intro i. rewrite Hiys. simpl. 
        destruct (e0 == i) eqn:?, (e1 == i) eqn:?. destruct (last_value l i) eqn : ?.
        reflexivity. reflexivity. reflexivity. order e. reflexivity.
    + assert (Hlt : e1 < e0 = true) by (unfold le in H3; order e). clear H3 Heq.
      eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - constructor.
        ** eapply StronglySorted_R_ext; only 2: apply Hsortedys.
           intros. simpl. order e.
        ** apply Forall_lt_last.
           rewrite Forall_le_last in H.
           intros i v Hi. rewrite Hiys in Hi.  simpl in Hi. unfold lt.
           destruct (e0 == i) eqn : ?. order e. apply H in Hi. unfold le in Hi. order e.
      - intro i. simpl. rewrite Hiys. simpl. reflexivity.
Qed.

Lemma combineEqGo_spec2:
  forall x xs,
  StronglySorted (fun x y => ge x y) (x :: xs) ->
  forall P : list (e * a) -> Prop,
  (forall (ys: list (e * a)),
     StronglySorted (fun x y => gt x y) ys ->
     (forall i, last_value ys i = last_value (x :: xs) i) ->
     P ys) ->
  P (combineEqGo x xs).
Proof.
  intros x xs Hsorted.
  inversion Hsorted; subst; clear Hsorted.
  revert x H2.
  induction H1; intros x Hlt.
  * intros X HX; apply HX; clear X HX.
    + unfold lt. unfold ge in Hlt. unfold combineEqGo. simpl. destruct x.
      constructor; constructor.
    + intro. unfold combineEqGo. simpl. destruct x.  simpl. reflexivity.
  * inversion Hlt; subst; clear Hlt.  
    simpl. unfold combineEqGo in *. simpl in *. destruct a0. destruct x.
    destruct_match.
    + eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - assumption.
      - intro i. rewrite Hiys. simpl. 
        destruct (e0 == i) eqn:?, (e1 == i) eqn:?. destruct (last_value l i) eqn : ?.
        reflexivity. reflexivity. reflexivity. order e. reflexivity.
    + assert (Hlt : e1 > e0 = true) by (unfold ge in H3; order e). clear H3 Heq.
      eapply IHStronglySorted; only 1: assumption; intros ys Hsortedys Hiys.
      intros X HX; apply HX; clear X HX.
      - constructor.
        ** eapply StronglySorted_R_ext; only 2: apply Hsortedys.
           intros. simpl. order e.
        ** apply Forall_gt_last.
           rewrite Forall_ge_last in H.
           intros i v Hi. rewrite Hiys in Hi.  simpl in Hi. unfold lt.
           destruct (e0 == i) eqn : ?. order e. apply H in Hi. unfold ge in Hi. order e.
      - intro i. simpl. rewrite Hiys. simpl. reflexivity.
Qed.

Lemma combineEq_spec:
  forall xs,
  StronglySorted (fun x y => le x  y) xs ->
  forall P : list (e * a) -> Prop,
  (forall ys,
     StronglySorted (fun x y => lt x y) ys ->
     (forall i, last_value ys i = last_value xs i) ->
     P ys) ->
  P (combineEq xs).
Proof.
  intros xs Hsorted.
  inversion Hsorted.
  * intros X HX. apply HX. clear X HX.
    - constructor.
    - intro. reflexivity.
  * rewrite <- H1 in Hsorted. clear xs H0 H1.
    assert (combineEq (a0 :: l) = combineEqGo a0 l). {
    unfold combineEqGo. simpl. destruct l. simpl. destruct a0. reflexivity.
    reflexivity. } rewrite H0.
    apply combineEqGo_spec. assumption.
Qed.

Lemma combineEq_spec2:
  forall xs,
  StronglySorted (fun x y => ge x  y) xs ->
  forall P : list (e * a) -> Prop,
  (forall ys,
     StronglySorted (fun x y => gt x y) ys ->
     (forall i, last_value ys i = last_value xs i) ->
     P ys) ->
  P (combineEq xs).
Proof.
  intros xs Hsorted.
  inversion Hsorted.
  * intros X HX. apply HX. clear X HX.
    - constructor.
    - intro. reflexivity.
  * rewrite <- H1 in Hsorted. clear xs H0 H1.
    assert (combineEq (a0 :: l) = combineEqGo a0 l). {
    unfold combineEqGo. simpl. destruct l. simpl. destruct a0. reflexivity.
    reflexivity. } rewrite H0.
    apply combineEqGo_spec2. assumption.
Qed.


(** ** Verification of [fromAscList] *)

(*See whether a key, value pair is in a list, comparing the keys with Haskell equality
and the values with Coq equality. This will be used in place of List.In in the following
analogues of [Forall_forall]*)
Fixpoint weak_In (l : list (e * a)) (x : e * a) :=
  match l with
  | nil => False
  | (a,b) :: t => let (x0, y0) := x in (a == x0 = true) /\ b = y0 \/ weak_In t x
  end.

Lemma Forall_forall_lt: 
  forall  (l : list (e * a)) t, Forall (lt t) l <-> (forall x, weak_In l x -> lt t x).
Proof.
  intros. split; intros; induction l; intros.
  - simpl in H0. destruct H0.
  - simpl in H0. destruct a0. destruct x. destruct H0. inversion H; subst.
    destruct H0. subst. destruct t. unfold lt in *. order e.
  - apply IHl. inversion H; subst. assumption. apply H0.
  - apply Forall_nil.
  - apply Forall_cons. simpl in H. destruct a0. apply H. left.
    split. apply Eq_Reflexive. reflexivity. simpl in H.
    destruct a0. apply IHl. intros. apply H. destruct x. right. assumption.
Qed.

Lemma Forall_forall_gt: 
  forall  (l : list (e * a)) t, Forall (gt t) l <-> (forall x, weak_In l x -> gt t x).
Proof.
  intros. split; intros; induction l; intros.
  - simpl in H0. destruct H0.
  - simpl in H0. destruct a0. destruct x. destruct H0. inversion H; subst.
    destruct H0. subst. destruct t. unfold gt in *. order e.
  - apply IHl. inversion H; subst. assumption. apply H0.
  - apply Forall_nil.
  - apply Forall_cons. simpl in H. destruct a0. apply H. left.
    split. apply Eq_Reflexive. reflexivity. simpl in H.
    destruct a0. apply IHl. intros. apply H. destruct x. right. assumption.
Qed.

Lemma strongly_sorted_in_sem_lt: forall l x v,
  StronglySorted lt l ->
  sem_for_lists l x = Some v <-> weak_In l (x,v).
Proof.
  intros; revert x v; induction l; intros; split; intros.
  - inversion H0.
  - destruct H0.
  - simpl. simpl in H0. destruct a0. destruct (x == e0) eqn : ?.
    left. split. order e. inversion H0; subst; reflexivity.
    right. apply IHl. inversion H; subst; assumption. apply H0.
  - simpl in H0. simpl. destruct a0.
    destruct H0. destruct H0. subst. assert (x == e0 = true) by (order e).
    rewrite H1. reflexivity. inversion H; subst.
    rewrite Forall_forall_lt in H4. assert (A:=H0). apply H4 in H0. unfold lt in H0.
    assert (x == e0 = false) by (order e). rewrite H1. apply IHl. apply H3. apply A.
Qed.

Lemma strongly_sorted_in_sem_gt: forall l x v,
  StronglySorted gt l ->
  sem_for_lists l x = Some v <-> weak_In l (x,v).
Proof.
  intros; revert x v; induction l; intros; split; intros.
  - inversion H0.
  - destruct H0.
  - simpl. simpl in H0. destruct a0. destruct (x == e0) eqn : ?.
    left. split. order e. inversion H0; subst; reflexivity.
    right. apply IHl. inversion H; subst; assumption. apply H0.
  - simpl in H0. simpl. destruct a0.
    destruct H0. destruct H0. subst. assert (x == e0 = true) by (order e).
    rewrite H1. reflexivity. inversion H; subst.
    rewrite Forall_forall_gt in H4. assert (A:=H0). apply H4 in H0. unfold gt in H0.
    assert (x == e0 = false) by (order e). rewrite H1. apply IHl. apply H3. apply A.
Qed.

Lemma strongly_sorted_last_lt:
  forall l x,
  StronglySorted lt l ->
  last_value l x = sem_for_lists l x.
Proof.
  intros. revert x. induction H; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. destruct (x == e0) eqn : ?.
    rewrite Forall_forall_lt in H0.
    rewrite IHStronglySorted.
    destruct (sem_for_lists l x) eqn : ?. 
    + rewrite strongly_sorted_in_sem_lt in Heqo. apply H0 in Heqo.
      unfold lt in Heqo. order e. apply H. destruct (e0 == x) eqn : ?. reflexivity.
    order e. assert (e0 == x = false) by (order e). rewrite H1. apply IHStronglySorted.
Qed.

Lemma strongly_sorted_last_gt:
  forall l x,
  StronglySorted gt l ->
  last_value l x = sem_for_lists l x.
Proof.
  intros. revert x. induction H; intros.
  - simpl. reflexivity.
  - simpl. destruct a0. destruct (x == e0) eqn : ?.
    rewrite Forall_forall_gt in H0.
    rewrite IHStronglySorted.
    destruct (sem_for_lists l x) eqn : ?. 
    + rewrite strongly_sorted_in_sem_gt in Heqo. apply H0 in Heqo.
      unfold gt in Heqo. order e. apply H. destruct (e0 == x) eqn : ?. reflexivity.
    order e. assert (e0 == x = false) by (order e). rewrite H1. apply IHStronglySorted.
Qed.


Lemma fromAscList_Desc:
  forall xs,
  StronglySorted (fun x y => le x y) xs ->
  Desc' (fromAscList xs) None None (fun i => last_value xs i).
Proof.
  intros. rewrite <- fromAscList_equiv. unfold fromAscList'.
  eapply combineEq_spec; only 1: assumption; intros ys HSorted Helem.
  apply fromDistinctAscList_Desc; only 1: assumption.
  intros s HB Hsz Hf.
  solve_Desc. intros. rewrite <- Helem. rewrite strongly_sorted_last_lt.
  apply Hf. apply HSorted.
Qed.

(** ** Verification of [fromDescList] *)

Lemma fromDescList_Desc:
  forall xs,
  StronglySorted (fun x y => ge x y) xs ->
  Desc' (fromDescList xs) None None (fun i => last_value xs i).
Proof.
  intros. rewrite <- fromDescList_equiv. unfold fromDescList'.
  unfold fromDescList.
  eapply combineEq_spec2;  only 1: assumption; intros ys HSorted Helem.
  apply fromDistinctDescList_Desc; only 1: assumption.
  intros s HB Hsz Hf.
  solve_Desc. intros. rewrite <- Helem. rewrite strongly_sorted_last_gt.
  apply Hf. apply HSorted.
Qed.

(** ** Verification of [fromList] *)

(** The verification of [fromList] should be similar to that of [fromDistinctAscList], only
that the condition is checked and -- if it fails -- we resort to a backup implementation. *)

(* The following definitions are copied from the local definitions of [fromList]; 
   my ltac foo failed to do that automatic.
*)

Definition fromList' :=
          fun (t0: Map e a) (xs: list (e * a)) =>
            let ins :=
              fun arg_2__ arg_3__ =>
                match arg_2__, arg_3__ with
                | t, pair k x => insert k x t
                end in
            Data.Foldable.foldl' ins t0 xs.

Definition not_ordered :=
          fun (arg_7__ : e) (arg_8__: list (e * a)) =>
            match arg_7__, arg_8__ with
            | _, nil => false
            | kx, cons (pair ky _) _ => kx GHC.Base.>= ky
            end .

Definition fromList_create_f : (Int -> list (e * a) -> Map e a * list (e * a) * list (e * a)) -> 
(Int -> list (e * a) -> Map e a * list (e * a)  * list (e * a))
  := (fun create arg_11__ arg_12__ =>
      match arg_11__, arg_12__ with
      | _, nil => pair (pair Tip nil) nil
      | s, (cons xp xss as xs) =>
       if s GHC.Base.== #1 : bool
       then let 'pair kx x := xp in
         if not_ordered kx xss : bool
         then pair (pair (Bin #1 kx x Tip Tip) nil) xss else
         pair (pair (Bin #1 kx x Tip Tip) xss) nil else
         match create (Data.Bits.shiftR s #1) xs with
         | (pair (pair _ nil) _ as res) => res
         | pair (pair l (cons (pair ky y) nil)) zs =>
              pair (pair (insertMax ky y l) nil) zs
         | pair (pair l (cons (pair ky y) yss as ys)) _ =>
             if not_ordered ky yss : bool then pair (pair l nil) ys else
             let 'pair (pair r zs) ws := create (Data.Bits.shiftR s #1) yss in
                       pair (pair (link ky y l r) zs) ws
         end
       end).

Definition fromList_create : Int -> list (e * a) -> Map e a * list (e * a) * list (e * a)
  := deferredFix2 (fromList_create_f).

Definition fromList_go_f :=
  (fun (go: Int -> Map e a -> list (e * a) -> Map e a) (arg_28__ : Int)
   (arg_29__ : Map e a) (arg_30__: list (e * a)) =>
    match arg_28__, arg_29__, arg_30__ with
    | _, t, nil => t
    | _, t, cons (pair kx x) nil => insertMax kx x t
    | s, l, (cons (pair kx x) xss as xs) =>
          if not_ordered kx xss : bool then fromList' l xs else
          match fromList_create s xss with
          | pair (pair r ys) nil => go (Data.Bits.shiftL s #1) (link kx x l r) ys
          | pair (pair r _) ys => fromList' (link kx x l r) ys
          end
   end).

Definition fromList_go := deferredFix3 (fromList_go_f).

(** zeta-reduces exactly one (the outermost) [let] *)
Ltac zeta_one :=
  lazymatch goal with |- context A [let x := ?rhs in @?body x] =>
     let e' := eval cbv beta in (body rhs) in
     let e'' := context A [e'] in
     change e''
  end.

(* Identical to [fromDistinctAscList_create_eq] *)
Lemma fromList_create_eq:
  forall i xs, (1 <= i)%Z ->
  fromList_create i xs = fromList_create_f fromList_create i xs.
Proof.
  intros.
  change (uncurry fromList_create (i, xs) = uncurry (fromList_create_f fromList_create) (i, xs)).
  apply deferredFix_eq_on with
    (f := fun g => uncurry (fromList_create_f (curry g)))
    (P := fun p => (1 <= fst p)%Z)
    (R := fun x y => (1 <= fst x < fst y)%Z).
  * eapply wf_inverse_image with (R := fun x y => (1 <= x < y)%Z).
    apply Z.lt_wf with (z := 1%Z).
  * clear i xs H.
    intros g h x Px Heq.
    destruct x as [i xs]. simpl in *.
    unfold fromList_create_f.
    destruct_match; try reflexivity.
    repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1); try reflexivity.
    unfold curry.
    assert (1 < i)%Z by lia.
    assert (1 <= Z.shiftr i 1)%Z by (apply Z_shiftr_pos; lia).
    assert (Z.shiftr i 1 < i)%Z by (apply Z_shiftr_lt; lia).
    repeat expand_pairs. simpl.
    rewrite Heq by eauto.
    destruct_match; try reflexivity.
    rewrite Heq by eauto.
    reflexivity.
  * simpl; lia.
Qed.

(* We need to know that [create] returns no longer list than it receives.
   Like [fromDistinctAscList_create_preserves_length], just a few more cases.
 *)
Program Fixpoint fromList_create_preserves_length
  i xs {measure (Z.to_nat i)} :
  (1 <= i)%Z ->
  forall (P : Map e a * list (e * a) * list (e * a) -> Prop),
  ( forall s ys zs ,
    (length ys <= length xs)%nat ->
    P (s, ys, zs)
  ) ->
  P (fromList_create i xs) := _.
Next Obligation.
  intros.
  rename fromList_create_preserves_length into IH.
  rewrite fromList_create_eq by assumption.
  unfold fromList_create_f.
  destruct xs.
  * apply H0. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    destruct (Z.eqb_spec i 1).
    + destruct p. destruct_match.
      - apply H0. simpl. lia.
      - apply H0. simpl. lia.
    + assert (Z.to_nat (Bits.shiftR i #1) < Z.to_nat i)%nat. {
        apply Z2Nat.inj_lt.
        apply Z.shiftr_nonneg. lia.
        lia.
        apply Z_shiftr_lt; lia.
      }
      apply IH.
      - assumption. 
      - apply Z_shiftr_pos; lia.
      - intros.
        destruct_match.
        ** apply H0. simpl in *. lia.
        ** apply IH.
           -- assumption.
           -- apply Z_shiftr_pos; lia.
           -- intros.
              repeat destruct_match.
              ++ apply H0. simpl in *. lia.
              ++ apply H0. simpl in *. lia.
              ++ apply H0. simpl in *. lia.
Qed.

Lemma fromList_go_eq:
  forall i s xs, (0 < i)%Z ->
  fromList_go i s xs = fromList_go_f fromList_go i s xs.
Proof.
  intros.
  change (deferredFix (fun g => uncurry (uncurry (fromList_go_f (curry (curry g))))) (i, s, xs) =
    uncurry (uncurry (fromList_go_f fromList_go)) (i, s, xs)).
  rewrite deferredFix_eq_on with
    (P := fun p => (1 <= fst (fst p))%Z)
    (R := fun x y => (length (snd x) < length (snd y))%nat); only 1: reflexivity.
  * apply well_founded_ltof with (f := fun x => length (snd x)).
  * intros g h p Px Heq.
    destruct p as [[x y] z].
    simpl in *.
    unfold fromList_go_f.
    destruct_match; try reflexivity.
    eapply fromList_create_preserves_length; try lia.
    intros s' ys zs Hlength.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    destruct_match; try reflexivity.
    apply Heq.
    + apply Z_shiftl_pos.
      lia.
    + simpl. simpl in *. lia.
  * simpl. lia.
Qed.

Program Fixpoint fromList_create_Desc
  sz lb xs {measure (Z.to_nat sz)} :
  (0 <= sz)%Z ->
  not_ordered lb xs = false ->
(*   StronglySorted (fun x y => x < y = true) (lb :: xs) -> *)
  forall (P : Map e a * list (e * a) * list (e * a) -> Prop),
  ( forall s ys zs,
    Bounded s (Some lb) (safeHd ys) ->
    isUB (safeHd ys) lb = true ->
    xs = toList s ++ ys ++ zs->
    ys = nil \/ (size s = (2*2^sz-1)%Z /\ zs = nil) ->
    P (s, ys, zs)
  ) ->
  P (fromList_create (2^sz)%Z xs) := _.
Next Obligation.
  intros ???? Hnonneg HheadOrdered.
  rename fromList_create_Desc into IH.
  rewrite fromList_create_eq
    by (enough (0 < 2^sz)%Z by lia; apply Z.pow_pos_nonneg; lia).
  unfold fromList_create_f.
  destruct xs.
  * intros X HX. apply HX. clear HX.
    - solve_Bounded.
    - reflexivity.
    - reflexivity.
    - left. reflexivity.
  * repeat replace (#1) with 1%Z by reflexivity.
    unfold op_zeze__, Eq_Integer___, op_zeze____.
    
    simpl in HheadOrdered. destruct p.

(*     assert (isUB (safeHd xs) e0 = true). {
      destruct xs; try reflexivity.
      inversion H5. assumption.
    } *)

    destruct (Z.eqb_spec (2^sz) 1); [ destruct_match | ].
    - intros X HX. apply HX; clear HX.
      ++ solve_Bounded.
      ++ reflexivity.
      ++ rewrite toList_Bin, toList_Tip, app_nil_r. reflexivity.
      ++ left. reflexivity.
    - intros X HX. apply HX; clear HX.
      ++ destruct xs; simpl in Heq;  solve_Bounded. destruct p. unfold safeHd. unfold isUB. order e.
      ++ destruct xs; simpl in *; solve_Bounds. destruct p. solve_Bounds.
      ++ rewrite toList_Bin, toList_Tip, !app_nil_r, !app_nil_l. reflexivity.
      ++ right. split. rewrite size_Bin. lia. reflexivity.
    - assert (~ (sz = 0))%Z by (intro; subst; simpl in n; congruence).
      assert (sz > 0)%Z by lia.
      replace ((Bits.shiftR (2 ^ sz)%Z 1%Z)) with (2^(sz - 1))%Z.
      Focus 2.
        unfold Bits.shiftR, Bits.instance_Bits_Int.
        rewrite Z.shiftr_div_pow2 by lia.
        rewrite Z.pow_sub_r by lia.
        reflexivity.
      assert (Z.to_nat (sz - 1) < Z.to_nat sz)%nat.
      { rewrite Z2Nat.inj_sub by lia. 
        apply Nat.sub_lt.
        apply Z2Nat.inj_le.
        lia.
        lia.
        lia.
        replace (Z.to_nat 1) with 1 by reflexivity.
        lia.
      }
      eapply IH.
      ++ assumption.
      ++ lia.
      ++ eassumption.
      ++ intros l ys zs HBounded_l HisUB_l Hlist_l Hsize_l.
         destruct ys.
         + intros X HX. apply HX. clear HX.
           ** solve_Bounded.
           ** assumption.
           ** assumption.
           ** left; reflexivity.
         + simpl in HBounded_l.
           destruct Hsize_l as [? | [??]]; try congruence.
           subst. rewrite app_nil_r in Hlist_l. destruct p.
           assert (isLB (Some lb) e1 = true) by solve_Bounds.
           destruct ys; only 2: destruct_match.
           -- intros X HX. apply HX; clear HX.
              ** assert (isUB None e1 = true) by reflexivity.
                 applyDesc insertMax_Desc.
              ** reflexivity.
              ** erewrite toList_insertMax by eassumption.
                 rewrite app_nil_l, <- app_assoc.
                 assumption.
              ** left; reflexivity.
           -- intros X HX. apply HX; clear HX.
              ** solve_Bounded.
              ** reflexivity.
              ** rewrite app_nil_l. simpl in Hlist_l.
                 assumption.
              ** left; reflexivity.
           -- eapply IH; clear IH.
              ** assumption.
              ** lia.
              ** eassumption.
              ** simpl in Heq.
                 intros r zs zs' HBounded_r HisUB_r Hlist_r Hsize_r.
                 intros X HX. apply HX. clear HX.
                 --- applyDesc link_Desc.
                 --- solve_Bounds.
                 --- erewrite toList_link by eassumption.
                     rewrite Hlist_l. rewrite Hlist_r.
                     rewrite <- !app_assoc.  reflexivity.
                 --- destruct Hsize_r; [left; assumption| right].
                     destruct H4.
                     split; only 2: assumption.
                     applyDesc link_Desc.
                     replace (size l). rewrite H4.
                     rewrite mul_pow_sub in * by lia.
                     lia.
Qed.

Lemma foldl_foldl' : forall {b} f (x : b) (l: list (e * a)),
  Foldable.foldl f x l = Foldable.foldl' f x l.
Proof.
  intros.  unfold Foldable.foldl, Foldable.foldl'; unfold Foldable.Foldable__list;
    unfold  Foldable.foldl__ , Foldable.foldl'__ ; 
    unfold Foldable.Foldable__list_foldl', Foldable.Foldable__list_foldl;
    unfold Base.foldl, Base.foldl'. reflexivity.
Qed.

Definition fromList'' :=
          fun (t0: Map e a) (xs: list (e * a)) =>
            let ins :=
              fun arg_2__ arg_3__ =>
                match arg_2__, arg_3__ with
                | t, pair k x => insert k x t
                end in
            Data.Foldable.foldl ins t0 xs.


Lemma fromList'_fromList'': forall m l,
  fromList' m l = fromList'' m l.
Proof.
  intros. unfold fromList'. unfold fromList''. rewrite <- (foldl_foldl' _ m l). reflexivity.
Qed.

Lemma fromList'_Desc:
  forall s l,
  Bounded s None None ->
  Desc' (fromList' s l) None None (fun i => sem_for_lists (rev l) i ||| sem s i).
Proof.
  intros. rewrite fromList'_fromList''.
  unfold fromList''.
  rewrite Foldable.hs_coq_foldl_list.
  revert s H.
  induction l.
  * intros.
    simpl.
    solve_Desc.
  * intros.
    simpl. destruct a0.
    applyDesc insert_Desc.
    applyDesc IHl.
    solve_Desc. f_solver; rewrite sem_list_app in Heqo0.
    + rewrite Heqo1 in Heqo0. inversion Heqo0. reflexivity.
    + rewrite Heqo1 in Heqo0. inversion Heqo0. reflexivity.
    + rewrite Heqo1 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. rewrite Hsem in Hsem0.
      rewrite Hsem0 in Heqo0. assumption.
    + rewrite Heqo1 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. inversion Heqo0.
    + rewrite Heqo2 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
    + rewrite Heqo1 in Heqo0. simpl in Heqo0. rewrite Heqb in Heqo0. inversion Heqo0.
Qed. 

(*In a well formed map, we can only find each key once in the list, so it doesn't matter
if we look in the list or the reverse list*)
Lemma sem_toList_reverse: forall m lb ub i,
  Bounded m lb ub ->
  sem_for_lists (rev (toList m)) i = sem_for_lists (toList m) i.
Proof.
  intros. revert i. induction H; intros.
  - simpl. reflexivity.
  - rewrite toList_Bin. rewrite rev_app_distr. rewrite sem_list_app.
    rewrite sem_list_app. simpl. rewrite sem_list_app. 
    rewrite IHBounded2. simpl. rewrite IHBounded1. repeat (erewrite <- toList_sem'').
    destruct (sem s2 i) eqn : ?. assert (sem s1 i = None). { eapply sem_outside_above.
    apply H. unfold isUB. apply (sem_inside H0) in Heqo. destruct Heqo. order_Bounds. }
    rewrite H5. simpl. assert (i == x = false) by solve_Bounds. rewrite H6. reflexivity.
    simpl. destruct (i == x) eqn : ?. assert (sem s1 i = None). { eapply sem_outside_above.
    apply H. unfold isUB. order_Bounds. } rewrite H5. simpl. reflexivity. simpl.
    rewrite oro_None_r. reflexivity. apply H. apply H0.
Qed.


Program Fixpoint fromList_go_Desc
  sz s xs {measure (length xs)} :
  (0 <= sz)%Z ->
  Bounded s None (safeHd xs) ->
  xs = nil \/ size s = (2*2^sz-1)%Z ->
  Desc' (fromList_go (2^sz)%Z s xs) None None
    (fun i => sem_for_lists (rev xs) i ||| sem s i) := _.
Next Obligation.
  intros.
  rename fromList_go_Desc into IH.
  rewrite fromList_go_eq by (apply Z.pow_pos_nonneg; lia).
  unfold fromList_go_f.
  destruct xs as [ | ? [ | ?? ]].
  * solve_Desc.
  * destruct H1; try congruence.
    simpl safeHd in *. destruct p.
    assert (isUB None e0 = true) by reflexivity.
    applyDesc insertMax_Desc.
    solve_Desc. simpl.
    (*setoid_rewrite elem_cons.*)
    f_solver.
  * destruct H1; try congruence.
    repeat replace (#1) with 1%Z by reflexivity.
    replace ((Bits.shiftL (2 ^ sz)%Z 1))%Z with (2 ^ (1 + sz))%Z.
    Focus 2.
      unfold Bits.shiftL, Bits.instance_Bits_Int.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.pow_add_r by lia.
      lia. destruct p.
    destruct_match.
    --  apply Bounded_relax_ub_None in H0. 
        applyDesc fromList'_Desc.
        solve_Desc.
    --  eapply fromList_create_Desc.
        - lia.
        - eassumption.
        - intros.
          subst.
          simpl safeHd in *.

          applyDesc link_Desc.
          destruct zs.
          ++  rewrite app_nil_r in H4.
              eapply IH.
              + rewrite H4. simpl. rewrite app_length. lia.
              + lia.
              + assumption.
              + destruct H5 as [?|[??]]; [left; assumption | right].
                replace (size s1). replace (size s).  replace (size s0).
                rewrite Z.pow_add_r by lia.
                lia.
              + intros.
                rewrite H4.
                solve_Desc. simpl.
                (*setoid_rewrite elem_cons.*)
                setoid_rewrite sem_list_app. setoid_rewrite rev_app_distr.
                setoid_rewrite sem_list_app. 
                setoid_rewrite (sem_toList_reverse s0 _ _ _ H2). 
                setoid_rewrite <- toList_sem''; only 2: eassumption. f_solver.
                ** assert (sem s i = None). { eapply sem_outside_above. apply H0. solve_Bounds. }
                   rewrite H9 in Hsem. simpl in Hsem. assert (i == e0 = false) by solve_Bounds.
                   rewrite H10 in Hsem. simpl in Hsem. rewrite Hsem in H8. inversion H8; reflexivity.
                ** simpl in Heqo2. destruct( i == e0) eqn : ?. simpl in Hsem. 
                   assert (sem s i = None). { eapply sem_outside_above. apply H0.
                   solve_Bounds. } rewrite H9 in Hsem. simpl in Hsem. rewrite Hsem in H8.
                  rewrite Heqo2 in H8. inversion H8; reflexivity.
                ** inversion Heqo2.
                ** simpl in Heqo2. destruct (i == e0) eqn : ?. inversion Heqo2.
                   simpl in Hsem. rewrite Hsem in H8. inversion H8.
                ** destruct (sem s i); simpl in Hsem; inversion Hsem. rewrite H8 in H10.
                   inversion H10. destruct (i == e0); simpl in Hsem; inversion Hsem.
                    rewrite H8 in H11. inversion H11. rewrite H11 in H8. inversion H8.
                ** simpl in Heqo2. destruct (i == e0) eqn : ?. simpl in Hsem.
                   destruct (sem s i); simpl in Hsem. rewrite Hsem in H8. inversion H8.
                    rewrite Hsem in H8; inversion H8. inversion Heqo2.
         ++ destruct H5 as [ ? | [? Habsurd]]; try congruence.
            subst. rewrite app_nil_l in H4.
            rewrite H4.
            apply Bounded_relax_ub_None in HB.
            applyDesc fromList'_Desc.
            solve_Desc. simpl.
            (*setoid_rewrite elem_cons.*)
            setoid_rewrite sem_list_app. setoid_rewrite rev_app_distr. simpl.
            setoid_rewrite sem_list_app. setoid_rewrite (sem_toList_reverse s0 _ _ _ H2). 
            setoid_rewrite <- toList_sem''; only 2: eassumption. simpl in Hsem0.
            f_solver.
            ** assert (sem s i = None). { eapply sem_outside_above. apply H0.
              solve_Bounds. } rewrite H5 in Hsem. simpl in Hsem. 
              assert (i == e0 = false) by solve_Bounds. rewrite H6 in Hsem. simpl in Hsem.
              rewrite Hsem in Hsem0. inversion Hsem0; reflexivity.
            **  assert (sem s i = None). { eapply sem_outside_above. apply H0.
              solve_Bounds. } rewrite H5 in Hsem. simpl in Hsem. rewrite Hsem in Hsem0.
              inversion Hsem0; reflexivity.
            ** destruct (sem s i); simpl in Hsem; rewrite Hsem in Hsem0. inversion Hsem0.
                destruct (i == e0); simpl in Hsem. inversion Hsem0. inversion Hsem0.
            ** destruct (sem s i). simpl in Hsem. rewrite Hsem in Hsem0. inversion Hsem0.
              simpl in Hsem. rewrite Hsem in Hsem0. inversion Hsem0.
Qed.

Lemma fromList_Desc:
  forall xs,
  Desc' (fromList xs) None None (fun i => sem_for_lists (rev xs) i).
Proof.
  intros.
  cbv beta delta [fromList].
  destruct xs as [ | ? [|??] ].
  * solve_Desc.
  * destruct p. solve_Desc.
  * fold fromList'. destruct p.
    zeta_one.
    fold not_ordered.
    zeta_one.
    fold fromList_create_f.
    fold fromList_create.
    zeta_one.
    fold fromList_go_f.
    fold fromList_go.
    zeta_one.
    destruct_match.
    - applyDesc fromList'_Desc.
      solve_Desc. simpl. setoid_rewrite sem_list_app. setoid_rewrite sem_list_app.
       simpl. destruct p0. simpl in Hsem. setoid_rewrite sem_list_app in Hsem. simpl in Hsem.
      (*setoid_rewrite elem_cons.*)
      f_solver.
    - repeat replace (#1) with (2^0)%Z by reflexivity.
      eapply fromList_go_Desc.
      + lia.
      + destruct p0. simpl in Heq. 
        solve_Bounded.
      + right. reflexivity.
      + intros.
        solve_Desc. simpl. setoid_rewrite sem_list_app. setoid_rewrite sem_list_app.
        simpl. simpl in H1. setoid_rewrite sem_list_app in H1. simpl in H1.
        f_solver.
Qed.


(** ** Verification of [Eq] *)

(*Note: This is substantially different from SetProofs because the values' equality may differ between
Coq and Haskell. Instead of a single spec, we will prove 3 different specifications of [Eq]
1. [weak_equals_spec]: This states that m1 == m2 iff for every key, sem m1 key == sem m2 key 
 (all according to Haskell notions of equality)
2. [strong_eq1]: If sem m1 key = sem m2 key for all keys, then m1 == m2 (the other direction is not true
in general)
3. [strong_eq2]: If Haskell equality is equivalent to Coq equality for the values (for example, if the
values are integers), then m1 == m2 iff for every key, sem m1 key = sem m2 key

The benefit of this is that the stronger notions of equality are much easier to work with in Coq proofs,
and means that if Coq and Haskell equality agree, we have a very strong specification of the equality of the
corresponding maps.
*)

(*[eqlist] is symmetric*)
Lemma eqlist_sym:
  forall {a} `{EqLaws a} (xs ys : list a),
  eqlist xs ys = eqlist ys xs.
Proof.
  intros. generalize dependent ys. induction xs; intros.
  - destruct ys. reflexivity. simpl. reflexivity. 
  - destruct ys. simpl. reflexivity. simpl.
    destruct (a1 == a2) eqn : ?.
    + simpl. rewrite Eq_Symmetric. simpl. apply IHxs. apply Heqb.
    + simpl. assert (a2 == a1 = false). apply Lemmas.Eq_neq_sym. assumption.
      rewrite H1. simpl. reflexivity.
Qed. 

(*Equal lists have the same length*)
Lemma eqlist_length:
  forall {a} `{Eq_ a} (xs ys : list a),
  eqlist xs ys = true ->
  length xs = length ys.
Proof.
  intros. generalize dependent ys. induction xs; intros.
  - destruct ys. reflexivity. simpl in H0. discriminate H0.
  - destruct ys. simpl in H0. discriminate H0. simpl in H0.
    simpl. rewrite (IHxs ys). reflexivity. apply andb_true_iff in H0.
    destruct H0. assumption.
Qed.

(*Since I could not find a Typeclass instance for (e * a) (assuming that e and a satsify EqLaws),
The following 3 lemmas prove that equality on tuples is transitive, symmetric, and reflexive.
TODO: Add an EqLaws instance for (e * a)*)


Lemma Eq_Tuple_Trans: forall `{Eq_ a} `{EqLaws a} (x1 x2 x3 : e) (y1 y2 y3 : a),
  (x1, y1) == (x2, y2) = true -> (x2, y2) == (x3, y3) = true -> (x1, y1) == (x3, y3) = true.
Proof.
  intros. unfold op_zeze__ in *. unfold Eq_pair___ in *. unfold op_zeze____ in *. unfold eq_pair in *.
  rewrite andb_true_iff in *. destruct H2. destruct H3. split. eapply Eq_Transitive. apply H2. apply H3.
  eapply Eq_Transitive. apply H4. apply H5.
Qed.

Lemma Eq_Tuple_Sym: forall `{Eq_ a} `{EqLaws a} (x1 x2 : e) (y1 y2 : a),
  (x1, y1) == (x2, y2) = true <-> (x2, y2) == (x1, y1) = true.
Proof.
  intros. unfold op_zeze__ in *. unfold Eq_pair___  in *. unfold op_zeze____ in *. unfold eq_pair in *.
  rewrite andb_true_iff in *. rewrite andb_true_iff in *. split; intros.
  - destruct H2. split. apply Eq_Symmetric. apply H2. apply Eq_Symmetric. apply H3.
  - destruct H2. split. apply Eq_Symmetric. apply H2. apply Eq_Symmetric. apply H3.
Qed. 

Lemma Eq_Tuple_Refl: forall `{Eq_ a} `{EqLaws a} (x :e) (y : a),
  (x, y) == (x, y) = true.
Proof.
  intros. unfold_zeze. unfold eq_pair. rewrite andb_true_iff. split; apply Eq_Reflexive.
Qed.

(*Equal lists have the same elements in them*)
Lemma eqlist_elem:
  forall `{Eq_ a}  `{EqLaws a} (xs ys : list (e * a)) x y,
  eqlist xs ys = true ->
  List.elem (x, y) xs = true <-> List.elem (x, y) ys = true.
Proof.
  intros. generalize dependent ys. induction xs; intros.
  - simpl. destruct ys. simpl. reflexivity. simpl in H2. discriminate H2.
  - destruct ys. simpl in H2. discriminate H2. simpl. simpl in H2. split; intros.
    + destruct p. rewrite andb_true_iff in H2. destruct H2. rewrite orb_true_iff.
      rewrite orb_true_iff in H3. destruct H3. left. destruct a0.  eapply Eq_Tuple_Trans. 
      apply H3. apply H2. right. apply IHxs. assumption. assumption.
    + rewrite orb_true_iff. rewrite orb_true_iff in H3. rewrite andb_true_iff in H2.
      destruct H2. destruct H3. left. destruct a0. destruct p. eapply Eq_Tuple_Trans.
      apply H3. eapply Eq_Tuple_Sym. assumption. right. rewrite (IHxs ys). assumption. assumption.
Qed.

(*States that a map is empty iff sem key map returns None for every key*)
Lemma sem_false_nil:
  forall m,
  (forall i, sem m i = None) <-> m = Tip.
Proof.
  intros. remember m as m1. split; intros.
  - destruct m.
    + assert (sem m1 e0 <> None). { subst. 
      simpl. destruct (sem m2 e0). 
      * simpl. intro. discriminate H0.
      * simpl. rewrite Eq_Reflexive. simpl. intro. discriminate H0. }
        specialize (H e0). rewrite H in H0. contradiction.
    + assumption.
  - rewrite H. simpl. reflexivity.
Qed. 

(*We don't want to use Forall_forall because all we know is that List.elem is true,
which is much weaker than List.In*)
Lemma Forall_lt: forall `{Eq_ a} `{EqLaws a} (l : list (e * a)) t,
  Forall (lt t) l <-> (forall x y, List.elem (x, y) l = true -> lt t (x,y)).
Proof.
  intros. split; induction l; intros.
  - simpl in H3. discriminate H3.
  - inversion H2. subst. simpl in H3. rewrite orb_true_iff in H3. destruct H3.
    destruct t. destruct a0. unfold lt in H6. unfold lt. rewrite eq_tuple_prop in H3.
    order e. apply IHl. apply H7. apply H3.
  - apply Forall_nil.
  - apply Forall_cons. destruct a0. specialize (H2 e0 a0). apply H2. simpl.
    apply orb_true_iff. left. apply Eq_Tuple_Refl. apply IHl. intros. apply H2.
    simpl. apply orb_true_iff. right. apply H3.
Qed. 

(*If two tuples are equal according to Haskell, List.elem returns the same result for either on a list*)
Lemma list_elem_eq : forall `{Eq_ a} `{EqLaws a} (x1 x2 : e) (y1 y2 : a) l,
  (x1, y1) == (x2, y2) = true ->
  List.elem (x1, y1) l = true <-> List.elem (x2, y2) l = true.
Proof.
  intros. induction l.
  - simpl. split; intros; discriminate H3.
  - split; intros; simpl in *; rewrite orb_true_iff in *.
    + destruct H3.
      * left. destruct a0. eapply Eq_Tuple_Trans. eapply Eq_Tuple_Sym. apply H2. apply H3.
      * right. apply IHl. apply H3.
    + destruct H3.
      * left. destruct a0. eapply Eq_Tuple_Trans. apply H2. apply H3.
      * right. apply IHl. apply H3.
Qed.

(*Strongly sorted lists with the same elements are the same.*)
(*TODO: Clean up the proof*)
Lemma strongly_sorted_unique:
  forall `{Eq_ a} `{EqLaws a} (xs ys : list (e * a)),
  StronglySorted lt xs ->
  StronglySorted lt ys ->
  (forall x y, List.elem (x, y) xs = true <-> List.elem (x,y) ys = true) ->
  eqlist xs ys = true.
Proof.
  intros. generalize dependent ys. induction xs; intros.
  - simpl in H4. destruct ys. reflexivity. 
    assert (forall x y, List.elem (x,y) (p :: ys) = false). { intros. specialize (H4 x y).
   destruct H4. apply contrapositive in H5. destruct (List.elem (x, y) (p :: ys)). contradiction.
    reflexivity. intro. discriminate H6. }
    assert (List.elem p (p :: ys) = true). { simpl. rewrite orb_true_iff. left. destruct p.
    apply Eq_Tuple_Refl. } destruct p. specialize (H5 e0 a0). rewrite H6 in H5. discriminate H5.
  - destruct ys. 
    + assert (forall x y, List.elem (x,y) (a0 :: xs) = false). { intros x y.
      specialize (H4 x y). destruct H4. apply contrapositive in H4. destruct (List.elem (x, y) (a0 :: xs)).
      contradiction. reflexivity. intro. simpl in H6. discriminate H6. }
      destruct a0. assert (List.elem (e0, a0) ((e0, a0) :: xs) = true). { simpl. rewrite orb_true_iff.
      left. apply Eq_Tuple_Refl. }
      specialize (H5 e0 a0). rewrite H6 in H5. discriminate H5.
    + simpl. rewrite andb_true_iff. inversion H2; subst. inversion H3; subst. split. 
      assert (A:=H4). destruct a0. destruct p. specialize (H4 e0 a0). specialize (A e1 a1).
      destruct H4. destruct A. 
      assert (List.elem (e0, a0) ((e1, a1) :: ys) = true). { apply H4. simpl. rewrite orb_true_iff.
      left. apply Eq_Tuple_Refl. }
      assert (List.elem (e1, a1) ((e0, a0) :: xs) = true). { apply H11. simpl. rewrite orb_true_iff.
      left. apply Eq_Tuple_Refl. }
      rewrite Forall_lt in H8. rewrite Forall_lt in H10. simpl in H12. simpl in H13. 
      rewrite orb_true_iff in *. destruct H12. destruct H13. apply H12. apply H12. 
      destruct H13. apply Eq_Tuple_Sym. apply H13. apply H8 in H13. apply H10 in H12. 
      unfold lt in H12. unfold lt in H13. order e. 
      apply IHxs. assumption. assumption. intros. split; intros.
      * assert (A1:=H4). specialize (H4 x y). destruct H4. rewrite Forall_lt in H8. rewrite Forall_lt in H10.
        assert (A:=H5).  assert (List.elem (x,y) (a0 :: xs) = true). {
        simpl. rewrite orb_true_iff. right. assumption. }
        apply H4 in H11. simpl in H11.  rewrite orb_true_iff in H11. destruct H11.
        { apply H8 in H5. destruct p. assert (List.elem (e0, a1) (a0 :: xs) = true). {
          apply A1. simpl. rewrite orb_true_iff. left. apply Eq_Tuple_Refl. }
          simpl in H12. rewrite orb_true_iff in H12. destruct H12.
          { destruct a0. unfold lt in H5. rewrite eq_tuple_prop in H11. rewrite eq_tuple_prop in H12.
            order e. }
          { destruct a0. assert (List.elem (e1, a0) ((e0, a1) :: ys) = true). { apply A1.
            simpl. rewrite orb_true_iff. left. apply Eq_Tuple_Refl. }
           simpl in H13. rewrite orb_true_iff in H13. destruct H13.
            { rewrite eq_tuple_prop in H11. rewrite eq_tuple_prop in H13.
              apply H8 in A. apply H8 in H12. unfold lt in *. order e. }
            { assert (A2:=H13). assert (A3:=H12). apply H10 in H13. apply H8 in H12.
              unfold lt in *. order e. }
            }
          }
          { apply H11. }
          (*Basically the same proof - try to clean up*)
        * assert (A1:=H4). specialize (H4 x y). destruct H4. rewrite Forall_lt in H8. rewrite Forall_lt in H10.
        assert (A:=H5).  assert (List.elem (x,y) (p :: ys) = true). {
        simpl. rewrite orb_true_iff. right. assumption. }
        apply H6 in H11. simpl in H11.  rewrite orb_true_iff in H11. destruct H11.
        { apply H10 in H5. destruct p. assert (List.elem (e0, a1) (a0 :: xs) = true). {
          apply A1. simpl. rewrite orb_true_iff. left. apply Eq_Tuple_Refl. }
          simpl in H12. rewrite orb_true_iff in H12. destruct H12.
          { destruct a0. unfold lt in H5. rewrite eq_tuple_prop in H11. rewrite eq_tuple_prop in H12.
            order e. }
          { destruct a0. assert (List.elem (e1, a0) ((e0, a1) :: ys) = true). { apply A1.
            simpl. rewrite orb_true_iff. left. apply Eq_Tuple_Refl. }
           simpl in H13. rewrite orb_true_iff in H13. destruct H13.
            { rewrite eq_tuple_prop in H11. rewrite eq_tuple_prop in H13.
              apply H10 in A. apply H8 in H12. unfold lt in *. order e. }
            { assert (A2:=H13). assert (A3:=H12). apply H10 in H13. apply H8 in H12.
              unfold lt in *. order e. }
            }
          }
          { apply H11. }
Qed.

(*A few final lemmas before the [Eq] specs. The first states that if a key is not in [toList],
  then sem returns false, and vice versa. *)

Lemma elem_not_in_list : forall `{Eq_ a} `{EqLaws a} key map lb ub,
  Bounded map lb ub ->
  (forall value, List.elem (key, value) (toList map) = false) <-> sem map key = None.
Proof.
  intros; split; intros.
  - destruct (sem map key) eqn : ?.
    + assert (sem map key == Some a0 = true). { rewrite Heqo. apply Eq_Reflexive. } eapply toList_sem' in H4.
      specialize (H3 a0). rewrite H4 in H3. discriminate H3. apply H2.
    + reflexivity.
  - destruct (List.elem (key, value) (toList map)) eqn : ?.
    + rewrite <- toList_sem' in Heqb. rewrite H3 in Heqb. discriminate Heqb. apply H2.
    + reflexivity.
Qed.
      
(*If two maps have equal lists, their size is equal*)
Lemma eq_size : forall `{Eq_ a} `{EqLaws a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  toList m1 == toList m2 = true ->
  Internal.size m1 = Internal.size m2.
Proof.
  intros. rewrite size_size. erewrite size_spec. erewrite size_spec. 
  unfold op_zeze__ in H4. unfold Eq_list in H4. unfold op_zeze____ in H4. apply eqlist_length in H4.
  rewrite H4. reflexivity. apply H3. apply H2.
Qed.

(*Map equality is defined by checking both [length] and [toList], but [length] does not matter.
This makes the next proofs a bit easier.*)
Lemma eq_toList : forall `{Eq_ a} `{EqLaws a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  m1 == m2 = true <-> (toList m1 == toList m2) = true.
Proof.
  intros. split; intros.
  - unfold op_zeze__ in H4. unfold Eq___Map in H4. unfold op_zeze____ in H4. 
    unfold Internal.Eq___Map_op_zeze__ in H4. rewrite andb_true_iff in H4. destruct H4.
    unfold toList. assumption.
  - unfold_zeze. unfold  Eq___Map. unfold Internal.Eq___Map_op_zeze__. rewrite andb_true_iff.
    split. assert (Internal.size m1 = Internal.size m2). eapply eq_size. apply H2. apply H3.
    assumption. rewrite H5. apply Eq_Reflexive. unfold toList in *. assumption.
Qed.

Lemma weak_equals_spec:
  forall `{Eq_ a} `{EqLaws a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  m1 == m2 = true <-> (forall i, sem m1 i == sem m2 i = true).
Proof.
  intros. split; intros. unfold op_zeze__ in H4. unfold Eq___Map in H4.
      unfold op_zeze____ in H4. unfold Internal.Eq___Map_op_zeze__ in H4.  rewrite andb_true_iff in H4.
      destruct H4. unfold op_zeze__ in H5. unfold Eq_list in H5. unfold op_zeze____ in H5.
  - destruct (sem m1 i) eqn : ?. 
    + eapply eqlist_elem in H5. assert (sem m1 i == Some a0 = true). { rewrite Heqo. apply Eq_Reflexive. }
      rewrite toList_sem' in H6. unfold toList in H6. apply H5 in H6. rewrite <- toList_sem' in H6.
      apply Eq_Symmetric. apply H6. apply H3. apply H2.
    + rewrite <- elem_not_in_list in Heqo. pose proof (toList_sem') as H7. specialize (H7 m2 lb ub H3 i).
      assert (forall value, List.elem (i, value) (toList m2) = false). { intros.
      specialize (H7 value). destruct H7. apply contrapositive in H7.
      destruct (List.elem (i, value) (toList m2)). contradiction. reflexivity. 
      assert (forall value, List.elem (i, value) (toAscList m2) = false). { intros.
      apply (eqlist_elem _ _ i value0) in H5. destruct H5. apply contrapositive in H8.
      destruct (List.elem (i, value0) (toAscList m2)). contradiction. reflexivity.
      destruct (List.elem (i, value0) (toAscList m1)) eqn : ?. specialize (Heqo value0).
      unfold toList in Heqo. rewrite Heqo in Heqb. discriminate Heqb. intro. discriminate H9. }
      eapply elem_not_in_list in H8. rewrite H8. intro. discriminate H9. apply H3. }
      eapply elem_not_in_list in H6. rewrite H6. order e. apply H3. apply H2.
  - eapply eq_toList. apply H2. apply H3. apply strongly_sorted_unique. eapply to_List_sorted.
    apply H2. eapply to_List_sorted. apply H3. intros. split; intros.
    + rewrite <- toList_sem' in H5. specialize (H4 x). assert (sem m2 x == Some y = true).
      { eapply Eq_Transitive. apply Eq_Symmetric. apply H4. apply H5. }
      rewrite toList_sem' in H6. assumption. apply H3. apply H2.
    + rewrite <-toList_sem' in H5. specialize (H4 x). assert (sem m1 x == Some y = true).
      { eapply Eq_Transitive. apply H4. apply H5. } rewrite toList_sem' in H6. assumption.
      apply H2. apply H3.
Qed.

Lemma strong_eq1 : forall `{Eq_ a} `{EqLaws a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  (forall i, sem m1 i = sem m2 i) -> m1 == m2 = true.
Proof. intros.
  assert (forall i, (sem m1 i == sem m2 i = true)). { intros. specialize (H4 i).
  rewrite H4. apply Eq_Reflexive. } eapply weak_equals_spec in H5. assumption.
  apply H2. apply H3.
Qed.

Lemma strong_eq2 : forall `{Eq_ a} `{EqLaws a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  (forall (y1 : a) (y2 : a), y1 == y2 = true <-> y1 = y2) ->
  (forall i, sem m1 i =  sem m2 i) <-> m1 == m2 = true.
Proof.
  intros. split; intros.
  - eapply strong_eq1. apply H2. apply H3. apply H5.
  - rewrite weak_equals_spec in H5. specialize (H5 i).
    destruct (sem m1 i). destruct (sem m2 i). 
    rewrite simpl_option_some_eq in H5. rewrite H4 in H5. subst. reflexivity.
    discriminate H5. destruct (sem m2 i). discriminate H5. reflexivity. apply H2. apply H3.
Qed.



(** ** Verification of [splitLookup] *)

(* Rewrite to avoid local [go] and StrictTriple *)
Fixpoint splitLookup' (k : e) (s : Map e a) : (Map e a * option a * Map e a) :=
  match s with
   | Tip => (Tip, None, Tip)
   | Bin _ kx x l r => match GHC.Base.compare k kx with
     | Lt => match splitLookup' k l with
               | (lt, z, gt) => match link kx x gt r with
                                              | gt' => (lt, z, gt')
                                            end
             end
     | Gt => match splitLookup' k r with
               | (lt, z, gt) => match link kx x l lt with
                                              | lt' => (lt', z, gt)
                                            end
             end
     | Eq => (l, Some x, r)
    end
 end.

Lemma splitLookup_splitLookup' : forall x map, splitLookup x map  = splitLookup' x map.
Proof.
  intros.
  unfold splitLookup.
  induction map.
  * simpl.
    rewrite <- IHmap1. clear IHmap1.
    rewrite <- IHmap2. clear IHmap2.
    destruct (compare x k).
    + reflexivity.
    + destruct (_ x map1); reflexivity.
    + destruct (_ x map2); reflexivity.
  * reflexivity.
Qed.

Lemma splitLookup_Desc:
  forall x s lb ub,
  Bounded s lb ub ->
  forall (P : Map e a * option a * Map e a -> Prop),
  (forall s1 b s2,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    b = sem s x ->
    (forall i, sem s i =
          (if i == x then sem s i
           else  (sem s1 i ||| sem s2 i))) ->
    P (s1, b, s2)) ->
  P (splitLookup x s) : Prop.
Proof.
  intros ?? ?? HB.
  rewrite splitLookup_splitLookup'.
  induction HB.
  Ltac solveThis ::= intros X HX; apply HX; clear X HX; [solve_Bounded|solve_Bounded|try reflexivity |f_solver].
  * solveThis.
  * simpl.
    destruct (compare x x0) eqn:?.
    + solveThis.
      replace (x == x0) with true by order_Bounds.
      simpl_options.
      assert (sem s1 x = None). { eapply sem_outside_above. apply HB1. solve_Bounds. }
      rewrite H3. simpl. reflexivity.
    + apply IHHB1.
      intros s1_2 b s1_3 HB1_2 HB1_3 Hb Hsems1.
      clear IHHB1 IHHB2.
      applyDesc link_Desc.
      solveThis.
      replace (x == x0) with false by order_Bounds.
      rewrite (sem_outside_below HB2) by order_Bounds.
      simpl_options. assumption.
    + apply IHHB2.
      intros s2_2 b s2_3 HB2_2 HB2_3 Hb Hsems2.
      clear IHHB1 IHHB2.
      applyDesc link_Desc.
      solveThis.
      replace (x == x0) with false by order_Bounds.
      rewrite (sem_outside_above HB1) by order_Bounds.
      simpl_options. assumption.
Qed.


(** ** Verification of [submap] *)

Lemma submap'_spec:
  forall m1 m2 lb ub f,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  submap' f m1 m2 = true <-> 
  (forall i value, sem m1 i = Some value -> exists v, (sem m2 i = Some v /\ f value v = true)).
Proof.
  intros ????? HB1 HB2.
  revert dependent m2.
  induction HB1; intros; simpl; subst.
  * intuition. discriminate H0. 
  * destruct m2 eqn:Hs0.
    - rewrite <- Hs0 in *.
      clear s e0 a0 m1 m3 Hs0.
      eapply splitLookup_Desc; [solve_Bounded|].
      intros sr1 b sr2 HBsr1 HBsr2 Hb Hsem.
      destruct HB2.
      + simpl. split; intros. simpl in Hb. subst. discriminate H1. specialize (H1 x v).
        assert (sem s1 x = None). { eapply sem_outside_above. apply HB1_1. unfold isUB. order e. }
        rewrite H3 in H1. simpl in H1. rewrite Eq_Reflexive in H1. simpl in H1. 
        assert (exists v0 : a, None = Some v0 /\ f v v0 = true) by  (apply H1; reflexivity).
        destruct H4. destruct H4. discriminate H4.
      + destruct b. rewrite andb_true_iff. rewrite andb_true_iff. rewrite IHHB1_1 by eassumption. 
        rewrite IHHB1_2 by eassumption. split; intro.
        -- destruct H6. destruct H7. intros i value Hi. rewrite Hsem. destruct (sem s1 i) eqn : ?.
            ** apply H7 in Heqo. destruct Heqo. destruct H9. exists x1.
               destruct (i == x) eqn : ?. solve_Bounds. rewrite H9. simpl. simpl in Hi. split. reflexivity.
              inversion Hi. subst. apply H10.
            ** simpl in Hi. destruct (i == x) eqn : ?. simpl in Hi. exists a0. split. 
              eapply sem_resp_eq in Heqb. rewrite <- Hb in Heqb. assumption. inversion Hi; subst.
              assumption. simpl in Hi. apply H8 in Hi. destruct Hi. exists x1.
              assert (sem sr1 i = None). { eapply sem_outside_above. apply HBsr1. 
              destruct H9. apply (sem_inside HBsr2) in H9. destruct H9. solve_Bounds. }
              rewrite H10. simpl. apply H9.
       -- split. specialize (H6 x v). assert (sem s1 x = None). { eapply sem_outside_above.
          apply HB1_1. unfold isUB. order e. } rewrite H7 in H6. simpl in H6. rewrite Eq_Reflexive in H6.
          simpl in H6. 
          assert (exists v1 : a, sem s0 x ||| SomeIf (_GHC.Base.==_ x x0) v0 ||| sem s3 x = Some v1 
          /\ f v v1 = true) by (apply H6; reflexivity). destruct H8. simpl in Hb. rewrite <- Hb in H8.
          destruct H8. inversion H8; subst. assumption.
          split.
          ** intros. specialize (H6 i value). rewrite H7 in H6. simpl in H6.
             assert (exists v : a, sem s0 i ||| SomeIf (_GHC.Base.==_ i x0) v0 ||| sem s3 i = Some v
             /\ f value v = true) by (apply H6; reflexivity). destruct H8. destruct H8. 
            specialize (Hsem i). simpl in Hsem. rewrite H8 in Hsem. destruct (i==x) eqn : ?.
            ++ solve_Bounds.
            ++ assert (sem sr2 i = None). { eapply (sem_inside HB1_1) in H7. destruct H7.
              unfold isUB in H10. eapply (sem_outside_below). apply HBsr2. solve_Bounds. }
              rewrite H10 in Hsem. rewrite oro_None_r in Hsem. exists x1. split. symmetry.
              apply Hsem. apply H9.
          ** intros. specialize (H6 i value). rewrite H7 in H6.
              assert (sem s1 i = None). eapply sem_outside_above. apply HB1_1. eapply (sem_inside HB1_2) in H7.
              destruct H7. solve_Bounds. rewrite H8 in H6. simpl in H6. destruct (i == x) eqn : ?.
              ++ solve_Bounds.
              ++ simpl in H6. assert ( exists v : a, sem s0 i ||| 
              SomeIf (_GHC.Base.==_ i x0) v0 ||| sem s3 i = Some v /\ f value v = true) by (apply H6; reflexivity).
             destruct H9. specialize (Hsem i). simpl in Hsem. destruct H9. rewrite H9 in Hsem.
              rewrite Heqb in Hsem. assert (sem sr1 i = None). { eapply (sem_inside HB1_2) in H7.
              destruct H7. unfold isLB in H7. eapply sem_outside_above. apply HBsr1. solve_Bounds. }
              rewrite H11 in Hsem. simpl in Hsem. exists x1. split. symmetry. apply Hsem. apply H10.
          -- split; intros. discriminate H6. specialize (H6 x). assert (sem s1 x = None). {
              eapply sem_outside_above. apply HB1_1. unfold isUB.  order e. } rewrite H7 in H6. simpl in H6.
              specialize (H6 v). rewrite Eq_Reflexive in H6. simpl in H6. destruct H6. reflexivity.
              simpl in Hb. rewrite <- Hb in H6. destruct H6. discriminate H6.
    - intuition. 
      + discriminate H1.
      + subst. simpl in H1. specialize (H1 x v). assert (sem s1 x = None). { eapply sem_outside_above.
        apply HB1_1. unfold isUB. order e. } rewrite H3 in H1. simpl in H1. rewrite Eq_Reflexive in H1.
        simpl in H1. destruct H1. reflexivity. destruct H1. discriminate H1.
Qed.

Lemma submap_size : 
  forall m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  (forall i value, sem m1 i = Some value ->  exists v, sem m2 i = Some v) ->
  (size m1 <= size m2)%Z.
Proof.
  intros ???? HB1 HB2 Hsubmap.
  revert dependent m2.
  induction HB1; intros; simpl; subst.
  * simpl. solve_size.
  * assert (exists v, sem m2 x = Some v). { specialize (Hsubmap x v). simpl in Hsubmap.
    assert (sem s1 x = None). { eapply sem_outside_above. apply HB1_1. unfold isUB. order e. }
    rewrite H1 in Hsubmap. simpl in Hsubmap. rewrite Eq_Reflexive in Hsubmap. simpl in Hsubmap.
    destruct Hsubmap. reflexivity. exists x0. assumption. }
    assert (size m2 = let '(sl,sr) := split x m2 in 1 + size sl + size sr)%Z.
    { eapply split_Desc; [eassumption|]. intros. destruct H1. rewrite H1 in H5. simpl in H5. lia. }
    rewrite H3.
    eapply split_Desc; [eassumption|]. intros.
    assert (size s1 <= size s0)%Z.
    { apply IHHB1_1; try assumption.
      intros i v1 Hi.
      specialize (Hsubmap i). simpl in Hsubmap.
      rewrite Hi in Hsubmap. simpl in Hsubmap.
      specialize (Hsubmap v1). destruct Hsubmap. reflexivity. 
      specialize (H7 i). destruct (i == x) eqn : ?.
      { solve_Bounds. }
      { assert (sem s3 i = None). { assert (i < x = true) by solve_Bounds. eapply sem_outside_below.
        apply H5. unfold isLB. order e. }
        rewrite H9 in H7. rewrite oro_None_r  in H7. exists x0. rewrite <- H7. assumption. }
   }
    assert (size s2 <= size s3)%Z.
    { apply IHHB1_2; try assumption.
      intros i v1 Hi.
      specialize (Hsubmap i). simpl in Hsubmap.
      rewrite Hi in Hsubmap. simpl in Hsubmap.
      specialize (Hsubmap v1).
      assert (sem s1 i = None). { eapply sem_outside_above. apply HB1_1. solve_Bounds. }
      rewrite H9 in Hsubmap. simpl in Hsubmap.
      assert (i == x = false) by solve_Bounds. rewrite H10 in Hsubmap. simpl in Hsubmap.
      destruct Hsubmap. reflexivity. specialize (H7 i). rewrite H11 in H7. rewrite H10 in H7.
     assert (sem s0 i = None). { assert (x < i = true) by solve_Bounds. eapply sem_outside_above.
      apply H4. solve_Bounds. }
      rewrite H12 in H7. simpl in H7. exists x0. symmetry. apply H7. }
    lia.
Qed.

Lemma isSubmapOfBy_spec:
  forall m1 m2 f lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  isSubmapOfBy f m1 m2 = true <-> (forall i value, sem m1 i = Some value -> exists v, sem m2 i = 
  Some v /\ f value v = true).
Proof.
  intros. unfold isSubmapOfBy. split; intros.
  - eapply submap'_spec. apply H. apply H0. rewrite andb_true_iff in H1. destruct H1. apply H3.
    apply H2.
  - apply andb_true_iff. split. unfold op_zlze__. unfold Ord_Integer___. unfold op_zlze____.
    rewrite size_size. rewrite Z.leb_le. eapply submap_size. apply H. apply H0. intros.
    specialize (H1 i value). apply H1 in H2. destruct H2. destruct H2. exists x. apply H2.
    eapply submap'_spec. apply H. apply H0. apply H1.
Qed.

Lemma isSubmapOf_spec:
  forall `{Eq_ a} m1 m2 lb ub,
  Bounded m1 lb ub ->
  Bounded m2 lb ub ->
  isSubmapOf m1 m2 = true <-> (forall i value, sem m1 i = Some value -> exists v, sem m2 i = Some v /\
  value == v = true).
Proof.
  intros. eapply isSubmapOfBy_spec. apply H0. apply H1.
Qed.

(** ** Verification of [filter] *)

(**
For filter we need two lemmas: We need to know that [filter P s] is
well-formed even if P does not respect equality (this is
required by the [FSetInterface]). But to prove something about its
semantics, we need to assume that [P] respects equality.
*)

Lemma filterWithKey_Bounded:
  forall (P : e -> a -> bool) map lb ub,
  Bounded map lb ub ->
  Bounded (Internal.filterWithKey P map) lb ub.
Proof.
  intros.
  induction H.
  * simpl. solve_Bounded.
  * simpl.
    destruct (P x v) eqn:HPx.
    - destruct_ptrEq.
      + solve_Bounded.
      + applyDesc link_Desc.
    - applyDesc link2_Desc.
Qed.

Require Import Coq.Classes.Morphisms. (* For [Proper] *)

Lemma filterWithKey_Desc:
  forall (P : e -> a -> bool) map lb ub,
  Bounded map lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) P ->
  Desc' (Internal.filterWithKey P map) lb ub (fun x => match sem map x with
                                                      | Some y => if P x y then Some y else None
                                                      | None => None
                                                      end).
Proof.
  intros.
  induction H.
  * simpl. solve_Desc.
  * simpl.
    applyDesc IHBounded1.
    applyDesc IHBounded2.
    destruct (P x v) eqn:HPx.
    - destruct_ptrEq.
      + solve_Desc. f_solver. assert (P i v = true). { erewrite H0. apply HPx. apply Heqb. }
        rewrite Heqb0 in H4. inversion H4.
      + applyDesc link_Desc.
        solve_Desc. f_solver. assert (P i a0 = true). { erewrite H0. apply HPx. apply Heqb. }
        rewrite Heqb0 in H4. inversion H4.
    - applyDesc link2_Desc.
      solve_Desc. f_solver. assert (P x v = true). { erewrite H0. apply Heqb0. apply Eq_Symmetric.
      apply Heqb. } rewrite HPx in H6. inversion H6.
Qed.


(*This requires no conditions on the function P*)
Lemma filter_Desc:
  forall  (P : a -> bool) map lb ub,
  Bounded map lb ub ->
  Desc' (Internal.filter P map) lb ub (fun x => match sem map x with
                                                |Some y => if P y then Some y else None
                                                |None => None
                                                end).
Proof.
  intros. eapply filterWithKey_Desc. apply H. f_solver.
Qed.

(** ** Verification of [partition] *)

Lemma partitionWithKey_Bounded:
  forall p map lb ub,
  Bounded map lb ub ->
  forall (P : (Map e a * Map e a) -> Prop),
  (forall m1 m2, Bounded m1 lb ub /\ Bounded m2 lb ub -> P (m1, m2)) ->
  P (partitionWithKey p map).
Proof.
  intros ???? HB.
  induction HB.
  * intros X HX; apply HX; clear X HX; split; solve_Bounded.
  * simpl.
    apply IHHB1; intros sl1 sl2 [HDsl1 HDsl2]; clear IHHB1.
    apply IHHB2; intros sr1 sr2 [HDsr1 HDsr2]; clear IHHB2.
    destruct (p x) eqn:?.
    - intros X HX; apply HX; clear X HX; split.
      + destruct_ptrEq.
        -- solve_Bounded.
        -- applyDesc link_Desc.
      + applyDesc link2_Desc.
    - intros X HX; apply HX; clear X HX; split.
      + applyDesc link2_Desc.
      + destruct_ptrEq.
        -- solve_Bounded.
        -- applyDesc link_Desc.
Qed.

Lemma partitionWithKey_spec:
  forall (p : e -> a -> bool) map lb ub,
  Bounded map lb ub ->
  Proper ((fun i j : e => i == j = true) ==> eq) p ->
  forall (P : (Map e a * Map e a) -> Prop),
  (forall m1 m2,
    Desc' m1 lb ub (fun i => match sem m1 i with
                             | Some y => if p i y then Some y else None
                             | None => None
                              end)  /\
    Desc' m2 lb ub (fun i => match sem m2 i with
                             | Some y => if p i y then None else Some y
                             | None => None
                             end) ->
    P (m1, m2)) ->
  P (partitionWithKey p map).
Proof.
  intros ???? HB HProper.
  induction HB.
  * intros X HX; apply HX; clear X HX; split; solve_Desc.
  * simpl.
    apply IHHB1; intros sl1 sl2 [HDsl1 HDsl2]; clear IHHB1.
    applyDesc HDsl1; clear HDsl1.
    applyDesc HDsl2; clear HDsl2.
    apply IHHB2; intros sr1 sr2 [HDsr1 HDsr2]; clear IHHB2.
    applyDesc HDsr1; clear HDsr1.
    applyDesc HDsr2; clear HDsr2.
    destruct (p x) eqn:?.
    - intros X HX; apply HX; clear X HX; split.
      + destruct_ptrEq.
        -- solve_Desc. f_solver.
            **  destruct (sem sl1 i). destruct (p i a1) eqn : ?. inversion Hsem; subst. rewrite Heqb1 in Heqb0.
                discriminate Heqb0. discriminate Hsem. discriminate Hsem.
            **  assert (p i v = true). { erewrite HProper. apply Heqb. apply Heqb0. } rewrite H1 in Heqb1.
                discriminate Heqb1.
            **  destruct (sem sr1 i). destruct (p i a1) eqn : ?. inversion Hsem1; subst. rewrite Heqb2 in Heqb1.
                discriminate Heqb1. discriminate Hsem1. discriminate Hsem1.
        -- applyDesc link_Desc.
           solve_Desc. f_solver. 
            ** destruct (sem sl1 i). destruct (p i a1) eqn : ?. inversion Hsem; subst. rewrite Heqb1 in Heqb0.
               discriminate Heqb0. discriminate Hsem. discriminate Hsem.
            ** assert (p i a0 = true). { erewrite HProper. apply Heqb. apply Heqb1. } rewrite H1 in Heqb0.
               discriminate Heqb0.
            ** destruct (sem sr1 i). destruct (p i a1) eqn : ?; rewrite Hsem3 in Hsem1. inversion Hsem1; subst.
               rewrite Heqb0 in Heqb2. discriminate Heqb2. discriminate Hsem1. rewrite Hsem3 in Hsem1. 
              discriminate Hsem1.
      + applyDesc link2_Desc.
        solve_Desc. f_solver.
        -- destruct (sem sl2 i). destruct ( p i a1) eqn : ?. discriminate Hsem0. inversion Hsem0; subst.
          rewrite Heqb0 in Heqb1. discriminate Heqb1. discriminate Hsem0.
        -- rewrite Hsem3 in Hsem2. destruct (sem sr2 i). destruct (p i a1) eqn : ?; inversion Hsem2; subst.
           rewrite Heqb0 in Heqb1. discriminate Heqb1. discriminate Hsem2.
    - intros X HX; apply HX; clear X HX; split.
      + applyDesc link2_Desc.
        solve_Desc. f_solver.
        -- destruct (sem sl1 i). destruct (p i a1) eqn : ?. inversion Hsem; subst. rewrite Heqb0 in Heqb1.
          discriminate Heqb1. discriminate Hsem. discriminate Hsem.
        -- rewrite Hsem3 in Hsem1. destruct (sem sr1 i). destruct (p i a1) eqn : ?; inversion Hsem1; subst.
            rewrite Heqb0 in Heqb1. discriminate Heqb1. inversion Hsem1.
      + destruct_ptrEq.
        -- solve_Desc. f_solver.
           ** destruct (sem sl2 i). destruct (p i a1) eqn : ?; inversion Hsem0; subst. rewrite Heqb0 in Heqb1.
              inversion Heqb1. inversion Hsem0.
           ** assert (p x v = true). { erewrite HProper. apply Heqb1. apply Eq_Symmetric. apply Heqb0. }
              rewrite Heqb in H1. inversion H1.
           ** destruct (sem sr2 i). destruct (p i a1) eqn : ?; inversion Hsem2; subst. rewrite Heqb1 in Heqb2.
              inversion Heqb2. inversion Hsem2.
        -- applyDesc link_Desc.
           solve_Desc. f_solver.
          ** destruct (sem sl2 i). destruct (p i a1) eqn : ?; inversion Hsem0; subst. rewrite Heqb0 in Heqb1.
            inversion Heqb1. inversion Hsem0.
          ** assert (p x a0 = true). { erewrite HProper. apply Heqb0. apply Eq_Symmetric.
             apply Heqb1. } rewrite H1 in Heqb. inversion Heqb.
          ** rewrite Hsem3 in Hsem2. destruct (sem sr2 i). destruct (p i a1) eqn : ?; inversion Hsem2; subst.
             rewrite Heqb0 in Heqb2. inversion Heqb2. inversion Hsem2. 
Qed.

Lemma partition_spec:
  forall (p : a -> bool) map lb ub,
  Bounded map lb ub ->
  forall (P : (Map e a * Map e a) -> Prop),
  (forall m1 m2,
    Desc' m1 lb ub (fun i => match sem m1 i with
                             | Some y => if p y then Some y else None
                             | None => None
                              end)  /\
    Desc' m2 lb ub (fun i => match sem m2 i with
                             | Some y => if p y then None else Some y
                             | None => None
                             end) ->
    P (m1, m2)) ->
  P (partition p map).
Proof.
  intros. unfold partition. eapply partitionWithKey_spec. apply H. f_solver. apply H0.
Qed.

(** ** Verification of [take] *)
(*This is exactly the same as SetProofs, since the take function works the exact same way*)
Definition takeGo : Int -> Map e a -> Map e a.
Proof.
  let rhs := eval unfold take in (@take e a) in
  match rhs with fun n s => if _ then _ else ?go _ _  => exact go end.
Defined.

Lemma take_neg: forall a n (l : list a), (n <= 0)%Z -> List.take n l = nil.
Proof.
  intros. destruct l; simpl; destruct (Z.leb_spec n 0); try lia; try reflexivity.
Qed.

Lemma take_all:
  forall a n (xs : list a), (Z.of_nat (length xs) <= n)%Z -> List.take n xs = xs.
Proof.
  intros. revert n H.
  induction xs; intros n Hall.
  * simpl. destruct (Z.leb_spec n 0); reflexivity.
  * simpl.
    simpl length in Hall. rewrite Nat2Z.inj_succ, <- Z.add_1_l in Hall.
    rewrite IHxs by lia.
    destruct (Z.leb_spec n 0); [lia|reflexivity].
Qed.

Lemma take_app_cons:
  forall a n (l1 : list a) (x : a) (l2 : list a),
  List.take n (l1 ++ x :: l2) = match (n ?= Z.of_nat (length l1))%Z with
    | Lt => List.take n l1
    | Eq => l1
    | Gt => l1 ++ (x :: nil) ++ List.take (n - Z.of_nat (length l1) - 1)%Z l2
  end.
Proof.
  intros. revert n.
  induction l1; intros n.
  * simpl.
    rewrite Z.sub_0_r.
    destruct (Z.leb_spec n 0), (Z.compare_spec n 0)%Z; try reflexivity; lia.
  * cbn -[Z.add Z.of_nat].
    rewrite IHl1. clear IHl1.
    rewrite Nat2Z.inj_succ, <- Z.add_1_l.
    replace (n - (1 + Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    replace (n - 1 - (Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    destruct (Z.leb_spec n 0),
             (Z.compare_spec (n - 1) (Z.of_nat (length l1)))%Z,
             (Z.compare_spec n (1 + Z.of_nat (length l1)))%Z; try reflexivity; lia.
Qed.

Lemma takeGo_spec :
  forall n map lb ub,
  Bounded map lb ub ->
  forall (P : Map e a -> Prop),
  (forall m',
    Bounded m' lb ub /\
    toList m' = List.take n (toList map) ->
    P m') ->
  P (takeGo n map).
Proof.
  intros ???? HD. revert n.
  induction HD; intros n.
  * intros X HX; apply HX. split.
    + simpl. destruct_match; solve_Bounded.
    + simpl. do 2 destruct_match; reflexivity.
  * simpl.
    intros X HX; apply HX.
    rewrite toList_Bin.
    unfold op_zlze__ , Ord_Integer___, op_zlze____.
    unfold compare , Ord_Integer___, compare__.
    rewrite size_size.
    apply IHHD1. intros s1' [HBs1' Hs1']. clear IHHD1.
    apply IHHD2. intros s2' [HBs2' Hs2']. clear IHHD2.
    destruct (Z.leb_spec n 0).
    + rewrite take_neg by assumption. split.
      - solve_Bounded.
      - reflexivity.
    + simpl app.
      rewrite take_app_cons.
      erewrite <- size_spec by eassumption.
      destruct (Z.compare_spec n (size s1)).
      - split.
        ** eapply Bounded_relax_ub; eassumption.
        ** reflexivity.
      - split.
        ** eapply Bounded_relax_ub; eassumption.
        ** assumption.
      - split.
        ** applyDesc link_Desc.
        ** erewrite toList_link by solve_Precondition.
           rewrite Hs2'.
           reflexivity.
Qed.

Lemma toList_take:
  forall n map lb ub,
  Bounded map lb ub ->
  forall (P : Map e a -> Prop),
  (forall m',
    Bounded m' lb ub /\
    toList m' = List.take n (toList map) ->
    P m') ->
  P (take n map).
Proof.
  intros. apply H0.
  unfold take. fold takeGo.
  unfold op_zgze__ , Ord_Integer___, op_zgze____.
  rewrite size_size.
  destruct (Z.leb_spec (size map) n).
  * split; [assumption|].
    rewrite take_all. reflexivity.
    erewrite <- size_spec by eassumption.
    assumption.
  * eapply takeGo_spec; [solve_Precondition..|].
    intros. assumption.
Qed.

(** ** Verification of [drop] *)

Definition dropGo : Int -> Map e a -> Map e a.
Proof.
  let rhs := eval unfold drop in (@drop e a) in
  match rhs with fun n s => if _ then _ else ?go _ _  => exact go end.
Defined.

Lemma drop_neg: forall a n (l : list a), (n <= 0)%Z -> List.drop n l = l.
Proof.
  intros. destruct l; simpl; destruct (Z.leb_spec n 0); try lia; try reflexivity.
Qed.

Lemma drop_all:
  forall a n (xs : list a), (Z.of_nat (length xs) <= n)%Z -> List.drop n xs = nil.
Proof.
  intros. revert n H.
  induction xs; intros n Hall.
  * simpl. destruct (Z.leb_spec n 0); reflexivity.
  * simpl.
    simpl length in Hall. rewrite Nat2Z.inj_succ, <- Z.add_1_l in Hall.
    rewrite IHxs by lia.
    destruct (Z.leb_spec n 0); [lia|reflexivity].
Qed.
  
Lemma drop_app_cons:
  forall a n (l1 : list a) (x : a) (l2 : list a),
  List.drop n (l1 ++ x :: l2) = match (n ?= Z.of_nat (length l1))%Z with
    | Lt => List.drop n l1 ++ (x :: nil) ++ l2
    | Eq => (x :: nil) ++ l2
    | Gt => List.drop (n - Z.of_nat (length l1) - 1)%Z l2
  end.
Proof.
  intros. revert n.
  induction l1; intros n.
  * simpl.
    rewrite Z.sub_0_r.
    destruct (Z.leb_spec n 0), (Z.compare_spec n 0)%Z; try reflexivity; lia.
  * cbn -[Z.add Z.of_nat].
    rewrite IHl1. clear IHl1.
    rewrite Nat2Z.inj_succ, <- Z.add_1_l.
    replace (n - (1 + Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    replace (n - 1 - (Z.of_nat (length l1)) - 1)%Z with (n - 2 - Z.of_nat (length l1))%Z by lia.
    destruct (Z.leb_spec n 0),
             (Z.compare_spec (n - 1) (Z.of_nat (length l1)))%Z,
             (Z.compare_spec n (1 + Z.of_nat (length l1)))%Z; try reflexivity; lia.
Qed.


Lemma dropGo_spec :
  forall n map lb ub,
  Bounded map lb ub ->
  forall (P : Map e a -> Prop),
  (forall m',
    Bounded m' lb ub /\
    toList m' = List.drop n (toList map) ->
    P m') ->
  P (dropGo n map).
Proof.
  intros ???? HD. revert n.
  induction HD; intros n.
  * intros X HX; apply HX. split.
    + simpl. destruct_match; solve_Bounded.
    + simpl. do 2 destruct_match; reflexivity.
  * simpl.
    intros X HX; apply HX.
    rewrite toList_Bin.
    unfold op_zlze__ , Ord_Integer___, op_zlze____.
    unfold compare , Ord_Integer___, compare__.
    rewrite size_size.
    apply IHHD1. intros s1' [HBs1' Hs1']. clear IHHD1.
    apply IHHD2. intros s2' [HBs2' Hs2']. clear IHHD2.
    destruct (Z.leb_spec n 0).
    + rewrite drop_neg by assumption. split.
      - solve_Bounded.
      - rewrite toList_Bin.
        reflexivity.
    + simpl app.
      rewrite drop_app_cons.
      erewrite <- size_spec by eassumption.
      destruct (Z.compare_spec n (size s1)).
      - split.
        ** applyDesc insertMin_Desc.
        ** erewrite toList_insertMin  by solve_Precondition.
           reflexivity.
      - split.
        ** applyDesc link_Desc.
        ** erewrite toList_link by solve_Precondition.
           rewrite Hs1'.
           reflexivity.
      - split.
        ** eapply Bounded_relax_lb; eassumption.
        ** assumption.
Qed.

Lemma toList_drop:
  forall n map lb ub,
  Bounded map lb ub ->
  forall (P : Map e a -> Prop),
  (forall m',
    Bounded m' lb ub /\
    toList m' = List.drop n (toList map) ->
    P m') ->
  P (drop n map).
Proof.
  intros. apply H0.
  unfold drop. fold dropGo.
  unfold op_zgze__ , Ord_Integer___, op_zgze____.
  rewrite size_size.
  destruct (Z.leb_spec (size map) n).
  * split; [solve_Precondition|].
    rewrite drop_all. reflexivity.
    erewrite <- size_spec by eassumption.
    assumption.
  * eapply dropGo_spec; [solve_Precondition..|].
    intros. assumption.
Qed.

(** ** Verification of [splitAt] *)

Definition splitAtGo : Int -> Map e a -> (Map e a * Map e a).
Proof.
  let rhs := eval unfold splitAt in (@splitAt e a) in
  match rhs with fun n s => if _ then _ else Datatypes.id (?go _ _)  => exact go end.
Defined.

Lemma splitAtGo_spec :
  forall n s, splitAtGo n s = (takeGo n s, dropGo n s).
Proof.
  intros ??.
  revert n.
  induction s; intros n.
  * simpl.
    repeat destruct_match; try congruence.
  * simpl. repeat destruct_match; reflexivity.
Qed.


End WF.
(*Could not find [ordered], [valid], [validsize] or similar in Data.Map*)

(** ** Verification of [map] *)

(*Note: for map_spec, the definition we want is not provable:
[(forall i v, sem m i = Some v <-> sem (mapWithKey f m) i = Some (f i v))]

This is because of three problems
1. Even if two keys k1 and k2 are equal (k1 == k2), this does not guarantee
   that (f k = f k2).
2. We cannot compare the results using Haskell equality because neither a not b
   are required to be members of Eq.
3. If f is not injective, then the (<-) is clearly not true (for example, 
   suppose f = \x -> \y -> 1)

This is not an issue in SetProofs because [Ord b] is a necessary condition for the input and the
map function is defined very differently, leading to an entirely different specification.

There are two solutions to this: 
1. Require that if k == k1 and v == v1, then f k v = f k1 v1, which is not true in general
2. Require that [a] and [b] be members of [Eq], which is also not true in general. We also must
   require that k1 == k2 and v1 == v2 -> f k1 v1 == f k2 v2, which should be true in all cases, since
   this is the definition of a pure function in Haskell.

Both cases are proved below. We prove both cases because it could happen that Haskell equality agrees
with Coq equality on the values but the values are not an instance of [Ord].

*)

(*Specification using Coq equality*)

(*The same keys are in both maps*)
Lemma map_none_spec:
  forall {b} {a} {e} `{Eq_ e} `{Ord e} (f: e -> a -> b) (m: Map e a) lb ub,
  Bounded m lb ub ->
  (forall i, sem m i = None <-> sem (mapWithKey f m) i = None).
Proof.
  intros. generalize dependent i. induction H2; intros; split; intros.
  - reflexivity.
  - reflexivity.
  - simpl. simpl in H6. destruct (sem s1 i) eqn : ?. inversion H6. 
    apply IHBounded1 in Heqo. rewrite Heqo. simpl. simpl in H6.
    destruct (i == x) eqn : ?. inversion H6. simpl. simpl in H6.
    apply IHBounded2. apply H6.
  - simpl in H6. simpl. destruct (sem (mapWithKey f s1) i) eqn : ?. inversion H6.
    apply IHBounded1 in Heqo. rewrite Heqo. simpl. destruct (i == x) eqn : ?. inversion H6.
    simpl. simpl in H6. apply IHBounded2. apply H6.
Qed. 

(*Says that if we take any (key, value) pair in the map resulting from mapWithKey, then they
come from a corresponding entry in the original map*)
Lemma map_spec_reverse : 
  forall {b} {a} {t}  `{Ord t} (H : EqLaws t) (f : t -> a -> b) (m : Map t a) lb ub,
  Bounded m lb ub ->
  (forall k k2 v v2, k == k2 = true -> v = v2 -> f k v = f k2 v2) ->
  (forall i v, sem (mapWithKey f m) i = Some v -> exists value, sem m i = Some value /\ v = f i value).
Proof.
  intros. generalize dependent i. generalize dependent v. induction H2; intros.
  - simpl in H4. inversion H4.
  - simpl in H7. simpl. destruct ( sem (mapWithKey f s1) i ) eqn : ?. apply IHBounded1 in Heqo.
    destruct Heqo. exists x0. destruct H8. rewrite H8. simpl. split. reflexivity. inversion H7; subst.
    reflexivity. simpl in H7.  assert (sem s1 i = None). { erewrite map_none_spec. apply Heqo. apply H2_. }
    rewrite H8. destruct (i == x) eqn : ?. simpl in H7. simpl. exists v. split. reflexivity. inversion H7. 
    apply H3. apply Eq_Symmetric. apply Heqb0. reflexivity. simpl. inversion H7. apply IHBounded2.
    assumption.
Qed.

(*If (k,v) is in the original map, then (k, f k v) is in the new map*)
Lemma map_spec_coq:
  forall {b} {a} {e} `{Ord e} (H: EqLaws e) (f : e -> a -> b) (m : Map e a) lb ub,
  Bounded m lb ub ->
  (forall k k2 v v2, k == k2 = true -> v = v2 -> f k v = f k2 v2) ->
  (forall i v, sem m i = Some v -> sem (mapWithKey f m) i = Some (f i v)).
Proof.
  intros.  generalize dependent i. generalize dependent v. induction H2; intros.
  - inversion H4.
  - simpl. simpl in H7. destruct (sem s1 i) eqn : ?.
    * apply IHBounded1 in Heqo. rewrite Heqo. simpl. inversion H7; subst; reflexivity.
    * assert (sem (mapWithKey f s1) i = None). { erewrite <- map_none_spec. assumption. apply H2_. }
      simpl in H7. rewrite H8. simpl. destruct (i == x) eqn : ?.
      + simpl. simpl in H7. inversion H7; subst. erewrite H3. reflexivity. apply Eq_Symmetric.
        apply Heqb0. reflexivity.
      + simpl. apply IHBounded2. simpl in H7. assumption.
Qed.

(*If f is injective, then (k,v) is in the original map iff (k, f k v) is in the new map*)
Lemma map_spec_coq_injective:
  forall {b} {a} {e} `{Ord e} (H: EqLaws e) (f : e -> a -> b) (m : Map e a) lb ub,
  Bounded m lb ub ->
  (forall k k2 v v2, k == k2 = true -> v = v2 -> f k v = f k2 v2) ->
  (forall k k2 v v2, f k v = f k2 v2 -> k == k2 = true /\ v = v2) ->
  (forall i v, sem m i = Some v <-> sem (mapWithKey f m) i = Some (f i v)).
Proof.
  intros. split.
  - intros. eapply map_spec_coq; eassumption.
  - generalize dependent i. generalize dependent v. induction H2; intros.
    + inversion H2.
    + simpl in H8. simpl. destruct (sem (mapWithKey f s1) i) eqn : ?.
      * assert (A:= Heqo). eapply map_spec_reverse in Heqo. destruct Heqo.
        destruct H9. subst. inversion H8. rewrite H9. simpl.
        apply H4 in H10. destruct H10. subst. reflexivity. assumption. apply H2_.
        apply H3.
      * rewrite <- map_none_spec in Heqo. rewrite Heqo. simpl. simpl in H8. destruct (i == x) eqn : ?.
        -- simpl. simpl in H8. inversion H8. apply H4 in H10. destruct H10; subst; reflexivity.
        -- simpl in H8. simpl. apply IHBounded2. assert (A:= H8). eapply map_spec_reverse in H8.
           assumption. assumption. apply H2_0. assumption.
        -- apply H2_.
Qed.

(*Specification using Haskell Equality. This requires several lemmas to replace the use
of [subst] and [rewrite].*)

(*Haskell equality version of [oro_Some_l]*)
Lemma sem_haskell_eq_some : forall {a} {b} `{EqLaws a} `{EqLaws b} (a1: a) (m : Map a b) b1 o,
  sem m a1 == Some b1 = true ->
  (sem m a1 ||| o) == Some b1 = true.
Proof.
  intros. destruct (sem m a1) eqn : ?.
  - simpl. assumption.
  - inversion H3.
Qed.

(*Haskell equality version of [oro_None_l]*)
Lemma sem_haskell_eq_none: forall {a} {b} `{EqLaws a} `{EqLaws b} (a1: a) (m : Map a b) o,
  sem m a1 == None = true ->
  (sem m a1 ||| o) == o = true.
Proof.
  intros. destruct (sem m a1) eqn : ?.
  - inversion H3.
  - simpl. apply Eq_Reflexive.
Qed.


Lemma eq_coq_implies_haskell : forall {a} `{EqLaws a} (x y : a),
  x = y -> x == y = true.
Proof.
  intros. subst. apply Eq_Reflexive.
Qed.

(*Haskell equality version of [map_none_spec] *)
Lemma map_none_spec_haskell:
  forall {b} {a} {e} `{Ord e} (H : EqLaws e) `{EqLaws a} `{EqLaws b} (f: e -> a -> b) (m: Map e a) lb ub,
  Bounded m lb ub ->
  (forall i, sem m i == None = true <-> sem (mapWithKey f m) i == None = true).
Proof.
  intros. generalize dependent i. induction H6; intros; split; intros.
  - simpl. apply Eq_Reflexive. 
  - simpl. apply Eq_Reflexive. 
  - simpl. simpl in H10. destruct (sem s1 i) eqn : ?. simpl in H10. inversion H10. simpl in H10.
    destruct (i == x) eqn : ?. simpl in H10. inversion H10. simpl in H10. destruct (sem s2 i) eqn : ?.
    inversion H10. apply eq_coq_implies_haskell in Heqo. apply eq_coq_implies_haskell in Heqo0.
    apply IHBounded1 in Heqo. apply IHBounded2 in Heqo0. rewrite  oro_assoc. simpl.
    apply (sem_haskell_eq_none _  _ (sem (mapWithKey f s2) i)) in Heqo.
    eapply Eq_Transitive. apply Heqo. apply Heqo0.
  - simpl. simpl in H10. destruct (sem (mapWithKey f s1) i) eqn : ?. inversion H10.
    destruct (i == x) eqn : ?. inversion H10. destruct (sem (mapWithKey f s2) i) eqn : ?.
    inversion H10. apply eq_coq_implies_haskell in Heqo. apply eq_coq_implies_haskell in Heqo0.
    simpl. rewrite oro_assoc. simpl. apply IHBounded1 in Heqo. apply IHBounded2 in Heqo0.
    apply (sem_haskell_eq_none  _ _  (sem s2 i)) in Heqo. eapply Eq_Transitive.
    apply Heqo. apply Heqo0.
Qed.

(*Haskell equality version of [map_spec_reverse]*)
Lemma map_spec_haskell_reverse : 
  forall {b} {a} {t}  `{Ord t} (H : EqLaws t) `{EqLaws b} `{EqLaws a}
   (f : t -> a -> b) (m : Map t a) lb ub,
  Bounded m lb ub ->
  (forall x1 x2 y1 y2, x1 == x2 = true -> y1 == y2 = true -> f x1 y1 == f x2 y2 = true) ->
  (forall i v, sem (mapWithKey f m) i == Some v = true -> 
    exists value, sem m i == Some value = true /\ v == f i value = true).
Proof.
  intros.
  generalize dependent i. generalize dependent v. induction H6; intros.
  - inversion H8.
  - simpl in H11. simpl. destruct (sem (mapWithKey f s1) i) eqn : ?.
    + assert ( _GHC.Base.==_ (sem (mapWithKey f s1) i) (Some b0) = true). { rewrite Heqo.
      apply Eq_Reflexive. } apply IHBounded1 in H12. destruct H12. exists x0.
      destruct H12. split. rewrite oro_assoc. apply sem_haskell_eq_some. 
      apply H12. simpl in H11. rewrite simpl_option_some_eq in H11. eapply Eq_Transitive.
      apply Eq_Symmetric. apply H11. apply H13.
    + simpl in H11. apply eq_coq_implies_haskell in Heqo. rewrite <- map_none_spec_haskell in Heqo.
      destruct (sem s1 i). inversion Heqo. simpl. destruct (i == x) eqn : ?. simpl in H11.
      simpl. exists v. split. apply Eq_Reflexive. rewrite simpl_option_some_eq in H11. 
      assert ((f x v) == (f i v) = true). { apply H7. apply Eq_Symmetric. apply Heqb0. 
      apply Eq_Reflexive. } eapply Eq_Transitive. apply Eq_Symmetric. apply H11. apply H12.
      simpl. simpl in H11. apply IHBounded2 in H11. apply H11. apply H1. apply H5. apply H3.
      apply H6_.
Qed. 

(*A substitute for [rewrite]: If we know a1 == a3, and we have a1 == a2 in the goal, 
we can prove a2 == a3 instead*)
Lemma rewrite_eq_haskell : forall {a} `{EqLaws a} a1 a2 a3,
  a1 == a2 = true -> (a1 == a3 = true <-> a2 == a3 = true).
Proof.
  intros; split; intros.
  - eapply Eq_Transitive. apply Eq_Symmetric. apply H1. apply H2.
  - eapply Eq_Transitive. apply H1. apply H2.
Qed.

(*Specification for mapWithKey using Haskell equality*)
Lemma map_spec_haskell:
  forall {b} {a} {e} `{Ord e} (H: EqLaws e) `{EqLaws b} `{EqLaws a} (f : e -> a -> b) (m : Map e a) lb ub,
  Bounded m lb ub ->
  (forall x1 x2 y1 y2, x1 == x2 = true -> y1 == y2 = true -> f x1 y1 == f x2 y2 = true) ->
  (forall i v, sem m i == Some v = true -> sem (mapWithKey f m) i == Some (f i v) = true).
Proof.
  intros.  generalize dependent i. generalize dependent v. induction H6; intros.
  - inversion H8.
  - simpl. simpl in H11. destruct (sem s1 i) eqn : ?.
    * apply eq_coq_implies_haskell in Heqo. apply IHBounded1 in Heqo. rewrite oro_assoc.
      eapply sem_haskell_eq_some. simpl in H11. rewrite simpl_option_some_eq in H11.
      assert (f i a0 == f i v0 = true). { apply H7. apply Eq_Reflexive. apply H11. }
      eapply Eq_Transitive. apply Heqo. rewrite simpl_option_some_eq. apply H12.
    * apply eq_coq_implies_haskell in Heqo. erewrite map_none_spec_haskell in Heqo.
      rewrite oro_assoc. eapply (sem_haskell_eq_none i (mapWithKey f s1)
      (SomeIf (_GHC.Base.==_ i x) (f x v) ||| sem (mapWithKey f s2) i)) in Heqo.
      (*rewrite to make the goal simpler*)
      assert (_GHC.Base.==_ (sem (mapWithKey f s1) i ||| 
      (SomeIf (_GHC.Base.==_ i x) (f x v) ||| sem (mapWithKey f s2) i))
      (Some (f i v0)) = true <-> ((SomeIf (_GHC.Base.==_ i x) (f x v) ||| 
      sem (mapWithKey f s2) i) == Some (f i v0) = true)).
      apply rewrite_eq_haskell. apply Heqo. rewrite H12. clear H12.
      destruct (i == x) eqn : ?. simpl. simpl in H11. rewrite simpl_option_some_eq.
      apply H7. apply Eq_Symmetric. apply Heqb0. rewrite simpl_option_some_eq in H11. apply H11.
      simpl. apply IHBounded2. simpl in H11. apply H11. assumption. assumption. assumption.
      apply H6_.
Qed.

(*Once again. if f is injective, we get a stronger claim*)
Lemma map_spec_haskell_injective:
  forall {b} {a} {e} `{Ord e} (H: EqLaws e) `{EqLaws b} `{EqLaws a} (f : e -> a -> b) (m : Map e a) lb ub,
  Bounded m lb ub ->
  (forall x1 x2 y1 y2, x1 == x2 = true -> y1 == y2 = true -> f x1 y1 == f x2 y2 = true) ->
  (forall k k2 v v2, f k v == f k2 v2 = true -> k == k2 = true /\ v = v2) ->
  (forall i v, sem m i == Some v = true <-> sem (mapWithKey f m) i == Some (f i v) = true).
Proof.
  intros. split.
  - intros. eapply map_spec_haskell; eassumption.
  - generalize dependent i. generalize dependent v. induction H6; intros.
    + inversion H6.
    + simpl in H12. simpl. destruct (sem (mapWithKey f s1) i) eqn : ?.
      * assert (A:= Heqo). apply eq_coq_implies_haskell in Heqo. eapply map_spec_haskell_reverse in Heqo.
        destruct Heqo. destruct H13. simpl in H12. 
        apply eq_coq_implies_haskell in A. assert ( (sem (mapWithKey f s1) i) == (Some (f i v0)) = true).
        { eapply Eq_Transitive. apply A. apply H12. } apply IHBounded1 in H15.
         rewrite oro_assoc. eapply sem_haskell_eq_some. apply H15. assumption. assumption.
        apply H5. apply H6_. assumption.
      * apply eq_coq_implies_haskell in Heqo. rewrite <- map_none_spec_haskell in Heqo.
        destruct (sem s1 i). inversion Heqo. simpl. simpl in H12. destruct (i== x) eqn : ?.
        -- simpl. simpl in H12. apply H8 in H12. destruct H12; subst; apply Eq_Reflexive.
        -- simpl. simpl in H12. apply IHBounded2. apply H12.
        -- assumption.
        -- apply H5.
        -- assumption.
        -- apply H6_.
Qed.

Lemma map_no_key_spec :  forall {e} {a} {b} `{Ord e} (f : a -> b) (m : Map e a),
  Internal.map f m = mapWithKey (fun k v => f v) m.
Proof.
  intros. induction m.
  - simpl. rewrite IHm1. rewrite IHm2. reflexivity.
  - simpl. reflexivity.
Qed.


(** ** [Maps]s with [WF] *)

Definition WFMap  (e : Type) `{Ord e} (a: Type)  : Type := {m : Map e a | WF m}.
Definition pack   {e : Type} {a} `{Ord e} : forall (m : Map e a), WF m -> WFMap e a  := exist _.
Definition unpack {e : Type} {a} `{Ord e} : WFMap e a                  -> Map e a := @proj1_sig _ _.


(** * Type classes *)

(** Because a [Map e a] is only useful if it well-formed, we instantiate
the law classes with a subset type. *)

Require Import Proofs.GHC.Base.

Section TypeClassLaws.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.


(*First, we need lawful [Eq] and [Ord] instances for pairs and lists*)
Global Instance EqLaws_Pair {a} {b} `{EqLaws a} `{EqLaws b} : EqLaws (a * b).
Proof.
  constructor.
  - unfold "==". unfold Eq_pair___. unfold op_zeze____. unfold eq_pair. unfold ssrbool.reflexive.
    intros. destruct x. unfold is_true. rewrite andb_true_iff. split; apply Eq_Reflexive.
  - unfold "==". unfold Eq_pair___. unfold op_zeze____. unfold eq_pair. unfold ssrbool.symmetric.
    intros. destruct x. destruct y. rewrite prop_bool. apply Eq_Tuple_Sym.
  - unfold "==". unfold Eq_pair___. unfold op_zeze____. unfold eq_pair. unfold ssrbool.transitive.
    intros. destruct x. destruct y. destruct z. unfold is_true in *.
    rewrite andb_true_iff in H3. rewrite andb_true_iff in H4. destruct H3. destruct H4.
    eapply Eq_Tuple_Trans. rewrite eq_tuple_prop. split. apply H3. apply H5. rewrite eq_tuple_prop.
    split. apply H4. apply H6.
  - intros. unfold "==", "/=". unfold Eq_pair___. unfold op_zeze____ , op_zsze____ .
    destruct (eq_pair x y). reflexivity. reflexivity.
Qed.

Lemma eq_le : forall {a} `{OrdLaws a} (x y : a),
  x == y = true -> x <= y = true.
Proof.
  intros.
  order a0.
Qed.

(*If a and b are lawful members of [Ord], then so is a * b*)
Instance OrdLaws_Pair {a} {b} `{OrdLaws a} `{OrdLaws b} : OrdLaws (a * b).
Proof.
  constructor.
  - intros. destruct a1. destruct b0. unfold "<=", "==" in *. unfold Ord_pair___, Eq_pair___ in *.
    unfold ord_default, op_zeze____  in *. simpl in *. rewrite andb_true_iff.  rewrite negb_true_iff in *. 
    destruct (compare a2 a1) eqn : ?. destruct (compare b0 b1) eqn : ?.
    rewrite compare_Eq in Heqc. rewrite compare_Eq in Heqc0. split.
    apply Eq_Symmetric. apply Heqc. apply Eq_Symmetric. apply Heqc0.
    inversion Heqc0. inversion H1. rewrite compare_Eq in Heqc. apply Eq_Symmetric in Heqc.
    unfold is_true in Heqc. rewrite <- compare_Eq in Heqc. rewrite Heqc in H2.
    inversion H0. apply Ord_compare_Gt in Heqc0. apply Ord_compare_Lt in Heqc0.
    rewrite Heqc0 in H2. inversion H2. inversion H1. inversion H. rewrite Ord_compare_Gt in Heqc.
    apply Ord_compare_Lt in Heqc. rewrite Heqc in H2. inversion H2.
  - intros. destruct a1. destruct c. destruct b0. unfold "<=" in *. unfold Ord_pair___  in *.
    unfold compare_pair in *. unfold ord_default in *. simpl in *. rewrite negb_true_iff in *.
    repeat (try (destruct (compare a2 a1) eqn : ?); try (destruct (compare b2 b1) eqn : ?);
    try (destruct (compare a3 a1) eqn : ?); try (destruct (compare b0 b1) eqn : ?);
    try (destruct (compare a2 a3) eqn : ?); try (destruct (compare b2 b0) eqn : ?); 
    try (order b); try (order a0)).
  - intros. destruct a1. destruct b0. unfold "<=" in *. unfold Ord_pair___ in *. unfold compare_pair in *.
    unfold ord_default. unfold ord_default in *. simpl. rewrite negb_true_iff. rewrite negb_true_iff.
    destruct (compare a2 a1) eqn : ?. assert (compare a1 a2 = Eq) by (order a0). rewrite H1.
    destruct (compare b0 b1) eqn : ?. left. reflexivity. right. assert (compare b1 b0 <> Lt) by (order b).
    destruct (compare b1 b0). reflexivity. contradiction. reflexivity. left. reflexivity.
    right. destruct (compare a1 a2) eqn : ?. order a0. order a0. reflexivity.
    left. reflexivity.
  - intros. unfold compare.   unfold "<=" in *. unfold Ord_pair___ in *. unfold compare_pair in *.
    unfold ord_default. simpl. rewrite negb_false_iff. destruct a1. destruct b0. 
    split; intros. destruct (compare a1 a2). rewrite H1. reflexivity. reflexivity. inversion H1.
    destruct (compare a1 a2). destruct (compare b1 b0). inversion H1. reflexivity. inversion H1.
    reflexivity. inversion H1.
  - intros. unfold compare. unfold "==". unfold Ord_pair___ , Eq_pair___ . unfold compare_pair,op_zeze____ .
    unfold ord_default, eq_pair. simpl. destruct a1. destruct b0. split; intros. destruct (compare a1 a2) eqn : ?.
    inversion H. rewrite Ord_compare_Eq in Heqc. inversion H0. rewrite Ord_compare_Eq0 in H1. rewrite andb_true_iff.
    split; assumption. inversion H1. inversion H1. rewrite andb_true_iff in H1. destruct H1.
    inversion H. inversion H0. apply Ord_compare_Eq in H1. apply Ord_compare_Eq0 in H2. rewrite H1. assumption.
  - intros. unfold compare. unfold Ord_pair___ , "<=". unfold compare_pair. unfold ord_default. simpl.
    destruct a1. destruct b0. split; intros. rewrite negb_false_iff.  
    destruct (compare a1 a2) eqn : ?. assert (compare a2 a1 = Eq) by (order a0). rewrite H2.
    assert (compare b0 b1 = Lt) by (order b). rewrite H3. reflexivity. inversion H1. inversion H1.
    assert (compare a2 a1 = Lt) by (order a0). rewrite H2. reflexivity.
    rewrite negb_false_iff in H1. destruct (compare a2 a1) eqn : ?.
    assert (compare a1 a2 = Eq) by (order a0). rewrite H2. destruct (compare b0 b1) eqn : ?.
    inversion H1. order b. inversion H1. assert (compare a1 a2 = Gt) by (order a0). rewrite H2.
    reflexivity. inversion H1.
  - intros. unfold "<", "<=". unfold Ord_pair___.  unfold compare_pair; unfold ord_default; simpl.
    rewrite negb_involutive. reflexivity.
  - intros. unfold "<=", ">=". unfold Ord_pair___. unfold compare_pair; unfold ord_default; simpl.
    reflexivity.
  - intros. unfold ">", "<=". unfold Ord_pair___.  unfold compare_pair; unfold ord_default; simpl.
    rewrite negb_involutive. reflexivity.
Qed.


(** ** Verification of [Eq] *)
Global Program Instance Eq_Map_WF `{EqLaws a} : Eq_ (WFMap e a) := fun _ k => k
  {| op_zeze____ := @op_zeze__ (Map e a) _
   ; op_zsze____ := @op_zsze__ (Map e a) _
  |}.

Local Ltac unfold_WFMap_Eq :=
  unfold "_==_", "_/=_", Eq_Map_WF, op_zeze____; simpl;
  unfold "_==_", "_/=_", Eq___Map; simpl;
  unfold Internal.Eq___Map_op_zeze__, Internal.Eq___Map_op_zsze__ ; simpl.

Global Instance EqLaws_Map `{EqLaws a} : EqLaws (WFMap e a).
Proof.
  constructor.
  - unfold_WFMap_Eq. unfold ssrbool.reflexive. intros. unfold is_true. rewrite andb_true_iff.
    split. apply Eq_Reflexive. apply Eq_Reflexive.
  - unfold_WFMap_Eq. unfold ssrbool.symmetric. intros. rewrite prop_bool. split; intros; rewrite andb_true_iff in *.
    + destruct H1. split; apply Eq_Symmetric; assumption.
    + destruct H1. split; apply Eq_Symmetric; assumption.
  - unfold_WFMap_Eq. unfold ssrbool.transitive. intros. unfold is_true in *. rewrite andb_true_iff in *.
    destruct H1. destruct H2. split. eapply Eq_Transitive. apply H1. apply H2. eapply Eq_Transitive.
    apply H3. apply H4.
  - intros. unfold_WFMap_Eq. unfold Internal.Eq___Map_op_zeze__. rewrite negb_involutive . reflexivity.
Qed.

(** ** Verification of [ord] *)
Global Program Instance Ord_Map_WF `{OrdLaws a} : Ord (WFMap e a) := fun _ k => k
  {| op_zlze____ := @op_zlze__ (Map e a) _ _
   ; op_zgze____ := @op_zgze__ (Map e a) _ _
   ; op_zl____ := @op_zl__ (Map e a) _ _
   ; op_zg____ := @op_zg__ (Map e a) _ _
   ; compare__ := @compare (Map e a) _ _
   ; min__ := @min (Map e a) _ _
   ; max__ := @max (Map e a) _ _
  |}.
Next Obligation.
  destruct x. destruct x0. simpl.
  unfold max. unfold Ord__Map. unfold max__. unfold Internal.Ord__Map_max.
   destruct Internal.Ord__Map_op_zlze__; assumption.
Qed.
Next Obligation.
  destruct x. destruct x0. simpl.
  unfold min, Ord__Map, min__, Internal.Ord__Map_min.
  destruct (Internal.Ord__Map_op_zlze__ _ _); assumption.
Qed.


Lemma compare_neq_gt_iff_le {t} `{OrdLaws t} (l1 l2 : t) :
  (compare l1 l2 /= Gt = true) <-> (l1 <= l2) = true.
Proof.
  rewrite Neq_inv, negb_true_iff.
  destruct (_ <= _) eqn:LE; simpl.
  - split; trivial; intros _.
    enough ((compare l1 l2 == Gt) = false <-> compare l1 l2 <> Gt) as OK.
    + now apply OK; rewrite Ord_compare_Gt, LE.
    + now rewrite (ssrbool.rwP (Eq_eq _ Gt)); unfold is_true; rewrite not_true_iff_false.
  - now rewrite <-Ord_compare_Gt in LE; rewrite LE.
Qed.

Lemma WFMap_eq_size_length' (m : WFMap e a) :
  Data.Map.Internal.size (proj1_sig m) = Z.of_nat (Datatypes.length (toAscList (proj1_sig m))).
Proof.
  destruct m as [m WFm]; unfold "==", Eq_Map_WF; simpl.
  rewrite size_size; erewrite size_spec; trivial; exact WFm.
Qed.

Lemma WFMap_eq_size_length (m : WFMap e a) :
  Data.Map.Internal.size (unpack m) = Z.of_nat (Datatypes.length (toAscList (unpack m))).
Proof. apply WFMap_eq_size_length'. Qed.

Local Ltac unfold_WFMap_Ord :=
  unfold "_<=_", "_<_", "_>=_", "_>_", compare, Ord_Map_WF; simpl;
  unfold "_<=_", "_<_", "_>=_", "_>_", compare, Ord__Map; simpl;
  unfold Data.Map.Internal.Ord__Map_op_zlze__, (*Data.Map.Internal.Ord_Map_op_zl__*)
         Data.Map.Internal.Ord__Map_op_zgze__, (*Data.Map.Internal.Ord_Map__op_zg__*)
         Data.Map.Internal.Ord__Map_compare; simpl.

Local Ltac hideToAscList a :=
  let la := fresh "l" a in
  let EQ := fresh "EQ"  in
  remember (toAscList (unpack a)) as la eqn:EQ; try clear a EQ.

Global Instance OrdLaws_Map `{OrdLaws a} : OrdLaws (WFMap e a).
Proof.
  constructor; unfold_WFMap_Eq; unfold_WFMap_Ord.
  - intros a0 b; rewrite !compare_neq_gt_iff_le => LEab LEba.
    generalize (Ord_antisym _ _ LEab LEba) => EQab.
    match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP ssrbool.andP); split; trivial.
    rewrite !WFMap_eq_size_length'; rewrite <-(ssrbool.rwP (Eq_eq _ _)).
    rewrite Nat2Z.inj_iff; apply eqlist_length, EQab.
  - intros a0 b c; rewrite !compare_neq_gt_iff_le; order (list (e * a)).
  - intros a0 b; rewrite !compare_neq_gt_iff_le; apply Ord_total.
  - intros a0 b; rewrite Ord_compare_Lt,Neq_inv,negb_false_iff.
    match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP (Eq_eq _ _)).
    order (list (e * a)).
  - intros a0 b; rewrite Ord_compare_Eq.
    repeat match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP ssrbool.andP), <-(ssrbool.rwP (Eq_eq _ _)).
    split; [intros EQ | intros [LIST EQ]]; rewrite EQ; trivial.
    split; trivial. rewrite !WFMap_eq_size_length'.
    rewrite Nat2Z.inj_iff; apply eqlist_length, EQ. apply Eq_refl.
    apply Eq_refl.
  - intros a0 b; rewrite Ord_compare_Gt,Neq_inv,negb_false_iff.
    match goal with |- context[?b = true] => fold (is_true b) end.
    rewrite <-(ssrbool.rwP (Eq_eq _ _)).
    order (list (e * a)).
  - intros. unfold Internal.Ord__Map_op_zl__, "/=". unfold Internal.Ord__Map_compare, 
    Eq_comparison___. unfold op_zsze____ . rewrite negb_involutive. destruct (compare _ _) eqn : ?;
    unfold eq_comparison; unfold proj1_sig in *; destruct a0; destruct b. 
    assert (compare (toAscList x0) (toAscList x) = Eq) by (order (list (e * a))). rewrite H0.
    reflexivity.  assert (compare (toAscList x0) (toAscList x) = Gt) by (order (list (e * a))).
    rewrite H0. reflexivity. assert (compare (toAscList x0) (toAscList x) = Lt) by (order (list (e * a))).
    rewrite H0. reflexivity.
  - now intros a0 b; rewrite !Neq_inv,                  compare_flip; destruct (compare _ _).
  - intros. unfold Internal.Ord__Map_op_zg__ , "/=". unfold Internal.Ord__Map_compare, Eq_comparison___.
    unfold op_zsze____ . rewrite negb_involutive. reflexivity.
Qed.

(** ** Verification of [Semigroup] *)

Ltac unfold_Monoid_Map :=
  unfold mappend, mconcat, mempty, Monoid__Map, mappend__, mconcat__, mempty__,
         Internal.Monoid__Map_mappend, Internal.Monoid__Map_mconcat, Internal.Monoid__Map_mempty,
         op_zlzlzgzg__,  Semigroup__Map, op_zlzlzgzg____,
         Internal.Semigroup__Map_op_zlzlzgzg__
    in *.

Global Program Instance Semigroup_WF : Semigroup (WFMap e a) := fun _ k => k
  {| op_zlzlzgzg____  := @mappend (Map e a) _ _ |}.
Next Obligation.
  destruct x as [s1 HB1], x0 as [s2 HB2]. simpl.
  unfold_Monoid_Map.
  eapply union_Desc; try eassumption. intuition.
Qed.

(*I'm not sure why, but SemigroupLaws requires that (WFMap e a) be a member of [Eq], so we need
the [EqLaws a] condition*)
Global Instance SemigroupLaws_Map `{EqLaws a} : SemigroupLaws (WFMap e a).
Proof.
  constructor.
  intros.
  destruct x as [s1 HB1], y as [s2 HB2], z as [s3 HB3].
  unfold op_zeze__, Eq_Map_WF, op_zeze____, proj1_sig.
  unfold op_zlzlzgzg__, Semigroup_WF, op_zlzlzgzg____.
  unfold mappend, Monoid__Map, mappend__.
  unfold Internal.Monoid__Map_mappend.
  unfold proj1_sig.
  unfold op_zlzlzgzg__, Semigroup__Map, op_zlzlzgzg____.
  unfold Internal.Semigroup__Map_op_zlzlzgzg__.
  eapply (union_Desc s1 s2); try eassumption. intros s12 Hs12 _ Hsem12.
  eapply (union_Desc s2 s3); try eassumption. intros s23 Hs23 _ Hsem23.
  eapply (union_Desc s1 s23); try eassumption. intros s1_23 Hs1_23 _ Hsem1_23.
  eapply (union_Desc s12 s3); try eassumption. intros s12_3 Hs12_3 _ Hsem12_3.
  rewrite -> weak_equals_spec by eassumption.
  intro i. rewrite Hsem12_3,Hsem1_23,Hsem23,Hsem12.
  rewrite oro_assoc. apply Eq_Reflexive.
Qed.

(*Skipping Monoid for now - causes Coq to freeze*)


End TypeClassLaws.


Section ContainerAxioms.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.
(*The following theorems are the axioms from ContainerAxioms and have no clear analogue in SetProofs*)

(*Simpler definition of lookup*)
Fixpoint lookup' (key : e) (map : Map e a) : option a :=
  match map with
  | Tip => None
  | Bin sz k1 v1 lt rt => match compare key k1 with
                          | Eq => Some v1 
                          | Lt => lookup' key lt 
                          | Gt => lookup' key rt
                          end
 end.  

(*Prove the two definitions are equivalent*)
Lemma lookup_lookup'_equiv : forall  (key : e) (map : Map e a),
    lookup key map = lookup' key map.
Proof.
  intros. induction map.
  - simpl. destruct (compare key k); try (reflexivity); assumption.
  - simpl. reflexivity.
Qed.  

(*This lemma says that if two keys are equal, then the result of member is the same when either is called*)
Lemma member_eq: forall {a : Type} (n : e) (n' : e) (m : Map e a),
  n == n' = true ->
  member n m = member n' m.
Proof.
  intros. induction m.
   - simpl. destruct (compare n k) eqn : E.
    + rewrite Ord_compare_Eq in E.  
      apply Lemmas.Eq_trans_l  with(z:=k) in H.
      rewrite E in H. symmetry in H. rewrite <- Ord_compare_Eq in H.
      rewrite H. reflexivity.
    + rewrite Ord_compare_Lt in E. 
      apply Lemmas.Eq_le_r with(z:=k) in H. rewrite E in H. 
      symmetry in H. rewrite <- Ord_compare_Lt in H. 
      rewrite H. assumption.
    + rewrite Ord_compare_Gt in E. apply Lemmas.Eq_le_l with (z:=k) in H.
      rewrite E in H. symmetry in H. rewrite <- Ord_compare_Gt in H.
      rewrite H. assumption.
  - simpl. reflexivity.
Qed.

(*If we insert a (key, value) in a map, then looking up the key gives the value*)
Lemma lookup_insert : forall `{Eq_ a} `{EqLaws a} (key: e) (value : a) (map : Map e a) lb ub,
  Bounded map lb ub ->
  isLB lb key = true ->
  isUB ub key = true ->
  lookup' key (insert' key value map)  == Some value = true.
Proof.
  intros. pose proof (insert_Desc key value map lb ub) as H5. eapply H5 in H2. 
  unfold Desc in H2. destruct H2 with(P:= fun (map1 : Map e a) => lookup' key map1 == Some value = true).
  - intros. 
  assert (sem s key = (if _GHC.Base.==_ key key then Some value else None) ||| sem map key). { apply H8. }
  rewrite Eq_Reflexive in H9. simpl in H9. eapply lookup_spec in H6. 
  rewrite <- H6 in H9. rewrite <- lookup_lookup'_equiv. rewrite H9. apply Eq_Reflexive.
  - rewrite insert_insert'. reflexivity.
  - assumption.
  - assumption.
Qed.

(*If we lookup a key key1, the result is the same regardless of whether or not we have inserted key2 
(a different key than key1)*)
Lemma lookup_insert_neq : forall `{Eq_ a} `{EqLaws a} (key1: e) (key2: e) (value : a) (map : Map e a) lb ub,
  Bounded map lb ub ->
  isLB lb key2 = true ->
  isUB ub key2 = true ->
  key1 == key2 = false -> 
  lookup' key1 (insert' key2 value map) = lookup' key1 map.
Proof.
  intros. pose proof (insert_Desc key2 value map lb ub) as H6. assert (A := H2). eapply H6 in H2. 
  unfold Desc in H2. destruct H2 with(P:= fun (map1 : Map e a) => lookup' key1 map1 = lookup' key1 map).
  - intros. assert (sem s key1 = (if _GHC.Base.==_ key1 key2 then Some value else None) ||| sem map key1).
    { apply H9. } rewrite H5 in H10. simpl in H10. 
  eapply lookup_spec in H7. rewrite <- H7 in H10. eapply lookup_spec in A. rewrite <- H10 in A.
  rewrite <- lookup_lookup'_equiv. rewrite <- A. rewrite lookup_lookup'_equiv. reflexivity.
  - rewrite insert_insert'. reflexivity.
  - assumption.
  - assumption.
Qed.
 
 
(*States that if we check for key1 in the map in which we have inserted key2, then either
key1 was already in the map, or key1 == key2*)
Lemma member_insert: forall key1 key2 value (map: Map e a) lb ub,
  Bounded map lb ub ->
  isLB lb key2 = true ->
  isUB ub key2 = true ->
  member key1 (insert' key2 value map) = (key1 == key2) || member key1 map. 
Proof.
  intros. pose proof (insert_Desc key2 value map lb ub) as H5. assert (A := H). eapply H5 in H.
  unfold Desc in H. 
  destruct H with(P:= fun (map1 : Map e a) => member key1 map1 = (key1 == key2) || member key1 map).
  - intros. assert(sem s key1 = (if _GHC.Base.==_ key1 key2 then Some value else None) ||| sem map key1).
    { apply H4. } destruct (key1 == key2) eqn : ?. simpl in H6. 
    eapply member_spec in H2. destruct H2. assert (member key1 s = true). { apply H7. exists value.
    assumption. } rewrite H8. simpl. reflexivity. 
    eapply member_spec in H2. destruct H2. simpl in H6. destruct (sem s key1) eqn : E.
    + assert (member key1 s = true). { apply H7. exists a0. assumption. } 
      eapply member_spec in A. destruct A. assert (member key1 map =true). {
      apply H10. exists a0. symmetry in H6. assumption. }
      rewrite H11. simpl. assumption.
    + simpl. eapply member_spec in A. destruct A. assert (member key1 s = false). {
      apply contrapositive in H2. destruct (member key1 s)  eqn : ?. contradiction.
      reflexivity. intro. destruct H10. rewrite H10 in E. discriminate E. }
      assert (member key1 map = false). { apply contrapositive in H8. 
      destruct (member key1 map) eqn : ?. rewrite Heqb0 in H8. contradiction.
      reflexivity. intro. destruct H11. rewrite H11 in H6. discriminate H6. }
      rewrite H10. rewrite H11. reflexivity.
  - rewrite insert_insert'. reflexivity.
  - assumption.
  - assumption.
Qed.

(*If we lookup a key that is deleted, we should get None*)
Lemma delete_eq : forall key (map : Map e a) lb ub,
  Bounded map lb ub ->
  lookup key (delete key map) = None.
Proof.
  intros. pose proof (delete_Desc key map lb ub) as H2. eapply H2 in H. unfold Desc in H.
  destruct H with(P:= fun (map1 : Map e a) => lookup key map1 = None).
  - intros. eapply lookup_spec in H0.
    assert (sem s key = (if _GHC.Base.==_ key key then None else sem map key)). { apply H3. }
    rewrite Eq_Reflexive in H4. rewrite H4 in H0. assumption. 
  - reflexivity.
Qed.

(*If we delete a key key2 and then lookup a different key key1, then it should be the same regardless of
whether or not key2 was deleted.*)
Lemma delete_neq : forall key1 key2 (map : Map e a) lb ub,
  Bounded map lb ub ->
  key1 == key2 = false ->
  lookup key1 (delete key2 map) = lookup key1 map.
Proof.
  intros. pose proof(delete_Desc key2 map lb ub) as H1. assert(A:= H). eapply H1 in H.
  unfold Desc in H. destruct H with(P:= fun (map1 : Map e a) => lookup key1 map1 = lookup key1 map).
  - intros. assert (sem s key1 = (if _GHC.Base.==_ key1 key2 then None else sem map key1)). { apply H4. }
    rewrite H0 in H5. eapply lookup_spec in H2. eapply lookup_spec in A. rewrite H5 in H2.
    rewrite <- H2 in A. symmetry. assumption.
  - reflexivity.
Qed. 

(*Same as above but for member*)
Lemma member_delete_neq: forall key1 key2 (map: Map e a) lb ub,
  Bounded map lb ub ->
  key1 == key2 = false ->
  member key2 (delete key1 map) = member key2 map.
Proof.
  intros. pose proof(delete_Desc key1 map lb ub) as H1. assert(A:=H). eapply H1 in H.
  unfold Desc in H. destruct H with(P:= fun(map1 : Map e a) => member key2 map1 = member key2 map).
  - intros. assert (sem s key2 = (if _GHC.Base.==_ key2 key1 then None else sem map key2)). { apply H4. }
    rewrite Lemmas.Eq_neq_sym in H5. eapply member_spec in H2. eapply member_spec in A.
    destruct (sem s key2)  eqn : ?.
    + destruct A. assert (member key2 map = true). { apply H7. exists a0. symmetry. assumption. }
      destruct H2. assert (member key2 s = true). { apply H9. exists a0. assumption. }
      rewrite H8. rewrite H10. reflexivity.
    + destruct A. destruct H2. apply contrapositive in H6. apply contrapositive in H2.
      destruct (member key2 s) eqn : ?. contradiction. destruct (member key2 map) eqn : ?.
      contradiction. reflexivity. intro. destruct H9. rewrite H9 in Heqo. discriminate Heqo.
      intro. destruct H9. rewrite H9 in H5. discriminate H5.
    + assumption.
 - reflexivity.
Qed.

(*States that if a key is not in the map, then looking it up will give None, and vice versa. *)
Lemma non_member_lookup :
  forall key (map: Map e a) lb ub,
  Bounded map lb ub ->
  (member key map = false) <-> (lookup key map = None).
Proof.
  intros. assert(A:=H). eapply member_spec in H.  destruct (member key map) eqn : E.
  - destruct H. apply H in E. destruct E. eapply lookup_spec in A. rewrite H1 in A.
    rewrite A.  split; intros; discriminate H2. 
  - split; intros. destruct H. apply contrapositive in H1. destruct (lookup key map) eqn :?.
    + unfold not in H1. destruct H1. exists a0. eapply lookup_spec in A.
      rewrite Heqo in A. symmetry. assumption.
    + reflexivity. 
    + intro. rewrite H2 in E. discriminate E.
    + reflexivity.
Qed.

(*If two keys are equal (according to the Eq typeclass), then their values in 
a map are equal*)
Lemma lookup_eq : forall k k' (m : Map e a),
    k == k' = true ->
    lookup k m = lookup k' m.
Proof.
  intros. induction m.
  - simpl. destruct (compare k k0) eqn : E.
    + rewrite Ord_compare_Eq in E. apply Lemmas.Eq_trans_l with(z:=k0) in H .
      rewrite E in H. symmetry in H. rewrite <- Ord_compare_Eq in H.
      rewrite H. reflexivity.
    + rewrite Ord_compare_Lt in E. apply Lemmas.Eq_le_r with (z:= k0) in H.
      rewrite E in H. symmetry in H. rewrite <- Ord_compare_Lt in H.
      rewrite H. assumption.
    + rewrite Ord_compare_Gt in E. apply Lemmas.Eq_le_l with (z:=k0) in H.
      rewrite E in H. symmetry in H. rewrite <- Ord_compare_Gt in H.
      rewrite H. assumption.
  - simpl. reflexivity.
Qed.

(*This follows almost immediately from member_spec*)
Lemma member_lookup : 
  forall key (map: Map e a) lb ub,
  Bounded map lb ub -> 
  (member key map = true) <-> (exists value, lookup key map = Some value).
Proof.
  intros. assert(A:=H). eapply member_spec in A. eapply lookup_spec in H.
  rewrite <- H in A. apply A.
Qed. 

(** ** Verification of [null] *)
Lemma null_empty: 
    @null e a empty = true.
Proof.
  unfold null. simpl. reflexivity.
Qed. 

(*A key is a member of the union of two maps whenever it is a member of at least one of the maps*)
Lemma member_union :
  forall key (map1: Map e a) map2 lb ub,
  Bounded map1 lb ub ->
  Bounded map2 lb ub ->
  member key (union map1 map2) = member key map2 || member key map1.
Proof.
  intros. pose proof(union_Desc map1 map2 lb ub) as H1. assert (A:=H).
  eapply H1 in H. unfold Desc' in H. 
  destruct H with(P:= fun (m : Map e a) => member key m = member key map2 || member key map1).
  - intros. assert (sem s key = sem map1 key ||| sem map2 key). { apply H4. }
    eapply member_spec in H2. eapply member_spec in A.
    unfold oro in H5. destruct (sem map1 key) eqn : ?.
    + assert (member key s = true). { apply H2. exists a0. assumption. }
      assert (member key map1 = true). { apply A. exists a0. assumption. }
      rewrite H6. rewrite H7. symmetry. rewrite orb_true_iff. right. reflexivity.
    + destruct A. destruct H2. eapply member_spec in H0. destruct H0.
      destruct (sem s key) eqn : ?.
      * assert (member key s = true). { apply H8. exists a0. reflexivity. }
        assert (member key map2 = true). { apply H9. exists a0. symmetry. assumption. }
        rewrite H10. rewrite H11. simpl. reflexivity.
      * apply  contrapositive in H6. apply contrapositive in H2. apply contrapositive in H0.
        destruct (member key s). contradiction. destruct (member key map1). contradiction.
        destruct (member key map2). contradiction. simpl. reflexivity.
        intro. destruct H10. rewrite H10 in H5. discriminate H5.
        intro. destruct H10. discriminate H10.
        intro. destruct H10. rewrite H10 in Heqo. discriminate Heqo.
  - reflexivity.
  - assumption.
Qed. 

(*The union of a map with the empty map (in both directions) is itself*)
Lemma union_nil_l : forall (map: Map e a) ub lb,
  Bounded map ub lb ->
  union empty map = map.
Proof.
  intros.  induction H.
  - reflexivity.
  - simpl. destruct s1 eqn : ?. reflexivity.
    destruct s2 eqn : ?. reflexivity.
    unfold insertR. unfold singleton. simpl in H3.
    rewrite H3. reflexivity.
Qed.

Lemma union_nil_r : forall (map: Map e a) ub lb,
  Bounded map ub lb ->
  union map empty = map.
Proof.
  intros. induction H.
  - simpl. reflexivity.
  - simpl. destruct s1. reflexivity. destruct s2. reflexivity. reflexivity.
Qed.

(*The difference between a map and itself is the empty map*)
Lemma difference_self: forall (map: Map e a) lb ub,
  Bounded map lb ub ->
  difference map map = empty.
Proof.
  intros. pose proof(difference_Desc map map lb ub) as H1. assert(A:=H). 
  eapply H1 with(P:= fun(map1 : Map e a) => map1 = empty) in A .
  - assumption.
  - assumption.
  - intros. assert ( forall i, sem s i = None). {
    intros. assert (sem s i = diffo (sem map i) (sem map i)). { apply H4. }
    unfold diffo in H5. destruct (sem map i) eqn : ?.
    assumption. assumption. }
    rewrite sem_false_nil in H5. assumption.
Qed.

(*The difference of a map with the empty map is itself*)
Lemma difference_nil_r: forall `{Eq_ a} `{EqLaws a} (B : Type) (map: Map e a) lb ub,
  Bounded map lb ub ->
  difference map (@empty e B) = map.
Proof.
  intros. inversion H2.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(*The difference of the empty map with any map is empty*)
Lemma difference_nil_l: forall `{Eq_ a} `{EqLaws a} (B : Type) (map: Map e a) lb ub (key : e),
  Bounded map lb ub ->
  difference (@empty e B) map = empty.
Proof.
  intros. inversion H2.
  - simpl. reflexivity.
  - simpl. unfold empty. reflexivity.
Qed.

(*Follows from sem_inside, says that if a key is in a map, it is between the bounds*)
Lemma keys_inside_bounds : forall (map: Map e a) key lb ub,
  Bounded map lb ub ->
  member key map = true ->
  isLB lb key = true /\ isUB ub key = true .
Proof.
  intros. eapply member_spec in H0. destruct H0.
  eapply sem_inside. apply H. apply H0. apply H.
Qed.

(*If a key is in a map, the difference of the singleton map containing only that key
and the original map is empty*)
Lemma difference_Tip_member: forall (map: Map e a) (key :e) lb ub,
  Bounded map lb ub ->
  member key map = true ->
  forall (value : a), difference (singleton key value) map = empty.
Proof.
  intros. assert (A:=H). induction H.
  - discriminate H0.
  - pose proof(difference_Desc (singleton key value) (Bin sz x v s1 s2) lb ub) as H6. 
  eapply H6 with(P:=(fun map1 => map1 = empty)). eapply BoundedBin. apply BoundedTip.
  apply BoundedTip. eapply keys_inside_bounds in H0. destruct H0.
  apply H0. apply A. eapply keys_inside_bounds in H0. destruct H0. apply H7.
  apply A. simpl. reflexivity. simpl. unfold balance_prop. simpl. omega. apply A.
  intros.  eapply member_spec in H0. destruct H0.
  assert (forall i : e, sem s i = None). {
  intros i. assert (sem s i = diffo (sem (singleton key value) i) (sem (Bin sz x v s1 s2) i)). {
  apply H10. } destruct (i == key) eqn : ?.
  + simpl in H11. rewrite Heqb in H11. simpl in H11. 
    assert (sem s1 i = sem s1 key). { apply sem_resp_eq. assumption. } 
    assert (sem s2 i = sem s2 key). { apply sem_resp_eq. assumption. } 
    assert ((i == x) = (key == x)). { eapply Lemmas.Eq_trans_l. assumption. }
    rewrite H12 in H11. rewrite H14 in H11. rewrite H13 in H11. simpl in H0.
    rewrite H0 in H11. simpl in H11. apply H11. 
  + simpl in H11. rewrite Heqb in H11. simpl in H11. unfold diffo in H11. 
    destruct (sem s1 i ||| SomeIf (_GHC.Base.==_ i x) v ||| sem s2 i) eqn : ?.
    assumption. assumption. }
    rewrite <- sem_false_nil. assumption. apply A.
Qed.

(*Might have to put this back in WF
Lemma difference_Tip_non_member: forall `{Eq_ a} `{EqLaws a} (map: Map e a) (key :e) lb ub,
  Bounded map lb ub ->
  isUB ub key = true ->
  isLB lb key = true ->
  member key map = false ->
  forall (value : a), difference (singleton key value) map == (singleton key value) = true.
Proof.
  intros. pose proof(difference_Desc (singleton key value) map lb ub) as H6. 
  assert(A:=H). assert (Bounded (singleton key value) lb ub). { unfold singleton.
  apply BoundedBin. apply BoundedTip. apply BoundedTip. assumption. assumption. simpl.
  reflexivity. simpl. unfold balance_prop. omega. } 
  eapply H6 with(P:=(fun map1 => map1 == singleton key value = true)). assumption.
  assumption. intros.
  simpl in H8.
  pose proof(@member_spec map lb ub key) as H12. assert(A1:=A). apply H12 in A.
  destruct A. apply contrapositive in H14. assert (sem map key = None). {
  unfold not in H14. destruct (sem map key). destruct H14. exists a0. reflexivity.
  reflexivity. }
  assert (forall i, i == key = false -> sem s i = None). {
  intros. assert (sem s i = diffo (SomeIf (_GHC.Base.==_ i key) value ||| None) (sem map i)). {
  apply H11. } rewrite H16 in H17. simpl in H17. unfold diffo in H17. destruct (sem map i); assumption.
  }
  assert (sem s key = Some value). { 
  assert (sem s key = diffo (SomeIf (_GHC.Base.==_ key key) value ||| None) (sem map key)). {
  apply H11. } rewrite Eq_Reflexive in H17. simpl in H17. rewrite H15 in H17. simpl in H17.
  assumption. }
  assert (forall i, sem s i = SomeIf (i == key) value). {
  intros. destruct (i == key) eqn : ?. { simpl. rewrite <- (sem_resp_eq s key).
  assumption. apply Eq_Symmetric. apply Heqb. }
  { simpl. apply H16 in Heqb. assumption. }
  } applyDesc singleton_Desc. assert (forall i, sem s i = sem s0 i). {
    intros. rewrite H18. rewrite Hsem. reflexivity. }
    eapply strong_eq1. apply H8. apply HB. apply H19. intro. rewrite H15 in H5.
    discriminate H5. intros. apply H2.
Qed.*)
End ContainerAxioms.


