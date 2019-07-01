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

Definition ando' {b : Type} : option a -> option b -> option a :=
  fun x y => match y with None => None | _ => x end.

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

Lemma Desc'_WF:
  forall s f,
    Desc' s None None f -> WF s.
Proof.
  intros. unfold WF.
  apply H; auto.
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
  forall x (v : a) lb ub,
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

(** ** Verification of [balance] *)
Lemma balance_Desc:
  forall x v s1 s2 lb ub,
  Bounded s1 lb (Some x) ->
  Bounded s2 (Some x) ub ->
  isLB lb x = true ->
  isUB ub x = true ->
  balance_prop (size s1) (size s2)  \/
  balance_prop_inserted (size s2 - 1) (size s1) /\ (1 <= size s2)%Z  \/
  balance_prop (size s1 + 1) (size s2) \/ 
  balance_prop_inserted (size s1 - 1) (size s2) /\ (1 <= size s1)%Z \/
  balance_prop (size s1) (size s2 + 1) ->
  Desc (balance x v s1 s2) lb ub (1 + size s1 + size s2) (fun i => sem s1 i ||| SomeIf (i == x) v ||| sem s2 i).
Proof.
  intros. unfold balance.
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

Lemma balance_noop :
    forall x y s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) ->
    balance x y s1 s2 = Bin (1 + size s1 + size s2) x y s1 s2.
Proof.
  intros.

  unfold balance.
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

End WF.
