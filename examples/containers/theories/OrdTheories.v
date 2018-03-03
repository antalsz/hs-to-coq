Require Import GHC.Base.
Import Notations.
Require Import GHC.Num.
Import Notations.
Require Import Proofs.GHC.Base.

From mathcomp Require Import ssrbool ssreflect.
Set Bullet Behavior "Strict Subproofs".

Require Import OrderedType.
Require Import OrdTactic.
Require Import Tactics.

Module OrdTheories(E: OrderedType).
  Instance Eq_t : GHC.Base.Eq_ E.t :=
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

  Instance Ord_t : GHC.Base.Ord E.t := GHC.Base.ord_default compare.

  Module OrdFacts := OrderedTypeFacts(E).

  Ltac rewrite_compare_e :=
    rewrite /Base.compare /Ord_t /ord_default /= /compare.

  Definition elt := E.t.

  Lemma elt_eqP { e1 e2 } : reflect (E.eq e1 e2) (e1 GHC.Base.== e2).
  Proof.
    rewrite /_GHC.Base.==_ /Eq_t /=.
    destruct (E.eq_dec e1 e2); constructor; auto.
  Qed.
        
  Lemma elt_ltP { e1 e2 } : reflect (E.lt e1 e2) (e1 GHC.Base.< e2).
  Proof.
    rewrite /_GHC.Base.<_ /Ord_t /ord_default /=.
    rewrite /_GHC.Base.==_ /Eq_comparison___ /= /eq_comparison /compare.
    do 2 destruct_match; constructor; auto.
  Qed.

  Lemma elt_leP { e1 e2 } : reflect (OrdFacts.TO.le e1 e2) (e1 GHC.Base.<= e2).
  Proof.
    rewrite /_GHC.Base.<=_ /Ord_t /ord_default /=.
    rewrite /_GHC.Base.==_ /Eq_comparison___ /= /eq_comparison /compare.
    do 2 destruct_match; constructor; auto;
      rewrite /OrdFacts.TO.le /OrdFacts.TO.eq /OrdFacts.TO.lt;
      intuition; OrdFacts.order.
  Qed.

  Lemma elt_gtP { e1 e2 } : reflect (E.lt e2 e1) (e1 GHC.Base.> e2).
  Proof.
    rewrite /_GHC.Base.>_ /Ord_t /ord_default /=.
    rewrite /_GHC.Base.==_ /Eq_comparison___ /= /eq_comparison /compare.
    do 2 destruct_match; constructor; auto.
  Qed.

  Lemma elt_geP { e1 e2 } : reflect (OrdFacts.TO.le e2 e1) (e1 GHC.Base.>= e2).
  Proof.
    rewrite /_GHC.Base.>=_ /Ord_t /ord_default /=.
    rewrite /_GHC.Base.==_ /Eq_comparison___ /= /eq_comparison /compare.
    do 2 destruct_match; constructor; auto;
      rewrite /OrdFacts.TO.le /OrdFacts.TO.eq /OrdFacts.TO.lt;
      intuition; OrdFacts.order.
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

  Hint Resolve elt_eqP.
  Hint Resolve elt_ltP.
  Hint Resolve elt_gtP.
  Hint Resolve elt_leP.
  Hint Resolve elt_geP.
  Hint Resolve elt_compare_ltP.
  Hint Resolve elt_compare_lt'P.
  Hint Resolve elt_compare_gtP.
  Hint Resolve elt_compare_gt'P.
  Hint Resolve elt_compare_eqP.
  Hint Resolve elt_compare_eq'P.

  Lemma elt_eq : forall e1 e2, E.eq e1 e2 <-> e1 GHC.Base.== e2.
  Proof. move=>e1 e2. apply rwP =>//. Qed.
  
  Lemma elt_lt : forall e1 e2, E.lt e1 e2 <-> e1 GHC.Base.< e2.
  Proof. move=>e1 e2. apply rwP =>//. Qed.

  Lemma elt_gt : forall e1 e2, E.lt e2 e1 <-> e1 GHC.Base.> e2.
  Proof. move=>e1 e2. apply rwP =>//. Qed.

  Lemma elt_le : forall e1 e2, OrdFacts.TO.le e1 e2 <-> e1 GHC.Base.<= e2.
  Proof. move=>e1 e2. apply rwP =>//. Qed.

  Lemma elt_ge : forall e1 e2, OrdFacts.TO.le e2 e1 <-> e1 GHC.Base.>= e2.
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

  Hint Rewrite <- elt_eq : elt_compare.
  Hint Rewrite <- elt_lt : elt_compare.
  Hint Rewrite <- elt_gt : elt_compare.
  Hint Rewrite <- elt_le : elt_compare.
  Hint Rewrite <- elt_ge : elt_compare.
  Hint Rewrite <- elt_compare_lt : elt_compare.
  Hint Rewrite <- elt_compare_gt : elt_compare.
  Hint Rewrite <- elt_compare_eq : elt_compare.

  Instance EqLaws_elt : EqLaws elt.
  Proof.
    constructor.
    - rewrite /ssrbool.reflexive. intros.
      apply /elt_eqP. auto.
    - rewrite /ssrbool.symmetric. intros x y.
      apply /elt_eqP. destruct_match; move: Heq; move /elt_eqP; auto.
    - rewrite /ssrbool.transitive. intros y x z.
      move /elt_eqP => H1 /elt_eqP H2. apply /elt_eqP; OrdFacts.order.
    - intros x y. rewrite /_GHC.Base./=_ /Eq_t /=.
      rewrite negb_involutive. apply /elt_eqP.
      destruct_match; move: Heq; move /elt_eqP; auto.
  Defined.

  (** [rewrite -/is_true] does not work, so we use this: *)
  Ltac rewrite_is_true :=
      match goal with
      | [ |- ?e = true -> _ ] => replace (e = true) with (is_true e) by reflexivity;
                              autorewrite with elt_compare; move=>?
      | [ |- ?e = true] => replace (e = true) with (is_true e) by reflexivity;
                         autorewrite with elt_compare
      end.

  Instance OrdLaws_elt : OrdLaws elt.
  Proof.
    constructor.
    all: repeat match goal with
                | [ |- _ -> _ ] => first [rewrite_is_true | intro]
                end; try rewrite_is_true;
      try OrdFacts.order.
    Local Ltac solve_iff lem:=
      autorewrite with elt_compare;
      split; [intro; apply /lem; OrdFacts.order |
              case /lem; OrdFacts.order].
    all: try solve [autorewrite with elt_compare; split;
                    [(intro; apply /elt_leP; OrdFacts.order) |
                     (move /elt_leP; OrdFacts.order)]].
    all: try solve [autorewrite with elt_compare; split;
                    [(intro; apply /elt_eqP; OrdFacts.order) |
                     (move /elt_eqP; OrdFacts.order)]].
    all: try solve [apply /elt_leP; destruct_match; move: Heq;
                    move /elt_leP; OrdFacts.order].
    - destruct (OrdFacts.lt_total a b) as [|[|]];
        (left + right); solve [rewrite_is_true; OrdFacts.order].
  Defined.
End OrdTheories.

Module CompareTactics.
Ltac destruct_compare :=
  match goal with
  | [ H :context[match (GHC.Base.compare ?a ?b) with _ => _ end] |- _] =>
    let Heq := fresh "Heq" in
    destruct (GHC.Base.compare a b) eqn:Heq=>//;
    autorewrite with elt_compare in Heq
  | [ |- context[match (GHC.Base.compare ?a ?b) with _ => _ end]] =>
    let Heq := fresh "Heq" in
    destruct (GHC.Base.compare a b) eqn:Heq=>//;
    autorewrite with elt_compare in Heq
  end.
End CompareTactics.
