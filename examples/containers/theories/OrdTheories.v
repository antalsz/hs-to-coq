Require Import GHC.Base.
Import Notations.
Require Import GHC.Num.
Import Notations.

From mathcomp Require Import ssrbool ssreflect.

Require Import OrderedType.
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
End OrdTheories.
