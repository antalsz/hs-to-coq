Require Import GHC.Base.
Import Notations.
Require Import GHC.Num.
Import Notations.

Require Import IntToZ.
Require OrdTheories.
Import OrdTheories.CompareTactics.
Require Import Tactics.

Require Import Data.Set.Internal.
Require Import Coq.FSets.FSetInterface.
Require Import SetProofs.
Require Import Omega.

From mathcomp Require Import ssrbool ssreflect.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.


Module SM (E: OrderedType) : WSfun(E).
  Include OrdTheories.OrdTheories E.

  Definition partial_lt (x : elt) : elt -> bool :=
  (fun arg => arg GHC.Base.< x).
  Definition partial_gt  (x : elt) : elt -> bool :=
  (fun arg => arg GHC.Base.> x).
  
  Fixpoint bounded (lo hi: elt -> bool) (t': Set_ elt):=
    match t' with
  | Tip => true
  | Bin _ x l r =>
    andb (lo x)
         (andb (hi x)
                    (andb
                       (bounded lo (partial_lt x) l)
                       (bounded (partial_gt x) hi r)))
  end.

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


(* Well-formedness alternative definition *)


Fixpoint bounded' (t: Set_ elt) (lo hi: option elt): bool :=
  match t with
  | Tip => true
  | Bin _ x l r =>
    match lo with
    | None => true
    | Some lo' => (OrdFacts.lt_dec lo' x)
    end &&
     match hi with
    | None => true
    | Some hi' => (OrdFacts.lt_dec x hi')
    end && 
    bounded' l lo (Some x) && bounded' r (Some x) hi
  end.


Lemma partial_lt_eq: forall x y,
    partial_lt x y = OrdFacts.lt_dec y x.
Proof.
  intros.
  rewrite eq_iff_eq_true.
  destruct (OrdFacts.lt_dec y x) eqn: H.
  - split; auto.
    intros.
    apply elt_lt.
    auto.
  - split; auto.
    move /elt_lt.
    intros.
    auto.
Qed.

Lemma partial_gt_eq: forall x y,
    partial_gt x y = OrdFacts.lt_dec x y.
Proof.
  intros.
  rewrite eq_iff_eq_true.
  destruct (OrdFacts.lt_dec x y) eqn: H.
  - split; auto.
    intros.
    apply elt_lt.
    auto.
  - split; auto.
    move /elt_lt.
    intros.
    auto.
Qed.


Lemma andb_pw: forall a b a' b',
    a=a' -> b=b' ->
    andb a b = andb a' b'.
Proof.
  intros.
  subst.
  eauto.
Qed.

Lemma bounded_alt: forall t l r,
    let fl :=
        match l with
        | None => (fun _ => true)
        | Some l' => (partial_gt l')
        end in
    let fg :=
        match r with
        | None => (fun _ => true)
        | Some r' => (partial_lt r')
        end in
      bounded fl fg t = bounded' t l r.
Proof.
  intros t. simpl.
  induction t; auto.
  intros l r.
  destruct l as [l'|]; destruct r as [r'|]; simpl.
  - rewrite -IHt1 -IHt2 partial_gt_eq partial_lt_eq.
    rewrite andb_assoc.
    intuition.
  - rewrite -IHt1 -IHt2 partial_gt_eq.
    rewrite andb_true_r.
    intuition.
  - simpl.
    rewrite -IHt1 -IHt2 partial_lt_eq.
    intuition.
  - simpl.
    by rewrite -IHt1 -IHt2.
Qed.

Definition ordered' t := bounded' t None None.

Lemma ordered_alt: forall t, ordered t = ordered' t.
Proof.
  intros t.   
  rewrite /ordered'.
  rewrite -bounded_alt.
  rewrite /ordered /bounded /partial_gt /partial_lt.
  reflexivity.
Qed.


 
  Definition WF (s : Set_ elt) := valid s.
  (* Will it be easier for proof if [WF] is an inductive definition? *)
  Definition t := {s : Set_ elt | WF s}.
  Definition pack (s : Set_ elt) (H : WF s): t := exist _ s H.