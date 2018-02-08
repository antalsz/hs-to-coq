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

Definition partial_lt {a} `{GHC.Base.Ord a}
  (x : a) : a -> bool  :=
  (fun arg => arg GHC.Base.< x).
Definition partial_gt {a} `{GHC.Base.Ord a}
           (x : a) : a -> bool :=
  (fun arg => arg GHC.Base.> x).

Module SM (E: OrderedType) : WSfun(E).
Include OrdTheories.OrdTheories E.

Fixpoint bounded (lo hi: elt -> bool) (t': Set_ elt) : bool :=
  match t' with
  | Tip => true
  | Bin _ x l r =>
    andb (lo x)
         (andb (hi x)
               (andb
                  (bounded lo (partial_lt x) l)
                  (bounded (partial_gt x) hi r)))
  end.

Lemma partial_lt_relax : forall x y z,
      E.lt x y \/ E.eq x y ->
      partial_lt x z -> partial_lt y z.
Proof.
  move=>x y z [Hlt | Heq]; rewrite /partial_lt;
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

(* Well-formedness alternative definition *)

Fixpoint bounded' (t: Set_ elt) (lo hi: option elt): bool :=
  match t with
  | Tip => true
  | Bin _ x l r =>
    match lo with
    | None => true
    | Some lo' => OrdFacts.lt_dec lo' x
    end &&
        match hi with
    | None => true
    | Some hi' => OrdFacts.lt_dec x hi'
        end && 
        bounded' l lo (Some x) && bounded' r (Some x) hi
  end.

Lemma andb_pw: forall a b a' b',
    a=a' -> b=b' ->
    andb a b = andb a' b'.
Proof.
  intros.
  subst.
  eauto.
Qed.

Lemma bounded_alt: forall (t: Set_ elt) l r,
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

Lemma ordered_alt: forall t : Set_ elt, ordered  t = ordered' t.
Proof.
  intros t.   
  rewrite /ordered'.
  rewrite -bounded_alt.
  rewrite /ordered /bounded /partial_gt /partial_lt.
  reflexivity.
Qed.

Definition before_balancedL (x: elt) (l r : Set_ elt) : Prop :=
    (size l + size r <= 2 /\ size r <= 1) \/
    (size l <= delta * size r + 1 /\ size r <= delta * size l).

Definition valid' `{Eq_ elt} `{Ord elt} (t : Set_ elt): bool :=
  balanced t && ordered' t && validsize t.

Definition WF (s : Set_ elt) := valid' s.

Ltac solve_bounded' :=
  repeat match goal with
         | [H: is_true (bounded' _ _ _) |- _ ] =>
           move: H; rewrite /bounded'=>?
         | [ H: is_true (andb (andb (andb _ _) _) _) |- _ ] =>
             let Hlo := fresh "Hlo" in
             let Hhi := fresh "Hhi" in
             let Hboundl := fresh "Hboundl" in
             let Hboundh := fresh "Hboundh" in
             move: H; repeat case /andP; 
             move=>Hlo Hhi Hboundl Hboundh
         | [ |- is_true(andb _ _) ] =>
           apply /andP=>//; split=>//
         end; autorewrite with elt_compare in *; eauto.

(* Lemmas about bounded *)

Lemma bounded_impl_left_None : forall t l r,
      bounded' t l r -> bounded' t None r.
Proof.
  induction t; intros; auto.
  solve_bounded'.
Qed.

Lemma bounded_impl_right_None : forall t l r,
      bounded' t l r -> bounded' t l None.
Proof.
  induction t; intros; auto.
  solve_bounded'.
Qed.


 Lemma balanceL_ordered : forall s (x: elt) (l r : Set_ elt) lo hi,
      WF l ->
      WF r ->
      before_balancedL x l r ->
      bounded' (Bin s x l r) lo hi  ->
      bounded' (balanceL x l r) lo hi .
  Proof.
    move=> s x l r lo hi Hwfl Hwfr.
    destruct r as [sr xr rl rr | ];
      destruct l as [sl xl ll lr | ];
      move=>Hbb Hb.
    - 
      destruct lo as [lo'|];
        destruct hi as [hi'|].
      + admit.
      + admit.
      + admit.
      + move: Hb. rewrite /bounded'.
        case /and2P.
        do 6 rewrite andb_assoc.
        case /and3P.
        repeat apply andb_true_l.
        repeat apply andb_true_r.
        
        Check andb_true_iff.
        Check andb_true_l.
        intros && H2]
        repeat rewrite andb_true_l.
        Check  eq_iff_eq_true.
        repeat rewrite eq_iff_eq_true.
        simpl.
        match goal with
           | [H: is_true (bounded' _ _ _) |- _ ] =>
             move: H; rewrite /bounded'=>?
         end.
         
           | [ H: is_true (andb _ (andb _ (andb _ ))) |- _ ] =>
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
           end. autorewrite with elt_compare in *; eauto.
        unfold bounded' in *.
        do 2 rewrite andb_true_r in Hb.
        do 2 rewrite andb_true_l in Hb.
        move : Hb.
        case /and3P.
        case /andP.
        case /andP.
        intros Hb1 Hb2 Hb3 Hb4 Hb5.
        move : Hb4.
        case /andP.
        intros Hb4 Hb6.
        rewrite /balanceL; rewrite_Int.
        
        destruct_match.
        destruct ll as [sll xll lll llr | ];
        destruct lr as [slr xlr lrl lrr | ].
      + destruct_match.
        * destruct lo as [lo'|].
          dest
          simpl in Hb.
      auto.
      try solve [solve_local_bounded].
      destruct ll as [sll xll lll llr | ];
        destruct lr as [slr xlr lrl lrr | ];
        try solve [lucky_balanced_solve].
          
      rewrite /bounded' /balanceL; rewrite_Int.
       
               
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


 
  Definition WF (s : Set_ elt) := valid s.
  (* Will it be easier for proof if [WF] is an inductive definition? *)
  Definition t := {s : Set_ elt | WF s}.
  Definition pack (s : Set_ elt) (H : WF s): t := exist _ s H.