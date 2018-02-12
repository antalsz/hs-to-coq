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
             move: H; do 3 case /andP; 
             move=>Hlo Hhi Hboundl Hboundh
         | [ |- is_true(bounded' _ _ _) ] =>
           rewrite /bounded'
         | [ |- is_true(andb _ _) ] => 
           apply /andP=>//; split=>//
         end; autorewrite with elt_compare in *; eauto.

Lemma bounded_Bin_iff: forall s x l r lo hi,
  (forall lo', lo = Some lo' ->  E.lt lo' x) ->
  (forall hi', hi = Some hi' -> E.lt x hi') ->
  bounded' l lo (Some x) -> bounded' r (Some x) hi ->
  bounded' (Bin s x l r) lo hi.
Proof.
  intros.
  solve_bounded'.
  - destruct lo as [lo'|]; auto.
    rewrite <- partial_lt_eq.
    specialize (H lo').
    apply elt_lt in H; auto.
  - destruct hi as [hi'|]; auto.
    rewrite <- partial_gt_eq.
    specialize (H0 hi').
    apply elt_lt in H0; auto.
Qed.
(*
Ltac solve_bounded' :=
  repeat match goal with
         | [H: is_true (bounded' _ _ _) |- _ ] =>
           move: H; rewrite /bounded'=>?
         | [ |- is_true(bounded' _ _ _) ] =>
           apply bounded_Bin_iff
         | [ |- is_true(andb _ _) ] => 
           apply /andP=>//; split=>//
         end; autorewrite with elt_compare in *; eauto.
*)
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



Lemma ordered'_children : forall s x l r,
    ordered' (Bin s x l r) ->
    ordered' l /\ ordered' r.
Proof.
  split;
    unfold ordered' in *;
    solve_bounded';
    fold bounded' in *.
    eapply bounded_impl_right_None; eauto.
    eapply bounded_impl_left_None; eauto.
  Qed.

Lemma size_irrelevance_in_ordered : forall s1 s2 x l r,
      ordered' (Bin s1 x l r) -> ordered' (Bin s2 x l r).
Proof. move=>s1 s2 x l r. rewrite /ordered; auto. Qed.

Ltac move_wf_back_to_goal :=
    repeat match goal with
           | [Hwf: is_true (WF (Bin ?s ?a ?l ?r)) |- _ ] =>
             move: Hwf
           end.

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

Lemma balanced_children : forall {a} (s1 s2 : Set_ a) l e,
      balanced (Bin l e s1 s2) -> balanced s1 /\ balanced s2.
Proof.
  split; simpl in H; move: H; case: and3P=>//; elim; done.
Qed.

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
  
Lemma WF_children : forall s1 s2 l e, WF (Bin l e s1 s2) -> WF s1 /\ WF s2.
Proof.
  rewrite /WF /valid.
  move=>s1 s2 l e.
  do 2 case /andP.
  move=>Hb Ho Hv;
  split; repeat (apply /andP; split);
    apply balanced_children in Hb;
  apply ordered'_children in Ho;
    apply validsize_children in Hv; intuition.
Qed.

Lemma WF_size_children : forall s1 s2 l e,
    WF (Bin l e s1 s2) -> size s1 + size s2 + 1 = l.
Proof.
  rewrite /WF /valid. move=>s1 s2 l e.
  do 2 case /andP=>//.
  move=>Hb Ho Hv.
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
      rewrite /size. subst. apply IHs1 in H.
      apply IHs2 in H0. omega.
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
Proof.
  move=>t; rewrite /WF /valid; do 2 case /andP=>//.
Qed.

Lemma WF_ordered' : forall t,
    WF t -> ordered' t.
Proof.
  move=>t; rewrite /WF /valid; do 2 case /andP=>//.
Qed.

Lemma WF_validsize : forall t,
    WF t -> validsize t.
Proof.
  move=>t; rewrite /WF /valid; do 2 case /andP=>//.
Qed.

Lemma WF_singleton : forall e,
    WF (singleton e).
Proof.
  intros. rewrite /WF /valid. do 2 apply /andP=>//.
Qed.

Ltac rewrite_size :=
  unfold Size in *;
  repeat match goal with
         | [ |- _ ] => rewrite ![size (Bin _ _ _ _)]/size
         | [ |- _ ] => rewrite ![size Tip]/size
         | [H: context[size (Bin _ _ _ _)] |- _ ] =>
           rewrite ![size (Bin _ _ _ _)]/size in H
         | [H: context[size Tip] |- _ ] =>
           rewrite ![size Tip]/size in H
         end.

Ltac prepare_for_omega :=
  repeat match goal with
         | [H: context[_ <? _] |- _ ] => move: H
         | [H: context[_ <=? _] |- _ ] => move: H
         | [H: _ < _ |- _ ] => move: H
         | [H: _ <= _ |- _ ] => move: H
         | [H: _ > _ |- _ ] => move: H
         | [H: _ >= _ |- _ ] => move: H
           | [H: context[_ =? _] |- _ ] => move: H
           | [H: ?a = ?b |- _ ] =>
             first [match a with
                    | context [_ + _] => idtac
                    end |
                    match b with
                    | context [_ + _] => idtac
                    end ]; move: H
         end; rewrite_size; rewrite_Int;
  rewrite /is_true ?Z.ltb_lt ?Z.ltb_ge ?Z.leb_le ?Z.leb_gt ?Z.eqb_eq.

Ltac rewrite_for_omega :=
  repeat match goal with
         | [H: context[delta] |- _ ] => move: H
         | [H: context[ratio] |- _ ] => move: H
         end; rewrite /delta /ratio; prepare_for_omega.

Ltac derive_constraints_rec Hwf :=
    match type of Hwf with
    | is_true (WF (Bin ?s ?x ?a ?b)) =>
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
      let Hord := fresh "Hord" in
      have Hord: ordered' (Bin s x a b) by
          [apply WF_ordered' in Hwf];
      derive_constraints_rec Hwfl;
      derive_constraints_rec Hwfr
    | is_true (WF ?t) =>
      let Hnonneg := fresh "Hnonneg" in
      have: WF t by [done];
      move /WF_size_nonneg; move=>Hnonneg;
      let Hvs := fresh "Hvs" in
      have Hvs: validsize t by
          [apply WF_validsize in Hwf]
    end.

Ltac derive_validsize :=
  repeat match goal with
    | [H: is_true (validsize (Bin ?s ?x ?l ?r)) |- _ ] =>
      have: validsize (Bin s x l r) by [done];
      apply validsize_children in H; destruct H;
      rewrite /validsize -/local_realsize;
      move /option_int_eqP ->
    | [H: is_true (validsize ?t) |- _ ] =>
      move: H; rewrite /validsize -/local_realsize;
      move /option_int_eqP ->
         end.
  
Ltac derive_constraints :=
  move_wf_back_to_goal;
  repeat match goal with
         | [ |- is_true (WF ?t) -> _ ] =>
           let Hwf := fresh "Hwf" in
           move=>Hwf;
                derive_constraints_rec Hwf
         end; derive_validsize.

Ltac lucky_balanced_solve :=
  derive_constraints;
  subst; rewrite_for_omega; intros; omega.

Lemma lt_dec_eq: forall x y, OrdFacts.lt_dec x y <-> E.lt x y.
Proof.
  split;
    rewrite -partial_lt_eq;
    rewrite -elt_lt; auto.
Qed.


Ltac rewrite_lt_dec:=
  repeat match goal with
    | [H: is_true (is_left (OrdFacts.lt_dec _ _)) |- _ ] =>
      apply lt_dec_eq in H
    | [|- is_true (is_left (OrdFacts.lt_dec _ _))] =>
      rewrite lt_dec_eq
         end.

Ltac solve_lt_dec:=
  rewrite_lt_dec; try OrdFacts.order.

Ltac solve_option_lt_dec:=
  match goal with
  | [|- is_true (match ?g with | _ => _ end )] =>
    match type of g with
    | option _ =>  destruct g; auto;
                  solve_lt_dec
    end
  end.

Lemma balanceL_ordered : forall s (x: elt) (l r : Set_ elt) lo hi,
    WF l ->
    WF r ->
    before_balancedL x l r ->
    bounded' (Bin s x l r) lo hi  ->
    bounded' (balanceL x l r) lo hi .
Proof.
  move=> s x l r f g Hwfl Hwfr.
  destruct r as [sr xr rl rr | ];
    destruct l as [sl xl ll lr | ];
    rewrite /balanceL; rewrite_Int;
      move=>Hbb Hb;
       try solve [solve_bounded'].
  - (** Both [r] and [l] are [Bin]s *)
    destruct_match.
    destruct ll as [sll xll lll llr | ];
      destruct lr as [slr xlr lrl lrr | ];
      try solve [lucky_balanced_solve].
    destruct_match; rewrite_Int;
      solve_bounded'; solve_option_lt_dec.
  - (** [r] is a [Tip] *)
    destruct ll as [sll xll lll llr | ];
      destruct lr as [slr xlr lrl lrr | ];
     try solve [solve_bounded'; solve_option_lt_dec].
    destruct_match; solve_bounded'; solve_option_lt_dec.
Qed.

Definition before_balancedR (x: elt) (l r : Set_ elt) : Prop :=
  (size l + size r <= 2 /\ size l <= 1) \/
  (size r <= delta * size l + 1 /\ size l <= delta * size r).
    
Lemma balanceR_ordered : forall s (x: elt) (l r : Set_ elt) lo hi,
  WF l ->
  WF r ->
  before_balancedR x l r ->
  bounded' (Bin s x l r) lo hi ->
  bounded' (balanceR x l r) lo hi.
Proof.
  move=>s x l r f g Hwfl Hwfr.
  destruct l as [sl xl ll lr | ];
    destruct r as [sr xr rl rr | ];
    rewrite /balanceR; rewrite_Int;
    move=>Hbb Hb;
           try solve [solve_bounded'].
  - (** Both [r] and [l] are [Bin]s *)
      destruct_match; try solve [solve_bounded'].
      destruct rl as [srl xrl rll rlr | ];
        destruct rr as [srr xrr rrl rrr | ];
        try solve [lucky_balanced_solve].
      destruct_match; rewrite_Int;
        solve_bounded'; solve_option_lt_dec.
  - (** [l] is a [Tip] *)
    destruct rl as [srl xrl rll rlr | ];
      destruct rr as [srr xrr rrl rrr | ];
      try solve [solve_bounded'; solve_option_lt_dec].
    destruct_match; solve_bounded'; solve_option_lt_dec.
Qed.

Ltac derive_compare_rec H :=
  match type of H with
  | is_true (andb (andb  (andb _ _) _) _) =>
    let Hc1 := fresh "Hcomp" in
    let Hc2 := fresh "Hcomp" in
    let Hl1 := fresh "Hlb" in
    let Hl2 := fresh "Hlb" in
    move: H; do 3 case /andP=>//;
     rewrite -/bounded';
    move=> Hc1 Hc2 Hl1 Hl2;
          autorewrite with elt_compare in Hc1;
          autorewrite with elt_compare in Hc2;
          derive_compare_rec Hl1;
          derive_compare_rec Hl2
    | is_true (bounded' _ _ _) =>
      idtac
  end.




Ltac derive_compare :=
  repeat match goal with
         | [H: is_true (andb (andb (andb _ _) _) _) |- _] =>
           derive_compare_rec H
         | [H: is_true (bounded' _ _ _) |- _ ] =>
           let Hc1 := fresh "Hcomp" in
             let Hc2 := fresh "Hcomp" in
             let Hl1 := fresh "Hlb" in
             let Hl2 := fresh "Hlb" in
             move: H; rewrite /bounded';
             do 3 case /andP=>//;
                rewrite -/bounded';
             move=> Hc1 Hc2 Hl1 Hl2;
                   autorewrite with elt_compare in Hc1;
                   autorewrite with elt_compare in Hc2
         end.
 
Ltac rel_deriver := eauto 2.

Ltac rel_deriver' := OrdFacts.order.



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
    | [ |- context[Base.compare ?a ?b]] =>
      do [have: E.lt a b by [rel_deriver']
         | have: E.eq a b by [rel_deriver']
         | have: E.lt b a by [rel_deriver']]
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
  repeat (prepare_relations;
          solve_relations;
          try match goal with
              | [ |- context[Base.compare ?a ?b]] =>
                  let H := fresh "Hcomp" in
                  destruct (Base.compare a b) eqn:H;
                  autorewrite with elt_compare in H
              end).


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
      rewrite /balanceR; intros; try solve [solve_realsize].
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
             derive_constraints;
             apply /orP=>//;
                   ((right; apply /andP=>//) + left);
             solve [rewrite_for_omega; omega]
         end;
  try solve [derive_constraints;
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
          try solve [derive_constraints; 
                     rewrite_for_omega; intros; omega].
        destruct_match; rewrite_for_omega; omega.
      + intros. rewrite_size; rewrite_Int; omega.
  - intros. rewrite_size; rewrite_Int; omega.
  - rewrite /balanceL;
        destruct ll as [sll xll lll llr | ];
        destruct lr as [slr xlr lrl lrr | ].
    + destruct_match; intros; rewrite_size; rewrite_Int; omega.
    + intros. derive_constraints;
                destruct Hbalanced; rewrite_for_omega; intros; omega.
      + intros. derive_constraints;
                  destruct Hbalanced; rewrite_for_omega; intros; omega.
      + intros; derive_constraints. move: Hsum.
        rewrite_for_omega. intros; omega.
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
          try solve [derive_constraints; rewrite_for_omega; intros; omega].
        destruct_match; rewrite_for_omega; omega.
      + intros. rewrite_size; rewrite_Int; omega.
    - intros. rewrite_size; rewrite_Int; omega.
    - rewrite /balanceR;
        destruct rl as [srl xrl rll rlr | ];
        destruct rr as [srr xrr rrl rrr | ].
      + destruct_match; intros; rewrite_size; rewrite_Int; omega.
      + intros. derive_constraints; 
        destruct Hbalanced; rewrite_for_omega; intros; omega.
      + intros. derive_constraints; 
        destruct Hbalanced; rewrite_for_omega; intros; omega.
      + intros; derive_constraints. move: Hsum.
        rewrite_for_omega. intros; omega.
    - rewrite_size. do 2 elim. rewrite_Int. reflexivity.
Qed.


Lemma balanceL_balanced: forall (x: elt) (l r : Set_ elt),
      WF l -> WF r ->
      before_balancedL x l r -> balanced (balanceL x l r).
Proof.
  intros x l r Hwfl Hwfr.
  destruct r as [sr xr rl rr | ];
    destruct l as [sl xl ll lr | ];
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
Time Qed. (* Finished transaction in 8.423 secs (8.39u,0.023s) (successful) *)

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
Time Qed. (* Finished transaction in 8.689 secs (8.652u,0.024s) (successful) *)


Lemma balanceL_WF: forall s (x: elt) (l r : Set_ elt),
    WF l -> WF r ->
    before_balancedL x l r ->
    bounded' (Bin s x l r) None None ->
    WF (balanceL x l r).
Proof with auto.
  intros. rewrite /WF /valid'.
  repeat (apply /andP=>//; split).
  - apply balanceL_balanced...
  - unfold ordered'. apply balanceL_ordered with (s:=0)...
  - apply balanceL_validsize...
Qed.

Lemma balanceR_WF: forall s (x: elt) (l r : Set_ elt),
    WF l -> WF r ->
    before_balancedR x l r ->
    ordered' (Bin s x l r) ->
    WF (balanceR x l r).
Proof with auto.
  intros. rewrite /WF /valid.
  repeat (apply /andP=>//; split).
  - apply balanceR_balanced...
  - unfold ordered' in  *. apply balanceR_ordered with (s:=0)...
  - apply balanceR_validsize...
Qed.

Lemma bounded_left_relax : forall s lo hi lo',
    (E.lt lo' lo \/  E.eq lo' lo)  ->
    bounded' s (Some lo) hi ->
    bounded' s (Some lo') hi.
Proof.
  induction s; intros; auto; 
    solve_bounded'.
  destruct H;
    solve_lt_dec.
Qed.

Lemma bounded_right_relax : forall s lo hi hi',
    (E.lt hi hi' \/  E.eq hi' hi)  ->
    bounded' s lo (Some hi) ->
    bounded' s lo (Some hi').
Proof.
  induction s; intros; auto; 
    solve_bounded'.
  destruct H;
    solve_lt_dec.
Qed.

Lemma bounded_rewrite : forall (s1 s2: Set_ elt) l e1 e2 lo hi,
    E.eq e1 e2 -> bounded' (Bin l e1 s1 s2) lo hi ->
    bounded' (Bin l e2 s1 s2) lo hi.
Proof.
  move=>s1 s2 l e1 e2 lo hi Heq.
  rewrite -/bounded'.
  do 3 case /andP=>//; intros.
  repeat (apply /andP=>//; split=>//);
    try solve_option_lt_dec.
  - apply bounded_right_relax with (hi:=e1); auto. 
  - apply bounded_left_relax with (lo:=e1); auto.
Qed.

Lemma insert_prop : forall e s,
    WF s ->
    WF (insert e s) /\
    (size (insert e s) = size s + 1 \/ size (insert e s) = size s).
Proof.
  intros e s.
  induction s.
  - intros H.
    rewrite /insert/=.
    destruct_match; split; derive_constraints.
    + (** s is Bin, e = a, prove: WF (insert e s) *)
      destruct (PtrEquality.ptrEq e a); [assumption|].
        replace (Datatypes.id e) with e; auto.
        apply elt_compare_eq in Heq. move: Hwf.
        rewrite /WF /valid'.
        do 2 case /andP=>//; intros.
        repeat (apply /andP=>//; split=>//).
      * unfold ordered' in b.
        eapply bounded_right_relax;
          try solve [right; apply Heq].
        solve_bounded'.
      * unfold ordered' in b.
        eapply bounded_left_relax;
          try solve [right; apply Heq].
        solve_bounded'.
    + (** prove [size (insert e s) = size s] *)
      destruct_match; [solve [auto]|].
      replace (Datatypes.id e) with e.
      right. rewrite /size=>//. auto.
    + (** s is Bin, e < a, prove: WF (insert e s) *)
      intros. destruct_match.
      apply balanceL_WF with (s:=0); auto.
      * (** WF (insert e s2) *)
          by apply IHs1.
      * (** (insert e s2) and s3 satisfy [before_balancedL]'s
              pre-condbitions. *)
        rewrite -/insert /before_balancedL.
        apply IHs1 in Hwfl; destruct Hwfl.
        (** cases analysis: 
             did we insert an element to s2?  *)
        destruct H0 as [H0 | H0].
        -- (** we did *)
          destruct s2; destruct s3; derive_constraints.
            all: try (rewrite_for_omega; intros; omega).
            all: derive_compare;
                 destruct_match; destruct_match;
                 first
                   [(rewrite_for_omega; intros; omega) |
                    (apply IHs1 in Hwfl;
                     destruct Hwfl as [_ [Hwlf' | Hwlf']];
                     move: Hwlf'; rewrite /insert;
                     move: Heq1 ->; move: Heq2 ->;
                      rewrite_for_omega; intros; omega)].
        -- (** we didn't *)
          derive_constraints; subst.
          rewrite H0.
          destruct Hbalanced;
            (left + right); omega.
      * (** prove [before_ordered] pre-conditions *)
        rewrite -/insert.
        unfold ordered' in *.
        (*move: Hord0.*)
        apply IHs1 in Hwfl.
        destruct Hwfl as [ _ [_ Hord']]
          specialize (Hord' a)
          derive_constraints.
          solve_bounded'.
          ; destruct Hord'.
          apply H=>//. autorewrite with elt_compare in *. auto.
          unfold bounded'
           (*case /andP=>// => _ _ Hlo Hhi.          
          split; [| split; [| split;
                              [| split; [| split]]]]=>//.*)
         
