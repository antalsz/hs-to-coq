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

Lemma bounded_Bin_iff: forall s x l r lo hi,
    (match lo with
    | None => True
    | Some lo' => E.lt lo' x
    end) ->
    (match hi with
    | None => True
    | Some hi' => E.lt x hi'
    end) ->
    bounded' l lo (Some x) -> bounded' r (Some x) hi ->
    bounded' (Bin s x l r) lo hi.
Proof.
  intros.
  solve_bounded'.
  - destruct lo as [lo'|]; auto.
    rewrite <- partial_lt_eq.
    apply elt_lt in H.
    auto.
  - destruct hi as [hi'|]; auto.
    rewrite <- partial_gt_eq.
    apply elt_lt in H0.
    auto.
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
      have Hord: ordered (Bin s x a b) by
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

(*
Ltac rewrite_lt_dec:=
  repeat match goal with
    | [H: is_true (OrdFacts.lt_dec _ _) |- _ ] =>
      rewrite -partial_lt_eq in H
    | [|- is_true (OrdFacts.lt_dec _ _)] =>
      rewrite -partial_lt_eq
         end.
*)
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
      destruct lr as [slr xlr lrl lrr | ].
    + destruct_match; rewrite_Int; solve_bounded'.
      * destruct g; auto.
        clear -Hhi1 Hhi.
        rewrite -partial_lt_eq.
        rewrite -partial_lt_eq in Hhi.
        rewrite -partial_lt_eq in Hhi1.
        rewrite -elt_lt.
        apply elt_lt in Hhi.
        apply elt_lt in Hhi1.
        eapply E.lt_trans; eauto.
      * destruct f; auto.
        clear -Hlo1 Hlo2.
        rewrite -partial_lt_eq.
        rewrite -partial_lt_eq in Hlo1.
        rewrite -partial_lt_eq in Hlo2.
        rewrite -elt_lt.
        apply elt_lt in Hlo1.
        apply elt_lt in Hlo2.
        eapply E.lt_trans; eauto.
      * destruct g; auto.
        clear -Hhi2 Hhi.
        rewrite -partial_lt_eq.
        rewrite -partial_lt_eq in Hhi.
        rewrite -partial_lt_eq in Hhi2.
        rewrite -elt_lt.
        apply elt_lt in Hhi.
        apply elt_lt in Hhi2.
        eapply E.lt_trans; eauto.
    +  
      destruct_match; try solve [solve_local_bounded].
      destruct ll as [sll xll lll llr | ];
        destruct lr as [slr xlr lrl lrr | ];
        try solve [lucky_balanced_solve].
      destruct_match; rewrite_Int; solve_local_bounded.
      
  - split; auto.
    intros.
    apply elt_lt.
        rewrite 
        rewrite partial_lt_eq.
        rewrite partial_lt_eq in Hhi.
        clear Hwfl Hwfr Hbb Hlo Hboundl0
              Hboundh0 Hboundl2 Hboundh Hboundl
              Hboundh1.
      destruct_match ; lucky_balanced_solve.
    try solve [solve_bounded'];
    try solve [lucky_balanced_solve].
    destruct_match; rewrite_Int; solve_bounded'.
  - (** [r] is a [Tip] *)
    destruct ll as [sll xll lll llr | ];
      destruct lr as [slr xlr lrl lrr | ];
      try solve [solve_local_bounded].
    destruct_match; solve_local_bounded.
  Time Qed.

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