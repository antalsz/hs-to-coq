Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.
Require Import Data.Map.Internal.
Require Import Data.Set.Internal.
Import GHC.Num.Notations.
Require Import OrdTactic.
Require Import Psatz.
Require Import Tactics.
Set Bullet Behavior "Strict Subproofs".
Require Import MapProofs.Bounds.
Require Import MapProofs.Tactics.
Require Import SetProofs.
Require Import Coq.Classes.Morphisms.
Require Import MapProofs.UnionIntersectDifferenceProofs.

(*This is a separate file for the proofs that refer to Sets, because many things are named the same*)

Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(*Ltac copied from Set for working with Desc*)
Ltac order_Bounds_set :=
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

Ltac postive_sizes_set :=
  repeat match goal with [ H : Bounded ?s _ _ |- _ ] => pose_new (size_nonneg H) end.

Ltac postive_heights_set :=
  repeat match goal with [ s : Set_ e |- _ ] => pose_new (height_nonneg s) end.

Ltac inside_bounds_set :=
  repeat lazymatch goal with
    | H : Bounded ?s _ _, H2 : sem ?s ?i = true |- _ =>
       apply (sem_inside H) in H2; destruct H2
  end.

(** Solve [isLB] and [isUB] goals.  *)
Ltac solve_Bounds_set := first
  [ eassumption
  | solve [inside_bounds_set; order_Bounds_set]
  | idtac "solve_Bounds gave up"
  ].

(* Solve equations of the form
     forall i, f i = f0 i || f1 i
   possibly using equations from the context.
   Fails if it does not start with [forall i,], but may leave a partially solve goal.
    *)
Ltac f_solver_simple_set  :=
  let i := fresh "i" in 
  intro i;
  try reflexivity; (* for when we have an existential variable *)
  repeat multimatch goal with [ H : (forall i, _) |- _] => specialize (H i) end;
  repeat match goal with [ H : ?f = _ |- context [?f i] ] => rewrite H in *; clear H end;
  simpl sem in *; rewrite ?orb_assoc, ?orb_false_r, ?orb_false_l;
  try reflexivity.

(*
(** This auxillary tactic destructs one boolean atom in the argument *)

Ltac split_bool_go_set expr :=
  lazymatch expr with 
    | true       => fail
    | false      => fail
    | Some _     => fail
    | None       => fail
    | match ?x with _ => _ end => split_bool_go x || (simpl x; cbv match)
    | negb ?x    => split_bool_go x
    | ?x && ?y   => split_bool_go x || split_bool_go y
    | ?x || ?y   => split_bool_go x || split_bool_go y
    | xorb ?x ?y => split_bool_go x || split_bool_go y
    | ?bexpr     => destruct bexpr eqn:?
  end.

(** This auxillary tactic destructs one boolean or option atom in the goal *)

Ltac split_bool :=
  match goal with 
    | |- ?lhs = ?rhs        => split_bool_go lhs || split_bool_go rhs
    (* A bit ad-hoc, could be improved: *)
    | H : ?x || ?y = true  |- _ => split_bool_go x
    | H : ?x || ?y = false |- _ => split_bool_go x
    | H : ?x && ?y = true  |- _ => split_bool_go x
    | H : ?x && ?y = false |- _ => split_bool_go x
  end.
*)

Ltac f_solver_cleanup_set :=
  simpl negb in *;
  rewrite ?andb_true_r, ?andb_true_l, ?andb_false_r, ?andb_false_l,
          ?orb_true_r, ?orb_true_l, ?orb_false_r, ?orb_false_l,
          ?orb_assoc, ?and_assoc in *;
  try congruence;
  repeat lazymatch goal with
    |  H1 : true = true |- _ => clear H1
    |  H1 : true = _    |- _ => symmetry in H1
    |  H1 : false = false |- _ => clear H1
    |  H1 : false = _    |- _ => symmetry in H1
  end;
  try solve [exfalso; inside_bounds; order_Bounds];
  try reflexivity;
  try lazymatch goal with
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = true, H3 : sem ?s ?j = false |- _
      => exfalso; rewrite (sem_resp_eq s i j H1) in H2; congruence
    |  H1 : (?i == ?j) = true , H2 : sem ?s ?i = false, H3 : sem ?s ?j = true |- _
      => exfalso; rewrite (sem_resp_eq s i j H1) in H2; congruence
    |  HProper : Proper ((fun i j : e => i == j = true) ==> eq) ?P,
       H1 : (?i == ?j) = true , H2 : ?P ?i = true, H3 : ?P ?j = false |- _
      => exfalso; rewrite (HProper _ _ H1) in H2; congruence
    |  HProper : Proper ((fun i j : e => i == j = true) ==> eq) ?P,
       H1 : (?i == ?j) = true , H2 : ?P ?i = false, H3 : ?P ?j = true |- _
      => exfalso; rewrite (HProper _ _ H1) in H2; congruence
  end.

Ltac f_solver_step_set := first
  [ split_bool
  | lazymatch goal with H : context [if ?x == ?y then _ else _] |- _
      => destruct (x == y) eqn:?
    end
  | exfalso
  ].

Ltac f_solver_set := f_solver_simple_set; repeat (f_solver_cleanup_set; f_solver_step_set).

(** A variant of [lia] that unfolds a few specific things and knows that
   the size of a well-formed tree is positive. *)
Ltac lia_sizes_set :=
  postive_sizes_set;
  unfold balance_prop_inserted, balance_prop, delta, ratio in *;
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__,
                      Num_Integer__, Ord_Integer___,
                      op_zg____, op_zl____ in *;
  rewrite ?size_size in *;
  rewrite ?size_Bin in *; simpl (size Tip) in *;
  lia.

(** A tactic to solve questions about size. *)
Ltac solve_size_set := first
  [ assumption
  | reflexivity
  | lia_sizes_set
  | idtac "solve_size gave up"
  ].

(** Solve goals of Bounded. Should be back-tracking free, I think. *)
Ltac solve_Bounded_set := eassumption || lazymatch goal with
  | [ |- Bounded Tip _ _ ]
    => apply BoundedTip
  | [ H : Bounded ?s ?lb (Some ?ub) |- Bounded ?s ?lb (Some ?ub') ]
    => apply (Bounded_change_ub _ _ _ _ H); solve_Bounds_set
  | [ H : Bounded ?s (Some ?lb) ?ub  |- Bounded ?s (Some ?lb') ?ub ]
    => apply (Bounded_change_lb _ _ _ _ H); solve_Bounds_set
  | [ H : Bounded ?s ?lb (Some ?ub) |- Bounded ?s ?lb ?ub' ]
    => apply (Bounded_relax_ub _ _ _ _ H); solve_Bounds_set
  | [ H : Bounded ?s (Some ?lb) ?ub  |- Bounded ?s ?lb' ?ub ]
    => apply (Bounded_relax_lb _ _ _ _ H); solve_Bounds_set
  | [ |- Bounded (Bin _ _ _ _) _ _ ]
    => apply BoundedBin;
        [ solve_Bounded_set
        | solve_Bounded_set
        | solve_Bounds_set
        | solve_Bounds_set
        | solve_size_set
        | solve_size_set
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

Ltac solve_Precondition_set := lazymatch goal with
  | |- Bounded _ _ _          => solve_Bounded_set
  | |- isLB _ _ = true        => solve_Bounds_set
  | |- isUB _ _ = true        => solve_Bounds_set
  | |- context [set_size]     => simpl; lia    (* in well-founded recursion *)
  | |- @eq _ ?x ?x            => reflexivity
  | |- @eq Z _ _              => solve_size_set
  | |- context [balance_prop] => solve_size_set
  | |- ?H                     => fail "solve_Precondition does not recognize this goal: " H
  end.

(** For every set in the context, try to see if [lia] knows it is empty. *)
Ltac find_Tip_size :=
  match goal with [ H : Bounded ?s _ _ |- _ ] =>
    assert_new (size s = 0)%Z lia_sizes_set;
    rewrite (size_0_iff_tip H) in *;
    subst s;
    inversion H;
    clear H;
    subst
  end.

Ltac applyDesc_set lem :=
  apply hide;
  eapply lem;
  [ solve_Precondition_set ..
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

Ltac solve_Desc_set :=
 lazymatch goal with
 | |- (Desc _ _ _ _ _)
 => apply showDesc; split; [solve_Bounded_set | split; [solve_size_set | simpl sem; try solve [f_solver_set]]]
 | |- (Desc' _ _ _ _)
 => apply showDesc'; split; [solve_Bounded_set | simpl sem; try solve [f_solver_set]]
 | |- ?P
 => fail "solve_Desc: Goal not a Desc or Desc' proposition: " P
 end.




(** ** Verification of [keysSet] *)
(*Note: this is a Desc for a Set, not a Map*)
Lemma keysSet_Desc: forall (m : Map e a) lb ub,
  MapProofs.Bounds.Bounded m lb ub ->
  Desc (keysSet m) lb ub (MapProofs.Bounds.size m) (fun i => isSome (MapProofs.Bounds.sem m i)).
Proof.
  intros. induction H.
  - simpl. solve_Desc_set.
  - simpl. eapply IHBounded1. intros. eapply IHBounded2. intros. solve_Desc_set.
    rewrite H6. rewrite H9. solve_size. intros. rewrite H7. rewrite H10.
    destruct (Bounds.sem s1 i). reflexivity. destruct (i == x). reflexivity. reflexivity.
Qed.

(** ** Verification of [fromSet] *)
Lemma fromSet_Desc: forall (s: Set_ e) (f: e -> a) lb ub,
  Bounded s lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  MapProofs.Bounds.Desc (fromSet f s) lb ub (size s) (fun i => if sem s i then Some (f i) else None).
Proof.
  intros. induction H.
  - simpl. solve_Desc e.
  - simpl. eapply IHBounded1. intros. eapply IHBounded2. intros. solve_Desc e.
    rewrite H10. rewrite H7. solve_size. intros. rewrite H11. rewrite H8.
    destruct (sem s1 i). reflexivity. destruct (i == x) eqn : ?. simpl. 
    assert (f x = f i). apply H0. order e. rewrite H12. reflexivity. reflexivity.
Qed.

Lemma expand_bounds_l_set : forall {e} `{OrdLaws e} (m: Set_ e) lb x,
  Bounded m lb x ->
  Bounded m None x.
Proof.
  intros. induction H0.
  - constructor.
  - constructor; try (reflexivity); try (assumption).
Qed.

Lemma expand_bounds_r_set : forall {e} `{OrdLaws e} (m: Set_ e) ub x,
  Bounded m x ub ->
  Bounded m x None.
Proof.
  intros. induction H0.
  - constructor.
  - constructor; try (reflexivity); try (assumption).
Qed.

Ltac wf_bounds_set:= eapply expand_bounds_l_set; eapply expand_bounds_r_set; eassumption.
Set Bullet Behavior "Strict Subproofs".

(** ** Verification of [restrictKeys] *)
Lemma restrictKeys_Desc: forall (s: Set_ e) (m : Map e a) lb ub,
  WF s ->
  MapProofs.Bounds.Bounded m lb ub ->
  MapProofs.Bounds.Desc' (restrictKeys m s) lb ub (fun i => if (sem s i) then MapProofs.Bounds.sem m i else None).
Proof.
  intros. revert H. revert s. induction H0; intros.
  - simpl. solve_Desc e. intros. destruct (sem s i); reflexivity.
  - simpl. eapply SetProofs.splitMember_Desc. apply H3. intros. eapply IHBounded1.
    wf_bounds_set. intros. eapply IHBounded2. wf_bounds_set. intros. destruct_ptrEq.
    + destruct s.
      * destruct b. 
        -- solve_Desc e. f_solver e. rewrite H6 in H12. inversion H12.
        -- eapply link2_Desc; try(eassumption). intros. solve_Desc e. f_solver e.
           rewrite H6 in H12. rewrite H12 in H14. inversion H14.
      * solve_Desc e. f_solver e.
    + eapply Bounds.link_Desc. apply H7. apply H10. assumption. assumption. intros.
      eapply link2_Desc; try (eassumption). intros. destruct s.
      * destruct b.
        -- solve_Desc e. f_solver e; try (rewrite H15 in H12; destruct (sem s3 i); inversion H12; 
            reflexivity).
            ++ rewrite H6 in H12. rewrite H15 in H12. inversion H12.
            ++ assert (i > x = true) by solve_Bounds_set. solve_Bounds e.
            ++ assert (i < x = true) by solve_Bounds_set. solve_Bounds e.
            ++ rewrite H6 in H12. rewrite H12 in H15. inversion H15.
        -- solve_Desc e. f_solver e; try (rewrite H18 in H12; destruct (sem s3 i); inversion H12; reflexivity).
            ++ rewrite H6 in H12. rewrite H18 in H12. inversion H12.
            ++ assert (i > x = true) by solve_Bounds_set. solve_Bounds e.
            ++ assert (i < x = true) by solve_Bounds_set. solve_Bounds e.
            ++ rewrite H6 in H12. rewrite H18 in H12. inversion H12.
      * solve_Desc e. f_solver e.
Qed.

(** ** Verification of [withoutKeys] *)

(*These proofs are particularly annoying because the Bounds for sets and maps are technically different,
so solve_Desc and f_solver don't do as much as we would like.*)

Lemma withoutKeys_Desc: forall (s: Set_ e) (m: Map e a) lb ub,
  Bounded s lb ub ->
  MapProofs.Bounds.Bounded m lb ub ->
  MapProofs.Bounds.Desc' (withoutKeys m s) lb ub (fun i => if (sem s i) then None else MapProofs.Bounds.sem m i).
Proof.
  intros. revert H0. revert m. induction H; intros.
  - inversion H0; simpl. solve_Desc e. intros. reflexivity. solve_Desc e. reflexivity.
  - simpl. inversion H5.
    + subst. simpl. solve_Desc e. f_solver e.
    + eapply splitMember_Desc. constructor; try eassumption. intros.
      eapply IHBounded1. apply H15. eapply IHBounded2. apply H16. intros.
      eapply link2_Desc. apply H22. apply H19. assumption. assumption. intros.
      destruct b. 
      * simpl. solve_Desc e. f_solver e; subst; 
        try (assert (i > x  = true) by (solve_Bounds_set); solve_Bounds e). 
        -- rewrite H27 in H21. destruct (sem s2 i). inversion H21.
           assert (i > x = true) by (solve_Bounds e). solve_Bounds_set.
        -- rewrite H27 in H21. destruct (sem s2 i). inversion H21. 
           assert (i > x = true) by (solve_Bounds e). solve_Bounds_set.
        -- rewrite H27 in H21. destruct (sem s2 i). inversion H21. 
           assert (i > x = true) by (solve_Bounds e). solve_Bounds_set.
      * simpl. destruct_ptrEq.
        -- solve_Desc e. f_solver e; subst; 
           try (assert (i > x = true) by (solve_Bounds e); solve_Bounds_set);
           try (assert (i > x = true) by (solve_Bounds_set); solve_Bounds e).
        -- solve_Desc e. f_solver e; intros.
           ++ rewrite H27 in H21. destruct (sem s2 i). inversion H21.
              assert (i > x = true) by (solve_Bounds e). solve_Bounds_set.
           ++ assert (i > x = true) by (solve_Bounds_set). solve_Bounds e.
Qed.

End WF.
