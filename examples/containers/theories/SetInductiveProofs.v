Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import Data.Set.Internal.
Require Import OrdTactic.
Require Import Psatz.
Set Bullet Behavior "Strict Subproofs".


Section WF.
Context (e : Type) {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(* We don’t have a OrdLawful class yet. We need to introduce that,
   add it to the context, and derive all axioms from that.
 *)
Lemma compare_Eq : forall (x y : e),
  compare x y = Eq <-> x == y = true.
Proof. intuition; order e. Qed.
Lemma compare_Lt : forall (x y : e),
  compare x y = Lt <-> x < y = true.
Proof. intuition; order e. Qed.
Lemma compare_Gt : forall (x y : e),
  compare x y = Gt <-> x > y = true.
Proof. intuition; order e. Qed.

Lemma lt_eq_r : forall x y z,
  x < y = true ->
  z == y = true ->
  x < z = true.
Proof. intuition; order e. Qed.

Lemma lt_eq_l : forall x y z,
  x < y = true ->
  z == x = true ->
  z < y = true.
Proof. intuition; order e. Qed.

Lemma lt_not_eq : forall (x y : e),
  x < y = true -> x == y = false.
Proof. intuition; order e. Qed.

Lemma gt_not_eq : forall (x y : e),
 x > y = true -> x == y = false.
Proof. intuition; order e. Qed.


Lemma lt_gt : forall (x y : e), (x > y) = (y < x).
Proof. intros. rewrite eq_iff_eq_true. intuition; order e. Qed.

Lemma lt_trans : forall (x y z : e),
  x < y = true -> y < z = true -> x < z = true.
Proof. intuition; order e. Qed.


(** This is just like size, but with a type signature that does not confuse [lia] *)
Definition size (s : Set_ e) : Z :=
  match s with | Bin sz _ _ _ => sz
               | Tip => 0 end.

Lemma size_size: Internal.size = size.
Proof. reflexivity. Qed.

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
  (sz1 + sz2 <= 1 \/ sz1 <= (delta * sz2) /\ sz2 <= delta * sz1)%Z.

(** This is the low-level, all in one predicate that says:
   - the set is well-formed (balanced, sizes valid, in order)
   - is within the bounds (exclusive)
   - describes the function
*)

Fixpoint sem (s : Set_ e) (i : e) : bool :=
  match s with | Bin _ x s1 s2 => sem s1 i || (i == x) || sem s2 i
               | Tip => false end.

Inductive Bounded : Set_ e -> bound -> bound -> Prop :=
  | BoundedTip : forall lb ub,
    Bounded Tip lb ub
  | BoundedBin :
    forall lb ub,
    forall s1,
    forall s2,
    forall x sz,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true ->
    sz = (1 + size s1 + size s2)%Z ->
    balance_prop (size s1) (size s2) ->
    Bounded (Bin sz x s1 s2) lb ub.

(** There are no values outside the bounds *)
Lemma sem_outside_below:
  forall {s lb ub i},
  Bounded s lb ub ->
  isLB lb i = false ->
  sem s i = false.
Proof.
  intros ???? HD ?.
  induction HD; intros; subst; simpl in *; intuition.
  rewrite H2.
  rewrite IHHD2 by order_Bounds.
  rewrite orb_false_l. rewrite orb_false_r. order_Bounds.
Qed.

Lemma sem_outside_above:
  forall {s lb ub i},
  Bounded s lb ub ->
  isUB ub i = false ->
  sem s i = false.
Proof.
  intros ???? HD ?.
  induction HD; intros; subst; simpl in *; intuition.
  rewrite H2.
  rewrite IHHD1 by order_Bounds.
  rewrite orb_false_l. rewrite orb_false_r. order_Bounds.
Qed.

Lemma sem_inside:
  forall {s lb ub i},
  Bounded s lb ub ->
  sem s i = true ->
  isLB lb i = true /\ isUB ub i = true.
Proof.
  intros ???? HD ?.
  induction HD; intros; subst; simpl in *; rewrite ?orb_true_iff in *; intuition;
  order_Bounds.  
Qed.


(* We use this as a rewrite rule because
   [simpl (size (Bin _ _ _ _ ))]
   simplifies the [ 1 + _ ] which is annoying. *)
Lemma size_Bin: forall sz x (s1 s2 : Set_ e),
  size (Bin sz x s1 s2) = sz.
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
  intros.
  induction H.
  * intuition.
  * postive_sizes;
    rewrite size_Bin in *.
    intuition try (congruence || lia).
Qed.

(* Solve equations of the form
     forall i, f i = f0 i || f1 i
   possibly using equations from the context.
   Fails if it does not start with [forall i,], but may leave a partially solve goal.
    *)
Ltac f_solver_simple  :=
  let i := fresh "i" in 
  intro i;
  try reflexivity; (* for when we have an existential variable *)
  repeat match goal with [ H : (forall i, ?f i = _) |- context [?f i] ] => rewrite H; clear H end;
  simpl sem; rewrite ?orb_assoc, ?orb_false_r, ?orb_false_l;
  try reflexivity.


(** This auxillary tactic destructs one boolean atom in the argument *)

Ltac split_bool_go expr :=
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
    | [ |- ?lhs = ?rhs] => split_bool_go lhs || split_bool_go rhs
  end.
  
Ltac f_solver := f_solver_simple;
  repeat (try solve [exfalso; order_Bounds];
          rewrite ?andb_true_r, ?andb_true_l, ?andb_false_r, ?andb_false_l,
                  ?orb_true_r, ?orb_true_l, ?orb_false_r, ?orb_false_l,
                  ?orb_assoc, ?and_assoc;
          try lazymatch goal with
            | H : Bounded ?s _ _, H2 : sem ?s ?i = true |- _ =>
               apply (sem_inside H) in H2; destruct H2
          end;
          try reflexivity;
          split_bool || exfalso
          ).


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
    simpl in *.
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
    simpl in *.
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


(** In order to stay sane and speed things up, here is
 a tactic that solves [Bounded] goals, which runs 
 the right auxillary tactic on the corresponding goals. *)

Ltac expand_pairs :=
  match goal with
    |- context[let (_,_) := ?e in _] =>
    rewrite (surjective_pairing e)
  end.

(** Solve [isLB] and [isUB] goals.  *)
Ltac solve_Bounds := first
  [ assumption
  | solve [order_Bounds]
  | idtac "solve_Bounds gave up"
  ].

(** A variant of [lia] that unfolds a few specific things and knows that
   the size of a well-formed tree is positive. *)
Ltac lia_sizes :=
  postive_sizes;
  unfold balance_prop, delta, fromInteger, Num_Integer__ in *;
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
  | [ |- Bounded (Bin _ _ _ _) _ _ ]
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


(** A proposition of the form [Desc s lb ub sz f] tells us
  everything we need to know about [s]. Therefore, we
  can use this lemma to replace all occurrences of
    [Bounded s lb ub], [sem s] and [size s]
  (for some concrete, non-variable s) with their actual values. *)
Inductive Foo P Q : Prop -> Prop :=
  FooI : P -> Q -> Foo P Q True.

Definition Desc s lb ub sz f : Prop :=
  Foo (size s = sz) (sem s = f) (Bounded s lb ub).

(** To actually establish [Desc s lb ub sz f], use this lemma. *)
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Lemma showDesc :
  forall s lb ub sz f,
  Bounded s lb ub /\ size s = sz /\ (forall i, sem s i = f i) ->
  Desc s lb ub sz f.
Proof.
  intros. unfold Desc.
  destruct H as [HB [Hsz Hf]].
  rewrite <- Hsz.
  replace f with (sem s) by (extensionality i; apply Hf).
  replace (Bounded s lb ub) with True by (apply propositional_extensionality; tauto).
  eapply FooI; try reflexivity.
Qed.

Lemma Desc_change_f:
  forall s lb ub sz f f',
  (forall i, f' i = f i) ->
  Desc s lb ub sz f' <-> Desc s lb ub sz f.
Proof.
  intros.
  split; intro HD; apply showDesc; induction HD; subst; intuition.
Qed.


Ltac solve_Desc := apply showDesc; split; [solve_Bounded | split; [solve_size | simpl sem; try solve [f_solver]]].


(** And any set that has a bounds is well-formed *)
Definition WF (s : Set_ e) : Prop := Bounded s None None.

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

(* verification of singleton *)

Lemma singleton_Desc:
  forall x lb ub,
  isLB lb x = true ->
  isUB ub x = true ->
  Desc (singleton x) lb ub 1 (fun i => i == x).
Proof.
  intros.

  unfold singleton.
  unfold fromInteger, Num_Integer__.
  solve_Desc.
Qed.

(* Can we abstract over this pattern? *)
Ltac singleton_Desc :=
  lazymatch goal with |- context [Bounded (singleton ?y) ?lb ?ub] =>
    induction (singleton_Desc y lb ub); subst
  end.

Lemma singleton_WF:
  forall y, WF (singleton y).
Proof. intros. unfold WF. destruct (singleton_Desc y None None); try reflexivity. Qed.

(* verification of [balanceL] and [balanceR] *)


Lemma balanceL_Desc:
    forall x s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub  ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) \/
    balance_prop (size s1 - 1)%Z (size s2) /\ (1 <= size s1)%Z  \/
    balance_prop (size s1)%Z (size s2 + 1) ->
    Desc (balanceL x s1 s2) lb ub (1 + size s1 + size s2) (fun i => sem s1 i || (i == x) || sem s2 i).
Proof.
  intros.
  
  unfold balanceL, balance_prop, delta, ratio in *.
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__, Num_Integer__, Ord_Integer___, op_zg____, op_zl____.
  rewrite ?size_size.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try solve [solve_Desc].
Qed.

Lemma balanceR_Desc:
    forall x s1 s2 lb ub,
    Bounded s1 lb (Some x) ->
    Bounded s2 (Some x) ub ->
    isLB lb x = true ->
    isUB ub x = true->
    balance_prop (size s1) (size s2) \/
    balance_prop (size s1) (size s2 - 1)%Z /\ (1 <= size s2)%Z  \/
    balance_prop (size s1 + 1) (size s2) ->
    Desc (balanceR x s1 s2) lb ub (1 + size s1 + size s2) (fun i => sem s1 i || (i == x) || sem s2 i).
Proof.
  intros.

  unfold balanceR, balance_prop, delta, ratio in *.
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__, Num_Integer__, Ord_Integer___, op_zg____, op_zl____.
  rewrite ?size_size.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_sizes]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try solve [solve_Desc].
Qed.

(* verification of member *)

Lemma member_Desc:
 forall {s lb ub i}, Bounded s lb ub -> member i s = sem s i.
Proof.
  intros ???? HB.
  induction HB.
  * simpl. reflexivity.
  * subst; simpl.
    destruct (compare i x) eqn:?.
    + replace (i == x) with true by order_Bounds.
      rewrite orb_true_r.
      reflexivity.
    + replace (i == x) with false by order_Bounds.
      rewrite IHHB1.
      rewrite (sem_outside_below HB2) by order_Bounds.
      rewrite !orb_false_r.
      reflexivity.
    + replace (i == x) with false by order_Bounds.
      rewrite IHHB2.
      rewrite (sem_outside_above HB1) by order_Bounds.
      rewrite orb_false_l.
      reflexivity.
Qed.

(* verification of insert *)

(* The [orig] passing and the local fixpoint in insert is plain ugly, so let’s to this instead *)

Fixpoint insert' (x : e) (s : Set_ e ) : Set_ e :=
  match s with 
    | Tip => singleton x
    | Bin sz y l r => match compare x y with
      | Lt =>
        let l' := insert' x l in
        if PtrEquality.ptrEq l' l then s else balanceL y l' r
      | Gt =>
        let r' := insert' x r in 
        if PtrEquality.ptrEq r' r then s else balanceR y l r'
      | Eq =>
        if PtrEquality.ptrEq x y then s else Bin sz x l r
     end
  end.

Lemma insert_insert' : forall x s, insert x s = insert' x s.
Proof.
  intros.
  unfold insert.
  induction s; simpl.
  * destruct (compare x a); try reflexivity.
    - rewrite IHs1. reflexivity.
    - rewrite IHs2. reflexivity.
  * reflexivity.
Qed.

Lemma insert_Desc:
  forall y s lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insert y s) lb ub (if sem s y then size s else (1 + size s)%Z) (fun i => (i == y) || sem s i).
Proof.
  intros ???? HB HLB HUB.

  rewrite insert_insert'.
  induction HB; intros.
  * simpl.
    apply showDesc.
    induction (singleton_Desc y lb ub); try assumption.
    repeat split; try f_solver.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in *.
      rewrite Heqc.
      rewrite ?orb_true_r, ?orb_true_l.
      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; [| clear Hpe]. 
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        solve_Desc.
      - unfold Datatypes.id.
        solve_Desc.
    + clear IHHB2.
      cbn -[Z.add].

      rewrite (sem_outside_below HB2) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      rewrite ?orb_false_r, ?orb_false_l.

      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; only 2: clear Hpe.
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        rewrite Hpe in *.
        
        assert (Hf' : sem s1 y = true). {
          destruct (sem s1 y) eqn:?; auto; exfalso.
          apply IHHB1.
        }
        rewrite Hf'.
        solve_Desc.
        f_solver_simple.
        (* can be automated from here *)
        assert (i == y = true -> sem s2 y = true -> sem s2 i = true) by admit.
        assert (i == y = true -> sem s1 y = true -> sem s1 i = true) by admit.
        destruct (i == y) eqn:?, (i == x)  eqn:?, (sem s1 i)  eqn:?, (sem s2 i)  eqn:?; 
          intuition congruence.

      - apply showDesc.
        induction (balanceL_Desc x (insert' y s1) s2 lb ub).
        ** repeat split.
           ++ induction IHHB1; [idtac | solve_Bounds | solve_Bounds].
              destruct (sem s1 y); solve_size.
           ++ induction IHHB1; [idtac | solve_Bounds | solve_Bounds].
              revert H1. inversion H4. intros.
              f_solver.
        ** induction IHHB1; [idtac | solve_Bounds | solve_Bounds].
           apply I.
        ** solve_Bounded.
        ** assumption.
        ** assumption.        
        ** induction IHHB1; [idtac | solve_Bounds | solve_Bounds].
           destruct (sem s1 y); solve_size.
    + (* more or less a copy-n-paste from above *)
      edestruct IHHB2 as [IH_Desc [IH_size IHf]]; only 1,2: solve_Bounds; try assumption; try (intro; reflexivity).
      simpl in IHf.

      rewrite (sem_outside_above HB1) by order_Bounds.
      replace (y == x) with false by order_Bounds.
      rewrite ?orb_false_r, ?orb_false_l.

      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; only 2: clear Hpe.
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        rewrite Hpe in IH_size.
        assert (Hf' : sem s2 y = true). {
          destruct (sem s2 y) eqn:?; auto; try lia.
        }
        rewrite Hf'.
        solve_Desc.
        f_solver_simple.
        (* can be automated from here *)
        assert (i == y = true -> sem s2 y = true -> sem s2 i = true) by admit.
        assert (i == y = true -> sem s1 y = true -> sem s1 i = true) by admit.
        destruct (i == y) eqn:?, (i == x)  eqn:?, (sem s1 i)  eqn:?, (sem s2 i)  eqn:?; 
          intuition congruence.

      - eapply balanceR_Desc; try solve_Bounded.
        ** f_solver. 
        ** destruct (sem s2 y); solve_size.
        ** destruct (sem s2 y); solve_size.
Admitted.

(*
Lemma insert_Sem:
  forall y,
  forall s f f',
  Sem s f ->
  (forall i, f' i = (i == y) || f i) ->
  Sem (insert y s) f'.
Proof. intros. eapply insert_Desc; try eassumption; try reflexivity. Qed.

Lemma insert_WF:
  forall y s, WF s -> WF (insert y s).
Proof.
  intros ?? HWF. destruct HWF. eexists.
  eapply insert_Sem. eassumption. reflexivity.
Qed.
*)

(* verification of maxViewSure *)

Lemma maxViewSure_Desc:
  forall sz' sz x s1 s2 lb ub f,
    Bounded (Bin sz' x s1 s2) lb ub ->

    let y := fst (maxViewSure x s1 s2) in
    let r := snd (maxViewSure x s1 s2) in
    (forall i, f i = ((sem s1 i || (i == x) || sem s2 i) && negb (i == y))) ->
    sz = size s1 + size s2 ->
    (* we know that y is in the input, and we actually know more: it is x or in s2 *)
    ((y == x) || sem s2 y) = true /\
     (* These two are obsolete, they follow from the above *)
    isUB ub y = true /\
    isLB lb y = true /\
    Desc r lb (Some y) sz f.
Proof.
  intros sz' sz x s1 s2 lb ub f HB y r  Hf Hsz.
  subst sz.

  (* Get rid of the [f] variable (maybe worth a tactic?) *)
  erewrite Desc_change_f by apply Hf; clear dependent f.

  revert sz' x s1 lb ub HB y r.
  induction s2; intros;subst.
  - clear IHs2_1.
    inversion HB; subst; clear HB.
    inversion H4; subst.
    cbn -[Z.add size] in *. subst y r. expand_pairs. cbn -[Z.add size] in *.

    edestruct IHs2_2 as [Hthere [IHUB [IHLB [IHB [IHsz IHf]]]]]; try eassumption; try reflexivity; subst.
    clear IHs2_2.

    split;[|split;[|split]].
    + rewrite <- !orb_assoc. rewrite Hthere.
      rewrite !orb_true_r. reflexivity.
    + assumption.
    + solve_Bounds.
    + apply balanceL_Desc; try assumption.
      * f_solver.
       * solve_size.
       * solve_size.
  - cbn -[Z.add size] in *; subst y r.
    inversion HB; subst; clear HB.
    rewrite Eq_refl.
    split;[|split;[|split]]; try assumption; try reflexivity.
    solve_Desc.
Qed.

(* verification of minViewSure *)

Lemma minViewSure_Desc:
  forall sz' sz x s1 s2 lb ub f,
    Bounded (Bin sz' x s1 s2) lb ub ->

    let y := fst (minViewSure x s1 s2) in
    let r := snd (minViewSure x s1 s2) in
    (forall i, f i = ((sem s1 i || (i == x) || sem s2 i) && negb (i == y))) ->
    sz = size s1 + size s2 ->
    (* we know that y is in the input, and we actually know more: it is x or in s1 *)
    (sem s1 y || (y == x)) = true /\
     (* These two are obsolete, they follow from the above *)
    isUB ub y = true /\
    isLB lb y = true /\
    Desc r (Some y) ub sz f.
Proof.
  intros sz' sz x s1 s2 lb ub f HB y r  Hf Hsz.
  subst sz.

  (* Get rid of the [f] variable (maybe worth a tactic?) *)
  erewrite Desc_change_f by apply Hf; clear dependent f.

  revert sz' x s2 lb ub HB y r.
  induction s1; intros;subst.
  - clear IHs1_2.
    inversion HB; subst; clear HB.
    inversion H3; subst.
    cbn -[Z.add size] in *. subst y r. expand_pairs. cbn -[Z.add size] in *.

    edestruct IHs1_1 as [Hthere [IHUB [IHLB [IHB [IHsz IHf]]]]]; try eassumption; try reflexivity; subst.
    clear IHs1_1.

    split;[|split;[|split]].
    + rewrite <- orb_assoc. rewrite Hthere.
      rewrite !orb_true_l. reflexivity.
    + solve_Bounds.
    + assumption.
    + apply balanceR_Desc; try assumption.
      * f_solver.
       * solve_size.
       * solve_size.
  - cbn -[Z.add size] in *; subst y r.
    inversion HB; subst; clear HB.
    rewrite Eq_refl.
    split;[|split;[|split]]; try assumption; try reflexivity.
    solve_Desc.
Qed.

(* verification of glue *)

Lemma glue_Desc:
  forall s1 s2 sz lb ub x f,
  Bounded s1 lb (Some x) ->
  Bounded s2 (Some x) ub ->
  isLB lb x = true ->
  isUB ub x = true ->
  balance_prop (size s1) (size s2) ->
  (forall i : e, f i = sem s1 i || sem s2 i) ->
  sz = (size s1 + size s2)%Z ->
  Desc (glue s1 s2) lb ub sz f.
Proof.
  intros ??????? HB1 HB2 ??? Hf ?.
  subst.

  (* Get rid of the [f] variable (maybe worth a tactic?) *)
  erewrite Desc_change_f by apply Hf; clear dependent f.

  inversion HB1; inversion HB2; subst; cbn -[size Z.add]; clear HB1 HB2.
  1-3: solve [solve_Desc|solve_size].
  destruct (Z.ltb_spec (1 + size s4 + size s5) (1 + size s0 + size s3)).
  - expand_pairs.
    rewrite !size_Bin.

    epose proof (maxViewSure_Desc _ _ x0 s0 s3 _ _ _) as Hmvs.
    destruct Hmvs as [Hthere [HUB [HLB [HBounded [Hsize Hf]]]]];
      [solve_Bounded|reflexivity|reflexivity|].

    assert (isLB (Some (fst (maxViewSure x0 s0 s3))) x = true) by assumption.

    eapply balanceR_Desc.
    + eassumption.
    + solve_Bounded.
    + solve_Bounds.
    + solve_Bounds.
    + simpl.
      f_solver_simple. (* a sufficient smart [f_solver] should handle this *)
      destruct (i == fst (maxViewSure x0 s0 s3)) eqn:?.
      * simpl. rewrite andb_false_r, ?orb_true_l.
        admit.
      * simpl. rewrite andb_true_r, ?orb_false_r. reflexivity.
    + solve_size.
    + solve_size.
  - expand_pairs.
    rewrite !size_Bin.

    epose proof (minViewSure_Desc _ _ x1 s4 s5 _ _ _) as Hmvs.
    destruct Hmvs as [Hthere [HUB [HLB [HBounded [Hsize Hf]]]]];
      [solve_Bounded|reflexivity|reflexivity|].

    assert (isUB (Some (fst (minViewSure x1 s4 s5))) x = true) by assumption.

    eapply balanceL_Desc.
    + solve_Bounded.
    + eassumption.
    + solve_Bounds.
    + solve_Bounds.
    + simpl.
      f_solver_simple. (* a sufficient smart [f_solver] should handle this *)
      destruct (i == fst (minViewSure x1 s4 s5)) eqn:?.
      * simpl. rewrite andb_false_r, ?orb_true_r, ?orb_false_r.
        admit.
      * simpl. rewrite andb_true_r, ?orb_false_r, ?orb_assoc. reflexivity.
    + solve_size.
    + solve_size.
Admitted.

From Coq Require Import ssreflect.
Require Import Tactics.


Lemma delete_Desc :
  forall s lb ub sz f x,
  Bounded s lb ub ->
  sz = (if sem s x then (size s - 1) else size s) ->
  (forall i, f i = sem s i && negb (i == x)) ->
  Desc (delete x s) lb ub sz f.
Proof.
  intros ?????? HB ? Hf.
  subst sz.
  (* Get rid of the [f] variable (maybe worth a tactic?) *)
  erewrite Desc_change_f by apply Hf; clear dependent f.

  induction HB; intros; subst.
  - rewrite /delete.
    solve_Desc.
  - rewrite /delete -/delete.
    destruct (compare x x0) eqn:Heq.
    + eapply glue_Desc; eauto.
      * f_solver.
      * simpl sem. rewrite size_Bin.
        replace (x == x0) with true by solve_Bounds.
        rewrite orb_true_r. cbn -[Z.add]. solve_size.
    + destruct IHHB1 as [IHD1 [IHsz1 IHsem1]].
      destruct IHHB2 as [IHD2 [IHsz2 IHsem2]].
      destruct (PtrEquality.ptrEq (delete x s1) s1) eqn:Heq0.
      * apply PtrEquality.ptrEq_eq in Heq0; subst.
        rewrite -> Heq0 in *. clear Heq0.
        simpl sem. rewrite size_Bin.
        assert (Hnot_there: sem s1 x = false)
          by (destruct (sem s1 x); try congruence; lia).
        rewrite Hnot_there.
        replace (x == x0) with false by solve_Bounds.
        rewrite -> (sem_outside_below HB2) by solve_Bounds.
        cbn -[Z.add].
        solve_Desc.
      * eapply balanceR_Desc; try first [eassumption|reflexivity].
        -- f_solver.
        -- destruct (sem s1 x); solve_size.
        -- cbn -[Z.add].
           replace (x == x0) with false  by solve_Bounds.
           rewrite -> (sem_outside_below HB2) by solve_Bounds.
           destruct (sem s1 x); cbn -[Z.add]; solve_size.
    + destruct IHHB1 as [IHD1 [IHsz1 IHsem1]].
      destruct IHHB2 as [IHD2 [IHsz2 IHsem2]].
      destruct (PtrEquality.ptrEq (delete x s2) s2) eqn:Heq0.
      * apply PtrEquality.ptrEq_eq in Heq0; subst.
        rewrite -> Heq0 in *. clear Heq0.
        simpl sem. rewrite size_Bin.
        assert (Hnot_there: sem s2 x = false)
          by (destruct (sem s2 x); try congruence; lia).
        rewrite Hnot_there.
        replace (x == x0) with false by solve_Bounds.
        rewrite -> (sem_outside_above HB1) by solve_Bounds.
        cbn -[Z.add].
        solve_Desc.
      * eapply balanceL_Desc; try first [eassumption|reflexivity].
        -- f_solver.
        -- destruct (sem s2 x); solve_size.
        -- cbn -[Z.add].
           replace (x == x0) with false  by solve_Bounds.
           rewrite -> (sem_outside_above HB1) by solve_Bounds.
           destruct (sem s2 x); cbn -[Z.add]; solve_size.
Qed.
End WF.
