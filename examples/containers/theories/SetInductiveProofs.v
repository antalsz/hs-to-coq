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
    | H : context [isUB ?ub _] |- _ => destruct ub; simpl isUB in *
    | |-  context [isUB ?ub _]      => destruct ub; simpl isUB in *
    | H : context [isLB ?lb _] |- _ => destruct lb; simpl isLB in *
    | |-  context [isLB ?lb _]      => destruct lb; simpl isLB in *
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

Definition Desc : Set_ e -> bound -> bound -> (e -> bool) -> Prop :=
  fun s lb ub f => Bounded s lb ub /\ (forall i, f i = sem s i).

(** For the meaning of a set we do not care about the bounds *)
Definition Sem (s : Set_ e) (f : e -> bool) := Desc s None None f.

(** And any set that has a meaning is well-formed *)
Definition WF (s : Set_ e) : Prop := exists f, Sem s f.

(** There are no values outside the bounds *)
Lemma Desc_outside_below:
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

Lemma Desc_outside_above:
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
Ltac f_solver  :=
  let i := fresh "i" in 
  intro i;
  try reflexivity; (* for when we have an existential variable *)
  repeat match goal with [ H : (forall i, ?f i = _) |- context [?f i] ] => rewrite H; clear H end;
  simpl sem; rewrite ?orb_assoc, ?orb_false_r, ?orb_false_l;
  try reflexivity.

Lemma Bounded_change_ub:
  forall s lb ub ub',
  Bounded s lb (Some ub) ->
  ub' == ub = true ->
  Bounded s lb (Some ub').
Proof.
  intros ???? HD Heq.
  remember (Some ub) as ubo.
  induction HD; subst.
  * apply BoundedTip; auto.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    simpl in *.
    eapply lt_eq_r; eassumption.
Qed.

Lemma Bounded_change_lb:
  forall s lb lb' ub,
  Bounded s (Some lb) ub ->
  lb' == lb = true ->
  Bounded s (Some lb') ub.
Proof.
  intros ???? HD Heq.
  remember (Some lb) as lbo.
  induction HD; subst.
  * apply BoundedTip; reflexivity.
  * intuition.
    eapply BoundedBin; try eassumption; try reflexivity.
    simpl in *.
    eapply lt_eq_l; eassumption.
Qed.

(** In order to stay sane and speed things up, here is
 a tactic that solves [Desc] goals, which runs 
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
Ltac lia_Desc :=
  postive_sizes;
  unfold balance_prop, delta, fromInteger, Num_Integer__ in *;
  rewrite ?size_Bin in *; simpl (size Tip) in *;
  lia.

(** A tactic to solve questions about size. *)
Ltac solve_size := first
  [ assumption
  | reflexivity
  | lia_Desc
  | idtac "solve_size gave up"
  ].

(** Solve goals of Bounded. Should be back-tracking free, I think. *)
Ltac solve_Bounded := eassumption || lazymatch goal with
  | [ |- Bounded Tip _ _ ]
    => apply BoundedTip
  | [ H : Bounded ?s ?lb (Some ?ub), H2 : ?ub' == ?ub = true  |- Bounded ?s ?lb (Some ?ub') ]
    => apply (Bounded_change_ub _ _ _ _ H H2)
  | [ H : Bounded ?s ?lb (Some ?ub), H2 : isUB ?ub' ?ub = true  |- Bounded ?s ?lb ?ub' ]
    => admit
  | [ H : Bounded ?s (Some ?lb) ?ub, H2 : ?lb' == ?lb = true  |- Bounded ?s (Some ?lb') ?ub ]
    => apply (Bounded_change_lb _ _ _ _ H H2)
  | [ H : Bounded ?s (Some ?lb) ?ub, H2 : isLB ?lb' ?lb = true  |- Bounded ?s ?lb' ?ub ]
    => admit
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

Ltac solve_Desc := split; [solve_Bounded | simpl sem; try solve [f_solver] ].


(** For every set in the context, try to see if [lia] knows it is empty. *)
Ltac find_Tip :=
  match goal with [ H : Bounded ?s _ _ |- _ ] =>
    assert_new (size s = 0)%Z lia_Desc;
    rewrite (size_0_iff_tip H) in *;
    subst s;
    inversion H;
    clear H;
    subst
  end.

Require Import Coq.Program.Tactics.

Open Scope Z_scope.

Lemma balanceL_Desc:
    forall lb ub,
    forall s1 f1,
    forall s2 f2,
    forall x f sz,
    Desc s1 lb (Some x) f1 ->
    Desc s2 (Some x) ub f2 ->
    isLB lb x = true ->
    isUB ub x = true->
    (forall i, f i = f1 i || (i == x) || f2 i) ->
    balance_prop (size s1) (size s2) \/
    balance_prop (size s1 - 1)%Z (size s2) /\ (1 <= size s1)%Z  \/
    balance_prop (size s1)%Z (size s2 + 1) ->
    sz = 1 + size s1 + size s2 ->
    Desc (balanceL x s1 s2) lb ub f /\ size (balanceL x s1 s2) = sz.
Proof.
  intros.
  destruct H, H0.

  unfold balanceL, balance_prop, delta, ratio in *.
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__, Num_Integer__, Ord_Integer___, op_zg____, op_zl____.
  rewrite ?size_size.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_Desc]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try solve [split; [solve_Desc | solve_size]].
Qed.


Lemma balanceR_Desc:
    forall lb ub,
    forall s1 f1,
    forall s2 f2,
    forall x f sz,
    Desc s1 lb (Some x) f1 ->
    Desc s2 (Some x) ub f2 ->
    isLB lb x = true ->
    isUB ub x = true->
    (forall i, f i = f1 i || (i == x) || f2 i) ->
    balance_prop (size s1) (size s2) \/
    balance_prop (size s1) (size s2 - 1)%Z /\ (1 <= size s2)%Z  \/
    balance_prop (size s1 + 1) (size s2) ->
    sz = 1 + size s1 + size s2 ->
    Desc (balanceR x s1 s2) lb ub f /\ size (balanceR x s1 s2) = sz.
Proof.
  intros.
  destruct H, H0.

  unfold balanceR, balance_prop, delta, ratio in *.
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__, Num_Integer__, Ord_Integer___, op_zg____, op_zl____.
  rewrite ?size_size.

  repeat lazymatch goal with [ H : Bounded ?s _ _ |- context [match ?s with _ => _ end] ] => inversion H; subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *; simpl sem;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_Desc]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: try solve [split; [solve_Desc | solve_size]].
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
    + replace (i == x) with true by (symmetry; order_Bounds).
      rewrite orb_true_r.
      reflexivity.
    + replace (i == x) with false by (symmetry; order_Bounds).
      rewrite IHHB1.
      rewrite (Desc_outside_below HB2) by order_Bounds.
      rewrite !orb_false_r.
      reflexivity.
    + replace (i == x) with false by (symmetry; order_Bounds).
      rewrite IHHB2.
      rewrite (Desc_outside_above HB1) by order_Bounds.
      rewrite orb_false_l.
      reflexivity.
Qed.

(* Lemma member_Sem:
 forall {s f i}, Sem s f -> member i s = f i.
Proof. intros. eapply member_Desc; eassumption. Qed.
 *)

(* verification of singleton *)
                 
Lemma singleton_Desc:
  forall x lb ub f',
  isLB lb x = true ->
  isUB ub x = true ->
  (forall i, f' i = (i == x)) ->
  Desc (singleton x) lb ub f'.
Proof.
  intros.
  unfold singleton.
  unfold fromInteger, Num_Integer__.
  solve_Desc.
Qed.

Lemma singleton_Sem:
  forall f x,
  (forall i, f i = (i == x)) ->
  Sem (singleton x) f.
Proof. intros. apply singleton_Desc; try eassumption; try reflexivity. Qed.

Lemma singleton_WF:
  forall y, WF (singleton y).
Proof. intros. eexists. eapply singleton_Sem. reflexivity. Qed.


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
  forall y,
  forall s lb ub f f',
  Desc s lb ub f ->
  isLB lb y = true ->
  isUB ub y = true ->
  (forall i, f' i = (i == y) || f i) ->
  Desc (insert y s) lb ub f' /\
  size (insert y s) = (if f y then size s else (1 + size s)%Z).
Proof.
  intros ?????? [HD Hf'] HLB HUB Hf.
  rewrite insert_insert'.
  revert f Hf' f' Hf.
  induction HD; intros.
  * unfold insert, Datatypes.id.
    split.
    + apply singleton_Desc; try assumption; f_solver.
    + rewrite Hf'; reflexivity.
  * subst; cbn -[Z.add].
    simpl sem in Hf'.
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in *.
      replace (f y) with true
        by (rewrite Hf'; rewrite Heqc; rewrite orb_true_r; reflexivity).
      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; [| clear Hpe]. 
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        split; try reflexivity.
        split; [apply BoundedBin|]; try eassumption; try reflexivity.
        f_solver. destruct (i == x), (sem s1 i), (sem s2 i); reflexivity.
      - unfold Datatypes.id.
        split; try reflexivity.
        split; [apply BoundedBin|].
        ** solve_Bounded.
        ** solve_Bounded.
        ** assumption.
        ** assumption.
        ** reflexivity.
        ** solve_size.
        ** f_solver.
           (* Ideally, the f_solver destructs these equalities, and knows that [f] respects them *)
           replace (i == x) with (i == y) by (apply eq_true_iff_eq; split; order e).
           destruct (i == y), (sem s1 i), (sem s2 i); reflexivity.
    + edestruct IHHD1 as [IH_Desc IH_size]; only 1,2: solve_Bounds; try assumption; try (intro; reflexivity).

      rewrite Hf'; setoid_rewrite Hf' in Hf; clear Hf'.
      rewrite (Desc_outside_below HD2) by order_Bounds.
      replace (y == x) with false by (symmetry; solve_Bounds).
      rewrite ?orb_false_r, ?orb_false_l.

      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; only 2: clear Hpe.
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        rewrite Hpe in IH_size.
        assert (Hf' : sem s1 y = true). {
          destruct (sem s1 y) eqn:?; auto; try lia.
        }
        rewrite Hf'.
        split; try reflexivity.
        solve_Desc.
        f_solver.
        (* can be automated from here *)
        assert (i == y = true -> sem s2 y = true -> sem s2 i = true) by admit.
        assert (i == y = true -> sem s1 y = true -> sem s1 i = true) by admit.
        destruct (i == y) eqn:?, (i == x)  eqn:?, (sem s1 i)  eqn:?, (sem s2 i)  eqn:?; 
          intuition congruence.

      - eapply balanceL_Desc;  try solve_Desc; try eassumption.
        ** intro i.
           rewrite Hf.
           rewrite !orb_assoc.
           (* here I can use some tactics from IntSet *)
           destruct (i == y), (i == x); reflexivity.
        ** destruct (sem s1 y); solve_size.
        ** destruct (sem s1 y); solve_size.
    + (* more or less a copy-n-paste from above *)
      edestruct IHHD2 as [IH_Desc IH_size]; only 1,2: solve_Bounds; try assumption; try (intro; reflexivity).

      rewrite Hf'; setoid_rewrite Hf' in Hf; clear Hf'.
      rewrite (Desc_outside_above HD1) by order_Bounds.
      replace (y == x) with false by (symmetry; solve_Bounds).
      rewrite ?orb_false_r, ?orb_false_l.

      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; only 2: clear Hpe.
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        rewrite Hpe in IH_size.
        assert (Hf' : sem s2 y = true). {
          destruct (sem s2 y) eqn:?; auto; try lia.
        }
        rewrite Hf'.
        split; try reflexivity.
        solve_Desc.
        f_solver.
        (* can be automated from here *)
        assert (i == y = true -> sem s2 y = true -> sem s2 i = true) by admit.
        assert (i == y = true -> sem s1 y = true -> sem s1 i = true) by admit.
        destruct (i == y) eqn:?, (i == x)  eqn:?, (sem s1 i)  eqn:?, (sem s2 i)  eqn:?; 
          intuition congruence.
Admitted.

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

(* verification of maxViewSure *)

Lemma maxViewSure_Desc:
  forall sz x l r lb ub f f',
    Desc (Bin sz x l r) lb ub f ->
    let y := fst (maxViewSure x l r) in
    (forall i, f' i = (f i && negb (i == y))) ->
    f y = true /\
    isUB ub y = true /\
    isLB lb y = true /\
    Desc (snd (maxViewSure x l r)) lb (Some y) f' /\
    size (snd (maxViewSure x l r)) = sz - 1%Z.
Proof.
  intros sz x l r.
  revert sz x l.
  induction r; intros sz x l lb ub f f' HD.
  - destruct HD as [HD Hf]; inversion HD; subst; clear HD. intros.
    edestruct IHr2 as [Hf1 [Hub1 [Hlb1 [HD1 Hsz1]]]];
      [solve_Desc |intro;reflexivity | ].
    clear IHr1 IHr2.
    inversion H4; subst; clear H4.
    subst y.
    cbn -[Z.add size].
    expand_pairs.
    cbn -[Z.add size].
    split; only 2: split; only 3: split.
    + simpl in Hf1.
      rewrite Hf. simpl.
      rewrite !orb_true_iff in Hf1. rewrite !orb_true_iff.
      intuition.
    + solve_Bounds. 
    + simpl isLB in *.
      solve_Bounds.
    + eapply balanceL_Desc; try eassumption. 
      * solve_Desc.
      * f_solver. simpl.
        expand_pairs. simpl.
        destruct (i == (fst (maxViewSure a r1 r2))) eqn:?.
        -- simpl.
           rewrite (Desc_outside_above H3) by order_Bounds.
           replace (i == x)  with false by (symmetry; solve_Bounds).
           reflexivity.
        -- simpl. rewrite !andb_true_r.
           repeat rewrite orb_assoc.
           reflexivity.
      * solve_size.
      * solve_size.
  - destruct HD as [HD Hf]; inversion HD; subst; clear HD.
    cbn -[Z.add]. intro Hf'.
    split; only 2: split; only 3: split; only 4: split.
    + rewrite Hf. simpl.
      rewrite Eq_refl.
      rewrite ?orb_true_r, ?orb_true_l.
      reflexivity.
    + solve_Bounded.
    + solve_Bounded.
    + solve_Desc.
      f_solver. destruct (i == x) eqn:?, (sem l i) eqn:?; try reflexivity; exfalso.
      rewrite (Desc_outside_above H3) in Heqb0. congruence.
      order_Bounds.
    + solve_size.
Qed.

(* verification of minViewSure *)

Lemma minViewSure_Desc:
  forall sz x l r lb ub f f',
    Desc (Bin sz x l r) lb ub f ->
    let y := fst (minViewSure x l r) in
    (forall i, f' i = (negb (i == y) && f i)) ->
    f y = true /\
    isUB ub y = true /\
    isLB lb y = true /\
    Desc (snd (minViewSure x l r)) (Some y) ub f' /\
    size (snd (minViewSure x l r)) = sz - 1%Z.
Proof.
Admitted.

(* verification of glue *)

Lemma glue_Desc:
  forall s1 s2 lb ub x f1 f2 f,
  Desc s1 lb (Some x) f1 ->
  Desc s2 (Some x) ub f2 ->
  isLB lb x = true ->
  isUB ub x = true ->
  balance_prop (size s1) (size s2) ->
  (forall i : e, f i = f1 i || f2 i) ->
  Desc (glue s1 s2) lb ub f /\
  size (glue s1 s2) = (size s1 + size s2)%Z.
Proof.
  intros ???????? [HD1 Hf1] [HD2 Hf2]. intros.
  inversion HD1; inversion HD2; subst; cbn -[size Z.add].
  1-3: solve [split; [solve_Desc|solve_size]].
  destruct (Z.ltb_spec (1 + size s4 + size s5) (1 + size s0 + size s3)).
  - expand_pairs.
    rewrite !size_Bin.
    (* epose proof (maxViewSure_Desc _ x0 s0 s3 lb (Some x)) as Hm. *)
    eapply balanceR_Desc with (f2:=f2).
    + eapply maxViewSure_Desc.
      * solve_Desc.
      * f_solver.
    + assert (isUB (Some x) (fst (maxViewSure x0 s0 s3)) = true).
      { eapply maxViewSure_Desc. solve_Desc. f_solver. }
      assert (isLB (Some (fst (maxViewSure x0 s0 s3))) x = true) by assumption.
      solve_Desc.
    + eapply maxViewSure_Desc. solve_Desc. f_solver.
    + assert (isUB (Some x) (fst (maxViewSure x0 s0 s3)) = true).
      { eapply maxViewSure_Desc. solve_Desc. f_solver. }
      admit.
    + set ( y := fst (maxViewSure x0 s0 s3)).
      assert (f1 y = true) by admit.
      admit.
    + admit.
    + admit.
  - admit.
Admitted.
  
End WF.
