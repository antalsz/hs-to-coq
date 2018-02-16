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
Inductive Desc : Set_ e -> bound -> bound -> (e -> bool) -> Prop :=
| DescTip : forall lb ub f,
    (forall i, f i = false) ->
    Desc Tip lb ub f
  | DescBin :
    forall lb ub,
    forall s1 f1,
    forall s2 f2,
    forall x sz f,
    Desc s1 lb (Some x) f1 ->
    Desc s2 (Some x) ub f2 ->
    isLB lb x = true ->
    isUB ub x = true ->
    sz = (1 + size s1 + size s2)%Z ->
    balance_prop (size s1) (size s2) ->
    (forall i, f i = (f1 i || (i == x) || f2 i)) ->
    Desc (Bin sz x s1 s2) lb ub f.

(** For the meaning of a set we do not care about the bounds *)
Definition Sem (s : Set_ e) (f : e -> bool) := Desc s None None f.

(** And any set that has a meaning is well-formed *)
Definition WF (s : Set_ e) : Prop := exists f, Sem s f.

Lemma Desc_change_f:
  forall {s lb ub f f'},
  Desc s lb ub f ->
  (forall i, f' i = f i) ->
  Desc s lb ub f'.
Proof.
  intros ????? HD Hf.
  induction HD.
  * apply DescTip. intro i. rewrite Hf, H. reflexivity.
  * eapply DescBin; try eassumption. intro i. rewrite Hf, H3. reflexivity.
Qed.

(** There are no values outside the bounds *)
Lemma Desc_outside_below:
  forall {s lb ub f i},
  Desc s lb ub f ->
  isLB lb i = false ->
  f i = false.
Proof.
  intros ????? HD ?.
  induction HD; intros; subst; simpl in *; intuition.
  rewrite H4.
  rewrite H2.
  rewrite IHHD2 by order_Bounds.
  rewrite orb_false_l. rewrite orb_false_r. order_Bounds.
Qed.

Lemma Desc_outside_above:
  forall {s lb ub f i},
  Desc s lb ub f ->
  isUB ub i = false ->
  f i = false.
Proof.
  intros ????? HD ?.
  induction HD; intros; subst; simpl in *; intuition.
  rewrite H4.
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
  forall {s lb ub f},
  Desc s lb ub f -> (0 <= size s)%Z.
Proof.
  intros ???? HD.
  induction HD.
  * simpl. lia.
  * simpl. lia.
Qed.


Ltac postive_sizes :=
  repeat match goal with [ H : Desc ?s _ _ _ |- _ ] => pose_new (size_nonneg H) end.

Lemma size_0_iff_tip:
  forall {s lb ub f},
  Desc s lb ub f -> (size s = 0)%Z <-> s = Tip.
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
  rewrite ?orb_assoc, ?orb_false_r, ?orb_false_l;
  try reflexivity.

Lemma Desc_change_ub:
  forall s lb ub ub' f,
  Desc s lb (Some ub) f ->
  ub' == ub = true ->
  Desc s lb (Some ub') f.
Proof.
  intros ????? HD Heq.
  remember (Some ub) as ubo.
  induction HD; subst.
  * apply DescTip; auto.
  * intuition.
    eapply DescBin; try eassumption; try reflexivity.
    simpl in *.
    eapply lt_eq_r; eassumption.
Qed.

Lemma Desc_change_lb:
  forall s lb lb' ub f,
  Desc s (Some lb) ub f ->
  lb' == lb = true ->
  Desc s (Some lb') ub f.
Proof.
  intros ????? HD Heq.
  remember (Some lb) as lbo.
  induction HD; subst.
  * apply DescTip; f_solver.
  * intuition.
    eapply DescBin; try eassumption; try reflexivity.
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

(** Solve goals of Desc. Should be back-tracking free, I think. *)
Ltac solve_Desc := eassumption || lazymatch goal with
  | [ |- Desc Tip _ _ _ ]
    => apply DescTip; f_solver
  | [ H : Desc ?s ?lb (Some ?ub) _, H2 : ?ub' == ?ub = true  |- Desc ?s ?lb (Some ?ub') _ ]
    => apply (Desc_change_ub _ _ _ _ _ H H2)
  | [ H : Desc ?s ?lb (Some ?ub) _, H2 : isUB ?ub' ?ub = true  |- Desc ?s ?lb ?ub' _ ]
    => admit
  | [ H : Desc ?s (Some ?lb) ?ub _, H2 : ?lb' == ?lb = true  |- Desc ?s (Some ?lb') ?ub _ ]
    => apply (Desc_change_lb _ _ _ _ _ H H2)
  | [ H : Desc ?s (Some ?lb) ?ub _, H2 : isLB ?lb' ?lb = true  |- Desc ?s ?lb' ?ub _ ]
    => admit
  | [ |- Desc (Bin _ _ _ _) _ _ _ ]
    => eapply DescBin;
        [ solve_Desc
        | solve_Desc
        | solve_Bounds
        | solve_Bounds
        | solve_size
        | solve_size
        | try solve [f_solver]
        ]
  | |- ?H => fail "solve_Desc gave up on" H
  end.

(** For every set in the context, try to see if [lia] knows it is empty. *)
Ltac find_Tip :=
  match goal with [ H : Desc ?s _ _ _ |- _ ] =>
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

  (* Clean up the precondition a bit; makes lia go much faster *)
  assert (size s1 + size s2 <= 2 /\ size s2 <= 1 \/
        size s1 <= delta * (size s2 + 1) /\ size s2 <= delta * size s1)%Z by lia_Desc.
  clear H6.

  unfold balanceL, balance_prop, delta, ratio in *.
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__, Num_Integer__, Ord_Integer___, op_zg____, op_zl____.
  rewrite ?size_size.
  
  repeat lazymatch goal with [ H : Desc ?s _ _ _ |- context [match ?s with _ => _ end] ] => inversion H;subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_Desc]. (* Some are simply impossible *)
  3: repeat find_Tip.
  all: split; [solve_Desc | solve_size].
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

  (* Clean up the precondition a bit; makes lia go much faster *)
  assert (size s1 + size s2 <= 2 /\ size s1 <= 1 \/
        size s1 <= delta * size s2 /\ size s2 <= delta * (size s1 + 1))%Z by lia_Desc.
  clear H6.

  unfold balanceR, balance_prop, delta, ratio in *.
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__, Num_Integer__, Ord_Integer___, op_zg____, op_zl____.
  rewrite ?size_size.

  repeat lazymatch goal with [ H : Desc ?s _ _ _ |- context [match ?s with _ => _ end] ] => inversion H;subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; lia_Desc]. (* Some are simply impossible *)
  4: repeat find_Tip.
  all: split; [solve_Desc | solve_size].
Qed.

(* verification of member *)

Lemma member_Desc:
 forall {s lb ub f i}, Desc s lb ub f -> member i s = f i.
Proof.
  intros.
  induction H.
  * simpl. rewrite H; reflexivity.
  * subst; simpl.
    rewrite H5; clear H5.
    destruct (compare i x) eqn:?.
    + replace (i == x) with true by (symmetry; order_Bounds).
      rewrite orb_true_r.
      reflexivity.
    + replace (i == x) with false by (symmetry; order_Bounds).
      rewrite IHDesc1.
      rewrite (Desc_outside_below H0) by order_Bounds.
      rewrite !orb_false_r.
      reflexivity.
    + replace (i == x) with false by (symmetry; order_Bounds).
      rewrite IHDesc2.
      rewrite (Desc_outside_above H) by order_Bounds.
      rewrite orb_false_l.
      reflexivity.
Qed.

Lemma member_Sem:
 forall {s f i}, Sem s f -> member i s = f i.
Proof. intros. eapply member_Desc; eassumption. Qed.

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
  intros ?????? HD HLB HUB Hf.
  rewrite insert_insert'.
  revert f' Hf.
  induction HD; intros.
  * unfold insert, Datatypes.id.
    split; try (rewrite H; reflexivity).
    apply singleton_Desc; try assumption.
    intro i. rewrite Hf. rewrite H. rewrite orb_false_r. reflexivity.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in *.
      replace (f y) with true
        by (rewrite H3; rewrite Heqc; rewrite orb_true_r; reflexivity).
      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; [| clear Hpe]. 
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        split; try reflexivity.
        eapply DescBin; try eassumption; try reflexivity.
        intro i. rewrite Hf, H3. destruct (i == x), (f1 i), (f2 i); reflexivity.
      - unfold Datatypes.id.
        split; try reflexivity.
        eapply DescBin.
        ** solve_Desc.
        ** solve_Desc.
        ** assumption.
        ** assumption.
        ** reflexivity.
        ** solve_size.
        ** f_solver.
           (* Ideally, the f_solver destructs these equalities, and knows that [f] respects them *)
           replace (i == x) with (i == y) by (apply eq_true_iff_eq; split; order e).
           destruct (i == y), (f1 i), (f2 i); reflexivity.
    + rewrite compare_Lt in *.
      edestruct IHHD1; try assumption; try (intro; reflexivity).
      rename H1 into IH_Desc, H4 into IH_size.

      rewrite H3; setoid_rewrite H3 in Hf; clear H3.
      rewrite (Desc_outside_below HD2) by order_Bounds.
      rewrite lt_not_eq by assumption.
      rewrite ?orb_false_r, ?orb_false_l.

      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; only 2: clear Hpe.
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        rewrite Hpe in IH_size.
        assert (Hf' : f1 y = true). {
          destruct (f1 y) eqn:?; auto; try lia.
        }
        rewrite Hf'.
        split; try reflexivity.
        solve_Desc.
        f_solver.
        (* can be automated from here *)
        assert (i == y = true -> f1 y = true -> f1 i = true) by admit.
        destruct (i == y) eqn:?, (i == x)  eqn:?, (f1 i)  eqn:?, (f2 i)  eqn:?; 
          intuition congruence.

      - eapply balanceL_Desc; try eassumption.
        ** intro i.
           rewrite Hf.
           rewrite !orb_assoc.
           (* here I can use some tactics from IntSet *)
           destruct (i == y), (i == x); reflexivity.
        ** destruct (f1 y); solve_size.
        ** destruct (f1 y); solve_size.
    + (* more or less a copy-n-paste from above *)
      rewrite compare_Gt in *.
      edestruct IHHD2; only 1: rewrite lt_gt in *; try assumption. try (intro; reflexivity).
      rename H1 into IH_Desc, H4 into IH_size.

      rewrite H3; setoid_rewrite H3 in Hf; clear H3.
      rewrite (Desc_outside_above HD1) by order_Bounds.
      rewrite gt_not_eq by assumption.
      rewrite !orb_false_l.

      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; only 2: clear Hpe.
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        rewrite Hpe in IH_size.
        assert (Hf' : f2 y = true). {
          destruct (f2 y) eqn:?; auto; try lia.
        }
        rewrite Hf'.
        split; try reflexivity.
        eapply DescBin; try eassumption; try reflexivity.
        intro i. rewrite Hf. rewrite !orb_assoc.
        (* can be automated from here *)
        assert (i == y = true -> f2 y = true -> f2 i = true) by admit.
        destruct (i == y) eqn:?, (i == x)  eqn:?, (f1 i)  eqn:?, (f2 i)  eqn:?; 
          intuition congruence.
      - eapply balanceR_Desc; try eassumption.
        ** intro i.
           rewrite Hf.
           rewrite !orb_assoc.
           (* here I can use some tactics from IntSet *)
           destruct (i == y), (i == x), (f1 i); reflexivity.
        ** destruct (f2 y); solve_size.
        ** destruct (f2 y); solve_size.
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
  - inversion HD; subst; clear HD. intros.
    edestruct IHr2 as [Hf1 [Hub1 [Hlb1 [HD1 Hsz1]]]];
      [apply H4 |intro;reflexivity | ].
    clear IHr1 IHr2.
    inversion H4; subst; clear H4.
    subst y.
    cbn -[Z.add size].
    expand_pairs.
    cbn -[Z.add size].
    split; only 2: split; only 3: split.
    + rewrite H12, Hf1.
      rewrite orb_true_r.
      reflexivity.
    + solve_Bounds. 
    + simpl isLB in *.
      solve_Bounds.
    + eapply balanceL_Desc; try eassumption. 
      * f_solver. simpl.
        expand_pairs. simpl.
        destruct (i == (fst (maxViewSure a r1 r2))) eqn:?.
        -- simpl.
           rewrite (Desc_outside_above H3)
             by order_Bounds.
           replace (i == x)  with false
             by (symmetry; solve_Bounds).
           reflexivity.
        -- simpl. rewrite !andb_true_r.
           repeat rewrite orb_assoc.
           reflexivity.
      * solve_size.
      * solve_size.
  - inversion HD; subst; clear HD.
    cbn -[Z.add]. intro Hf'.
    rewrite H5, H6.
    repeat split; try assumption.
    + rewrite H12.
      rewrite Eq_refl.
      rewrite ?orb_true_r, ?orb_true_l.
      reflexivity.
    + inversion H4; subst; clear H4.
      eapply Desc_change_f; only 1: eassumption.
      f_solver. destruct (i == x) eqn:?, (f1 i) eqn:?; try reflexivity; exfalso.
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
  intros sz x l.
  revert sz x.
  induction l; intros sz x r lb ub f f' HD.
  - inversion HD; subst; clear HD. intros.
    edestruct IHl1 as [Hf1 [Hub1 [Hlb1 [HD1 Hsz1]]]];
      [apply H3 |intro;reflexivity | ].
    clear IHl1 IHl2.
    inversion H3; subst; clear H3.
    subst y.
    cbn -[Z.add size].
    expand_pairs.
    cbn -[Z.add size].
    split; only 2: split; only 3: split.
    + rewrite H12, Hf1. reflexivity.
    + solve_Bounds. 
    + simpl isLB in *.
      solve_Bounds.
    + eapply balanceR_Desc; try eassumption.
      * f_solver. simpl.
        expand_pairs. simpl.
        destruct (i == (fst (minViewSure a l1 l2))) eqn:?.
        -- simpl.
           rewrite (Desc_outside_below H4) by order_Bounds.
           rewrite orb_false_r.
           symmetry.
           order_Bounds.
        -- reflexivity. 
      * solve_size.
      * solve_size.
  - inversion HD; subst; clear HD.
    cbn -[Z.add]. intro Hf'.
    rewrite H5, H6.
    repeat split; try assumption.
    + rewrite H12.
      rewrite Eq_refl.
      rewrite ?orb_true_r, ?orb_true_l.
      reflexivity.
    + inversion H3; subst; clear H3.
      eapply Desc_change_f; only 1: eassumption.
      f_solver.
      destruct (i == x) eqn:?, (f2 i) eqn:?;
               try reflexivity; exfalso.
      rewrite (Desc_outside_below H4) in Heqb0.
      congruence.
      order_Bounds.
    + solve_size.
Qed.

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
  intros ???????? HD1 HD2. intros.
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
