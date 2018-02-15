Require Import GHC.Base.
Require Import Proofs.GHC.Base.
Require Import Data.Set.Internal.
Set Bullet Behavior "Strict Subproofs".

Section WF.
Context (e : Type) `{Ord e}.

(* This needs to be in an OrdLawful class *)
Axiom compare_Eq : forall (x y : e),
  compare x y = Eq <-> x == y = true.
Axiom compare_Lt : forall (x y : e),
  compare x y = Lt <-> x < y = true.
Axiom compare_Gt : forall (x y : e),
  compare x y = Gt <-> x > y = true.

Axiom lt_not_eq : forall (x y : e),
  x < y = true -> x == y = false.
Axiom gt_not_eq : forall (x y : e),
  x > y = true -> x == y = false.
Axiom lt_gt : forall (x y : e),
  (x > y) = (y < x).

(** This is just like size, but with a type signature that does not confuse [omega] *)
Definition size (s : Set_ e) : Z :=
  match s with | Bin sz _ _ _ => sz
               | Tip => 0 end.

Lemma size_size: Internal.size = size. Proof. reflexivity. Qed.

Definition bound := (option e)%type.

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

Definition balance_prop sz1 sz2 :=
  (sz1 + sz2 <= 1 \/ sz1 <= (delta * sz2) /\ sz2 <= delta * sz1)%Z.

Inductive Desc : Set_ e -> bound -> bound -> (e -> bool) -> Prop :=
  | DescTip : forall lb ub, Desc Tip lb ub (fun _ => false)
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
    (forall i, f i = f1 i || (i == x) || f2 i) ->
    Desc (Bin sz x s1 s2) lb ub f.

Definition Sem (s : Set_ e) (f : e -> bool) := Desc s None None f.

(** The highest level: Just well-formedness.
 *)

Definition WF (s : Set_ e) : Prop := exists f, Sem s f.


Lemma Desc_outside_below:
 forall {s lb ub f i},
  Desc s (Some lb) ub f ->
  i < lb = true ->
  f i = false.
Admitted.

Lemma Desc_outside_above:
 forall {s lb ub f i},
  Desc s lb (Some ub) f ->
  i > ub = true ->
  f i = false.
Admitted.

Lemma size_Bin: forall sz x (s1 s2 : Set_ e),
  size (Bin sz x s1 s2) = sz.
Proof. intros. reflexivity. Qed.

Ltac pose_new prf :=
  let prop := type of prf in
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => pose proof prf
  end.

Ltac assert_new prop prf :=
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => assert prop by prf
  end.


Lemma size_nonneg:
  forall {s lb ub f},
  Desc s lb ub f -> (0 <= size s)%Z.
Admitted.


Lemma size_0_iff_tip:
  forall {s lb ub f},
  Desc s lb ub f -> (size s = 0)%Z <-> s = Tip.
Proof.
  intros.
  induction H1.
  * intuition.
  * repeat match goal with [ H : Desc ?s _ _ _ |- _ ] => pose_new (size_nonneg H) end;
    rewrite size_Bin in *.
    intuition try (congruence || omega).
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

Ltac postive_sizes :=
  repeat match goal with [ H : Desc ?s _ _ _ |- _ ] => pose_new (size_nonneg H) end.

Lemma isLB_lt:
  forall lb x y,
  isLB lb x = true->
  x < y = true ->
  isLB lb y = true.
Admitted.

Lemma isUB_lt:
  forall ub x y,
  isUB ub x = true->
  y < x = true ->
  isUB ub y = true.
Admitted.

(* In order to stay sane and speed things up, here is
 a tactic that solves [Desc] goals *)

Ltac solve_Bounds := first
  [ assumption
  | lazymatch goal with [ H2 : isLB ?lb ?x = true, H1 : ?x < ?y = true |- isLB ?lb ?y = true] => apply (isLB_lt _ _ _ H2 H1) end
  | lazymatch goal with [ H2 : isUB ?ub ?x = true, H1 : ?y < ?x = true |- isUB ?ub ?y = true] => apply (isUB_lt _ _ _ H2 H1) end
  | idtac "solve_Bounds gave up"
  ].

Ltac omega_Desc :=
  postive_sizes;
  unfold balance_prop, delta, fromInteger, Num_Integer__ in *;
  rewrite ?size_Bin in *; simpl (size Tip) in *;
  omega.

Ltac solve_size := first
  [ assumption
  | reflexivity
  | omega_Desc
  | idtac "solve_size gave up"
  ].

Ltac solve_Desc := eassumption || lazymatch goal with
  | [ |- Desc Tip _ _ _ ]
    => apply DescTip
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

Ltac find_Tip :=
  match goal with [ H : Desc ?s _ _ _ |- _ ] =>
    assert_new (size s = 0)%Z omega_Desc;
    rewrite (size_0_iff_tip H) in *;
    subst s;
    inversion H;
    clear H;
    subst
  end.

Require Import Coq.Program.Tactics.

Lemma balanceL_Desc:
    forall lb ub,
    forall s1 f1,
    forall s2 f2,
    forall x f,
    Desc s1 lb (Some x) f1 ->
    Desc s2 (Some x) ub f2 ->
    isLB lb x = true ->
    isUB ub x = true->
    (forall i, f i = f1 i || (i == x) || f2 i) ->
    balance_prop (size s1) (size s2) \/
    balance_prop (size s1 - 1)%Z (size s2) /\ (1 <= size s1)%Z  \/
    balance_prop (size s1)%Z (size s2 + 1) ->
    Desc (balanceL x s1 s2) lb ub f /\ size (balanceL x s1 s2) = (1 + size s1 + size s2)%Z.
Proof.
  intros.
  unfold balanceL, balance_prop, delta, ratio in *.
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__, Num_Integer__, Ord_Integer___, op_zg____, op_zl____.
  rewrite ?size_size.

  repeat lazymatch goal with [ H : Desc ?s _ _ _ |- context [match ?s with _ => _ end] ] => inversion H;subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; omega_Desc]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: split; [solve_Desc | solve_size].
Qed.

Lemma balanceR_Desc:
    forall lb ub,
    forall s1 f1,
    forall s2 f2,
    forall x f,
    Desc s1 lb (Some x) f1 ->
    Desc s2 (Some x) ub f2 ->
    isLB lb x = true ->
    isUB ub x = true->
    (forall i, f i = f1 i || (i == x) || f2 i) ->
    balance_prop (size s1) (size s2) \/
    balance_prop (size s1) (size s2 - 1)%Z /\ (1 <= size s2)%Z  \/
    balance_prop (size s1 + 1) (size s2) ->
    Desc (balanceR x s1 s2) lb ub f /\ size (balanceR x s1 s2) = (1 + size s1 + size s2)%Z.
Proof.
  intros.
  unfold balanceR, balance_prop, delta, ratio in *.
  unfold fromInteger, op_zg__, op_zl__, op_zt__, op_zp__, Num_Integer__, Ord_Integer___, op_zg____, op_zl____.
  rewrite ?size_size.

  repeat lazymatch goal with [ H : Desc ?s _ _ _ |- context [match ?s with _ => _ end] ] => inversion H;subst; clear H end;
  repeat lazymatch goal with [ |- context [if (?x <? ?y)%Z then _ else _] ] => destruct (Z.ltb_spec x y) end;
  rewrite ?size_Bin in *; simpl (size Tip) in *;
  simpl isLB in *;
  simpl isUB in *.
  all: try solve [exfalso; omega_Desc]. (* Some are simply impossible *)
  all: repeat find_Tip.
  all: split; [solve_Desc | solve_size].
Qed.


Lemma member_Desc:
 forall {s lb ub f i}, Desc s lb ub f -> member i s = f i.
Proof.
  intros.
  induction H1.
  * reflexivity.
  * subst; simpl.
    rewrite H5; clear H5.
    destruct (compare i x) eqn:?.
    + rewrite compare_Eq in *.
      rewrite Heqc.
      rewrite orb_true_r.
      reflexivity.
    + rewrite compare_Lt in *.
      rewrite lt_not_eq by assumption.
      rewrite IHDesc1.
      rewrite (Desc_outside_below H1_0) by assumption.
      rewrite !orb_false_r.
      reflexivity.
    + rewrite compare_Gt in *.
      rewrite gt_not_eq by assumption.
      rewrite IHDesc2.
      rewrite (Desc_outside_above H1_) by assumption.
      rewrite orb_false_l.
      reflexivity.
Qed.

Lemma member_Sem:
 forall {s f i}, Sem s f -> member i s = f i.
Proof. intros. eapply member_Desc; eassumption. Qed.

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
  eapply DescBin.
  * apply DescTip.
  * apply DescTip.
  * assumption.
  * assumption.
  * reflexivity.
  * unfold balance_prop, delta, fromInteger, Num_Integer__  in *. simpl size. omega.
  * intro i. rewrite H3.
    rewrite !orb_false_r.
    reflexivity.
Qed.

Lemma singleton_Sem:
  forall f x,
  (forall i, f i = (i == x)) ->
  Sem (singleton x) f.
Proof. intros. apply singleton_Desc; try eassumption; try reflexivity. Qed.

Lemma singleton_WF:
  forall y, WF (singleton y).
Proof. intros. eexists. eapply singleton_Sem. reflexivity. Qed.

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
    split; try reflexivity.
    apply singleton_Desc; try assumption.
    intro i. rewrite Hf. rewrite orb_false_r. reflexivity.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in *.
      replace (f y) with true
       by (rewrite H5; rewrite Heqc; rewrite orb_true_r; reflexivity).
      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; only 2: clear Hpe.
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        split; try reflexivity.
        eapply DescBin; try eassumption; try reflexivity.
        intro i. rewrite Hf, H5. destruct (i == x), (f1 i), (f2 i); reflexivity.
      - unfold Datatypes.id.
        split; try reflexivity.
        eapply DescBin. 
        ** assert (Desc s1 lb (Some y) f1) by admit. (* transitivity of the bound *)
           eassumption.
        ** assert (Desc s2 (Some y) ub f2) by admit. (* transitivity of the bound *)
           eassumption.
        ** assumption.
        ** assumption.
        ** reflexivity.
        ** solve_size.
        ** f_solver.
           replace (i == x) with (i == y) by admit. (* transitivity of == *)
           destruct (i == y), (f1 i), (f2 i); reflexivity.
    + rewrite compare_Lt in *.
      edestruct IHHD1; try assumption; try (intro; reflexivity).
      rename H3 into IH_Desc, H6 into IH_size.

      rewrite H5; setoid_rewrite H5 in Hf; clear H5.
      rewrite (Desc_outside_below HD2) by assumption.
      rewrite lt_not_eq by assumption.
      rewrite ?orb_false_r, ?orb_false_l.

      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; only 2: clear Hpe.
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        rewrite Hpe in IH_size.
        assert (Hf' : f1 y = true). {
          destruct (f1 y) eqn:?; auto; try omega.
        }
        rewrite Hf'.
        split; try reflexivity.
        solve_Desc.
        f_solver.
        (* can be automated from here *)
        assert (i == y = true -> f1 y = true -> f1 i = true) by admit.
        destruct (i == y) eqn:?, (i == x)  eqn:?, (f1 i)  eqn:?, (f2 i)  eqn:?; 
          intuition congruence.

      - replace ((if f1 y then (1 + size s1 + size s2)%Z else (1 + (1 + size s1 + size s2))%Z))
           with (1 + size (insert' y s1) + size s2)%Z.
        eapply balanceL_Desc; try eassumption.
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
      rename H3 into IH_Desc, H6 into IH_size.

      rewrite H5; setoid_rewrite H5 in Hf; clear H5.
      rewrite (Desc_outside_above HD1) by assumption.
      rewrite gt_not_eq by assumption.
      rewrite !orb_false_l.

      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; only 2: clear Hpe.
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        rewrite Hpe in IH_size.
        assert (Hf' : f2 y = true). {
          destruct (f2 y) eqn:?; auto; try omega.
        }
        rewrite Hf'.
        split; try reflexivity.
        eapply DescBin; try eassumption; try reflexivity.
        intro i. rewrite Hf. rewrite !orb_assoc.
        (* can be automated from here *)
        assert (i == y = true -> f2 y = true -> f2 i = true) by admit.
        destruct (i == y) eqn:?, (i == x)  eqn:?, (f1 i)  eqn:?, (f2 i)  eqn:?; 
          intuition congruence.
      - replace ((if f2 y then (1 + size s1 + size s2)%Z else (1 + (1 + size s1 + size s2))%Z))
           with (1 + size s1 + size (insert' y s2))%Z.
        eapply balanceR_Desc; try eassumption.
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
Proof. intros ?? HWF. destruct HWF. eexists. eapply insert_Sem. eassumption. reflexivity. Qed.


End WF.
