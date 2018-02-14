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

Inductive Desc : Set_ e -> Size -> bound -> bound -> (e -> bool) -> Prop :=
  | DescTip : forall lb ub, Desc Tip 0%Z lb ub (fun _ => false)
  | DescBin :
    forall lb ub,
    forall s1 sz1 f1,
    forall s2 sz2 f2,
    forall x sz sz' f,
    Desc s1 sz1 lb (Some x) f1 ->
    Desc s2 sz2 (Some x) ub f2 ->
    isLB lb x = true ->
    isUB ub x = true->
    sz = (1 + sz1 + sz2)%Z ->
    sz' = sz ->
    (forall i, f i = (i == x) || f1 i || f2 i) ->
    Desc (Bin sz' x s1 s2) sz lb ub f.

Inductive Sem : Set_ e -> (e -> bool) -> Prop :=
  | DescSem : forall s sz lb ub f (HD : Desc s sz lb ub f), Sem s f.

(** The highest level: Just well-formedness.
 *)

Definition WF (s : Set_ e) : Prop := exists f, Sem s f.


Lemma Desc_outside_below:
 forall {s sz lb ub f i},
  Desc s sz (Some lb) ub f ->
  i < lb = true ->
  f i = false.
Admitted.

Lemma Desc_outside_above:
 forall {s sz lb ub f i},
  Desc s sz lb (Some ub) f ->
  i > ub = true ->
  f i = false.
Admitted.

(* This has all the preconditions of [Bin], besides the one about [sz'] *)
Axiom balanceL_Desc:
    forall lb ub,
    forall s1 sz1 f1,
    forall s2 sz2 f2,
    forall x sz f,
    Desc s1 sz1 lb (Some x) f1 ->
    Desc s2 sz2 (Some x) ub f2 ->
    isLB lb x = true ->
    isUB ub x = true->
    sz = (1 + sz1 + sz2)%Z ->
    (forall i, f i = (i == x) || f1 i || f2 i) ->
    Desc (balanceL x s1 s2) sz lb ub f.


Lemma member_Desc:
 forall {s sz lb ub f i}, Desc s sz lb ub f -> member i s = f i.
Proof.
  intros.
  induction H1.
  * reflexivity.
  * subst; simpl.
    rewrite H5; clear H5.
    destruct (compare i x) eqn:?.
    + rewrite compare_Eq in *.
      rewrite Heqc.
      reflexivity.
    + rewrite compare_Lt in *.
      rewrite lt_not_eq by assumption.
      rewrite IHDesc1.
      rewrite (Desc_outside_below H1_0) by assumption.
      rewrite orb_false_l, orb_false_r.
      reflexivity.
    + rewrite compare_Gt in *.
      rewrite gt_not_eq by assumption.
      rewrite IHDesc2.
      rewrite (Desc_outside_above H1_) by assumption.
      rewrite orb_false_l.
      reflexivity.
Qed.

Lemma singleton_Desc:
  forall x  lb ub f',
  isLB lb x = true ->
  isUB ub x = true ->
  (forall i, f' i = (i == x)) ->
  Desc (singleton x) 1%Z lb ub f'.
Proof.
  intros.
  unfold singleton.
  unfold fromInteger, Num_Integer__.
  eapply DescBin.
  * apply DescTip.
  * apply DescTip.
  * assumption.
  * assumption.
  * omega.
  * reflexivity.
  * intro i. rewrite H3.
    rewrite !orb_false_r.
    reflexivity.
Qed.

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

Lemma insert'_unchanged:
  forall y,
  forall s sz lb ub f,
  Desc s sz lb ub f ->
(*
  isLB lb y = true ->
  isUB ub y = true ->
*)
  insert' y s = s ->
  f y = true.
Admitted.

Lemma insert_Desc:
  forall y,
  forall s sz lb ub f f',
  Desc s sz lb ub f ->
  isLB lb y = true ->
  isUB ub y = true ->
  (forall i, f' i = (i == y) || f i) ->
  Desc (insert y s) (if f y then sz else (1 + sz)%Z) lb ub f'.
Proof.
  intros ??????? HD HLB HUB Hf.
  rewrite insert_insert'.
  revert f' Hf.
  induction HD; intros.
  * unfold insert, Datatypes.id.
    apply singleton_Desc; try assumption.
    intro i. rewrite Hf. rewrite orb_false_r. reflexivity.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in *.
      replace (f y) with true by (rewrite H5; rewrite Heqc; reflexivity).
      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; only 2: clear Hpe.
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        eapply DescBin; try eassumption; try reflexivity.
        intro i. rewrite Hf, H5. rewrite !orb_assoc, orb_diag. reflexivity.
      - unfold Datatypes.id.
        eapply DescBin. 
        ** assert (Desc s1 sz1 lb (Some y) f1) by admit.
           eassumption.
        ** assert (Desc s2 sz2 (Some y) ub f2) by admit.
           eassumption.
        ** assumption.
        ** assumption.
        ** reflexivity.
        ** reflexivity.
        ** intro i. rewrite Hf. rewrite H5.
           replace (i == x) with (i == y) by admit. (* transitivity of == *)
           rewrite !orb_assoc.
           rewrite orb_diag.
           reflexivity.
    + rewrite compare_Lt in *.
      destruct (PtrEquality.ptrEq _ _) eqn:Hpe; only 2: clear Hpe.
      - apply PtrEquality.ptrEq_eq in Hpe; subst.
        rewrite H5.
        rewrite lt_not_eq by assumption.
        erewrite (insert'_unchanged y s1) by eassumption.
        rewrite (Desc_outside_below HD2) by assumption.
        rewrite orb_false_r, orb_false_l.
        eapply DescBin; try eassumption; try reflexivity.
        intro i. rewrite Hf, H5. rewrite !orb_assoc.
        assert (f1 y = true) by (eapply (insert'_unchanged y s1); try eassumption).
        (* can be automated from here *)
        assert (i == y = true -> f1 i = true) by admit.
        destruct (i == y) eqn:?, (i == x)  eqn:?, (f1 i)  eqn:?, (f2 i)  eqn:?; 
          intuition congruence.
      - eapply balanceL_Desc. 
        ** apply IHHD1.
           -- assumption.
           -- simpl. assumption.
           -- intro i. reflexivity.
        ** eassumption.
        ** assumption.
        ** assumption.
        ** rewrite H5.
           rewrite (Desc_outside_below HD2) by assumption.
           rewrite lt_not_eq by assumption.
           rewrite orb_false_r, orb_false_l.
           destruct (f1 y); omega.
        ** intro i.
           rewrite Hf.
           rewrite H5.
           rewrite !orb_assoc.
           (* here I can use some tactics from IntSet *)
           destruct (i == y), (i == x); reflexivity.
    + (* analogue, to be done when the rest is complete *)
      admit.
Admitted.

End WF.
