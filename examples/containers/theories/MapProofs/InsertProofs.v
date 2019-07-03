Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Proofs.GHC.Base.
Require Import Data.Map.Internal.
Import GHC.Num.Notations.
Require Import OrdTactic.
Require Import Psatz.
Require Import Tactics.
Set Bullet Behavior "Strict Subproofs".
Require Import MapProofs.Bounds.
Require Import MapProofs.Tactics.

Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.
(** ** Verification of [insert] *)

(* The [orig] passing and the local fixpoint in insert is plain ugly, so let’s to this instead *)

Fixpoint insert' (x : e) (v : a) (s : Map e a) : Map e a :=
  match s with 
    | Tip => singleton x v
    | Bin sz y vy l r => match compare x y with
      | Lt =>
        let l' := insert' x v l in
        if PtrEquality.ptrEq l' l then s else balanceL y vy l' r
      | Gt =>
        let r' := insert' x v r in 
        if PtrEquality.ptrEq r' r then s else balanceR y vy l r'
      | Eq =>
        if PtrEquality.ptrEq v vy && PtrEquality.ptrEq x y then s else Bin sz x v l r
     end
  end.

Lemma insert_insert' : forall x v s, insert x v s = insert' x v s.
Proof.
  intros.
  unfold insert.
  induction s; simpl.
  * destruct (compare x k).
    - reflexivity.
    - rewrite IHs1. reflexivity.
    - rewrite IHs2. reflexivity.
  * reflexivity.
Qed.

Lemma insert_Desc:
  forall y v (s: Map e a) lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insert y v s) lb ub (if isSome (sem s y) then size s else (1 + size s)%Z)
      (fun i => (if i == y then Some v else None) ||| sem s i).
Proof.
  intros ????? HB HLB HUB.
  rewrite insert_insert'.
  induction HB; intros.
  * simpl.
    applyDesc e (@singleton_Desc e a); try eassumption; solve_Desc e.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + assert (y == x = true) by (order e). 
      rewrite H1.
      rewrite ?isSome_oro, ?isSome_Some, ?orb_true_r, ?orb_true_l.
      destruct_ptrEq.
      - solve_Desc e.
      - unfold Datatypes.id.
        solve_Desc e.
    + clear IHHB2.
      applyDesc e IHHB1.

      rewrite (sem_outside_below HB2) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options.

      destruct_ptrEq.
      - destruct (sem s1 y) eqn:?; simpl isSome in *; try lia.
        solve_Desc e.
      - destruct (sem s1 y); simpl isSome in *;
        applyDesc e (@balanceL_Desc e a);
        cbv match in *;
        solve_Desc e.
    + (* more or less a copy-n-paste from above *)
      clear IHHB1.
      applyDesc e IHHB2.

      rewrite (sem_outside_above HB1) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options.

      destruct_ptrEq.
      - destruct (sem s2 y) eqn:?; simpl_options; try lia.
        solve_Desc e.
      - destruct (sem s2 y); simpl_options;
        applyDesc e (@balanceR_Desc e a);
        solve_Desc e.
Qed.

(** ** Verification of [insertWith] *)
Lemma insertWith_Desc:
  forall (f: a -> a -> a) y v s lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insertWith f y v s) lb ub (if isSome (sem s y) then size s else (1 + size s)%Z)
      (fun i => (if i == y then match (sem s y) with
                                | None => Some v
                                | Some x => Some (f v x)
                                end  else None ||| sem s i )).
Proof.
  intros ?????? HB HLB HUB.
  induction HB; intros.
  * simpl.
    applyDesc e (@singleton_Desc e a); try eassumption; solve_Desc e.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in Heqc. 
      rewrite Heqc.
      rewrite ?isSome_oro, ?isSome_Some, ?orb_true_r, ?orb_true_l.
      solve_Desc e.
    + clear IHHB2.
      applyDesc e IHHB1.
      rewrite (sem_outside_below HB2) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options. destruct (sem s1 y) eqn:?; simpl isSome in *; try lia;
      applyDesc e (@balanceL_Desc e a); solve_Desc e.
    + clear IHHB1.
      applyDesc e IHHB2.
      rewrite (sem_outside_above HB1) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options. destruct (sem s2 y) eqn:?; simpl_options; try lia; applyDesc e (@balanceR_Desc e a);
      solve_Desc e.
Qed.

(** ** Verification of [insertWithKey] *)
Lemma insertWithKey_Desc:
  forall (f: e -> a -> a -> a) y v s lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insertWithKey f y v s) lb ub (if isSome (sem s y) then size s else (1 + size s)%Z)
      (fun i => (if i == y then match (sem s y) with
                                | None => Some v
                                | Some x => Some (f y v x)
                                end  else None ||| sem s i )).
Proof.
  intros ?????? HB HLB HUB.
  induction HB; intros.
  * simpl.
    applyDesc e (@singleton_Desc e a); try eassumption; solve_Desc e.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in Heqc.
      rewrite Heqc.
      rewrite ?isSome_oro, ?isSome_Some, ?orb_true_r, ?orb_true_l.
      solve_Desc e.
    + clear IHHB2.
      applyDesc e IHHB1.
      rewrite (sem_outside_below HB2) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options. destruct (sem s1 y) eqn:?; simpl isSome in *; try lia;
      applyDesc e (@balanceL_Desc e a); solve_Desc e.
    + clear IHHB1.
      applyDesc e IHHB2.
      rewrite (sem_outside_above HB1) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options. destruct (sem s2 y) eqn:?; simpl_options; try lia; applyDesc e (@balanceR_Desc e a);
      solve_Desc e.
Qed.

(** ** Verification of [insertLookupWithKey] *)
Lemma pair_fst_snd: forall {a: Type} {b : Type} (p : a * b),
   p = (fst p, snd p).
Proof.
  intros. destruct p. simpl. reflexivity.
Qed.

Lemma insertLookupWithKey_lookup:
  forall (m: Map e a) lb ub f k v1,
  Bounded m lb ub ->
  sem m k = fst ((insertLookupWithKey f k v1 m)).
Proof.
  intros. generalize dependent k. revert f v1. induction H; intros.
  - simpl. reflexivity.
  - simpl.   destruct (sem s1 k) eqn : ?.
   + assert (compare k x = Lt) by (solve_Bounds e). rewrite H5. simpl. 
     rewrite (pair_fst_snd (insertLookupWithKey f k v1 s1 )). simpl.
     rewrite <- Heqo. apply IHBounded1.
   + simpl. destruct (k == x) eqn : ?.
      * simpl. assert (compare k x = Eq) by (order e).
        rewrite H5. simpl. reflexivity.
      * simpl. destruct (sem s2 k) eqn : ?.
        -- assert (compare k x = Gt) by (solve_Bounds e). rewrite H5. 
           rewrite (pair_fst_snd (insertLookupWithKey f k v1 s2 )). simpl.
           rewrite <- Heqo0. apply IHBounded2.
        -- destruct (compare k x) eqn : ?.
          ++ order e.
          ++ rewrite (pair_fst_snd (insertLookupWithKey f k v1 s1)). simpl.
             rewrite <- Heqo. apply IHBounded1.
          ++ rewrite (pair_fst_snd (insertLookupWithKey f k v1 s2)). simpl.
             rewrite <- Heqo0. apply IHBounded2.
Qed.

(*This makes the Desc incredibly easy*)
Lemma insertWithKey_insertLookupWithKey: forall (m: Map e a) f k v,
  insertWithKey f k v m = snd(insertLookupWithKey f k v m).
Proof.
  intros m. induction m; intros.
  - simpl. destruct (compare k0 k).
    + simpl. reflexivity.
    + simpl. rewrite (pair_fst_snd (insertLookupWithKey f k0 v m1)). simpl.
      rewrite IHm1. reflexivity.
    + rewrite (pair_fst_snd (insertLookupWithKey f k0 v m2)). simpl.
      rewrite IHm2. reflexivity.
  - simpl. reflexivity.
Qed.  

Lemma insertLookupWithKey_Desc:
  forall (f: e -> a -> a -> a) y v s lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (snd(insertLookupWithKey f y v s)) lb ub (if isSome (sem s y) then size s else (1 + size s)%Z)
      (fun i => (if i == y then match (sem s y) with
                                | None => Some v
                                | Some x => Some (f y v x)
                                end  else None ||| sem s i )).
Proof.
  intros. rewrite <- insertWithKey_insertLookupWithKey. apply insertWithKey_Desc; assumption.
Qed. 


(** ** Verification of [insertR] *)

Fixpoint insertR' (x : e) (v : a) (s : Map e a) : Map e a :=
  match s with 
    | Tip => singleton x v
    | Bin sz y vy l r => match compare x y with
      | Lt =>
        let l' := insertR' x v l in
        if PtrEquality.ptrEq l' l then s else balanceL y vy l' r
      | Gt =>
        let r' := insertR' x v r in 
        if PtrEquality.ptrEq r' r then s else balanceR y vy l r'
      | Eq => Bin sz y vy l r
     end
  end.

Lemma insertR_insertR' : forall x v s, insertR x v s = insertR' x v s.
Proof.
  intros.
  unfold insertR.
  induction s; simpl.
  * destruct (compare x k).
    - reflexivity.
    - rewrite IHs1. reflexivity.
    - rewrite IHs2. reflexivity.
  * reflexivity.
Qed.


Lemma insertR_Desc:
  forall y v (s: Map e a) lb ub,
  Bounded s lb ub ->
  isLB lb y = true ->
  isUB ub y = true ->
  Desc (insertR y v s) lb ub (if isSome (sem s y) then size s else (1 + size s)%Z)
    (fun i => sem s i ||| (if i == y then Some v else None)).
Proof.
  intros ????? HB HLB HUB.

  rewrite insertR_insertR'.
  induction HB; intros.
  * simpl.
    applyDesc e (@singleton_Desc e a); try eassumption; solve_Desc e.
  * subst; cbn -[Z.add].
    destruct (compare y x) eqn:?.
    + rewrite compare_Eq in Heqc.
      rewrite Heqc.
      rewrite ?isSome_oro, ?isSome_Some, ?orb_true_r, ?orb_true_l.
      solve_Desc e.
    + clear IHHB2.
      applyDesc e IHHB1.

      rewrite (sem_outside_below HB2) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options.

      destruct_ptrEq.
      - destruct (sem s1 y) eqn:?; simpl_options; try lia.
        solve_Desc e.
      - destruct (sem s1 y); simpl_options;
        applyDesc e (@balanceL_Desc e a);
        solve_Desc e.
    + (* more or less a copy-n-paste from above *)
      clear IHHB1.
      applyDesc e IHHB2.

      rewrite (sem_outside_above HB1) by order_Bounds e.
      replace (y == x) with false by order_Bounds e.
      simpl_options.
      
      destruct_ptrEq.
      - destruct (sem s2 y) eqn:?; simpl_options; try lia.
        solve_Desc e.
      - destruct (sem s2 y); simpl_options;
        applyDesc e (@balanceR_Desc e a);
        solve_Desc e.
Qed.


Lemma insert_WF:
  forall y v (s: Map e a), WF s -> WF (insert y v s).
Proof.
  intros. eapply Desc_WF.
  eapply insert_Desc; try reflexivity; try assumption.
Qed.

Lemma insertWith_WF:
  forall f y v (s: Map e a), WF s -> WF (insertWith f y v s).
Proof.
  intros. eapply Desc_WF.
  eapply insertWith_Desc; [assumption | | ]; reflexivity.
Qed.

End WF.


