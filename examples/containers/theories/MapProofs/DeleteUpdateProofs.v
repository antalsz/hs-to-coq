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
Require Import MapProofs.MaxMinProofs.
Require Import MapProofs.InsertProofs.

Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.

(** ** Verification of [glue] *)

Lemma glue_Desc:
  forall (s1: Map e a) s2 lb ub x,
  Bounded s1 lb (Some x) ->
  Bounded s2 (Some x) ub ->
  isLB lb x = true ->
  isUB ub x = true ->
  balance_prop (size s1) (size s2) ->
  Desc (glue s1 s2) lb ub ((size s1 + size s2)%Z) (fun i => sem s1 i ||| sem s2 i).
Proof.
  intros ????? HB1 HB2 ???.

  inversion HB1; inversion HB2; subst; cbn -[Z.add]; clear HB1 HB2.
  1-3: solve [solve_Desc e|solve_size].
  destruct (Z.ltb_spec (1 + size s4 + size s5) (1 + size s0 + size s3)).
  - eapply maxViewSure_Desc; only 1: solve_Bounded e.
    intros y vy r [Hthere HD].
    applyDesc e HD.
    destruct Hthere as [[??]|Hthere].
      (*TODO: See why this is not rewriting automatically*)
    * subst. applyDesc e (@balanceR_Desc e a). rewrite size_Bin in *. rewrite size_Bin in H1.
      solve_size. solve_Desc e. repeat(rewrite size_Bin in H1). rewrite size_Bin in Hsz0. solve_size.
      (*subst; applyDesc e (@balanceR_Desc e a); solve_Desc e.*)
    * subst; applyDesc e (@balanceR_Desc e a). rewrite size_Bin in *. rewrite size_Bin in H1. solve_size.
      solve_Desc e. rewrite size_Bin in Hsz0. solve_size.
  - eapply minViewSure_Desc; only 1: solve_Bounded e.
    intros y vy r [Hthere HD].
    applyDesc e HD.
    destruct Hthere as [[??]|Hthere]; subst; applyDesc e (@balanceL_Desc e a).
    rewrite size_Bin in H1. solve_size. solve_Desc e. rewrite size_Bin in Hsz0. solve_size.
    rewrite size_Bin in H1. solve_size. solve_Desc e. rewrite size_Bin in Hsz0. solve_size.
    
Qed.

(** ** Verification of [delete] *)

Lemma delete_Desc :
  forall x (s: Map e a) lb ub,
  Bounded s lb ub ->
  Desc (delete x s) lb ub (if isSome (sem s x) then (size s - 1) else size s) (fun i => if i == x then None else sem s i).
Proof.
  intros ???? HB.
  induction HB; intros; subst.
  - simpl. solve_Desc e.
  - cbn -[Z.add].
    destruct (compare x x0) eqn:Heq.
    + replace (x == x0) with true by solve_Bounds e.
      simpl_options.
      applyDesc e glue_Desc.
      solve_Desc e.
    + applyDesc e IHHB1; clear IHHB1 IHHB2.
      replace (x == x0) with false by solve_Bounds e.
      rewrite -> (sem_outside_below HB2) by solve_Bounds e.
      simpl_options.
      destruct_ptrEq.
      * replace (isSome (sem s1 x)) with false in *
          by (destruct (sem s1 x); simpl in *;  try congruence; lia).
        solve_Desc e.
      * destruct (sem s1 x); cbn -[Z.add] in *; applyDesc e (@balanceR_Desc e a); solve_Desc e.
    + applyDesc e IHHB2; clear IHHB1 IHHB2.
      replace (x == x0) with false by solve_Bounds e.
      rewrite -> (sem_outside_above HB1) by solve_Bounds e.
      simpl_options.
      destruct_ptrEq.
      * replace (isSome (sem s2 x)) with false by (destruct (sem s2 x); simpl in *; try congruence; lia).
        solve_Desc e.
      * destruct (sem s2 x); cbn -[Z.add] in *; applyDesc e (@balanceL_Desc e a); solve_Desc e.
Qed.

(** ** Verification of [deleteMin] *)

(** It is hard to phrase this without refering to [lookupMin] *)

Lemma deleteMin_Desc :
  forall (m: Map e a) lb ub,
  Bounded m lb ub ->
  deleteMin m = match lookupMin m with | None => m
                                       | Some (x, y) => delete x m end.
Proof.
  intros ??? HD.
  induction HD.
  * reflexivity.
  * clear IHHD2.
    cbn [deleteMin].
    rewrite IHHD1; clear IHHD1.

    destruct s1 eqn:?.
    + replace (lookupMin (Bin sz x v (Bin s e0 a0 m1 m2) s2)) with (lookupMin (Bin s e0 a0 m1 m2)) by reflexivity.
      rewrite <- Heqm in *. clear  s e0 a0 m1 m1 Heqm.

      pose proof (lookupMin_Desc s1 lb (Some x) HD1) as Hlookup.
      destruct (lookupMin s1) as [ex|].
      - destruct ex. destruct Hlookup as [Hthere Hextrem].
        simpl.
        apply (sem_inside HD1) in Hthere. destruct Hthere.
        replace (compare e0 x) with Lt by (symmetry; solve_Bounds e).
        ** destruct_ptrEq.
           ++ rewrite Hpe. clear Hpe.
              eapply balanceR_noop; try eassumption.
           ++ reflexivity.
       - rewrite H1.
          eapply balanceR_noop; try eassumption.
   + simpl.
     replace (compare x x) with Eq by (symmetry; order e).
     reflexivity.
Qed.

(** ** Verification of [deleteMax] *)

(** It is hard to phrase this without refering to [lookupMax] *)

Lemma deleteMax_Desc :
  forall (m: Map e a) lb ub,
  Bounded m lb ub ->
  deleteMax m = match lookupMax m with | None => m
                                       | Some (x, y) => delete x m end.
Proof.
  intros ??? HD.
  induction HD.
  * reflexivity.
  * clear IHHD1.
    cbn [deleteMax].
    rewrite IHHD2; clear IHHD2.

    destruct s2 eqn:?.
    + replace (lookupMax (Bin sz x v s1 (Bin s e0 a0 m1 m2))) with (lookupMax (Bin s e0 a0 m1 m2)) by reflexivity.
      rewrite <- Heqm in *. clear s e0 a0 m1 m2 Heqm.

      pose proof (lookupMax_Desc s2 (Some x) ub HD2) as Hlookup.
      destruct (lookupMax s2) as [ex|].
      - destruct ex. destruct Hlookup as [Hthere Hextrem].
        simpl.
        apply (sem_inside HD2) in Hthere. destruct Hthere.
        replace (compare e0 x) with Gt by (symmetry; solve_Bounds e).
        ** destruct_ptrEq.
           ++ rewrite Hpe. clear Hpe.
              eapply balanceL_noop; try eassumption.
           ++ reflexivity.
       - rewrite H1.
          eapply balanceL_noop; try eassumption.
   + simpl.
     replace (compare x x) with Eq by (symmetry; order e).
     destruct s1; reflexivity.
Qed.

(** ** Verification of [adjustWithKey *)
Require Import Coq.Classes.Morphisms. (* For [Proper] *)

(*TODO: Had to add assumption that f is proper*)
Lemma adjustWithKey_Desc :
  forall x f (m: Map e a) lb ub,
  Bounded m lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  Desc (adjustWithKey f x m) lb ub (size m) (fun i => if i == x then match (sem m x) with
                                                                     | Some v => Some (f x v)
                                                                     | None => None end else sem m i).
Proof.
  intros ????? HA HP. induction HA.
  - simpl. solve_Desc e.
  - cbn -[Z.add]. destruct (compare x x0) eqn : ?.
    + replace (x == x0) with true by solve_Bounds e. simpl_options.
      solve_Desc e. f_solver e.
      assert (f x0 v = f x v). apply equal_f. apply HP. order e. rewrite H3. reflexivity.
    + applyDesc e IHHA1; clear IHHA1 IHHA2. replace (x == x0) with false by solve_Bounds e.
      rewrite -> (sem_outside_below HA2) by solve_Bounds e.
      simpl_options. solve_Desc e. 
    + applyDesc e IHHA2; clear IHHA1 IHHA2. replace (x == x0) with false by solve_Bounds e.
      rewrite -> (sem_outside_above HA1) by solve_Bounds e. simpl_options.
      solve_Desc e.
Qed.

(** ** Verification of [adjust] *)
Lemma adjust_spec: forall (m: Map e a) (f: a -> a) k,
  adjust f k m = adjustWithKey (fun _ x => f x) k m.
Proof. 
  intros. unfold adjust. reflexivity.
Qed.

(** ** Verification of [updateWithKey] *)
Lemma updateWithKey_Desc:
  forall x f (m: Map e a) lb ub,
  Bounded m lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  Desc (updateWithKey f x m) lb ub (match sem m x with
                                    | None => size m
                                    | Some y => if isSome (f x y) then
                                       size m else size m - 1
                                      end) (fun i => if i == x then match (sem m x) with
                                                                     | Some v => f x v
                                                                     | None => None end else sem m i).
Proof.
intros ????? HB HP.
  induction HB; intros; subst.
  - simpl. solve_Desc e.
  - cbn -[Z.add].
    destruct (compare x x0) eqn:Heq.
    + assert (f x0 v = f x v). apply equal_f. apply HP. order e.
      replace (x == x0) with true by solve_Bounds e.
      simpl_options. destruct (f x0 v) eqn : ?.
      * solve_Desc e. rewrite size_Bin in *.
        rewrite -> (sem_outside_above HB1) by solve_Bounds e.
        rewrite -> (sem_outside_below HB2) by solve_Bounds e.
        simpl_options. rewrite <- H1. reflexivity. 
      * applyDesc e glue_Desc. solve_Desc e. 
        rewrite -> (sem_outside_above HB1) by solve_Bounds e.
        rewrite -> (sem_outside_below HB2) by solve_Bounds e.
        simpl_options. rewrite <-H1. cbn -[Z.add]. rewrite Hsz. omega.
    + applyDesc e IHHB1. replace (x == x0) with false by solve_Bounds e.
      rewrite -> (sem_outside_below HB2) by solve_Bounds e.
      simpl_options. destruct (sem s1 x); cbn -[Z.add] in *; applyDesc e (@balanceR_Desc e a).
      destruct (f x a0) eqn : ?. simpl in Hsz. rewrite Hsz. left. assumption.
      simpl in Hsz. rewrite Hsz. solve_size.
      solve_Desc e. rewrite Hsz0. destruct (f x a0); simpl in Hsz; rewrite Hsz;
      cbn -[Z.add]. reflexivity. omega. solve_Desc e.
    + applyDesc e IHHB2. replace (x == x0) with false by (order e). 
      rewrite -> (sem_outside_above HB1) by solve_Bounds e.
      simpl_options. destruct (sem s2 x); cbn -[Z.add] in *; applyDesc e (@balanceL_Desc e a).
      destruct (f x a0) eqn : ?. simpl in Hsz. rewrite Hsz. left. assumption.
      simpl in Hsz. rewrite Hsz. solve_size.
      solve_Desc e. rewrite Hsz0. destruct (f x a0); simpl in Hsz; rewrite Hsz; cbn -[Z.add]; omega.
      solve_Desc e.
Qed.

(** ** Verification of [update] *)
Lemma update_spec: forall (m: Map e a) (f: a -> option a) k,
  update f k m = updateWithKey (fun _ x => f x) k m.
Proof. 
  intros. unfold update. reflexivity.
Qed.

(** ** Verification of [updateLookupWithKey] *)
Lemma updateLookupWithKey_lookup_f_true:
  forall (m: Map e a) lb ub f k v v1,
  Bounded m lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  sem m k = Some v ->
  f k v = Some v1 ->
  fst ((updateLookupWithKey f k m)) = Some v1.
Proof.
  intros. generalize dependent k. revert v v1. induction H; intros.
  - inversion H1.
  - simpl. simpl in H6. destruct (sem s1 k) eqn : ?.
   + assert (compare k x = Lt) by (solve_Bounds e). rewrite H8. 
     rewrite (pair_fst_snd (updateLookupWithKey f k s1 )). simpl.
     eapply IHBounded1. apply Heqo. inversion H6. apply H7.
   + simpl in H6. destruct (k == x) eqn : ?.
      * simpl in H6. assert (compare k x = Eq) by (order e).
        rewrite H8. destruct (f x v) eqn : ?.
        -- simpl. inversion H6; subst. rewrite <- Heqo0. rewrite <- H7.
           apply equal_f. apply H0. order e.
        -- simpl. inversion H6; subst. assert (f k v0 = f x v0). apply equal_f.
           apply H0. order e. rewrite <- H4 in Heqo0. rewrite Heqo0 in H7.
           inversion H7.
      * simpl. destruct (sem s2 k) eqn : ?.
        -- assert (compare k x = Gt) by (solve_Bounds e). rewrite H8. 
           rewrite (pair_fst_snd (updateLookupWithKey f k s2 )). simpl.
           eapply IHBounded2. apply Heqo0. inversion H6; subst. apply H7.
        -- inversion H6.
Qed.

Lemma updateLookupWithKey_lookup_f_false:
  forall (m: Map e a) lb ub f k v,
  Bounded m lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  sem m k = Some v ->
  f k v = None ->
  fst ((updateLookupWithKey f k m)) = Some v.
Proof.
  intros. generalize dependent v. revert k. induction H; intros.
  - inversion H1.
  - simpl in H6. simpl. destruct (sem s1 k) eqn : ?.
    + assert (compare k x = Lt) by (solve_Bounds e). rewrite H8.
      rewrite (pair_fst_snd (updateLookupWithKey f k s1 )). simpl.
      eapply IHBounded1. inversion H6; subst. apply Heqo. apply H7.
    + simpl in H6. destruct (k == x) eqn : ?.
      * simpl in H6. assert (compare k x = Eq) by (order e).
        rewrite H8. destruct (f x v) eqn : ?.
        -- simpl. inversion H6; subst.  assert (f k v0 = f x v0). apply equal_f.
           apply H0. order e. rewrite H4 in H7. rewrite H7 in Heqo0. inversion Heqo0.
        -- simpl. assumption.
      * simpl in H6. assert (compare k x = Gt) by (solve_Bounds e). rewrite H8. 
           rewrite (pair_fst_snd (updateLookupWithKey f k s2 )). simpl.
           eapply IHBounded2. apply H6. apply H7.
Qed. 

Lemma updateLookupWithKey_lookup_None:
  forall (m: Map e a) lb ub f k,
  Bounded m lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  sem m k = None ->
  fst ((updateLookupWithKey f k m)) = None.
Proof.
  intros. generalize dependent k. induction H; intros.
  - simpl. reflexivity.
  - simpl in H6. simpl. destruct (sem s1 k) eqn : ?. inversion H6.
    destruct (k == x) eqn : ?. inversion H6. destruct (sem s2 k) eqn : ?.
    inversion H6.
    destruct (compare k x) eqn : ?.
    + order e.
    + rewrite (pair_fst_snd (updateLookupWithKey f k s1 )). simpl. apply IHBounded1.
      assumption.
    + rewrite (pair_fst_snd (updateLookupWithKey f k s2 )). simpl. apply IHBounded2.
      assumption.
Qed.

(*This makes the Desc incredibly easy*)
Lemma updateWithKey_updateLookupWithKey: forall (m: Map e a) f k,
  updateWithKey f k m = snd(updateLookupWithKey f k m).
Proof.
  intros m. induction m; intros.
  - simpl. destruct (compare k0 k).
    + destruct (f k a0); simpl; reflexivity. 
    + rewrite (pair_fst_snd (updateLookupWithKey f k0 m1)). simpl.
      rewrite IHm1. reflexivity.
    + rewrite (pair_fst_snd (updateLookupWithKey f k0 m2)). simpl.
      rewrite IHm2. reflexivity.
  - simpl. reflexivity.
Qed.  

Lemma updateLookupWithKey_Desc: 
  forall x f (m: Map e a) lb ub,
  Bounded m lb ub ->
  Proper ((fun i j : e => _GHC.Base.==_ i j = true) ==> eq) f ->
  Desc (snd(updateLookupWithKey f x m)) lb ub (match sem m x with
                                    | None => size m
                                    | Some y => if isSome (f x y) then
                                       size m else size m - 1
                                      end) (fun i => if i == x then match (sem m x) with
                                                                     | Some v => f x v
                                                                     | None => None end else sem m i).
Proof.
  intros. rewrite <- updateWithKey_updateLookupWithKey. apply updateWithKey_Desc; assumption.
Qed.


(** ** Verification of [alter] *)
(*Note: the bounds assumptions are only needed in the insert case, but we can always expand the bounds
  if needed*)
Lemma alter_Desc:
  forall m (f: option a -> option a) k lb ub,
  Bounded m lb ub ->
  isLB lb k = true ->
  isUB ub k = true ->
  Desc(alter f k m) lb ub (if (negb (isSome (sem m k)) && isSome (f None)) then (1 + size m)%Z
  else if (isSome(sem m k) && negb (isSome (f (sem m k)))) then (size m - 1)%Z else size m)
  (fun i => (if i == k then f (sem m k) else sem m i)).
Proof.
  intros ????? HB HL HU. induction HB.
  - simpl. destruct (f None).
    + applyDesc e (@singleton_Desc e a). solve_Desc e.
    + solve_Desc e.
  - cbn -[Z.add]. destruct (compare k x) eqn : Heq.
    + replace (k == x) with true by solve_Bounds e. simpl_options.
      destruct (f (Some v)) eqn : ?.
      * solve_Desc e. simpl. 
        rewrite -> (sem_outside_above HB1) by (solve_Bounds e). simpl_options.
        rewrite Heqo. simpl. reflexivity. f_solver e.
        assert (sem s1 k = None). eapply sem_outside_above. eassumption.
        solve_Bounds e. rewrite H3 in Heqo1. simpl in Heqo1. rewrite Heqo1 in Heqo.
        inversion Heqo. reflexivity.
        assert (sem s1 k = None). eapply sem_outside_above. eassumption. solve_Bounds e.
        rewrite H3 in Heqo1. simpl in Heqo1. rewrite Heqo1 in Heqo. inversion Heqo.
      * rewrite -> (sem_outside_above HB1) by (solve_Bounds e).
        rewrite -> (sem_outside_below HB2) by (solve_Bounds e).
        simpl_options. applyDesc e glue_Desc. solve_Desc e.
        simpl. rewrite Heqo. simpl. solve_size.
    + replace (k == x) with false by solve_Bounds e. 
      rewrite -> (sem_outside_below HB2) by (solve_Bounds e).
      simpl_options.
      applyDesc e IHHB1. applyDesc e (@balance_Desc e a). destruct (sem s1 k). simpl in Hsz.
      destruct (f (Some a0)); simpl in Hsz; solve_size. cbn -[Z.add] in *.
      destruct (f None). cbn -[Z.add] in *. solve_size.
      simpl in Hsz. solve_size. solve_Desc e.
      rewrite Hsz0. rewrite Hsz. destruct (sem s1 k); cbn -[Z.add].
      destruct (f(Some a0)); cbn -[Z.add]; solve_size.
      destruct (f(None)); cbn -[Z.add]; solve_size.
    + replace (k == x) with false by (order e).
      rewrite -> (sem_outside_above HB1) by (solve_Bounds e). 
      simpl_options.
      applyDesc e IHHB2. applyDesc e (@balance_Desc e a). destruct (sem s2 k); cbn -[Z.add] in *.
      destruct (f(Some a0)); cbn -[Z.add] in *; solve_size.
      destruct (f(None)); cbn -[Z.add] in *; solve_size.
      solve_Desc e. rewrite Hsz0. rewrite Hsz. destruct (sem s2 k); cbn -[Z.add].
      destruct (f(Some a0)); cbn -[Z.add]; solve_size.
      destruct (f(None)); cbn -[Z.add]; solve_size.
Qed.

Lemma delete_WF:
  forall x (s: Map e a), WF s -> WF (delete x s).
Proof.
  intros. eapply Desc_WF.
  eapply delete_Desc. assumption.
Qed.

Lemma alter_WF :
  forall f x (s : Map e a), WF s -> WF (alter f x s).
Proof.
  intros. eapply Desc_WF.
  eapply alter_Desc; [assumption | reflexivity | reflexivity ].
Qed.

Lemma adjust_WF :
  forall f x (s : Map e a),
    WF s -> WF (adjust f x s).
Proof.
  intros. eapply Desc_WF. rewrite adjust_spec.
  eapply adjustWithKey_Desc.
  - assumption.
  - intros i j Heq. reflexivity.
Qed.

End WF.
