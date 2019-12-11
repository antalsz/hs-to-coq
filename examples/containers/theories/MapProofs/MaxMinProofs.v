Require Import MapProofs.Common.
Set Bullet Behavior "Strict Subproofs".
Require Import MapProofs.Bounds.
Require Import MapProofs.Tactics.

Section WF.
Context {e : Type} {a : Type} {HEq : Eq_ e} {HOrd : Ord e} {HEqLaws : EqLaws e}  {HOrdLaws : OrdLaws e}.
(** ** Verification of [maxViewSure] *)

Lemma maxViewSure_Desc:
  forall sz' (x: e) (v: a) s1 s2 lb ub,
    Bounded (Bin sz' x v s1 s2) lb ub ->
    forall P,
    (forall y vy r,
      (y = x /\ vy = v \/ sem s2 y = Some vy) /\
      Desc r lb (Some y) (size s1 + size s2)
                         (fun i => if i == y then None else (sem s1 i ||| (if i == x then Some v else None) ||| sem s2 i)) ->
      P (Mk_MaxView y vy r)) ->
    P (maxViewSure x v s1 s2).
    (* we know that y is in the input, and we actually know more: it is x or in s2 *)
Proof.
  intros ??????? HB.
  revert sz' x v s1 lb ub HB.
  induction s2; intros sz' x v s1 lb ub HB;subst.
  - clear IHs2_1.
    simpl.
    intros X HX.
    destruct (maxViewSure k a0 s2_1 s2_2) eqn:HmaxView.
    apply HX. clear X HX.

    inversion HB; subst; clear HB.
    inversion H5; subst.

    revert HmaxView.
    eapply IHs2_2; only 1: solve_Bounded e.
    intros y vy r H; destruct H as [Hthere IHD]; clear IHs2_2.
    cbn -[Z.add size] in *; rewrite size_Bin in H11.

    intro HmaxView; inversion HmaxView; subst; clear HmaxView.

    applyDesc e IHD; clear IHD.

    split.
    + right.
      destruct Hthere as [[H H2]|H]; rewrite H in *.
      * subst. rewrite Eq_refl.
        erewrite sem_outside_above by solve_Bounds e.
        reflexivity.
      * erewrite sem_outside_above by solve_Bounds e.
        replace (e0 == k) with false by solve_Bounds e.
        reflexivity.
    + destruct Hthere as [[Heq Heq1]|Hthere].
      * subst; applyDesc e (@balanceL_Desc e a); solve_Desc e.
      * applyDesc e (@balanceL_Desc e a).
        solve_Desc e.
  - intros X HX.
    destruct (maxViewSure _ _ _ _) eqn:HmaxView.
    apply HX. clear X HX.
    cbn -[Z.add size] in *.
    inversion HB; subst; clear HB.
    inversion HmaxView; subst; clear HmaxView.
    split; [left; (split;reflexivity) | solve_Desc e].
Qed.

(** ** Verification of [lookupMin] *)

Lemma empty_no_elts : forall (m: Map e a),
  (forall i, sem m i = None) <-> m = empty.
Proof.
  intros. split; intros.
  destruct m. specialize (H e0). simpl in H. destruct (sem m1 e0); simpl in H.
  inversion H. rewrite Eq_Reflexive in H. inversion H. reflexivity. rewrite H. reflexivity.
Qed.

Lemma lookupMin_in_bin: forall (m: Map e a),
  m <> Tip -> forall k1 k2 v1 v2, lookupMinSure k1 v1 m = lookupMinSure k2 v2 m.
Proof.
  intros. destruct m; intros.
  - simpl. reflexivity.
  - contradiction.
Qed.

Lemma lookupMax_in_bin: forall (m: Map e a),
  m <> Tip -> forall k1 k2 v1 v2, lookupMaxSure k1 v1 m = lookupMaxSure k2 v2 m.
Proof.
  intros. destruct m; intros.
  - simpl. reflexivity.
  - contradiction.
Qed.

Lemma lookupMinSure_Desc:
  forall (m: Map e a) x v0 lb ub,
    Bounded m lb ub ->
    let (y, v) := lookupMinSure x v0 m in
    ((forall i, sem m i = None) /\ y = x /\ v = v0 \/
      sem m y = Some v /\ (forall i v1, sem m i = Some v1 -> (y GHC.Base.<= i) = true)).
Proof.
  intros.  revert x v0. induction H; intros.
  - left. simpl. intuition.
  - destruct (lookupMinSure x0 v0 (Bin sz x v s1 s2)) eqn : ?. right. simpl.
    specialize (IHBounded1 x0 v0). destruct (lookupMinSure x0 v0 s1) eqn : ?. destruct IHBounded1.
    + destruct H5. destruct H6. assert (sem s1 e0 = None) by (apply H5). rewrite H8; simpl. subst.
      simpl in Heqp. apply empty_no_elts in H5. subst. inversion Heqp. subst.
      rewrite Eq_Reflexive. simpl. split. reflexivity. intros.
      destruct (e0 == i) eqn : ?. order e. assert (i == e0 = false) by order e. rewrite H5 in H3.
      simpl in H3. solve_Bounds e.
    + destruct H5. simpl in Heqp. assert (s1 <> Tip). { destruct s1. intro. discriminate H7.
      simpl in H5. inversion H5. }
      eapply lookupMin_in_bin in H7. rewrite Heqp in H7. rewrite Heqp0 in H7. inversion H7; subst.
      rewrite H5. simpl. split. reflexivity. intros.
      destruct (sem s1 i) eqn : ?. simpl in H3. inversion H3; subst.
      apply H6 in Heqo. assumption.
      simpl in H3. assert (_GHC.Base.<=_  e1 x = true) by solve_Bounds e.
      destruct (i == x) eqn : ?. order e. simpl in H3. solve_Bounds e.
Qed.

Lemma lookupMin_Desc:
  forall (m: Map e a) lb ub,
    Bounded m lb ub ->
    match lookupMin m with
      | None => (forall i, sem m i = None)
      | Some (y, v) => sem m y = Some v /\ (forall i v1, sem m i = Some v1 -> (y GHC.Base.<= i) = true)
    end.
Proof.
  intros.
  unfold lookupMin.
  inversion H; subst; clear H.
  * reflexivity.
  * simpl.
    pose proof (lookupMinSure_Desc s1 x v lb (Some x) H0). destruct (lookupMinSure x v s1) eqn : ?.
    destruct H.
    - destruct H; subst. apply empty_no_elts in H; subst. simpl. simpl in Heqp. inversion Heqp; subst.
      rewrite Eq_Reflexive. simpl. split. reflexivity. intros. destruct (i == e0) eqn : ?.
      order e. simpl in H. solve_Bounds e.
    - destruct H. rewrite H. simpl; split. reflexivity. intros. destruct (sem s1 i) eqn : ?.
      apply H4 in Heqo. assumption. simpl in H6. destruct (i == x) eqn : ?.
      solve_Bounds e. simpl in H6. solve_Bounds e.
Qed.


(** ** Verification of [lookupMax] *)

Lemma lookupMaxSure_Desc:
  forall (m: Map e a) x v0 lb ub,
    Bounded m lb ub ->
    let (y, v) := lookupMaxSure x v0 m in
    ((forall i, sem m i = None) /\ y = x /\ v = v0 \/
      sem m y = Some v /\ (forall i v1, sem m i = Some v1 -> (i GHC.Base.<= y) = true)).
Proof.
  intros.  revert x v0. induction H; intros.
  - left. simpl. intuition.
  - destruct (lookupMaxSure x0 v0 (Bin sz x v s1 s2)) eqn : ?. right. simpl.
    specialize (IHBounded2 x0 v0). destruct (lookupMaxSure x0 v0 s2) eqn : ?. destruct IHBounded2.
    + destruct H5. destruct H6. assert (sem s2 e0 = None) by (apply H5). rewrite H8; simpl. subst.
      simpl in Heqp. apply empty_no_elts in H5. subst. inversion Heqp. subst.
      rewrite Eq_Reflexive. simpl.  assert (sem s1 e0 = None). { eapply sem_outside_above.
      apply H. unfold isUB. order e. } split. rewrite H3. reflexivity. intros.
      destruct (e0 == i) eqn : ?. order e. assert (i == e0 = false) by order e. rewrite H6 in H5.
      simpl in H5. rewrite oro_None_r in H5. rewrite oro_None_r in H5. solve_Bounds e.
    + destruct H5. simpl in Heqp. assert (s2 <> Tip). { destruct s2. intro. discriminate H7.
      simpl in H5. inversion H5. }
      eapply lookupMax_in_bin in H7. rewrite Heqp in H7. rewrite Heqp0 in H7. inversion H7; subst.
      rewrite H5. assert (sem s1 e1 = None). { eapply (sem_inside H0) in H5. destruct H5.
      eapply sem_outside_above. apply H. solve_Bounds e. } rewrite H3. simpl.
      destruct (e1 == x) eqn : ?. solve_Bounds e. simpl. split. reflexivity. intros.
      destruct (sem s1 i) eqn : ?. solve_Bounds e. simpl in H8. destruct (i == x) eqn : ?.
      solve_Bounds e. simpl in H8. apply H6 in H8. assumption.
Qed.

Lemma lookupMax_Desc:
  forall (m: Map e a) lb ub,
    Bounded m lb ub ->
    match lookupMax m with
      | None => (forall i, sem m i = None)
      | Some (y, v) => sem m y = Some v /\ (forall i v1, sem m i = Some v1 -> (i GHC.Base.<= y) = true)
    end.
Proof.
  intros.
  unfold lookupMax.
  inversion H; subst; clear H.
  * reflexivity.
  * simpl.
    pose proof (lookupMaxSure_Desc s2 x v (Some x) ub H1). destruct (lookupMaxSure x v s2) eqn : ?.
    destruct H.
    - destruct H; subst. apply empty_no_elts in H; subst. simpl. simpl in Heqp. inversion Heqp; subst.
      rewrite Eq_Reflexive. simpl. split. assert (sem s1 e0 = None). { eapply sem_outside_above.
      apply H0. solve_Bounds e. } rewrite H. reflexivity.
      intros. destruct (i == e0) eqn : ?.
      order e. simpl in H. rewrite oro_None_r in H. rewrite oro_None_r in H. solve_Bounds e.
    - destruct H. rewrite H. simpl; split. assert (sem s1 e0 = None). { eapply sem_outside_above.
      apply H0. apply (sem_inside H1) in H. solve_Bounds e. } rewrite H6.
      destruct (e0 == x) eqn : ?. solve_Bounds e. simpl. reflexivity.
      intros. destruct (sem s1 i) eqn : ?. solve_Bounds e. simpl in H6. destruct (i == x) eqn : ?.
      solve_Bounds e. simpl in H6. eapply H4. apply H6.
Qed.


(** ** Verification of [minViewSure] *)

Lemma minViewSure_Desc:
  forall sz' (x: e) (v: a) s1 s2 lb ub,
    Bounded (Bin sz' x v s1 s2) lb ub ->
    forall P,
    (forall y vy r,
      (y = x /\ vy = v \/ sem s1 y = Some vy) /\
      Desc r (Some y) ub (size s1 + size s2)
                         (fun i => if i == y then None else (sem s1 i ||| (if i == x then Some v else None) ||| sem s2 i)) ->
      P (Mk_MinView y vy r)) ->
    P (minViewSure x v s1 s2).
    (* we know that y is in the input, and we actually know more: it is x or in s2 *)
Proof.
  intros ??????? HB.
  revert sz' x v s2 lb ub HB.
  induction s1; intros sz' x v s2 lb ub HB;subst.
  - clear IHs1_2.
    simpl.
    intros X HX.
    destruct (minViewSure _ _ _ _ ) eqn:HmaxView.
    apply HX. clear X HX.

    inversion HB; subst; clear HB.
    inversion H4; subst.

    revert HmaxView.
    eapply IHs1_1; only 1: solve_Bounded e.
    intros y vy r H; destruct H as [Hthere IHD]; clear IHs1_1.
    cbn -[Z.add size] in *; rewrite size_Bin in H11.

    intro HmaxView; inversion HmaxView; subst; clear HmaxView.

    applyDesc e IHD; clear IHD.

    split.
    + right.
      destruct Hthere as [[H H2]|H]; rewrite H in *.
      * subst. rewrite Eq_refl.
        erewrite sem_outside_above by solve_Bounds e.
        reflexivity.
      * reflexivity.
    + destruct Hthere as [[Heq Heq1]|Hthere].
      * subst; applyDesc e (@balanceR_Desc e a); solve_Desc e.
      * applyDesc e (@balanceR_Desc e a); solve_Desc e.
  - intros X HX.
    destruct (minViewSure _ _ _ _) eqn:Hview.
    apply HX. clear X HX.
    cbn -[Z.add size] in *.
    inversion HB; subst; clear HB.
    inversion Hview; subst; clear Hview.
    split; [left; (split;reflexivity) | solve_Desc e].
Qed.

(** ** Verification of [maxView] *)

Lemma maxViewWithKey_Desc:
  forall (m: Map e a) lb ub,
    Bounded m lb ub ->
    forall (P : option ((e * a) * Map e a) -> Prop),
    (forall y r v,
      (sem m y = Some v) /\
      Desc r lb (Some y) (size m - 1) (fun i => if (i == y) then None else sem m i) ->
      P (Some ((y, v), r))) ->
    ((forall i, sem m i = None) -> P None) ->
    P (maxViewWithKey m).
Proof.
  intros ??? HB P HSome HNone.
  unfold maxViewWithKey.
  inversion HB; subst.
  * apply HNone. intro; reflexivity.
  * unfold op_zdzn__, Datatypes.id, op_zd__.
    eapply maxViewSure_Desc; only 1: eassumption.
    intros.
    apply HSome.
    split.
    - simpl. destruct H3. destruct H3. destruct H3. subst. rewrite Eq_Reflexive.
      assert (sem s1 x = None). { eapply sem_outside_above. apply H. solve_Bounds e. }
      rewrite H3. simpl. reflexivity. rewrite H3.
      assert (sem s1 y = None). { eapply sem_outside_above. apply H. solve_Bounds e. }
      rewrite H6. simpl. destruct (y == x) eqn : ?. solve_Bounds e. reflexivity.
    - applyDesc e H3. solve_Desc e.
Qed.

Lemma maxViewDesc:
  forall (m: Map e a) lb ub,
  Bounded m lb ub ->
  maxView m = match maxViewWithKey m with
            |None => None
            | Some ((x,y), m) => Some (y, m)
            end.
Proof.
  intros. unfold maxView. reflexivity.
Qed.

(** ** Verification of [minView] *)

Lemma minViewWithKey_Desc:
  forall (m: Map e a) lb ub,
    Bounded m lb ub ->
    forall (P : option ((e * a) * Map e a) -> Prop),
    (forall y r v,
      (sem m y = Some v) /\
      Desc r (Some y) ub  (size m - 1) (fun i => if (i == y) then None else sem m i) ->
      P (Some ((y, v), r))) ->
    ((forall i, sem m i = None) -> P None) ->
    P (minViewWithKey m).
Proof.
  intros ??? HB P HSome HNone.
  unfold minViewWithKey.
  inversion HB; subst.
  * apply HNone. intro; reflexivity.
  * unfold op_zdzn__, Datatypes.id, op_zd__.
    eapply minViewSure_Desc; only 1: eassumption.
    intros.
    apply HSome.
    split.
    - simpl. destruct H3. destruct H3. destruct H3. subst. rewrite Eq_Reflexive.
      assert (sem s1 x = None). { eapply sem_outside_above. apply H. solve_Bounds e. }
      rewrite H3. simpl. reflexivity. rewrite H3. simpl. reflexivity.
    - applyDesc e H3. solve_Desc e.
Qed.

Lemma minViewDesc:
  forall (m: Map e a) lb ub,
  Bounded m lb ub ->
  minView m = match minViewWithKey m with
            |None => None
            | Some ((x,y), m) => Some (y, m)
            end.
Proof.
  intros. unfold minView. reflexivity.
Qed.

End WF.
