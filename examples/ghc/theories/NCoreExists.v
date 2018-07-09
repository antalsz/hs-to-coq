Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Coq.Vectors.Vector.
Require Import Psatz.

Require Import Id.
Require Import Core.
Require Import BasicTypes.

Require Import Proofs.Var.
Require Import Proofs.CoreInduct.
Require Import Proofs.NCore.
Require Import Proofs.JoinPointInvariants.
Require Import Proofs.GhcTactics.
Require Import Proofs.VectorUtils.


Set Bullet Behavior "Strict Subproofs".

Lemma forall_exists:
  forall {a b} (f : a -> b) xs,
  Forall (fun x => exists nx, x = f nx) xs ->
  exists nxs, xs = map f nxs.
Proof.
  intros.
  induction H.
  * exists nil. reflexivity.
  * destruct IHForall as [nxs Heql]. rewrite Heql.
    destruct H as [nx Heq]. rewrite Heq. clear Heq. 
    simpl.
    exists (nx :: nxs).
    reflexivity.
Qed.


Lemma forall_exists_vector:
  forall {a b} (f : a -> b) xs,
  Forall (fun x => exists nx, x = f nx) xs ->
  exists nxs : Vector.t _ (length xs), xs = Vector.to_list (Vector.map f nxs).
Proof.
  intros.
  induction H.
  * exists (Vector.nil _). reflexivity.
  * destruct IHForall as [nxs Heql]. rewrite Heql.
    destruct H as [nx Heq]. rewrite Heq. clear Heq. 
    simpl.
    rewrite length_to_list.
    exists (Vector.cons _ nx _ nxs).
    reflexivity.
Qed.

Program Fixpoint isJoinPointsValid_to_NCore e n jps { measure e (CoreLT) }:
  isJoinPointsValid e n jps = true ->
  exists n, e = toExpr n := _.
Next Obligation.
  rename isJoinPointsValid_to_NCore into IH.
  destruct e.
  * exists (NVar s). reflexivity.
  * exists (NLit l). reflexivity.
  * simpl in H. simpl_bool.
    destruct H as [He1 He2].
    epose proof (IH _ _ _ _ He1) as IHe1.
    epose proof (IH _ _ _ _ He2) as IHe2.
    destruct IHe1 as [ne1 Heq1].
    destruct IHe2 as [ne2 Heq2].
    subst.
    exists (NApp ne1 ne2). reflexivity.
  * simpl in H. simpl_bool.
    destruct H as [HiJI He].
    rewrite negb_true_iff in *.
    epose proof (IH _ _ _ _ He) as IHe.
    destruct IHe as [ne Heq]; subst.
    exists (NLam c ne). reflexivity.
  * simpl in H.
    destruct b as [v rhs|pairs].
    + fold isJoinPointsValidPair in H.
      simpl_bool.
      destruct H as [Hpair He].
      destruct (isJoinId_maybe v) eqn:HisI.
      - eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS in Hpair; only 2: apply HisI.
        pose proof (isJoinRHS_mkLams3 _ _ _ Hpair).
        destruct H as [body [vs [Heq1 Heq2]]]. subst.
        pose proof (isJoinRHS_mkLams2 _ _ _ Hpair).
        destruct H as [Hnot_join_params Hbody].
        epose proof (IH _ _ _ _ Hbody) as IHrhs.
        destruct IHrhs as [nrhs ?]; subst.
        epose proof (IH _ _ _ _ He) as IHe.
        destruct IHe as [ne ?]; subst.
        exists (NLet (NNonRecJoin (Mk_NJPair v vs nrhs HisI)) ne).
        reflexivity.
      - apply isJoinPointsValidPair_isJoinPointsValid in Hpair; only 2: apply HisI.
        epose proof (IH _ _ _ _ Hpair) as IHrhs.
        destruct IHrhs as [nrhs ?]; subst.
        epose proof (IH _ _ _ _ He) as IHe.
        destruct IHe as [ne ?]; subst.
        exists (NLet (NNonRec (Mk_NPair v nrhs HisI)) ne).
        reflexivity.
     + simpl_bool.
       destruct H as [[Hnot_null Hall_or_none] [Hpairs Hbody]].
       rewrite negb_true_iff in Hnot_null.
       rewrite orb_true_iff in Hall_or_none.
       destruct Hall_or_none as [Hnone|Hall].
       - assert (exists m, length pairs = S m). {
           destruct pairs.
           + simpl in Hnot_null. congruence.
           + exists (length pairs). reflexivity.
         }
         destruct H as [m Hlength].
         assert (exists npairs, pairs = @Vector.to_list _ (S m) (Vector.map toPair npairs)).
         { rewrite <- Hlength.
           clear Hlength Hnot_null Hbody.
           apply forall_exists_vector.
           rewrite forallb_forall in *.
           rewrite Forall_forall.
           intros [v rhs] HIn.
           specialize (Hnone _ HIn).
           simpl in Hnone. rewrite negb_true_iff in Hnone.
           assert (isJoinId_maybe v = None) as HiJI
             by (rewrite isJoinId_eq in Hnone; destruct isJoinId_maybe; congruence).
           specialize (Hpairs _ HIn).
           simpl in Hpairs. fold isJoinPointsValidPair in Hpairs.
           apply isJoinPointsValidPair_isJoinPointsValid in Hpairs; only 2: apply HiJI.
           epose proof (IH _ _ _ _ Hpairs) as IHe.
           destruct IHe as [ne ?]; subst.
           exists (Mk_NPair v ne HiJI).
           reflexivity.
         }
         destruct H as [npairs Heq].
         rewrite Heq. clear Heq.
         epose proof (IH _ _ _ _ Hbody) as IHe.
         destruct IHe as [ne ?]; subst.
         exists (NLet (NRec m npairs) ne).
         reflexivity.
       - assert (exists m, length pairs = S m). {
           destruct pairs.
           + simpl in Hnot_null. congruence.
           + exists (length pairs). reflexivity.
         }
         destruct H as [m Hlength].
         assert (exists npairs, pairs = @Vector.to_list _ (S m) (Vector.map toJPair npairs)).
         { rewrite <- Hlength.
           clear Hlength Hnot_null Hbody.
           apply forall_exists_vector.
           rewrite forallb_forall in *.
           rewrite Forall_forall.
           intros [v rhs] HIn.
           specialize (Hall _ HIn).
           simpl in Hall.
           rewrite isJoinId_eq in Hall; destruct isJoinId_maybe eqn:HiJI; try congruence; clear Hall.
           specialize (Hpairs _ HIn).
           simpl in Hpairs. fold isJoinPointsValidPair in Hpairs.
           eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS in Hpairs; only 2: apply HiJI.
           pose proof (isJoinRHS_mkLams3 _ _ _ Hpairs).
           destruct H as [body [vs [Heq1 Heq2]]]. subst.
           pose proof (isJoinRHS_mkLams2 _ _ _ Hpairs).
           destruct H as [Hnot_join_params Hbody].
           epose proof (IH _ _ _ _ Hbody) as IHe.
           destruct IHe as [ne ?]; subst.
           exists (Mk_NJPair v vs ne HiJI).
           reflexivity.
         }
         destruct H as [npairs Heq].
         rewrite Heq. clear Heq.
         epose proof (IH _ _ _ _ Hbody) as IHe.
         destruct IHe as [ne ?]; subst.
         exists (NLet (NRecJoin m npairs) ne).
         reflexivity.
   * simpl in H. simpl_bool.
     destruct H as [[Hno_join Hscrut] Halts].
     epose proof (IH _ _ _ _ Hscrut) as IHe.
     destruct IHe as [ne ?]; subst.
     assert (exists nalts, l = (List.map (fun '(dc,pats,rhs) => (dc, pats, toExpr rhs)) nalts)).
     { apply forall_exists.
       rewrite Forall_forall.
       rewrite forallb_forall in *.
       intros [[dc pats] rhs] HIn.
       specialize (Halts _ HIn).
       simpl_bool.
       destruct Halts as [Hnot_join_v Hrhs].
       epose proof (IH _ _ _ _ Hrhs) as IHe.
       destruct IHe as [nrhs ?]; subst.
       exists (dc, pats, nrhs). reflexivity.
     } 
     destruct H as [nalts Heq]. subst.
     destruct u.
     exists (NCase ne c nalts).
     reflexivity.
   * simpl in H.
     epose proof (IH _ _ _ _ H) as IHe.
     destruct IHe as [ne ?]; subst.
     destruct u.
     exists (NCast ne).
     reflexivity.
   * simpl in H.
     epose proof (IH _ _ _ _ H) as IHe.
     destruct IHe as [ne ?]; subst.
     exists (NTick t ne).
     reflexivity.
   * simpl in H.
     destruct u.
     exists NType.
     reflexivity.
   * simpl in H.
     destruct u.
     exists NCoercion.
     reflexivity.
Unshelve.
  all: Core_termination || (unfold CoreLT; simpl; lia). (* phew *)
Qed.

Lemma isJoinPointsValid_to_NCore_join_pairs:
  forall pairs jps,
  forallb (fun p : Var * Expr CoreBndr => isJoinId (fst p)) pairs = true ->
  forallb (fun '(v, e) => isJoinPointsValidPair v e (updJPSs jps (map fst pairs))) pairs = true ->
  exists npairs, pairs = map toJPair npairs.
Proof.
  intros ?? Hall Hpairs.
  apply forall_exists.
  rewrite forallb_forall in *.
  rewrite Forall_forall.
  intros [v rhs] HIn.
  specialize (Hall _ HIn).
  simpl in Hall.
  rewrite isJoinId_eq in Hall; destruct isJoinId_maybe eqn:HiJI; try congruence; clear Hall.
  specialize (Hpairs _ HIn).
  simpl in Hpairs. fold isJoinPointsValidPair in Hpairs.
  eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS in Hpairs; only 2: apply HiJI.
  pose proof (isJoinRHS_mkLams3 _ _ _ Hpairs).
  destruct H as [body [vs [Heq1 Heq2]]]. subst.
  pose proof (isJoinRHS_mkLams2 _ _ _ Hpairs).
  destruct H as [Hnot_join_params Hbody].
  epose proof (isJoinPointsValid_to_NCore _ _ _ Hbody) as IHe.
  destruct IHe as [ne ?]; subst.
  exists (Mk_NJPair v vs ne HiJI).
  reflexivity.
Qed.

Lemma isValidJoinPointsPair_to_NCore_join_pairs:
  forall pairs jps,
  Forall (fun p => isValidJoinPointsPair (fst p) (snd p) (updJPSs jps (map fst pairs)) = true) pairs ->
  exists npairs, pairs = map toJPair npairs.
Proof.
  intros.
  rewrite Forall_isValidJoinPointsPair_forallb_isJoinId_isJoinPointsValidPair in H.
  destruct H.
  eapply isJoinPointsValid_to_NCore_join_pairs; eassumption.
Qed.