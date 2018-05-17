Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.

Require Import Coq.Lists.List.

Require Import Proofs.GhcTactics.
Require Import Proofs.Base.
Require Import Proofs.CoreInduct.
Require Import Proofs.Core.

Set Bullet Behavior "Strict Subproofs".

Axiom freeVarsBind1_freeVarsBind: freeVarsBind1 = freeVarsBind.

Import GHC.Base.Notations.

Scheme expr_mut := Induction for Expr Sort Prop
  with bind_mut := Induction for Bind Sort Prop.

(** Basic properties of [exprFreeVars] *)

Axiom exprFreeVars_Var: forall v, exprFreeVars (Mk_Var v) = unitVarSet v.

Axiom exprFreeVars_Lam:
  forall v e,
  exprFreeVars (Lam v e) = delVarSet (exprFreeVars e) v.

Lemma exprFreeVars_mkLams:
  forall vs e,
  exprFreeVars (mkLams vs e) = delVarSetList (exprFreeVars e) vs.
Proof.
  intros. 
  induction vs.
  - unfold mkLams. unfold_Foldable.
    unfold delVarSetList.
    unfold UniqSet.delListFromUniqSet.
    unfold UniqFM.delListFromUFM.
    destruct (exprFreeVars e).
    f_equal.
  - revert IHvs.
    unfold mkLams.
    unfold_Foldable.
    unfold exprFreeVars.
    unfold Base.op_z2218U__.
    unfold exprFVs.
    unfold Base.op_z2218U__.
    simpl.
Admitted.

(** Working with [freeVars] *)


Lemma deAnnotate_freeVars:
  forall e, deAnnotate (freeVars e) = e.
Proof.
  intro e.
  apply (core_induct e);
    intros; simpl; try reflexivity;
      try solve [destruct (freeVars e0) eqn:Hfv; simpl in H; rewrite H; reflexivity].
  - destruct (isLocalVar v); reflexivity.
  - symmetry. f_equal.
    + destruct (freeVars e1) eqn:fv. rewrite <- H; reflexivity.
    + destruct (freeVars e2) eqn:fv. rewrite <- H0; reflexivity.
  - destruct (freeVars e0) eqn:Hfv.
    destruct (delBinderFV v f) eqn:Hdb.
    unfold deAnnotate in H.
    destruct (Base.op_zg__ BinNums.Z0 i0); simpl; rewrite H; reflexivity.
  - rewrite freeVarsBind1_freeVarsBind.
    destruct binds; simpl.
    + destruct (freeVars body) eqn:Hfv. rewrite <- H0.
      destruct (freeVars e0) eqn:Hfv'. rewrite <- H. reflexivity.
    + destruct (List.unzip l) eqn:Hl. simpl.
      destruct (freeVars body) eqn:Hfv. rewrite <- H0. f_equal.
      generalize dependent l1; generalize dependent l0.
      induction l; simpl; intros.
      * inversion Hl; subst. reflexivity.
      * destruct a0. destruct (List.unzip l) eqn:Hl'. inversion Hl; subst.
        simpl. do 2 f_equal.
        -- f_equal. erewrite <- H with (v:=c). reflexivity. intuition.
        -- assert (forall (v : CoreBndr) (rhs : Expr CoreBndr),
                      In (v, rhs) l -> deAnnotate (freeVars rhs) = rhs).
           { intros. apply H with (v:=v).
             apply in_cons; assumption. }
           specialize (IHl H0 l2 l3 eq_refl). inversion IHl; reflexivity.
  - destruct (List.unzip
                (List.map
                   (fun '(con, args, rhs) =>
                      (delBindersFV args (freeVarsOf (freeVars rhs)),
                       (con, args, freeVars rhs))) alts)) eqn:Hl.
    simpl. destruct (freeVars scrut) eqn:Hfv. simpl in H; rewrite H. f_equal.
    generalize dependent l0. generalize dependent l. induction alts; intros.
    + simpl in Hl. inversion Hl; subst. reflexivity.
    + destruct a0 as [[x y] z]. simpl in Hl.
      destruct (List.unzip
                  (List.map
                     (fun '(con, args, rhs) =>
                        (delBindersFV args (freeVarsOf (freeVars rhs)),
                         (con, args, freeVars rhs))) alts)) eqn:Hl'.
      inversion Hl. simpl. f_equal.
      * f_equal. rewrite <- H0 with (dc:=x)(pats:=y).
        destruct (freeVars z) eqn:fv. reflexivity. intuition.
      * eapply IHalts; try reflexivity.
        intros. eapply H0; apply in_cons; eassumption.
Qed.

Lemma deAnnotate'_snd_freeVars:
  forall e, deAnnotate' (snd (freeVars e)) = e.
Proof.
  intros. symmetry. rewrite <- deAnnotate_freeVars at 1.
  destruct (freeVars e); reflexivity.
Qed.

Lemma freeVarsOf_freeVars:
  forall e,
  dVarSetToVarSet (freeVarsOf (freeVars e)) = exprFreeVars e.
Admitted.

Lemma collectNAnnBndrs_freeVars_mkLams:
  forall vs rhs,
  collectNAnnBndrs (length vs) (freeVars (mkLams vs rhs)) = (vs, freeVars rhs).
Proof.
  intros vs rhs.
  name_collect collect.
  assert (forall vs1 vs0 n, 
             n = length vs1 ->
             collect n vs0 (freeVars (mkLams vs1 rhs)) = (List.app (List.reverse vs0)  vs1, freeVars rhs)).
  { induction vs1; intros.
    + simpl in *.  subst. 
      unfold mkLams.
      unfold_Foldable.
      simpl. 
      rewrite List.app_nil_r.
      auto.
    + simpl in *. 
      destruct n; inversion H.
      pose (IH := IHvs1 (cons a vs0) n H1). clearbody IH. clear IHvs1.
      unfold mkLams in IH.
      unfold Foldable.foldr in IH.
      unfold Foldable.Foldable__list in IH.
      unfold Foldable.foldr__ in IH.
      simpl. 
      remember (freeVars (Foldable.Foldable__list_foldr Lam rhs vs1)) as fv.
      destruct fv.
      rewrite <-  H1.
      rewrite reverse_append in IH.
      auto.
  }       
  pose (K := H vs nil (length vs) eq_refl).
  simpl in K.
  auto.
Qed.

