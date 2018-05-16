Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.
Require Import CoreInduct.

Require Import Coq.Lists.List.

Set Bullet Behavior "Strict Subproofs".

Axiom freeVarsBind1_freeVarsBind: freeVarsBind1 = freeVarsBind.

Scheme expr_mut := Induction for Expr Sort Prop
  with bind_mut := Induction for Bind Sort Prop.

Lemma exprFreeVars_mkLams:
  forall vs e,
  exprFreeVars (mkLams vs e) = delVarSetList (exprFreeVars e) vs.
Admitted.

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
