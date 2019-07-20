(* Disable notation conflict warnings *)
Set Warnings "-notation-overridden".

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.



Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.
Require Import Proofs.CoreInduct.
Require Import Proofs.StrongFV.

Require Import Proofs.Data.Foldable.
Require Import Proofs.Data.Tuple.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Proofs.Axioms.
Require Import Proofs.GhcTactics.
Require Import Proofs.Base.
Require Import Proofs.CoreInduct.
Require Import Proofs.Core.
Require Import Proofs.GHC.List.
Require Import Proofs.Util.

Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.StrongVarSet.

Require Import Proofs.GHC.Base.
Require GHC.Base.
Import GHC.Base.ManualNotations.
Require Import GHC.Base.
Require Import Proofs.ScopeInvariant.

Require Import Proofs.Forall.

Set Bullet Behavior "Strict Subproofs".

Lemma unzip_fst {A B} l : forall (l0 : list A) (l1 : list B), List.unzip l = (l0, l1) -> List.map fst l = l0.
Proof. 
  induction l. 
  - simpl. move=> l0 l1 h. inversion h. auto.
  - move=> l0 l1. destruct a; simpl. 
    destruct (List.unzip l) eqn:LL.
    move=> h. inversion h. subst.
    f_equal. eapply IHl. eauto.
Qed.


Axiom unionVarSet_filterVarSet
     : forall (f : Var -> bool) (vs1 vs2 : VarSet),
       RespectsAEVar f ->
         (unionVarSet (filterVarSet f vs1) (filterVarSet f vs2)) {=}
         (filterVarSet f (unionVarSet vs1 vs2)).

Axiom filterVarSet_equal
     : forall (f : Var -> bool) (vs1 vs2 : VarSet),
       RespectsAEVar f ->
       vs1 {=} vs2 ->
       (filterVarSet f vs1) {=} (filterVarSet f vs2).

(** --------------------------- *)


(** *** Lemmas related to [StrongSubset] *)

Lemma WellScopedVar_StrongSubset : forall e vs1 vs2, 
    WellScopedVar e vs1 -> StrongSubset vs1 vs2 -> WellScopedVar e vs2.
Proof.
  intros v vs1 vs2 WS SS.
  unfold WellScopedVar, StrongSubset in *.
  specialize (SS v).
  destruct (lookupVarSet vs1 v); try contradiction.
  destruct (lookupVarSet vs2 v) eqn:LV2; try contradiction.
  intuition.
  eapply almostEqual_trans with (v2 := v0); auto.
Qed.


(* No such thing as WellScopedTickish anymore *)
(*
Lemma WellScopedTickish_StrongSubset : forall e vs1 vs2, 
    WellScopedTickish e vs1 -> StrongSubset vs1 vs2 -> WellScopedTickish e vs2.
Proof.
  move => e vs1 vs2 WS SS.
  unfold WellScopedTickish, StrongSubset in *.
  destruct_match; try done.
  eapply Forall_impl; eauto.
  move=> a h. eapply WellScopedVar_StrongSubset; eauto. simpl in h.
  auto.
Qed.
*)

Lemma WellScoped_StrongSubset : forall e vs1 vs2, 
    WellScoped e vs1 -> StrongSubset vs1 vs2 -> WellScoped e vs2.
Proof.
  intro e.
  apply (core_induct e); intros; try (destruct binds);
    unfold WellScoped in *; fold WellScoped in *; eauto.
  - eapply WellScopedVar_StrongSubset; eauto.
  - destruct H1. split; eauto.
  - split; only 1: apply H0.
    destruct H0 as [_ H0].
    eapply H; eauto.
    unfold StrongSubset in *.
    intro var.
    specialize (H1 var).
    unfold CoreBndr in v. (* make sure that the type class looks right.*)
    destruct (v GHC.Base.== var) eqn:Eq.
    + rewrite lookupVarSet_extendVarSet_eq; auto.
      rewrite lookupVarSet_extendVarSet_eq; auto.
      eapply almostEqual_refl.
    + rewrite lookupVarSet_extendVarSet_neq.
      destruct (lookupVarSet vs1 var) eqn:IN; auto.
      rewrite lookupVarSet_extendVarSet_neq.
      auto.
      intro h;
      rewrite Eq in h; discriminate.
      intro h;
      rewrite Eq in h; discriminate.
  - destruct H1 as [[GLV WE] Wb].
     split; only 1: split; eauto.
     eapply H0; eauto.
     eapply StrongSubset_extendVarSetList.
     auto.
  - destruct H1 as [[WE1 [WE2 WE3]] Wb].
     repeat split; auto.
     rewrite -> Forall'_Forall in *.
     rewrite -> Forall_forall in *.
     intros h IN. destruct h as [v rhs].
     specialize (WE3 (v,rhs)).
     simpl in *.
     eauto using StrongSubset_extendVarSetList.
     eauto using StrongSubset_extendVarSetList.
  - destruct H1 as [W1 [W2 W3]].    split; only 2: split; eauto.
     rewrite -> Forall'_Forall in *.
     rewrite -> Forall_forall in *.
     intros h IN. destruct h as [[dc pats] rhs].
     specialize (H0 dc pats rhs IN).
     specialize (W3 (dc,pats,rhs) IN).
     simpl in *.
     destruct W3 as [GLV WS].
     eauto using StrongSubset_extendVarSetList.
(*
  - move: H0 => [? ?].
    eauto using WellScopedTickish_StrongSubset.
*)
Qed.


Instance Respects_StrongSubset_WellScopedVar v : Respects_StrongSubset (WellScopedVar v).
Proof.
  intros ????.
  unfold WellScopedVar in *.
  destruct_match; only 2: contradiction.
  specialize (H v).
  rewrite Heq in H.
  destruct_match; only 2: contradiction.
  intuition.
  eapply almostEqual_trans; eassumption.
Qed.

(*
Instance Respects_StrongSubset_WellScopedTickish v : Respects_StrongSubset (WellScopedTickish v).
Proof.
  intros ????.
  unfold WellScopedTickish in *.
  destruct v; try done.
  rewrite -> Forall_forall in *.
  move=> x In.
  move: (H0 x In) => h.
  eapply Respects_StrongSubset_WellScopedVar; eauto.
Qed.
*)

Instance Respects_StrongSubset_WellScoped e : Respects_StrongSubset (WellScoped e).
Proof.
  apply (core_induct e); intros; simpl.
  * apply Respects_StrongSubset_WellScopedVar.
  * apply Respects_StrongSubset_const.
  * apply Respects_StrongSubset_and; assumption.
  * apply Respects_StrongSubset_and; try apply Respects_StrongSubset_const.
    apply Respects_StrongSubset_extendVarSet.
    assumption.
  * apply Respects_StrongSubset_and.
    - destruct_match.
      + apply Respects_StrongSubset_and; try apply Respects_StrongSubset_const.
        assumption.
      + simpl.
        repeat apply Respects_StrongSubset_and; try apply Respects_StrongSubset_const.
        setoid_rewrite Forall'_Forall.
        apply Respects_StrongSubset_forall.
        rewrite Forall_forall.
        intros [v rhs] HIn.
        specialize (H _ _ HIn).
        apply Respects_StrongSubset_extendVarSetList.
        apply H.
    - apply Respects_StrongSubset_extendVarSetList.
      apply H0.
   * repeat apply Respects_StrongSubset_and; try apply Respects_StrongSubset_const.
     - apply H.
     - setoid_rewrite Forall'_Forall.
       apply Respects_StrongSubset_forall.
       rewrite Forall_forall.
       intros [[dc pats] rhs] HIn.
       repeat apply Respects_StrongSubset_and; try apply Respects_StrongSubset_const.
       specialize (H0 _ _ _ HIn).
       apply Respects_StrongSubset_extendVarSetList.
       apply H0.
   * apply H.
(*   * apply H.
     (*
     unfold Respects_StrongSubset
     move=> vs1 vs2 SS.
     move=> [WSE WST].
     split.
     eauto.
     eapply Respects_StrongSubset_WellScopedTickish; eauto.
     *) *)
   * apply Respects_StrongSubset_const.
   * apply Respects_StrongSubset_const. 
Qed.


(** ** [FV] *)

Lemma emptyVarSet_bndrRuleAndUnfoldingFVs bndr sc :
  Denotes emptyVarSet (bndrRuleAndUnfoldingFVs bndr) sc.
Proof.
  destruct bndr; unfold bndrRuleAndUnfoldingFVs; simpl.
  eapply emptyVarSet_emptyFV.
(*  unfold idRuleFVs, idUnfoldingFVs, stableUnfoldingFVs. simpl.
  rewrite union_empty_l.
  eapply emptyVarSet_emptyFV. *)
Qed.

Lemma addBndr_fv fv bndr vs sc:
  Denotes vs fv sc -> 
  Denotes (delVarSet vs bndr) (addBndr bndr fv) (delVarSet sc bndr).
Proof.
  move => h.
  unfold addBndr, varTypeTyCoFVs.
  rewrite union_empty_l. 
  move: (delVarSet_delFV _ bndr _ _ h) => h1.
  eauto.
Qed.

Lemma addBndr_WF : forall fv bndr sc,
    WF_fv fv sc ->
    WF_fv (addBndr bndr fv) (delVarSet sc bndr).
Proof.
  move=> fv bndr sc [vs D].
  eexists.
  eauto using addBndr_fv.
Qed.

Axiom delVarSetList_commute
     : forall (bndrs : list Var) (vs : VarSet) (bndr : Var),
         (delVarSetList (delVarSet vs bndr) bndrs) {=}
         (delVarSet (delVarSetList vs bndrs) bndr).

Lemma addBndrs_fv fv bndrs vs sc :
  Denotes vs fv sc -> 
  Denotes (delVarSetList vs bndrs) (addBndrs bndrs fv) (delVarSetList sc bndrs).
Proof.
  move => h.
  unfold addBndrs, varTypeTyCoFVs.
  move: bndrs vs fv sc h .
  elim => [|bndr bndrs].
  - intros. hs_simpl. auto.
  - move=> Ih vs fv sc h.
    hs_simpl.
    rewrite delVarSetList_commute.
    eapply Denotes_weaken.
    eapply delVarSetList_commute.
    eapply addBndr_fv.
    eauto.
Qed.

Instance WF_fv_m : 
  Proper (Logic.eq ==> StrongEquivalence ==> iff) WF_fv.
Proof.                       
  move=> f1 f2 Ef sc1 sc2 Esc. subst f2.
  unfold WF_fv.
  split. move=> [vs D]. exists vs; eauto. 
  rewrite <- Esc. auto.
  move=> [vs D]. exists vs; eauto. 
  rewrite -> Esc. auto.
Qed.

Lemma WF_fv_weaken fv sc1 sc2:
  sc1 {<=} sc2 ->
  WF_fv fv sc1 -> WF_fv fv sc2.
Proof.
  move=> h [vs D].
  exists vs. 
  eapply Denotes_weaken; eauto.
Qed.

Lemma addBndrs_WF : forall fv sc bndrs,
    WF_fv fv sc ->
    WF_fv (addBndrs bndrs fv) (delVarSetList sc bndrs).
Proof.
  induction bndrs; unfold addBndrs;
    rewrite hs_coq_foldr_list; hs_simpl; auto.
  intros. simpl. 
  rewrite delVarSetList_commute. apply addBndr_WF. auto.
Qed.

Lemma bndrRuleAndUnfoldingFVs_WF bndr sc : WF_fv (bndrRuleAndUnfoldingFVs bndr) sc.
Proof.
  destruct bndr; unfold bndrRuleAndUnfoldingFVs; simpl.
  eapply empty_FV_WF.
(*   unfold idRuleFVs, idUnfoldingFVs, stableUnfoldingFVs. simpl.
  eapply union_FV_WF; eapply empty_FV_WF. *)
Qed.
Hint Resolve bndrRuleAndUnfoldingFVs_WF.

Require Import Proofs.ScopeInvariant.

(* NOTE: for this to work, we need to know something about global vars *)
Lemma WellScopedVar_unitVarSet v sc : 
  WellScopedVar v sc -> (unitVarSet v) {<=} sc.
Proof.
  unfold WellScopedVar.
  move=> h v1.
Admitted.


Lemma delVarSet_extendVarSet sc v :
  delVarSet (extendVarSet sc v) v {<=} sc.
Proof.
  move=>x.
  destruct (v == x) eqn:EQ.
  + rewrite -> fold_is_true in EQ. 
    rewrite Eq_sym in EQ.
    erewrite lookupVarSet_eq; eauto.
    rewrite lookupVarSet_delVarSet_None.
    auto.
  + rewrite lookupVarSet_delVarSet_neq; eauto.
    rewrite lookupVarSet_extendVarSet_neq; eauto.
    destruct lookupVarSet.
    reflexivity.
    auto.
Qed.
Hint Resolve delVarSet_extendVarSet.

Lemma delVarSetList_extendVarSetList xs :
  forall sc, delVarSetList (extendVarSetList sc xs) xs {<=} sc.
Proof.
  induction xs.
  move=> sc. hs_simpl. reflexivity.
  move=> sc. hs_simpl.
Admitted.
Hint Resolve delVarSetList_extendVarSetList.

Lemma expr_fvs_WF : forall e sc,
    WellScoped e sc ->
    WF_fv (expr_fvs e) sc.
Proof.
  intros e. apply (core_induct e); intros; 
    unfold WellScoped in *; 
    unfold WellScopedBind in *; 
    fold WellScoped in *; 
    fold WellScopedBind in *; simpl; auto.
  - eapply WellScopedVar_unitVarSet in H.
    eapply unit_FV_WF.
    auto.
    
  - move: H1 => [h0 h1]. auto.
  - move: H0 => [h0 h1].
    have DD: (delVarSet (extendVarSet sc v) v {<=} sc) by auto.
    eapply WF_fv_weaken; eauto.
  - move: H1 => [h0 h1].
    destruct binds; auto;
      unfold WellScopedBind in *; fold WellScoped in *.
    + move: h0 => [gvc h2].
      apply union_FV_WF; apply union_FV_WF; eauto.
      have DD: (delVarSet (extendVarSet sc c) c {<=} sc) by auto.
      eapply WF_fv_weaken; eauto.
    + move: h0 => [gvs [ND FVs]].
      set (xs := List.map fst l) in *.
      have DD: (delVarSetList (extendVarSetList sc xs) xs {<=} sc) by auto.
      eapply WF_fv_weaken; eauto.
      apply addBndrs_WF.
      apply union_FV_WF; auto. 
      ++ apply unions_FV_WF.
         intros.
         subst xs.
         rewrite -> in_map_iff in H1.
         move:H1 => [[bndr rhs] [h2 h3]]. subst fv.
         specialize (H _ _ h3).
         rewrite -> Forall.Forall'_Forall in FVs.
         rewrite -> Forall_forall in FVs.
         specialize (FVs _ h3).
         eauto.
      ++ eapply H0.
         eapply WellScoped_StrongSubset; eauto.
         simpl.
         subst xs.
         rewrite bindersOf_Rec_cleanup.
         reflexivity.

  - move: H1 => [h0 [h1 h2]]. 
    apply union_FV_WF; auto.
    have DD: delVarSet (extendVarSet sc bndr) bndr {<=} sc. auto.
    eapply WF_fv_weaken; eauto.
    apply addBndr_WF. 
    apply unions_FV_WF.
    intros fv IN.
    rewrite -> in_map_iff in IN.
    move: IN => [ [[a bndrs] rhs] [h3 IN]]. subst fv.
    specialize (H0 _ _ _ IN).
    rewrite -> Forall.Forall'_Forall in h2.
    rewrite -> Forall_forall in h2.
    specialize (h2 _ IN). simpl in h2.
    move: h2 => [GV WS]. hs_simpl in WS.
    have DD2: delVarSetList (extendVarSetList (extendVarSet sc bndr) bndrs) bndrs {<=}
                           (extendVarSet sc bndr) by auto.
    eapply WF_fv_weaken; eauto.
    eapply addBndrs_WF. auto.
Qed.

Lemma Denotes_fvVarSet e sc: 
  WellScoped e sc -> Denotes (FV.fvVarSet (expr_fvs e)) (expr_fvs e) sc.
Proof. 
  move=> WS.
  move: (expr_fvs_WF e sc WS) => [vs h].
  move: (Denotes_fvVarSet_vs _ _ _ h) => eq.
  rewrite eq.
  auto.
Qed.


Lemma WellScoped_exprFreeVars e sc:
  WellScoped e sc -> exprFreeVars e {<=} sc.
Proof.
  move=> WS.
  unfold exprFreeVars, exprFVs.
  simpl.
  move: (expr_fvs_WF e sc WS) => [vs h].
  eapply filterVarSet_filterFV with (f := isLocalVar) in h; auto.
  move: (Denotes_fvVarSet_vs _ _ _ h) => h0.
  eapply Denotes_sc in h.
  rewrite h0.
  auto.
Qed.

(** Unfolding tactics *)
Ltac unfold_FV := 
  repeat unfold Base.op_z2218U__, FV.filterFV, FV.fvVarSet, 
       FV.unitFV, FV.fvVarListVarSet.


(* Definition disjoint E F := inter E F {=} empty. *)

(** ** [exprFreeVars] *)

(* Nice rewrite rules for [exprFreeVars] *)

Lemma exprFreeVars_Var: forall v, 
    isLocalVar v = true -> 
    exprFreeVars (Mk_Var v) = unitVarSet v.
Proof.
  intros v NG.
  unfold exprFreeVars, exprFVs, expr_fvs.
  unfold_FV. unfold elemVarSet; simpl.
  rewrite NG.
  simpl. unfold unitVarSet, UniqSet.unitUniqSet.
  f_equal. unfold UniqFM.unitUFM. f_equal. simpl.
  unfold IntMap.insert, IntMap.singleton, IntMap.empty.
  f_equal. apply proof_irrelevance.
Qed.

Lemma exprFreeVars_global_Var: forall v, 
    isLocalVar v = false -> 
    exprFreeVars (Mk_Var v) = emptyVarSet.
Proof.
intros v NG.
unfold exprFreeVars, exprFVs, expr_fvs.
unfold_FV.
rewrite NG.
auto.
Qed.

Lemma exprFreeVars_Lit : forall i, 
    exprFreeVars (Lit i) = emptyVarSet.
Proof.
  intro. reflexivity.
Qed.

Hint Rewrite exprFreeVars_Lit : hs_simpl.

Lemma exprFreeVars_App:
  forall e1 e2 sc,
  WellScoped (App e1 e2) sc ->
  exprFreeVars (App e1 e2) {=} unionVarSet (exprFreeVars e1) (exprFreeVars e2).
Proof.
  move=> e1 e2 sc h.
  unfold exprFreeVars,  Base.op_z2218U__.
  unfold exprFVs, Base.op_z2218U__ .
  move: (expr_fvs_WF (App e1 e2) sc h) => [vs0 D0].
  inversion h.
  move: (expr_fvs_WF e1 sc H) => [vs1 D1].
  move: (expr_fvs_WF e2 sc H0) => [vs2 D2].
  move: (Denotes_fvVarSet_vs _ _ _ (filterVarSet_filterFV isLocalVar _ _ _ RespectsAEVar_isLocalVar D0)) => D3.
  move: (Denotes_fvVarSet_vs _ _ _ (filterVarSet_filterFV isLocalVar _ _ _  RespectsAEVar_isLocalVar D1)) => D4.
  move: (Denotes_fvVarSet_vs _ _ _ (filterVarSet_filterFV isLocalVar _ _ _ RespectsAEVar_isLocalVar D2)) => D5.
  rewrite D3.
  rewrite D4.
  rewrite D5.
  rewrite unionVarSet_filterVarSet; try done.
  
  unfold expr_fvs in D0. fold expr_fvs in D0.
  move: (unionVarSet_unionFV _ _ (expr_fvs e2) (expr_fvs e1) _ D2 D1) => D6.
  move: (Denotes_inj1 _ _ _ _ D0 D6) => E.
  rewrite -> StrongFV.unionVarSet_commute in E.
  apply (filterVarSet_equal _ _ _ RespectsAEVar_isLocalVar E).
  eapply Denotes_sc; eauto.
  eapply Denotes_sc; eauto.
Qed.

Hint Rewrite exprFreeVars_App : hs_simpl.


Lemma exprFreeVars_mkLams_rev:
  forall vs e sc,
   WellScoped (mkLams (rev vs) e) sc ->
   exprFreeVars (mkLams (rev vs) e) {=} delVarSetList (exprFreeVars e) vs.
Proof.
  intros vs e sc. revert vs. 
Admitted.
(*
  apply rev_ind
    with (P := fun vs => 
                ((WellScoped (mkLams (rev vs) e) sc ->
                 exprFreeVars (mkLams (rev vs) e) {=} delVarSetList (exprFreeVars e) vs)))
                             ; intros.
  - unfold exprFreeVars, exprFVs, Base.op_z2218U__, mkLams.
    unfold Foldable.foldr, Foldable.Foldable__list. simpl.
    unfold delVarSetList, UniqSet.delListFromUniqSet.
    destruct (FV.fvVarSet (FV.filterFV isLocalVar (expr_fvs e))); reflexivity.
  - revert H; unfold exprFreeVars, exprFVs, Base.op_z2218U__, mkLams.
    rewrite delVarSetList_app. rewrite delVarSetList_single.
    rewrite rev_app_distr. repeat rewrite hs_coq_foldr_list.
    rewrite fold_right_app. intros H. rewrite <- H. simpl.
    unfold addBndr, varTypeTyCoFVs. rewrite union_empty_l.
    rewrite delVarSet_fvVarSet; [reflexivity |].
    apply filter_FV_WF. 
    apply RespectsAEVar_isLocalVar.
    apply expr_fvs_WF.
    admit.
Admitted. *)

Lemma exprFreeVars_mkLams:
  forall vs e sc, 
    WellScoped (mkLams vs e) sc ->
    exprFreeVars (mkLams vs e) {=} delVarSetList (exprFreeVars e) (rev vs).
Proof.
  intros. replace vs with (rev (rev vs)) at 1.
  replace vs with (rev (rev vs)) in H.
  - eapply exprFreeVars_mkLams_rev. eauto.
  - apply rev_involutive.
  - apply rev_involutive.
Qed.



Lemma exprFreeVars_Lam:	
  forall v e sc, 
    WellScoped (Lam v e) sc ->
   exprFreeVars (Lam v e) {=} delVarSet (exprFreeVars e) v.
Proof.
  intros v e.
  replace (Lam v e) with (mkLams (rev [v]) e).
  - rewrite <- delVarSetList_single. apply exprFreeVars_mkLams_rev.
  - simpl. unfold mkLams. rewrite hs_coq_foldr_list. reflexivity.
Qed.

Hint Rewrite exprFreeVars_Lam : hs_simpl.

(* If h0 : Denote vs fv, then specialize h0 and rewrite with the second version. *)
Ltac denote h0 h5:=
  inversion h0;
  match goal with [H : forall (f : Var -> bool), _ |- _] =>
     specialize (H (fun v0 : Var => Base.const true v0 && isLocalVar v0) emptyVarSet emptyVarSet nil ltac:(eauto));
       hs_simpl in H;
       move: (H ltac:(reflexivity)) => [_ h5]; clear H
  end;
  rewrite h5; clear h5.


Lemma exprFreeVars_Let_NonRec:
  forall v rhs body sc,
  WellScoped (Let (NonRec v rhs) body) sc ->
  exprFreeVars (Let (NonRec v rhs) body) {=}
    unionVarSet (exprFreeVars rhs) (delVarSet (exprFreeVars body) v).
Proof.
  move=> v rhs body sc WS.
  inversion WS.
  unfold exprFreeVars.
  unfold_FV.
  unfold exprFVs.
  unfold_FV.
  unfold expr_fvs. fold expr_fvs.
  move: (expr_fvs_WF body _ H0) => [vbody h1].
Admitted.
(*
  denote h1 h5.
  move: (expr_fvs_WF rhs) => [vrhs h0].
  denote h0 h5.
  move: (addBndr_fv (expr_fvs body) v vbody h1) => h2.
  move: (emptyVarSet_bndrRuleAndUnfoldingFVs v) => h4.
  move: (unionVarSet_unionFV _ _ _ _ h4 h0) => h3.
  move: (unionVarSet_unionFV _ _ _ _ h2 h3) => h6.
  denote h6 h5.

  rewrite <- unionVarSet_filterVarSet => //.
  rewrite unionVarSet_sym.
  rewrite filterVarSet_delVarSet => //.
  eapply union_equal_1.
  eapply filterVarSet_equal.
  eauto.
  rewrite unionEmpty_l.
  reflexivity.
Qed.

Lemma push_foldable (f : VarSet -> VarSet) b (xs : list VarSet) :
  (forall x y, f (unionVarSet x y) [=] unionVarSet (f x) (f y)) ->
  f (Foldable.foldr unionVarSet b xs) [=] 
  Foldable.foldr unionVarSet (f b) (map f xs).
Proof. 
  elim: xs => [|x xs Ih].
  hs_simpl. move=> h. reflexivity.
  move=>h. hs_simpl.
  rewrite h.
  rewrite Ih => //.
Qed.  




Lemma exprFreeVars_Let_Rec:
  forall pairs body,
  exprFreeVars (Let (Rec pairs) body) [=]
    delVarSetList 
       (unionVarSet (exprsFreeVars (map snd pairs))
                    (exprFreeVars body))
          (map fst pairs).
Proof.
  move=> pairs body.
  unfold exprFreeVars, exprsFreeVars.
  unfold_FV.
  unfold exprFVs, exprsFVs, exprFVs.
  unfold_FV.
  unfold expr_fvs. fold expr_fvs.
  move: (expr_fvs_WF body) => [vbody h1].
  denote h1 h5.

  set (f:= (fun (x : CoreExpr) (fv_cand1 : FV.InterestingVarFun)
                    (in_scope : VarSet) =>
                  [eta expr_fvs x (fun v : Var => fv_cand1 v && isLocalVar v)
                         in_scope])).

  set f1 := fun rhs => filterVarSet isLocalVar (FV.fvVarSet (expr_fvs rhs)).

  have h: Forall2 Denotes 
              (map f1 (map snd pairs))
              (map f (map snd pairs)).
  { elim: (map snd pairs) => [|p ps].  simpl. 
    eauto.
    move=> h.
    econstructor; eauto.
    unfold f1. unfold f.
    move: (expr_fvs_WF p) => [vsp h0].
    econstructor.
    move=> f0 in_scope vs' l Rf0 eql.
    inversion h0.
    have g: RespectsVar (fun v => f0 v && isLocalVar v). 
    { apply RespectsVar_andb; eauto. }
    specialize (H (fun v => f0 v && isLocalVar v) in_scope vs' l g eql).
    move: H => [h2 h3].
    rewrite h2. rewrite h3. split; try reflexivity.
    f_equiv.
    f_equiv.
    rewrite filterVarSet_comp.
    apply Denotes_fvVarSet_vs in h0.
    apply filterVarSet_equal.
    apply g.
    symmetry.
    done.
  } 

  move : (mapUnionVarSet_mapUnionFV _ _ _ _ h) => h2.
  inversion h2.
  specialize (H (Base.const true) emptyVarSet
                emptyVarSet nil ltac:(eauto)).
  hs_simpl in H;
       move: (H ltac:(reflexivity)) => [_ h5]; clear H.
  rewrite h5.

  have g0 : Forall2 Denotes 
                 (map (fun '(bndr,rhs) => (FV.fvVarSet (FV.unionFV (expr_fvs rhs)(bndrRuleAndUnfoldingFVs bndr)))) pairs)
                 (map (fun '(bndr, rhs) => (FV.unionFV (expr_fvs rhs) (bndrRuleAndUnfoldingFVs bndr))) pairs).
  { 
    clear h h2 H2 H3 h5.
    elim: pairs => [|p ps].  simpl. 
    eauto.
    simpl.
    move: p => [bndr rhs]. simpl.
    move=> Ih.
    econstructor; eauto.
    rewrite Denotes_fvVarSet_vs.
    eapply unionVarSet_unionFV.
    eapply emptyVarSet_bndrRuleAndUnfoldingFVs.
    eapply Denotes_fvVarSet.
    eapply unionVarSet_unionFV.
    eapply emptyVarSet_bndrRuleAndUnfoldingFVs.
    eapply Denotes_fvVarSet.
  }

  move: (unionsVarSet_unionsFV _ _ g0) => h4.
  move: (unionVarSet_unionFV _ _ _ _ h1 h4) => g5.
  move: (addBndrs_fv _ (Base.map Tuple.fst pairs) _ g5) => h6.
  
  denote h6 h7.

  rewrite filterVarSet_delVarSetList; try done.
  f_equiv.
  rewrite <- unionVarSet_filterVarSet; try done.
  rewrite unionVarSet_sym.
  f_equiv.
  unfold mapUnionVarSet.
  rewrite Foldable_foldr_map.
  rewrite List.map_map.
  unfold f1.
  rewrite push_foldable.
  + generalize pairs.
    induction pairs0. hs_simpl. reflexivity.
    hs_simpl. rewrite map_cons.
    rewrite map_cons. destruct a. 
    simpl.
    rewrite Foldable_foldr_cons.
    rewrite Foldable_foldr_cons.
    rewrite <- IHpairs0.
    f_equiv.
    * eapply filterVarSet_equal. eauto.
      eapply Denotes_fvVarSet_vs.
      rewrite Denotes_fvVarSet_vs.
      eapply unionVarSet_unionFV.
      eapply emptyVarSet_bndrRuleAndUnfoldingFVs.
      eapply Denotes_fvVarSet.
      rewrite unionEmpty_l.
      eapply Denotes_fvVarSet.
    * rewrite filterVarSet_emptyVarSet. reflexivity.
  + move=> x y.
    rewrite unionVarSet_filterVarSet.
    reflexivity.
    done. 
Qed.

Lemma exprFreeVars_Case:
  forall scrut bndr ty alts,
  exprFreeVars (Case scrut bndr ty alts) [=]
    unionVarSet (exprFreeVars scrut) (mapUnionVarSet (fun '(dc,pats,rhs) => delVarSetList (exprFreeVars rhs) (pats ++ [bndr])) alts).
Proof. 
  move=> scrut bndr ty alts.
  unfold exprFreeVars.
  unfold_FV.
  unfold exprFVs.
  unfold_FV.
  unfold expr_fvs. fold expr_fvs.
  move: (expr_fvs_WF scrut) => [vscrut h1].
  denote h1 h5. subst.
  set f := (fun v : Var => Base.const true v && isLocalVar v).
  have Hf: RespectsVar f by eapply RespectsVar_andb; eauto.
  
  set (f2:= (fun (x : CoreExpr) (fv_cand1 : FV.InterestingVarFun)
                    (in_scope : VarSet) =>
                  [eta expr_fvs x (fun v : Var => fv_cand1 v && isLocalVar v)
                         in_scope])).


  set f1 := fun rhs pat => 
              delVarSetList 
                (FV.fvVarSet (expr_fvs rhs)) pat.

  have k: forall rhs pat, filterVarSet [eta isLocalVar] (f1 rhs pat)
                     [=] delVarSetList
                     (filterVarSet f
                                   (FV.fvVarSet (expr_fvs rhs))) pat.
  { move => rhs pat.
    unfold f1.
    rewrite filterVarSet_delVarSetList => //.
  } 
  rewrite union_empty_r.

  have h: Forall2 Denotes 
                  (map (fun '(_, bndrs, rhs) => f1 rhs bndrs) alts)
                  (map (fun '(_, bndrs, rhs) => addBndrs bndrs (expr_fvs rhs)) alts).
  { 
    elim: alts => [|alt alts IH].
    - simpl. auto.
    - simpl. move: alt => [[_ bndrs] rhs].
      econstructor; eauto.
      unfold f1.
      move: (Denotes_fvVarSet rhs) => h.
      move: (addBndrs_fv _ bndrs _ h) => h2.
      auto.
  }
  move: (unionsVarSet_unionsFV _ _ h) => h2.
  move: (addBndr_fv _ bndr _ h2) => h3. 
  move: (unionVarSet_unionFV _ _ _ _ h3 h1) => h4.
  denote h4 h6.

  rewrite <- unionVarSet_filterVarSet => //.
  rewrite unionVarSet_sym.
  f_equiv.
  rewrite filterVarSet_delVarSet => //.
  rewrite push_foldable. 2:{  move=> x y. rewrite unionVarSet_filterVarSet; eauto.
                              reflexivity. }
  rewrite filterVarSet_emptyVarSet.
  unfold mapUnionVarSet.
  rewrite Foldable_foldr_map.
  move: (push_foldable (fun x => delVarSet x bndr)) => p.  
  rewrite p. 2: {   move=> x y.
  rewrite delVarSet_unionVarSet. reflexivity. }

  rewrite List.map_map. rewrite List.map_map.
  hs_simpl.

  apply unionsVarSet_equal.
  clear h h2 h3 h4 H0 H1.
  elim: alts => [|[[x pat] rhs] alts IH].
  simpl. auto.
  simpl. 
  econstructor; eauto.
  
  move: (Denotes_fvVarSet rhs) => h5.
  denote h5 h6.

  hs_simpl.
  f_equiv.

  unfold f1.

  rewrite filterVarSet_delVarSetList => //.
Qed.


Lemma exprFreeVars_Cast:
  forall e co,
  exprFreeVars (Cast e co) [=] exprFreeVars e.
Proof. 
  intros. reflexivity.
Qed.

(*

Definition tickishFreeVars := 
fun arg_0__ : Tickish Var => match arg_0__ with
                          | Breakpoint _ ids => mkVarSet ids
                          | _ => emptyVarSet
                          end.
*)

Lemma mkVarSet_mapUnionFV vs : 
  Denotes (mkVarSet vs) (FV.mapUnionFV FV.unitFV vs). 
Proof.
  rewrite mkVarSet_extendVarSetList.
  elim: vs => [|x xs IH].
  - apply emptyVarSet_emptyFV.
  - hs_simpl.
    rewrite extendVarSetList_extendVarSet_iff.
    move: (unionVarSet_unionFV _ _ _ _ ( unitVarSet_unitFV x) IH) => h.
    hs_simpl in h.
    assumption.
Qed.

(*
Lemma Denotes_tickish co : 
  Denotes (tickishFreeVars co) (tickish_fvs co).
Proof.
  elim C: co; simpl.
  all: try (apply emptyVarSet_emptyFV).
  unfold FV.mkFVs.
  apply mkVarSet_mapUnionFV.
Qed.
*)

(*
Lemma exprFreeVars_Tick:
  forall e t,
  exprFreeVars (Tick t e) [=] (unionVarSet (exprFreeVars e) (filterVarSet isLocalVar (tickishFreeVars t))).
Proof. 
  move=> e co.
  unfold exprFreeVars, exprFVs, Base.op_z2218U__.  
  unfold expr_fvs. fold expr_fvs.
  move: (expr_fvs_WF e) => [vs D].
  move: (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D) => D1.
  move: (Denotes_fvVarSet_vs _ _ D1) => D2.
  rewrite D2.

  move: (unionVarSet_unionFV _ _ _ _ D (Denotes_tickish co)) => D3.
  move: (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D3) => D4.
  move: (Denotes_fvVarSet_vs _ _ D4) => D5.
  rewrite D5.
  rewrite <- unionVarSet_filterVarSet; try done.
Qed.
*)

(*
Lemma exprFreeVars_Tick:
  forall e t,
  exprFreeVars (Tick t e) [=] exprFreeVars e.
Proof. done. Qed.
*)

Lemma exprFreeVars_Type:
  forall t,
  exprFreeVars (Mk_Type t) = emptyVarSet.
Proof. intros. reflexivity. Qed.

Lemma exprFreeVars_Coercion:
  forall co,
  exprFreeVars (Mk_Coercion co) = emptyVarSet.
Proof. intros. reflexivity. Qed.


(* ---------------------------------------------------------- *)

Lemma exprsFreeVars_nil : exprsFreeVars [] = emptyVarSet. 
Proof.
  unfold exprsFreeVars.
  unfold Base.op_z2218U__.
  unfold exprsFVs.
  unfold FV.mapUnionFV.
  unfold FV.fvVarSet.
  unfold Base.op_z2218U__ .
  unfold FV.fvVarListVarSet.
  simpl.
  reflexivity.
Qed.
Hint Rewrite exprsFreeVars_nil : hs_simpl.


Lemma exprsFreeVars_cons x xs : exprsFreeVars (x :: xs) [=] 
             unionVarSet (exprsFreeVars xs) (exprFreeVars x).
Proof.
  unfold exprsFreeVars.
  unfold Base.op_z2218U__.
  unfold exprsFVs.
  rewrite mapUnionFV_cons.
  unfold exprFreeVars.
  unfold Base.op_z2218U__.
  unfold exprFVs.
  unfold Base.op_z2218U__.
  move: (Denotes_fvVarSet x) => h0.
  move: (filterVarSet_filterFV isLocalVar _ _ ltac:(eauto) h0) => h1.
  set f2 := (fun x0 : CoreExpr => FV.filterFV isLocalVar (expr_fvs x0)).
  set f1 := fun x => filterVarSet isLocalVar (FV.fvVarSet (expr_fvs x)).
  have h2: Forall2 Denotes (map f1 xs) (map f2 xs). 
  { elim xs. simpl. auto.
    move=> a l IH. simpl.
    econstructor; eauto.
    unfold f1. unfold f2.
    eapply filterVarSet_filterFV. auto.
    eapply Denotes_fvVarSet.
  }
  move: (mapUnionVarSet_mapUnionFV _ xs f1 f2 h2) => h3.
  move: (unionVarSet_unionFV _ _ _ _ h1 h3) => h4.
  rewrite (Denotes_fvVarSet_vs _ _ h4).  
  rewrite (Denotes_fvVarSet_vs _ _ h3).  
  rewrite (Denotes_fvVarSet_vs _ _ h1).  
  rewrite unionVarSet_sym.
  reflexivity.
Qed.
Hint Rewrite exprsFreeVars_cons : hs_simpl.


Lemma subVarSet_exprFreeVars_exprsFreeVars:
  forall v rhs (pairs : list (CoreBndr * CoreExpr)) ,
  List.In (v, rhs) pairs ->
  subVarSet (exprFreeVars rhs) (exprsFreeVars (map snd pairs)) = true.
Proof.
  move => v rhs.
  elim => [|[v0 rhs0] ps IH]; simpl. done.
  hs_simpl. move => [eq|I]. 
  inversion eq.
  set_b_iff. fsetdec.
  set_b_iff. 
  specialize (IH I).
  fsetdec.
Qed.

Lemma subVarSet_exprsFreeVars:
  forall (es : list CoreExpr) vs,
  Forall (fun e => subVarSet (exprFreeVars e) vs = true) es ->
  subVarSet (exprsFreeVars es) vs = true.
Proof.
  move=> es vs.
  elim.
  - hs_simpl. 
    set_b_iff. fsetdec.
  - move=> x l S1 F1 S2. 
    hs_simpl.
    set_b_iff. fsetdec.
Qed.

Lemma elemVarSet_exprFreeVars_Var_false: forall v' v,
    varUnique v' <> varUnique v ->
    elemVarSet v' (exprFreeVars (Mk_Var v)) = false.
Proof.
intros.
unfold exprFreeVars, exprFVs, expr_fvs.
unfold_FV.
simpl.
destruct (isLocalVar v).
- simpl.
  unfold varUnique in H.
  rewrite ContainerAxioms.member_insert.
  apply /orP. intro. intuition.
  apply H. f_equal. apply /Eq_eq =>//.
- reflexivity.
Qed.

(** Working with [exprFreeVars] *)

 
(** Working with [freeVars] *)

Ltac DVarToVar := 
    replace unionDVarSet with unionVarSet; auto;
    replace emptyDVarSet with emptyVarSet; auto;
    replace delDVarSet with delVarSet; auto;
    replace FV.fvDVarSet with FV.fvVarSet; auto;
    replace unionDVarSets with unionVarSets; auto.

Lemma no_TyCoVars bndr: (dVarTypeTyCoVars bndr) {=} emptyVarSet.
  unfold  dVarTypeTyCoVars, varTypeTyCoFVs. 
  DVarToVar.
  rewrite Denotes_fvVarSet_vs;
    try apply emptyVarSet_emptyFV.
  reflexivity.
Qed.

Lemma no_RuleAndUnfoldingFVs l0 : 
  (FV.fvVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs l0)) {=} emptyVarSet.
Proof.
  rewrite Denotes_fvVarSet_vs.
  2: { 
    unfold bndrRuleAndUnfoldingFVs.
    eapply mapUnionVarSet_mapUnionFV with (f1 := fun x => emptyVarSet).
    induction l0; simpl in *.
    eauto.
    econstructor; eauto.
    unfold isId, idRuleFVs, idUnfoldingFVs.
    destruct a. simpl.
    rewrite union_empty_r.
    eapply emptyVarSet_emptyFV.
  }
  induction l0.
  hs_simpl.
  rewrite mapUnionVarSets_unionVarSets. simpl. reflexivity.
  rewrite mapUnionVarSet_cons.  rewrite IHl0.
  rewrite unionEmpty_r.
  reflexivity.
Qed.

Lemma freeVarsOf_freeVars_revised:
  forall e,
  (freeVarsOf (freeVars e)) {=} exprFreeVars e.
Proof.
  intro e; apply (core_induct e).
  - intros x; simpl.
    destruct (isLocalVar x) eqn:IS; simpl. 
    rewrite exprFreeVars_Var //.
    rewrite exprFreeVars_global_Var //.
  - intros l. rewrite exprFreeVars_Lit //.
  - intros e1 e2 h1 h2. rewrite exprFreeVars_App //.
    unfold freeVars; fold freeVars.
    rewrite <- h1. rewrite <- h2.
    simpl.
    reflexivity.
  - intros.
    rewrite exprFreeVars_Lam.
    unfold freeVars; fold freeVars.
    destruct (freeVars e0). unfold freeVarsOf.
    rewrite <- H. unfold freeVarsOf.
    unfold unionFVs. unfold delBinderFV.
    rewrite no_TyCoVars.
    fsetdec.
  - intros.
    destruct binds.
    + rewrite exprFreeVars_Let_NonRec.
      unfold freeVars; fold freeVars.
      unfold freeVarsOf.
      destruct (freeVars e0).
      destruct (freeVars body).
      rewrite <- H0. rewrite <- H. unfold freeVarsOf.
      unfold delBinderFV. rewrite no_TyCoVars. 
      unfold bndrRuleAndUnfoldingVarsDSet.
      unfold bndrRuleAndUnfoldingFVs.
      DVarToVar.
      replace (isId c) with true; try (destruct c; reflexivity).
      fsetdec.
    + rewrite exprFreeVars_Let_Rec. 
      unfold freeVarsOf in H0.
      destruct (freeVars body) eqn:h.
      unfold freeVars. fold freeVars. simpl.
      rewrite h. rewrite <- H0. simpl.
      destruct List.unzip eqn:h0. simpl.
      unfold delBindersFV.
      rewrite <- snd_unzip. rewrite h0. simpl.
      unfold delBinderFV. unfold unionFVs.
      unfold dVarTypeTyCoVars. unfold varTypeTyCoFVs.
      DVarToVar.
      rewrite delVarSetList_foldr.

      move: (unzip_fst _ _ _ h0) => h1. rewrite h1.
      rewrite <- Foldable_foldr_map. unfold Base.op_z2218U__.
      eapply foldr_m; auto.
      ++ move => x1 x2 Ex s1 s2 Ev.
         rewrite Denotes_fvVarSet_vs;
           try apply emptyVarSet_emptyFV.
         rewrite unionEmpty_r. 
         rewrite Ev. rewrite -> Ex.
         reflexivity.
      ++ rewrite no_RuleAndUnfoldingFVs.
         rewrite unionEmpty_r.
         clear h1.
         move: l1 l0 h0 H. 
         induction l.
         simpl. move=> l1 l0 [] e1 e2. subst. hs_simpl. reflexivity.
         move=> l1 l0 UZ IH.
         destruct a0. simpl in UZ. destruct (List.unzip l) eqn:hl.  inversion UZ. subst.
         hs_simpl. rewrite IHl; eauto.
         +++ move: (IH c e0) => hh. rewrite hh; simpl; eauto.
             set_b_iff. fsetdec.
         +++ intros v rhs In. eapply (IH v). simpl. right. auto.              
  - intros.
    rewrite exprFreeVars_Case.
    unfold freeVars; fold freeVars.
    rewrite NestedRecursionHelpers.map_unzip.
    destruct List.unzip as [alt_fvs_s alts2] eqn:Z.
    simpl.
    unfold unionFVs, delBinderFV, unionFVss in *.
    DVarToVar.
    rewrite unionEmpty_r.
    rewrite unionVarSet_sym.
    rewrite H.
    eapply union_equal_2.
    rewrite no_TyCoVars.
    unfold unionFVs. DVarToVar.
    rewrite unionEmpty_r.

    rewrite delVarSet_unionVarSets.
    rewrite mapUnionVarSets_unionVarSets.
    rewrite unionVarSets_def.
    rewrite unionVarSets_def.
    eapply foldr_mE; try reflexivity.
    eapply unionVarSet_m.

    move: alts alt_fvs_s alts2 Z H0.
    induction alts.
    ++ intros. simpl in Z. inversion Z. simpl. auto.
    ++ intros. 
       destruct a. destruct p. simpl in Z.
       destruct List.unzip eqn:ZZ.
       simpl.
       inversion Z. destruct alt_fvs_s; inversion H2.
       destruct alts2; inversion H3. subst.
       simpl. clear H2. clear H3.
       eapply Forall2_cons.
       +++ move: (H0 a l c ltac:(simpl; eauto)) => h1. 
           unfold delBindersFV.
           hs_simpl.
           eapply delVarSet_m; try reflexivity.
           unfold delBinderFV.
           rewrite delVarSetList_foldr.
           eapply foldr_m; eauto.
           move=> x1 x2 Ex y1 y2 Ey.
           rewrite no_TyCoVars.
           unfold unionFVs. DVarToVar.
           rewrite unionEmpty_r.
           rewrite -> Ex. 
           rewrite Ey.
           reflexivity.
       +++ eapply IHalts; eauto.
           move=> dc pats rhs In. eapply H0. simpl. right. eauto.

  - intros. rewrite exprFreeVars_Cast. unfold freeVars. fold freeVars. 
    simpl. rewrite H. fsetdec.
  - intros. rewrite exprFreeVars_Type. unfold freeVars. fold freeVars.
    simpl. reflexivity.
  - intros. rewrite exprFreeVars_Coercion. unfold freeVars. fold freeVars.
    simpl. reflexivity.
Qed.

Lemma deAnnotate_freeVars:
  forall e, deAnnotate (freeVars e) = e.
Proof.
  intro e; apply (core_induct e);
    intros; simpl; try reflexivity;
      try solve [destruct (freeVars e0) eqn:Hfv; simpl in H; rewrite H; reflexivity].
  - destruct (isLocalVar v); reflexivity.
  - symmetry. f_equal.
    + destruct (freeVars e1) eqn:fv. rewrite <- H; reflexivity.
    + destruct (freeVars e2) eqn:fv. rewrite <- H0; reflexivity.
  - destruct (freeVars e0) eqn:Hfv.
    destruct (delBinderFV v f) eqn:Hdb.
    unfold deAnnotate in H. simpl; rewrite H; reflexivity.
  - destruct binds; simpl.
    + destruct (freeVars body) eqn:Hfv. rewrite <- H0.
      destruct (freeVars e0) eqn:Hfv'. rewrite <- H. reflexivity.
    + rewrite -map_map.
      replace @Base.map with map by done.
      rewrite -snd_unzip.
      replace @map with @Base.map by done.
      destruct (List.unzip l) eqn:Hl. rewrite !Hl. simpl.
      destruct (freeVars body) eqn:Hfv. rewrite <- H0. f_equal.
      generalize dependent l1; generalize dependent l0.
      induction l; simpl; intros.
      * inversion Hl; subst. reflexivity.
      * destruct a0. destruct (List.unzip l) eqn:Hl'. inversion Hl; subst.
        simpl. do 2 f_equal.
        -- f_equal. erewrite <- H with (v:=c). reflexivity. intuition.
        -- assert (forall (v : CoreBndr) (rhs : Expr CoreBndr),
                      List.In (v, rhs) l -> deAnnotate (freeVars rhs) = rhs).
           { intros. apply H with (v:=v).
             apply in_cons; assumption. }
           specialize (IHl H0 l2 l3 Logic.eq_refl). inversion IHl; reflexivity.
  - destruct (List.unzip
                (List.map
                   (fun '(con, args, rhs) =>
                      (delBindersFV args (freeVarsOf (freeVars rhs)),
                       (con, args, freeVars rhs))) alts)) eqn:Hl.
    simpl. destruct (freeVars scrut) eqn:Hfv.
    destruct NestedRecursionHelpers.mapAndUnzipFix eqn:Hmu. simpl.
    rewrite NestedRecursionHelpers.map_unzip in Hmu.
    simpl in H; rewrite H. f_equal.
    rewrite Hl in Hmu. inversion Hmu. subst.
    generalize dependent l1. generalize dependent l2. induction alts; intros.
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
  pose (K := H vs nil (length vs) Logic.eq_refl).
  simpl in K.
  auto.
Qed.
*)