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
Require Import Proofs.FV.

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
Import VarSetFSet.
Import VarSetDecide.
Import VarSetFacts.
Import VarSetProperties.
Import VarSetFSet.Notin.

Require Import Proofs.GHC.Base.
Require GHC.Base.
Import GHC.Base.ManualNotations.

(*
Require Import Proofs.ScopeInvariant.
*)

Set Bullet Behavior "Strict Subproofs".

Lemma unionsVarSet_equal : forall vss1 vss2, Forall2 Equal vss1 vss2 ->
  (Foldable.foldr unionVarSet emptyVarSet) vss1 [=]
  (Foldable.foldr unionVarSet emptyVarSet) vss2.
Proof.
  move=>vss1 vss2.
  elim.
  hs_simpl. reflexivity.
  move=> x y l l' Eq1 Eq2 IH.
  hs_simpl.
  f_equiv; auto.
Qed.

(* Definition mapUnionVarSet {A} f (ps : list A) :=
  Foldable.foldr unionVarSet emptyVarSet (map f ps).
*)

Lemma mapUnionVarSet_mapUnionFV A (ps : list A) 
      (f1 :  A -> VarSet) (f2 : A -> FV.FV) :
  Forall2 Denotes (map f1 ps) (map f2 ps) ->
  Denotes  (mapUnionVarSet f1 ps) (FV.mapUnionFV f2 ps).
Proof.
  elim: ps => [|p ps IH]; unfold mapUnionVarSet; simpl.
  hs_simpl.
  - move=>h. constructor; intros; subst.
    unfold Tuple.fst, Tuple.snd.
    hs_simpl.
    split; auto.
    reflexivity.
  - hs_simpl.
    move=>h. inversion h. subst.
    unfold mapUnionVarSet in IH.
    specialize (IH H4). clear H4.
    move: (unionVarSet_unionFV _ _ _ _ H2 IH) => h0.
    unfold FV.unionFV in h0.
    auto.
Qed.


Lemma unionsFV_cons fv fvs : 
  FV.unionsFV (fv :: fvs) = 
  FV.unionFV (FV.unionsFV fvs) fv.
Proof.
  repeat unfold FV.unionsFV, FV.unionFV.
  rewrite mapUnionFV_cons.
  unfold FV.unionFV.
  simpl.
  reflexivity.
Qed.


Lemma unionsVarSet_unionsFV vss fvs: 
   Forall2 Denotes vss fvs ->
   Denotes (Foldable.foldr unionVarSet emptyVarSet vss) (FV.unionsFV fvs).
Proof.
  elim.
  - hs_simpl. 
    unfold FV.unionsFV, FV.mapUnionFV.
    constructor; intros; subst.
    unfold Tuple.fst, Tuple.snd.
    hs_simpl.
    split; auto.
    reflexivity.
  - move => vs fv vss1 fvs1 D1 D2 IH. 
    hs_simpl. 
    move: (unionVarSet_unionFV _ _ _ _ D1 IH) => h0.
    rewrite unionsFV_cons.
    auto.
Qed.

(** ** [FV] *)

Lemma emptyVarSet_bndrRuleAndUnfoldingFVs bndr :
  Denotes emptyVarSet (bndrRuleAndUnfoldingFVs bndr).
Proof.
  destruct bndr; unfold bndrRuleAndUnfoldingFVs; simpl.
  eapply emptyVarSet_emptyFV.
(*  unfold idRuleFVs, idUnfoldingFVs, stableUnfoldingFVs. simpl.
  rewrite union_empty_l.
  eapply emptyVarSet_emptyFV. *)
Qed.

Lemma addBndr_fv fv bndr vs :
  Denotes vs fv -> 
  Denotes (delVarSet vs bndr) (addBndr bndr fv).
Proof.
  move => h.
  unfold addBndr, varTypeTyCoFVs.
  rewrite union_empty_l. 
  move: (delVarSet_delFV _ bndr _ h) => h1.
  eauto.
Qed.

Lemma addBndr_WF : forall fv bndr,
    WF_fv fv ->
    WF_fv (addBndr bndr fv).
Proof.
  move=> fv bndr [vs D].
  eexists.
  eauto using addBndr_fv.
Qed.

(** A very specialized [Proper] instance, written for the sole purpose
    of proving [delVarSetList_commute]. *)
Instance foldl_m :
  Proper (Equal ==> (fun (a b : list Var) => a = b) ==> Equal)
         (Foldable.foldl delVarSet).
Proof.
  intros s1 s2 Heqs l1 l2 Heql; subst.
  generalize dependent s2.
  generalize dependent s1.
  induction l2.
  - rewrite /Foldable.foldl //=.
  - intros s1 s2 Heqs. rewrite !Foldable_foldl_cons.
    apply IHl2. rewrite Heqs. reflexivity.
Qed.

Lemma delVarSetList_commute :forall (bndrs:list Var) vs bndr,
  Foldable.foldl delVarSet (delVarSet vs bndr) bndrs [=]
  delVarSet (Foldable.foldl delVarSet vs bndrs) bndr.
Proof.
  elim => [|bndr' bndrs].
  - move=> vs bndr. hs_simpl. reflexivity.
  - move=> IH vs bndr.
    hs_simpl.
    rewrite delVarSet_commute.
    eapply IH.
Qed.


Lemma addBndrs_fv fv bndrs vs :
  Denotes vs fv -> 
  Denotes (delVarSetList vs bndrs) (addBndrs bndrs fv).
Proof.
  move => h.
  unfold addBndrs, varTypeTyCoFVs.
  rewrite delVarSetList_foldl.
  move: bndrs vs fv h.
  elim => [|bndr bndrs].
  - hs_simpl. auto.
  - move=> Ih vs fv h.
    hs_simpl.
   rewrite delVarSetList_commute.
   eapply addBndr_fv.
   eauto.
Qed.

Lemma addBndrs_WF : forall fv bndrs,
    WF_fv fv ->
    WF_fv (addBndrs bndrs fv).
Proof.
  induction bndrs; unfold addBndrs;
    rewrite hs_coq_foldr_list; auto.
  intros. simpl. apply addBndr_WF. auto.
Qed.

Lemma bndrRuleAndUnfoldingFVs_WF bndr : WF_fv (bndrRuleAndUnfoldingFVs bndr).
Proof.
  destruct bndr; unfold bndrRuleAndUnfoldingFVs; simpl.
  eapply empty_FV_WF.
(*   unfold idRuleFVs, idUnfoldingFVs, stableUnfoldingFVs. simpl.
  eapply union_FV_WF; eapply empty_FV_WF. *)
Qed.


Lemma expr_fvs_WF : forall e,
    WF_fv (expr_fvs e).
Proof.
  intros e. apply (core_induct e); intros; simpl; auto.
  - destruct binds; auto. 
    apply union_FV_WF; apply union_FV_WF; try done.
    eapply bndrRuleAndUnfoldingFVs_WF.
    eapply del_FV_WF; auto.
    apply addBndrs_WF.
    apply union_FV_WF; auto. apply unions_FV_WF.
    intros. induction l; simpl in H1; try contradiction.
    destruct a. destruct H1. 
    + rewrite <- H1. 
      eapply union_FV_WF.
      apply H with (v:=c). constructor; reflexivity.
      eapply bndrRuleAndUnfoldingFVs_WF.
    + apply IHl; auto. intros.
      specialize (H v rhs). apply H. apply in_cons; auto.
  - apply union_FV_WF; auto.
    apply addBndr_WF. apply unions_FV_WF.
    induction alts; simpl; try contradiction.
    intros. destruct a as [[? ?] ?]. destruct H1.
    + rewrite <- H1. apply addBndrs_WF. apply (H0 a l c).
      constructor; reflexivity.
    + apply IHalts; auto. intros. specialize (H0 dc pats rhs).
      apply H0. apply in_cons; auto.
Qed.

(** Unfolding tactics *)

Ltac unfold_FV := 
  repeat unfold Base.op_z2218U__, FV.filterFV, FV.fvVarSet, 
       FV.unitFV, FV.fvVarListVarSet.


Definition disjoint E F := inter E F [=] empty.

(** ** [exprFreeVars] *)

(* Nice rewrite rules for [exprFreeVars] *)

Lemma exprFreeVars_Var: forall v, 
    isLocalVar v = true -> 
    exprFreeVars (Mk_Var v) = unitVarSet v.
Proof.
  intros v NG.
  unfold exprFreeVars, exprFVs, expr_fvs.
  unfold_FV. unfold elemVarSet; simpl.
  set_b_iff. rewrite NG.
  simpl. unfold singleton, unitVarSet, UniqSet.unitUniqSet.
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
set_b_iff.
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
  forall e1 e2,
  exprFreeVars (App e1 e2) [=] unionVarSet (exprFreeVars e1) (exprFreeVars e2).
Proof.
  move=> e1 e2.
  unfold exprFreeVars,  Base.op_z2218U__.
  unfold exprFVs, Base.op_z2218U__ .
  move: (expr_fvs_WF (App e1 e2)) => [vs0 D0].
  move: (expr_fvs_WF e1) => [vs1 D1].
  move: (expr_fvs_WF e2) => [vs2 D2].
  move: (DenotesfvVarSet _ _ (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D0)) => D3.
  move: (DenotesfvVarSet _ _ (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D1)) => D4.
  move: (DenotesfvVarSet _ _ (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D2)) => D5.
  rewrite D3.
  rewrite D4.
  rewrite D5.
  rewrite unionVarSet_filterVarSet; try done.
  
  unfold expr_fvs in D0. fold expr_fvs in D0.
  move: (unionVarSet_unionFV _ _ (expr_fvs e2) (expr_fvs e1) D2 D1) => D6.
  move: (Denotes_inj1 _ _ _ D0 D6) => E.
  rewrite -> unionVarSet_sym in E.
  apply (filterVarSet_equal RespectsVar_isLocalVar E).
Qed.

Hint Rewrite exprFreeVars_App : hs_simpl.


Lemma exprFreeVars_mkLams_rev:
  forall vs e, exprFreeVars (mkLams (rev vs) e) [=] delVarSetList (exprFreeVars e) vs.
Proof.
  intros vs e. revert vs. apply rev_ind; intros.
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
    apply RespectsVar_isLocalVar.
    apply expr_fvs_WF.
Qed.

Lemma exprFreeVars_mkLams:
  forall vs e, exprFreeVars (mkLams vs e) [=] delVarSetList (exprFreeVars e) (rev vs).
Proof.
  intros. replace vs with (rev (rev vs)) at 1.
  - apply exprFreeVars_mkLams_rev.
  - apply rev_involutive.
Qed.



Lemma exprFreeVars_Lam:	
  forall v e, exprFreeVars (Lam v e) [=] delVarSet (exprFreeVars e) v.
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
  forall v rhs body,
  exprFreeVars (Let (NonRec v rhs) body) [=]
    unionVarSet (exprFreeVars rhs) (delVarSet (exprFreeVars body) v).
Proof.
  move=> v rhs body.
  unfold exprFreeVars.
  unfold_FV.
  unfold exprFVs.
  unfold_FV.
  unfold expr_fvs. fold expr_fvs.
  move: (expr_fvs_WF body) => [vbody h1].
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


Lemma Denotes_fvVarSet e: Denotes (FV.fvVarSet (expr_fvs e)) (expr_fvs e).
Proof. 
  move: (expr_fvs_WF e) => [vs h].
  move: (DenotesfvVarSet _ _ h) => eq.
  rewrite eq.
  auto.
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
    apply DenotesfvVarSet in h0.
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
    rewrite DenotesfvVarSet.
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
      eapply DenotesfvVarSet.
      rewrite DenotesfvVarSet.
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
  move: (DenotesfvVarSet _ _ D1) => D2.
  rewrite D2.

  move: (unionVarSet_unionFV _ _ _ _ D (Denotes_tickish co)) => D3.
  move: (filterVarSet_filterFV isLocalVar _ _ RespectsVar_isLocalVar D3) => D4.
  move: (DenotesfvVarSet _ _ D4) => D5.
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
  rewrite (DenotesfvVarSet _ _ h4).  
  rewrite (DenotesfvVarSet _ _ h3).  
  rewrite (DenotesfvVarSet _ _ h1).  
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
    replace FV.fvDVarSet with FV.fvVarSet; auto.

Lemma freeVarsOf_freeVars_revised:
  forall e,
  (freeVarsOf (freeVars e)) [=] exprFreeVars e.
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
    unfold unionFVs. unfold delBinderFV. unfold dVarTypeTyCoVars. unfold varTypeTyCoFVs.
    DVarToVar.
    fsetdec.
  - intros.
    destruct binds.
    + rewrite exprFreeVars_Let_NonRec.
      unfold freeVars; fold freeVars.
      unfold freeVarsOf.
      destruct (freeVars e0).
      destruct (freeVars body).
      rewrite <- H0. rewrite <- H. unfold freeVarsOf.
      unfold delBinderFV. unfold dVarTypeTyCoVars. unfold varTypeTyCoFVs.
      unfold bndrRuleAndUnfoldingVarsDSet.
      unfold bndrRuleAndUnfoldingFVs.
      DVarToVar.
      replace (isId c) with true; try (destruct c; reflexivity).
      fsetdec.
    + rewrite exprFreeVars_Let_Rec. rewrite <- H0.
      induction l. 
      ++ hs_simpl.         
         unfold freeVars; fold freeVars.
         simpl.
         unfold delBindersFV.
         hs_simpl.
         reflexivity.
      ++ admit.
  - intros.
    rewrite exprFreeVars_Case.
    unfold freeVars; fold freeVars.
    admit.
  - intros. rewrite exprFreeVars_Cast. unfold freeVars. fold freeVars. 
    simpl. rewrite H. fsetdec.
  - intros. rewrite exprFreeVars_Type. unfold freeVars. fold freeVars.
    simpl. reflexivity.
  - intros. rewrite exprFreeVars_Coercion. unfold freeVars. fold freeVars.
    simpl. reflexivity.
 Abort.

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
