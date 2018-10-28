From mathcomp.ssreflect
Require Import ssreflect ssrnat prime ssrbool eqtype.

Require Import Name.
Require Import Id.
Require Import Core.
Require Import CoreFVs.
Require Import CoreUtils.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import Proofs.Base.
Require Import Proofs.GhcTactics.
Require Import Proofs.Forall.
Require Import Proofs.Unique.
Require Import Proofs.CoreFVs.
Require Import Proofs.VarSet.
Require Import Proofs.VarEnv.
Require Import Proofs.CoreInduct.
Require Import Proofs.Var.

Import GHC.Base.Notations.

Set Bullet Behavior "Strict Subproofs".

(** * Core invariants related to variables and scope *)

(** ** The invariants *)

(**
First we define invariants for [Var] that are independent of scope, namely:
- It is a localVar iff the unique is local.
- The [Unique] cached in the [Var] is the same as the [Unique] of the name
  of the var.
- The var must be an identifier (i.e. a term variable)
- but not one that is a coercion variable.
*)
Definition GoodVar (v : Var) : Prop :=
  isLocalVar v = isLocalUnique (varUnique v) /\
  varUnique v = nameUnique (varName v) /\
  isId v = true /\
  isCoVar v = false.

Definition GoodLocalVar (v : Var) : Prop :=
  GoodVar v /\ isLocalVar v = true.




(**

Next we define when a variable occurrence is ok in a given scope.
 * Global variables are always ok (not yet tracked).
 * Local variables are ok if they are in scope, and
   are almost the same as the binder; i.e., only the 
   [idInfo] may vary

We do not have to check [GoodVar] here; instead we check that
for all binders.
*)

Definition WellScopedVar (v : Var) (in_scope : VarSet) : Prop :=
  if isLocalVar v then
   match lookupVarSet in_scope v with
    | None => False
    | Some v' => almostEqual v v'
    end
  else True (* we do not track global variables yet *).


(**

Finally, we lift this to whole expressions, keeping track of the variables
that are in [in_scope]. Remember that GHC allows shadowing!

*)

Fixpoint WellScoped (e : CoreExpr) (in_scope : VarSet) {struct e} : Prop :=
  match e with
  | Mk_Var v => WellScopedVar v in_scope
  | Lit l => True
  | App e1 e2 => WellScoped e1 in_scope /\  WellScoped e2 in_scope
  | Lam v e => GoodLocalVar v /\ WellScoped e (extendVarSet in_scope v)
  | Let bind body =>
      WellScopedBind bind in_scope /\
      WellScoped body (extendVarSetList in_scope (bindersOf bind))
  | Case scrut bndr ty alts  => 
    WellScoped scrut in_scope /\
    GoodLocalVar bndr /\
    Forall' (fun alt =>
      Forall GoodLocalVar (snd (fst alt)) /\
      let in_scope' := extendVarSetList in_scope (bndr :: snd (fst alt)) in
      WellScoped (snd alt) in_scope') alts
  | Cast e _ =>   WellScoped e in_scope
  | Tick _ e =>   WellScoped e in_scope
  | Type_ _  =>   True
  | Coercion _ => True
  end
with WellScopedBind (bind : CoreBind) (in_scope : VarSet) : Prop :=
  match bind with
  | NonRec v rhs =>
    GoodLocalVar v /\
    WellScoped rhs in_scope
  | Rec pairs => 
    Forall (fun p => GoodLocalVar (fst p)) pairs /\
    NoDup (map varUnique (map fst pairs)) /\
    Forall' (fun p => WellScoped (snd p) (extendVarSetList in_scope (map fst pairs))) pairs
  end.

Definition WellScopedAlt bndr (alt : CoreAlt) in_scope  :=
    Forall GoodLocalVar (snd (fst alt)) /\
    let in_scope' := extendVarSetList in_scope (bndr :: snd (fst alt)) in
    WellScoped (snd alt) in_scope'.

(**

A [CoreProgram] can be treated like one big recursive group, despite that it
is a sequence of [Rec] and [NonRec] bindings.

*)
Definition WellScopedProgram (pgm : CoreProgram) : Prop :=
   NoDup (map varUnique (bindersOfBinds pgm)) /\
   Forall' (fun p => WellScoped (snd p) (mkVarSet (bindersOfBinds pgm))) (flattenBinds pgm).


(** ** Lemmas *)


(** *** Lemmas about [GoodLocalVar] *)

Lemma GoodLocalVar_uniqAway:
  forall vss v, GoodLocalVar v -> GoodLocalVar (uniqAway vss v).
Proof.
  intros.
  unfold GoodLocalVar, GoodVar in *.
  destruct H; destruct H; destruct H1. destruct H2.
  rewrite isLocalVar_uniqAway.
  rewrite isLocalUnique_uniqAway.
  rewrite isId_uniqAway.
  rewrite isCoVar_uniqAway.
  repeat split; auto.
  rewrite nameUnique_varName_uniqAway; auto.
Qed.

Lemma GoodLocalVar_asJoinId_mkSysLocal:
  forall s u ty n,
  isLocalUnique u = true ->
  GoodLocalVar (asJoinId (mkSysLocal s u ty) n).
Proof.
  intros.
  split; only 1: split.
  * destruct u. symmetry. apply H.
  * split. destruct u. reflexivity. 
    auto.
  * destruct u. reflexivity. 
Qed.


Lemma GoodLocalVar_almostEqual:
  forall v1 v2,
  GoodLocalVar v1 ->
  almostEqual v1 v2 ->
  GoodLocalVar v2.
Proof.
  intros.
  destruct H. destruct H.
  induction H0.
  * split; only 1: split; assumption.
  * split; only 1: split; assumption.
  * split; only 1: split; assumption.
Qed.


(** *** Structural lemmas *)

Lemma WellScopedVar_extendVarSet:
  forall v vs,
  WellScopedVar v (extendVarSet vs v).
Proof.
  intros.
  unfold WellScopedVar.
  rewrite lookupVarSet_extendVarSet_self.
  destruct_match.
  * apply almostEqual_refl.
  * trivial.
Qed.


Lemma WellScoped_varToCoreExpr:
  forall v isvs,
  WellScopedVar v isvs -> WellScoped (varToCoreExpr v) isvs.
Proof.
  intros.
  destruct v; simpl; try trivial.
  unfold varToCoreExpr; simpl.
  destruct_match; simpl; try trivial.
Qed.


Lemma WellScoped_Lam:
  forall v e isvs,
  WellScoped (Lam v e) isvs <-> GoodLocalVar v /\ WellScoped e (extendVarSet isvs v).
Proof. intros. reflexivity. Qed.


Lemma WellScoped_mkLams:
  forall vs e isvs,
  WellScoped (mkLams vs e) isvs <-> Forall GoodLocalVar vs /\ WellScoped e (extendVarSetList isvs vs).
Proof.
  induction vs; intros.
  * intuition.
  * simpl.
    rewrite extendVarSetList_cons.
    rewrite Forall_cons_iff.
    rewrite and_assoc.
    rewrite <- (IHvs _ _).
    reflexivity.
Qed.

Lemma WellScoped_mkVarApps:
  forall e vs isvs,
  WellScoped e isvs -> 
  Forall (fun v => WellScopedVar v isvs) vs ->
  WellScoped (mkVarApps e vs) isvs.
Proof.
  intros.
  unfold mkVarApps.
  rewrite Foldable.hs_coq_foldl_list.
  revert e H.
  induction H0; intros.
  * simpl. intuition.
  * simpl.
    apply IHForall; clear IHForall.
    simpl.
    split; try assumption.
    apply WellScoped_varToCoreExpr; assumption.
Qed.

Lemma WellScoped_MkLetRec: forall pairs body isvs,
  WellScoped (mkLetRec pairs body) isvs <-> WellScoped (Let (Rec pairs) body) isvs .
Proof.
  intros.
  unfold mkLetRec.
  destruct pairs; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

Lemma WellScoped_MkLet: forall bind body isvs,
  WellScoped (mkLet bind body) isvs <-> WellScoped (Let bind body) isvs .
Proof.
  intros.
  unfold mkLet.
  destruct bind; try reflexivity.
  destruct l; try reflexivity.
  simpl.
  rewrite extendVarSetList_nil.
  split; intro; repeat split; try constructor; intuition.
Qed.

(** *** Lemmas related to [StrongSubset] *)

Lemma WellScopedVar_StrongSubset : forall e vs1 vs2, 
    WellScopedVar e vs1 -> StrongSubset vs1 vs2 -> WellScopedVar e vs2.
Proof.
  intros v vs1 vs2 WS SS.
  unfold WellScopedVar, StrongSubset in *.
  destruct_match; only 2: trivial.
  specialize (SS v).
  destruct (lookupVarSet vs1 v); try contradiction.
  destruct (lookupVarSet vs2 v) eqn:LV2; try contradiction.
  eapply almostEqual_trans with (v2 := v0); auto.
Qed.

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
  - destruct H1 as [W1 [W2 W3]].
    split; only 2: split; eauto.
     rewrite -> Forall'_Forall in *.
     rewrite -> Forall_forall in *.
     intros h IN. destruct h as [[dc pats] rhs].
     specialize (H0 dc pats rhs IN).
     specialize (W3 (dc,pats,rhs) IN).
     simpl in *.
     destruct W3 as [GLV WS].
     eauto using StrongSubset_extendVarSetList.
Qed.

(** *** Relation to [exprFreeVars] *)

Require Import Proofs.VarSetFSet.

Lemma WellScoped_subset:
  forall e vs,
    WellScoped e vs -> subVarSet (exprFreeVars e) vs = true.
Proof.
  intro e.
  apply (core_induct e); intros.
  - unfold WellScoped, WellScopedVar in *.
    destruct (isLocalVar v) eqn:HisLocal.
    + destruct (lookupVarSet vs v) eqn:Hl; try contradiction.
      rewrite -> exprFreeVars_Var by assumption.
      rewrite subVarSet_unitVarSet.
      eapply lookupVarSet_elemVarSet; eassumption.
    + rewrite -> exprFreeVars_global_Var by assumption.
      apply subVarSet_emptyVarSet.
  - apply subVarSet_emptyVarSet.
  - simpl in H1.
    rewrite exprFreeVars_App.
    rewrite subVarSet_unionVarSet.
    rewrite andb_true_iff.
    intuition.
  - simpl in H0.
    destruct H0.
    rewrite exprFreeVars_Lam.
    apply H in H1.
    set_b_iff. fsetdec.
  - destruct binds as [v rhs | pairs].
    + simpl in H1. decompose [and] H1; clear H1.
      rewrite exprFreeVars_Let_NonRec.
      apply H in H5.
      apply H0 in H3.
      rewrite -> extendVarSetList_cons, extendVarSetList_nil in H3.
      set_b_iff. fsetdec.
    + simpl in H1. decompose [and] H1; clear H1.
      rewrite -> Forall'_Forall in H6.
      rewrite exprFreeVars_Let_Rec.
      apply H0 in H3; clear H0.
      rewrite Core.bindersOf_Rec_cleanup in H3.
      apply subVarSet_delVarSetList_extendVarSetList_dual.
      unfold is_true.
      rewrite -> subVarSet_unionVarSet, andb_true_iff; split.
      * apply subVarSet_exprsFreeVars.
        rewrite -> Forall_map, Forall_forall in *.
        intros [v rhs] HIn. simpl in *.
        apply (H _ _ HIn).
        apply (H6 _ HIn).
      * assumption.
  - simpl in H1. decompose [and] H1; clear H1.
    rewrite -> Forall'_Forall in H5.
    rewrite exprFreeVars_Case.
    rewrite -> subVarSet_unionVarSet, andb_true_iff; split.
    * apply H; assumption.
    * apply subVarSet_mapUnionVarSet.
      rewrite -> Forall_forall in *.
      intros [[dc pats] rhs] HIn.
      specialize (H5 _ HIn). destruct H5. simpl in *.
      (* Some reordering is needed here. This is a bit smelly,
         maybe there should be a [rev] in [exprFreeVars_Case] already? *)
      rewrite <- delVarSetList_rev.
      rewrite rev_app_distr.
      rewrite delVarSetList_app.
      rewrite !delVarSetList_rev.
      rewrite <- delVarSetList_app.
      simpl.
      apply subVarSet_delVarSetList_extendVarSetList_dual.
      apply (H0 _ _ _ HIn).
      assumption.
  - rewrite exprFreeVars_Cast. apply H; assumption.
  - rewrite exprFreeVars_Tick. apply H; assumption.
  - apply subVarSet_emptyVarSet.
  - apply subVarSet_emptyVarSet.
Qed.


(** *** Freshness *)

Lemma WellScopedVar_extendVarSetList_l:
  forall v vs1 vs2,
  WellScopedVar v vs1 ->
  elemVarSet v (mkVarSet vs2) = false ->
  WellScopedVar v (extendVarSetList vs1 vs2).
Proof.
  intros.
  unfold WellScopedVar in *.
  destruct_match; only 2: apply I.
  destruct_match; only 2: contradiction.
  rewrite lookupVarSet_extendVarSetList_l. 
  rewrite Heq0.
  assumption.
  rewrite H0. 
  auto.
Qed.

Lemma WellScopedVar_extendVarSetList_r:
  forall v vs1 vs2,
  List.In v vs2 ->
  NoDup (map varUnique vs2) ->
  WellScopedVar v (extendVarSetList vs1 vs2).
Proof.
  intros.
  unfold WellScopedVar in *.
  destruct_match; only 2: apply I.
  rewrite -> lookupVarSet_extendVarSetList_r_self by assumption.
  apply almostEqual_refl.
Qed.

(* There are a number of variants of the freshness lemmas.
   The simplest one that implies all others is this, so lets
   only do one induction:
*)

Lemma and_iff_compat_both:
  forall A B C D : Prop,
    A <-> C -> B <-> D ->
    A /\ B <-> C /\ D.
Proof. intros. intuition. Qed.

Lemma Forall_iff:
  forall a P Q (xs : list a),
    Forall (fun x => P x <-> Q x) xs ->
    Forall P xs <-> Forall Q xs.
Proof. intros. rewrite -> !Forall_forall in *. firstorder. Qed.


Lemma WellScoped_extendVarSetList_fresh_under:
  forall vs1 vs2 e vs,
  disjointVarSet (delVarSetList (exprFreeVars e) vs2) (mkVarSet vs1)  = true ->
  WellScoped e (extendVarSetList (extendVarSetList vs vs1) vs2) <->
  WellScoped e (extendVarSetList vs vs2).
Proof.
 (* This proof is similar to isJoinPointsValid_fresh_updJPSs_aux
    In particular, proving the assumtion [disjointVarSet ..] for all the inductive
    cases is identical (although here we have more inductive cases than there.
    Once could common it up with a deidcated induction rule. Or live with the duplication.
  *)
  intros.
  rewrite <- delVarSetList_rev in H.
  revert vs2 vs H.
  apply (core_induct e); intros.
  * simpl.
    unfold WellScopedVar.
    destruct_match; only 2: reflexivity.
    enough (lookupVarSet (extendVarSetList (extendVarSetList vs vs1) vs2) v = 
            lookupVarSet (extendVarSetList vs vs2) v) as Htmp
      by (rewrite Htmp; reflexivity).
    rewrite -> exprFreeVars_Var in H by assumption.
    rewrite delVarSetList_rev in H.
    clear -H.
    (* duplication with isJoinPointsValid_fresh_updJPSs_aux here *)
    induction vs2 using rev_ind.
    + rewrite !extendVarSetList_nil.
      rewrite delVarSetList_nil in H.
      revert vs; induction vs1; intros.
      - rewrite extendVarSetList_nil.
        reflexivity.
      - rewrite extendVarSetList_cons.
        rewrite -> fold_is_true in H.
        rewrite -> disjointVarSet_mkVarSet_cons in H.
        destruct H.
        rewrite -> IHvs1 by assumption.
        apply lookupVarSet_extendVarSet_neq.
        contradict H.
        rewrite not_false_iff_true.
        apply H.
    + rewrite -> delVarSetList_app, delVarSetList_cons, delVarSetList_nil in H.
      rewrite -> !extendVarSetList_append, !extendVarSetList_cons, !extendVarSetList_nil.
      destruct (x GHC.Base.== v) eqn:?.
      -- rewrite -> !lookupVarSet_extendVarSet_eq by assumption.
         reflexivity.
      -- rewrite <- not_true_iff_false in Heqb.
         rewrite -> !lookupVarSet_extendVarSet_neq by assumption.
         apply IHvs2.
         rewrite -> fold_is_true in *.
         rewrite -> disjointVarSet_mkVarSet in *.
         eapply Forall_impl; only 2: eapply H. intros v2 ?.
         cbv beta in H0.
         rewrite -> delVarSet_elemVarSet_false in H0; only 1: assumption.
         clear -Heqb.
         apply elemVarSet_delVarSetList_false_l.
         unfold is_true in Heqb.
         rewrite -> not_true_iff_false in Heqb.
         apply Heqb.
  * reflexivity.
  * simpl.
    apply and_iff_compat_both.
    - apply H.
      eapply disjointVarSet_subVarSet_l; only 1: apply H1.
      apply subVarSet_delVarSetList_both.
      rewrite exprFreeVars_App.
      set_b_iff; fsetdec.
    - apply H0.
      eapply disjointVarSet_subVarSet_l; only 1: apply H1.
      apply subVarSet_delVarSetList_both.
      rewrite exprFreeVars_App.
      set_b_iff; fsetdec.
  * simpl.
    apply and_iff_compat_both; try reflexivity.
    rewrite <- !extendVarSetList_singleton.
    rewrite <- !extendVarSetList_append with (vs1 := vs2).
    apply H.
    rewrite exprFreeVars_Lam in H0.
    rewrite rev_app_distr.
    simpl.
    rewrite delVarSetList_cons.
    assumption.
  * simpl.
    apply and_iff_compat_both.
    - destruct binds as [v rhs | pairs].
      + simpl.
        apply and_iff_compat_both; only 1: reflexivity.
        apply H.
        eapply disjointVarSet_subVarSet_l; only 1: apply H1.
        apply subVarSet_delVarSetList_both.
        rewrite exprFreeVars_Let_NonRec.
        set_b_iff; fsetdec.
      + simpl.
        repeat apply and_iff_compat_both; try reflexivity.
        rewrite !Forall'_Forall.
        apply Forall_iff.
        rewrite Forall_forall.
        intros [v rhs] HIn.
        rewrite <- !extendVarSetList_append with (vs1 := vs2).
        apply (H _ _ HIn).
        eapply disjointVarSet_subVarSet_l; only 1: apply H1.
        rewrite rev_app_distr; simpl.
        rewrite delVarSetList_app.
        apply subVarSet_delVarSetList_both.
        rewrite exprFreeVars_Let_Rec.
        pose proof (subVarSet_exprFreeVars_exprsFreeVars _ _ _ HIn).
        rewrite delVarSetList_rev.
        apply subVarSet_delVarSetList_both.
        set_b_iff; fsetdec.
    - rewrite <- !extendVarSetList_append with (vs1 := vs2).
      apply H0.
      eapply disjointVarSet_subVarSet_l; only 1: apply H1; clear H1.
      rewrite -> rev_app_distr, delVarSetList_app.
      apply subVarSet_delVarSetList_both.
      destruct binds as [v rhs | pairs].
      -- rewrite exprFreeVars_Let_NonRec.
         simpl.
         rewrite -> delVarSetList_cons, delVarSetList_nil.
         set_b_iff; fsetdec.
      -- rewrite exprFreeVars_Let_Rec.
         simpl. rewrite Core.bindersOf_Rec_cleanup.
         rewrite delVarSetList_rev.
         apply subVarSet_delVarSetList_both.
         set_b_iff; fsetdec.

  * simpl.
    repeat apply and_iff_compat_both; try reflexivity.
    - apply H.
      eapply disjointVarSet_subVarSet_l; only 1: apply H1; clear H1.
      apply subVarSet_delVarSetList_both.
      rewrite exprFreeVars_Case.
      set_b_iff; fsetdec.
    - rewrite !Forall'_Forall.
      apply Forall_iff.
      rewrite Forall_forall.
      intros [[dc pats] rhs] HIn; simpl.
      repeat apply and_iff_compat_both; try reflexivity.
      rewrite <- !extendVarSetList_append with (vs1 := vs2).
      apply (H0 _ _ _ HIn).
      eapply disjointVarSet_subVarSet_l; only 1: apply H1.
      rewrite rev_app_distr; simpl.
      rewrite -> !delVarSetList_app, delVarSetList_cons, delVarSetList_nil.
      apply subVarSet_delVarSetList_both.
      rewrite exprFreeVars_Case.
      unfold is_true.
      match goal with HIn : List.In _ ?xs |- context [mapUnionVarSet ?f ?xs] =>
        let H := fresh in
        epose proof (mapUnionVarSet_In_subVarSet f HIn) as H ; simpl in H end.
      rewrite -> delVarSetList_rev, <- delVarSetList_single, <- delVarSetList_app.
      set_b_iff; fsetdec.
  * apply H. 
    eapply disjointVarSet_subVarSet_l; only 1: apply H0.
    apply subVarSet_delVarSetList_both.
    rewrite exprFreeVars_Cast.
    set_b_iff; fsetdec.
  * apply H. 
    eapply disjointVarSet_subVarSet_l; only 1: apply H0.
    apply subVarSet_delVarSetList_both.
    rewrite exprFreeVars_Tick.
    set_b_iff; fsetdec.
  * reflexivity.
  * reflexivity.
Qed.

Lemma WellScoped_extendVarSetList_fresh:
  forall vs e vs1,
  disjointVarSet (exprFreeVars e) (mkVarSet vs) = true ->
  WellScoped e (extendVarSetList vs1 vs) <->
  WellScoped e vs1.
Proof.
  intros.
  epose proof (WellScoped_extendVarSetList_fresh_under vs [] e vs1 _).
  rewrite !extendVarSetList_nil in H0.
  eassumption.
  Unshelve.
  rewrite delVarSetList_nil. assumption.
Qed.

Lemma WellScoped_extendVarSet_fresh:
  forall v e vs,
  elemVarSet v (exprFreeVars e) = false ->
  WellScoped e (extendVarSet vs v) <-> WellScoped e vs.
Proof.
  intros.
  epose proof (WellScoped_extendVarSetList_fresh [v] e vs _).
  rewrite -> extendVarSetList_cons,extendVarSetList_nil in H0.
  assumption.
  Unshelve.
  rewrite -> fold_is_true in *.
  rewrite -> disjointVarSet_mkVarSet_cons, disjointVarSet_mkVarSet_nil.
  intuition congruence.
Qed.

Lemma WellScoped_extendVarSetList_fresh_between:
  forall (vs1 vs2 vs3 : list Var) (e : CoreExpr) (vs : VarSet),
  disjointVarSet (delVarSetList (exprFreeVars e) vs3) (mkVarSet vs2) = true ->
  WellScoped e (extendVarSetList vs ((vs1 ++ vs2) ++ vs3)) <->
  WellScoped e (extendVarSetList vs (vs1 ++ vs3)).
Proof.
  intros.
  rewrite <- app_assoc.
  rewrite !extendVarSetList_append.
  apply WellScoped_extendVarSetList_fresh_under.
  assumption.
Qed.

(** *** The invariants respect [StrongSubset] *)


Instance Respects_StrongSubset_WellScopedVar v : Respects_StrongSubset (WellScopedVar v).
Proof.
  intros ????.
  unfold WellScopedVar in *.
  destruct_match; only 2: apply I.
  destruct_match; only 2: contradiction.
  specialize (H v).
  rewrite Heq0 in H.
  destruct_match; only 2: contradiction.
  eapply almostEqual_trans; eassumption.
Qed.

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
   * apply H.
   * apply Respects_StrongSubset_const.
   * apply Respects_StrongSubset_const.
Qed.
