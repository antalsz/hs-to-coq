Require Import GHC.Base.
Require Import CoreFVs.
Require Import Id.
Require Import Exitify.
Require Import Core.

Require Import Proofs.GHC.Base.
Require Import Proofs.GHC.List.

Require Import Psatz.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.NArith.BinNat.

Require Import Coq.Logic.FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

Require Import Proofs.Base.
Require Import Proofs.JoinPointInvariants.
Require Import Proofs.ScopeInvariant.
Require Import Proofs.StateLogic.
Require Import Proofs.CoreInduct.
Require Import Proofs.Forall.
Require Import Proofs.Core.
Require Import Proofs.CoreFVs.
Require Import Proofs.GhcTactics.
Require Import Proofs.NCore.
Require Import Proofs.VectorUtils.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.Unique.

Close Scope Z_scope.


(* This section reflects the context of the local definition of exitifyRec *)
Section in_exitifyRec.
  (* Parameters of exitifyRec *)
  Variable in_scope : InScopeSet.
  Variable pairs : list NJPair.
  (* The actual parameter passed *)
  Definition in_scope2 := extendInScopeSetList in_scope (map (fun '(Mk_NJPair v _ _ _) => v) pairs).

  (* Parameters and assumptions of the proof *)
  Variable jps : VarSet.

  (* Giving names to the local functions of exitifyRec.
     See http://www.joachim-breitner.de/blog/738-Verifying_local_definitions_in_Coq
     for more on that idiom.
   *)
  Definition go_exit := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x := ?rhs in ?body) => 
      exact rhs
    end).

  Definition recursive_calls := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x := _ in let y := ?rhs in _) => 
      exact rhs
    end).

  Definition go := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let y := @?rhs x1 x2 in _) => 
      let def := eval cbv beta in (rhs go_exit recursive_calls) in
      exact def
    end).

  Definition ann_pairs := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let y := ?rhs in _) => 
      exact rhs
    end).

  Definition pairs'_exits := ltac:(
    let rhs := eval cbv beta delta [exitifyRec] in (exitifyRec in_scope2 (map toJPair pairs)) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let x4 := _ in let '(pairs',exits) := @?rhs x3 x4 in ?body) => 
      let def := eval cbv beta in (rhs go ann_pairs) in
      exact def
    end).
  Definition pairs' := fst pairs'_exits.
  Definition exits := snd pairs'_exits.

  (* Some useful definitions *)
  
  (* The names of the functions bound in this letrec *)
  Definition fs := map (fun '(Mk_NJPair v _ _ _) => v) pairs.

  (* [in_scope] and [in_scope2] should only be mentioned as concrete arguments
     to functions, but ideally quickly rewritten to these. *)
  (* The outermost scope *)
  Definition isvs := getInScopeVars in_scope.
  (* The let-scope, before *)
  Definition isvsp := extendVarSetList isvs fs .
  (* The outermost scope, including exits *)
  Definition isvs' := extendVarSetList isvs (map fst exits).
  (* The let-scope, after *)
  Definition isvsp' := extendVarSetList isvs' fs.

  (** Termination of [go] and a suitable induction lemma *)

  Definition go_f := ltac:(
    let rhs := eval cbv delta [go] in go in
    lazymatch rhs with
      | @DeferredFix.deferredFix2 ?a ?b ?r ?HDefault ?f =>
      exact f
    end).

  (* Termination of [go] *)
  Lemma go_eq :
     forall captured e,
     go captured (freeVars (toExpr e)) = go_f go captured (freeVars (toExpr e)).
  Proof.
    intros.
    unfold go; fold go_f.
    unfold DeferredFix.deferredFix2.
    unfold DeferredFix.curry.
    rewrite DeferredFix.deferredFix_eq_on with
      (P := fun p => exists u, snd p = freeVars (toExpr u))
      (R := fun p1 p2 => CoreLT (deAnnotate (snd p1)) (deAnnotate (snd p2))).
    * reflexivity.
    * apply Inverse_Image.wf_inverse_image.
      apply CoreLT_wf.
    * clear captured e.
      intros g h [captured ann_e] HP Hgh.
      destruct HP as [e Heq]. simpl in Heq. subst ann_e.

      simpl. cbv beta delta [go_f].
      repeat float_let; cse_let.

      enough (Hnext : j_40__ = j_40__0). {
        repeat (destruct_match; try reflexivity); try apply Hnext.
      }
      subst j_40__ j_40__0. cleardefs.

      destruct e;
        simpl; rewrite ?freeVarsBind1_freeVarsBind;
        try destruct n;
        simpl;
        try destruct (isLocalVar _);
        repeat expand_pairs;
        simpl;
        repeat destruct_match;
        simpl; rewrite ?freeVarsBind1_freeVarsBind;
        rewrite ?collectNAnnBndrs_freeVars_mkLams in *;
        try (simpl in Heq);
        try (inversion Heq; subst; clear Heq);
        try solve [congruence];
        try reflexivity.
      - f_equal.
        apply Hgh; simpl.
        + eexists; reflexivity.
        + simpl; rewrite ?freeVarsBind1_freeVarsBind.
          simpl.
          Core_termination.
      - f_equal.
        ** replace j with (length params) in Heq2 by congruence.
           rewrite collectNAnnBndrs_freeVars_mkLams in Heq2.
           inversion Heq2; subst; clear Heq2.
           apply Hgh; simpl.
           + eexists; reflexivity.
           + simpl; rewrite ?freeVarsBind1_freeVarsBind.
             simpl. repeat expand_pairs.
             rewrite !deAnnotate_freeVars, !deAnnotate'_snd_freeVars.
             Core_termination.
        ** extensionality join_body'.
           f_equal.
           apply Hgh.
           + eexists; reflexivity.
           + simpl. expand_pairs.
             Core_termination.
      - contradict H0.
        apply not_true_iff_false.
        rewrite zip_unzip_map.
        rewrite to_list_map.
        dependent inversion pairs0; subst.
        destruct h0.
        rewrite to_list_cons.
        simpl.
        rewrite isJoinId_eq. rewrite HnotJoin. reflexivity.
      - clear H0. f_equal.
        apply Hgh; simpl.
        + eexists; reflexivity.
        + simpl; rewrite ?freeVarsBind1_freeVarsBind.
          simpl. repeat expand_pairs. simpl.
          Core_termination.
      - clear H0.
        rewrite zip_unzip_map.
        rewrite to_list_map.
        rewrite !forM_map.
        f_equal.
        ** apply forM_cong. intros [j params rhs HiNJ] HIn.
           simpl.
           expand_pairs.
           erewrite idJoinArity_join by eassumption.
           rewrite collectNAnnBndrs_freeVars_mkLams.
           f_equal.
           apply Hgh.
           + eexists; reflexivity.
           + simpl.
             rewrite ?freeVarsBind1_freeVarsBind. simpl.
             repeat expand_pairs. simpl.
             rewrite !zip_unzip_map. rewrite !to_list_map.
             rewrite flat_map_unpack_cons_f.
             rewrite !map_map.
             eapply CoreLT_let_pairs_mkLam.
             rewrite in_map_iff.
             eexists. split. 2: eassumption. simpl.
             expand_pairs.
             rewrite ?deAnnotate_freeVars, ?deAnnotate'_snd_freeVars.
             reflexivity.
        ** extensionality pairs'.
           f_equal.
           apply Hgh.
           + eexists; reflexivity.
           + simpl.
             rewrite ?freeVarsBind1_freeVarsBind. simpl.
             repeat expand_pairs. simpl.
             Core_termination.
      - contradict H0.
        apply not_false_iff_true.
        rewrite zip_unzip_map.
        rewrite to_list_map.
        dependent inversion pairs0; subst.
        destruct h0.
        rewrite to_list_cons.
        simpl.
        rewrite isJoinId_eq. rewrite HisJoin. reflexivity.
      - f_equal.
        rewrite snd_unzip. rewrite !map_map, !forM_map.
        apply forM_cong. intros [[dc pats] rhs] HIn.
        simpl.
        f_equal. apply Hgh; clear Hgh.
        + eexists; reflexivity.
        + simpl. expand_pairs. simpl.
          rewrite snd_unzip, !map_map.
          simpl.
          eapply CoreLT_case_alts.
          rewrite in_map_iff.
          eexists. split. 2: eassumption. simpl.
          repeat expand_pairs. simpl.
          rewrite ?deAnnotate_freeVars, ?deAnnotate'_snd_freeVars.
          reflexivity.
  * eexists; reflexivity.
  Qed.

  Lemma go_ind_aux:
    forall (P : _ -> _ -> _ -> Prop),
    { IHs : Prop | 
    IHs ->
    forall e captured,
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    P captured e (go captured (freeVars (toExpr e)))
    }.
  Proof.
    intros P.
    eexists.
    intros IHs.
    pose proof IHs as IH1. eapply proj1 in IH1. eapply proj2 in IHs.
    pose proof IHs as IH2. eapply proj1 in IH2. eapply proj2 in IHs.
    pose proof IHs as IH3. eapply proj1 in IH3. eapply proj2 in IHs.
    pose proof IHs as IH4. eapply proj1 in IH4. eapply proj2 in IHs.
    pose proof IHs as IH5. eapply proj1 in IH5. eapply proj2 in IHs.
    pose proof IHs as IH6. eapply proj1 in IH6. eapply proj2 in IHs.
    rename IHs into IH7.
    refine (well_founded_ind NCoreLT_wf _ _).
    intros e IH captured HWS.

    rewrite go_eq.
    cbv beta delta [go_f]. (* No [zeta]! *)

    rewrite !deAnnotate_freeVars in *.
    rewrite !freeVarsOf_freeVars in *.

    (* Float out lets *)
    repeat float_let.
    enough (Hnext : P captured e j_40__). {
      clearbody j_40__; cleardefs.
      destruct (disjointVarSet fvs recursive_calls) eqn:Hdisjoint; try apply Hnext.
      clear IH Hnext.
      revert e captured fvs HWS Hdisjoint.
      refine IH1.
    }

    cleardefs.
    (* No exitification here, so descend*)
    subst j_40__.
    enough (Hnext: P captured e j_22__). {
      clearbody j_22__.
      destruct e; try apply Hnext.
      * (* spurious case Mk_Var *)
        simpl in *. destruct (isLocalVar _); apply Hnext.
      * (* spurious case Lam *)
        simpl in *. repeat expand_pairs. apply Hnext.
      * (* Case [Let] *) 
        clear Hnext.
        repeat float_let.
        simpl.
        do 2 expand_pairs. simpl.
        rewrite freeVarsBind1_freeVarsBind.
        unfold freeVarsBind.
        destruct n as [[x rhs] | [j params rhs] | n pairs' | n pairs']; simpl.
        + replace (isJoinId_maybe x) with (@None nat) by apply HnotJoin.
          lazymatch goal with |- context [go ?x (freeVars (toExpr ?y))] =>
             assert (IHe : P x y (go x (freeVars (toExpr y)))) end. {
            apply IH.
            ** NCore_termination.
            ** simpl.
               rewrite  extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
               apply HWS.
          }
          clear IH.
          revert captured x rhs e HnotJoin HWS IHe.
          refine IH2.
        + unfold CoreBndr in *.
          replace (isJoinId_maybe j) with (Some (length params)) by apply HisJoin.
          rewrite collectNAnnBndrs_freeVars_mkLams.
          lazymatch goal with |- context [go ?x (freeVars (toExpr ?y))] =>
            assert (IHrhs : P x y (go x (freeVars (toExpr y)) )) end. {
             apply IH.
             ** NCore_termination.
             ** rewrite extendVarSetList_append.
                rewrite <- WellScoped_mkLams.
                simpl in HWS.
                apply HWS.
          }
          assert (IHe : P (captured ++ [j]) e (go (captured ++ [j]) (freeVars (toExpr e)))). {
             apply IH.
             ** NCore_termination.
             ** rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
                apply HWS.
          } 
          clear IH.
          revert captured j params rhs e HisJoin HWS IHrhs IHe.
          refine IH3.
        + expand_pairs. simpl.
          rewrite to_list_map.
          rewrite !zip_unzip_map.
          rewrite !map_map.

          destruct (isJoinId _) eqn:Heq_isJoinId.
          Focus 1.
            exfalso.
            rewrite <- not_false_iff_true in Heq_isJoinId.
            contradict Heq_isJoinId.
            dependent inversion pairs'; subst; clear.
            dependent inversion h. simpl.
            rewrite isJoinId_eq. rewrite HnotJoin. reflexivity.
          clear Heq_isJoinId.

          clear IH1 IH2 IH3.

          (* Destruct well-scopedness assumption *)
          destruct HWS as [[HNoDup HWSpairs] HWSe].
          simpl toBind in HWSe.
          rewrite bindersOf_Rec in HWSe.
          rewrite Forall'_Forall in HWSpairs.
          rewrite to_list_map in HWSpairs.
          rewrite !map_map in HWSpairs.
          rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x) in HWSpairs
             by (intros; repeat expand_pairs; destruct a; reflexivity).
          rewrite Forall_map in HWSpairs.
          rewrite to_list_map in HWSe.
          rewrite !map_map in HWSe.
          rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x) in HWSe
             by (intros; repeat expand_pairs; destruct a; reflexivity).
          rewrite to_list_map in HNoDup.
          rewrite !map_map in HNoDup.
          rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => varUnique x) in HNoDup
             by (intros; repeat expand_pairs; destruct a; reflexivity).

          do 2 rewrite flat_map_unpack_cons_f.
          repeat rewrite map_map.
          rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x)
             by (intros; repeat expand_pairs; destruct a; reflexivity).

          lazymatch goal with |- context [go ?x (freeVars (toExpr ?y))] =>
            assert (IHe : P x y (go x (freeVars (toExpr y)) )) end. {
            apply IH.
            ** NCore_termination.
            ** rewrite !extendVarSetList_append.
               apply HWSe.
          }
          clear IH.
          revert n pairs' e captured HNoDup HWSpairs HWSe IHe.
          refine IH4.
        + clear IH1 IH2 IH3 IH4.

          expand_pairs. simpl.
          rewrite to_list_map.
          rewrite !zip_unzip_map.
          rewrite !map_map.
          rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x)
             by (intros; repeat expand_pairs; destruct a; reflexivity).

          destruct (isJoinId _) eqn:Heq_isJoinId.
          Focus 2.
            exfalso.
            rewrite <- not_true_iff_false in Heq_isJoinId.
            contradict Heq_isJoinId.
            dependent inversion pairs'; subst; clear.
            dependent inversion h. simpl.
            rewrite isJoinId_eq. rewrite HisJoin. reflexivity.
          clear Heq_isJoinId.

          (* Destruct well-scopedness assumption *)
          destruct HWS as [[HNoDup HWSpairs] HWSe].
          simpl toBind in HWSe.
          rewrite bindersOf_Rec in HWSe.
          rewrite Forall'_Forall in HWSpairs.
          rewrite to_list_map in HWSpairs.
          rewrite !map_map in HWSpairs.
          rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in HWSpairs
             by (intros; repeat expand_pairs; destruct a; reflexivity).
          rewrite Forall_map in HWSpairs.
          rewrite Forall_forall in HWSpairs.
          rewrite to_list_map in HWSe.
          rewrite !map_map in HWSe.
          rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in HWSe
             by (intros; repeat expand_pairs; destruct a; reflexivity).
          rewrite to_list_map in HNoDup.
          rewrite !map_map in HNoDup.
          rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => varUnique x) in HNoDup
             by (intros; repeat expand_pairs; destruct a; reflexivity).

          rewrite forM_map.
          assert (IHpairs : forall j params join_body HisJoin
            (HIn : In (Mk_NJPair j params join_body HisJoin) (Vector.to_list pairs')),
            P (captured ++ map (fun '(Mk_NJPair x0 _ _ _) => x0) (Vector.to_list pairs') ++ params) join_body
              (go (captured ++ map (fun '(Mk_NJPair x0 _ _ _) => x0) (Vector.to_list pairs') ++ params) (freeVars (toExpr join_body)))
          ). {
            intros j params rhs HisJoin HIn.
            apply IH.
            ** NCore_termination.
            ** rewrite !extendVarSetList_append.
               apply WellScoped_mkLams.
               eapply (HWSpairs _ HIn).
          }
          assert (IHe : P (captured ++ map (fun '(Mk_NJPair x _ _ _) => x) (Vector.to_list pairs')) e
                    (go (captured ++ map (fun '(Mk_NJPair x _ _ _) => x) (Vector.to_list pairs')) (freeVars (toExpr e)))).
          { 
            apply IH.
            ** NCore_termination.
            ** rewrite !extendVarSetList_append.
               apply HWSe.
          }
          clear IH. revert n pairs' e captured HNoDup HWSpairs HWSe IHpairs IHe.
          refine IH5.
      * (* Case [Case] *)
        clear IH1 IH2 IH3 IH4 IH5.
        simpl in *.

        do 2 expand_pairs. simpl.
        rewrite snd_unzip, !map_map.
        rewrite forM_map.

        destruct HWS as [HWSscrut HWSalts].
        rewrite Forall'_Forall in HWSalts.
        rewrite Forall_map in HWSalts.
        rewrite Forall_forall in HWSalts.

        assert (IHalts : forall dc pats rhs (HIn : In (dc, pats, rhs) l),
            P (captured ++ v :: pats) rhs (go (captured ++ v :: pats ) (freeVars (toExpr rhs)))). {
          intros.
          apply IH.
          ** NCore_termination.
          ** (* This needs automation! *)
             rewrite extendVarSetList_append.
             apply (HWSalts _ HIn).
        }
        clear IH Hnext. rename l into alts.
        revert e v alts captured HWSscrut HWSalts IHalts.
        refine IH6.
    }

    subst j_22__.
    clear IH. revert e captured HWS.
    refine IH7.
  Defined. (* important! *)

  (* We now uncurry the induction hypotheses
     (since we can’t do that right away in [go_ind_aux] *)
  Lemma uncurry_and : forall {A B C},
    (A /\ B -> C) -> (A -> B -> C).
  Proof. intros. intuition. Qed.
  Lemma under_imp: forall {A B C},
    (B -> C) -> (A -> B) -> (A -> C).
  Proof. intros. intuition. Qed.
  Ltac iterate n f x := lazymatch n with
    | 0 => x
    | S ?n => iterate n f uconstr:(f x)
  end.
  Ltac uncurryN n x :=
    let n' := eval compute in n in
    lazymatch n' with
    | 0 => x
    | S ?n => let uc := iterate n uconstr:(under_imp) uconstr:(uncurry_and) in
              let x' := uncurryN n x in
              uconstr:(uc x')
  end.
  Definition go_ind P
    := ltac:(let x := uncurryN 6 (proj2_sig (go_ind_aux P)) in exact x).
  Opaque go_ind go_ind_aux.

  (* Actually, we can simplify P to only take captured and e *)
  Definition go_ind' P := go_ind (fun captured e r => P captured e).

  (** ** Scope validity *)

  (** This predicate describes when a list of non-recursive bindings
      is ok to wrap around the [Let (Rec [pairs] body)] pair.

      (Maybe this could be abstracted over isvs and moved to [ScopeInvariants])
  *)
  Definition WellScopedFloats floats :=
    (* All added bindings are fresh with regard to the environment *)
    Forall (fun 'p => elemVarSet (fst p) isvs = false) floats /\
    (* All added bindings are fresh with regard to each other  *)
    NoDup (map (fun p => varUnique (fst p)) floats) /\
    (* All added bindings are well-scoped in the original environment  *)
    Forall (fun 'p => WellScoped (snd p) isvs) floats.

  (* Here we do the actual wrapping *)
  Lemma mkLets_WellScoped:
    forall exits' e,
    (* The body is well-scoped in the extended environment *)
    WellScoped e (extendVarSetList isvs (map fst exits')) ->
    WellScopedFloats exits' ->
    (* Then wrapping these bindings around [e] is well-scoped *)
    WellScoped (mkLets (map (fun '(v,rhs) => NonRec v rhs) exits') e) isvs.
   Proof.
    intros ?.
    unfold WellScopedFloats.
    generalize isvs as isvs.
    clear in_scope pairs jps.
    induction exits' as [|[v rhs] exits']; intros isvs' e Hbase Hfloats.
    * simpl. unfold Base.id. assumption.
    * simpl in *.
      rewrite extendVarSetList_cons, extendVarSetList_nil.
      destruct Hfloats as [Hfreshs [HNoDup Hrhss]].
      inversion HNoDup; subst; clear HNoDup. rename H1 into Hfresh, H2 into HNoDup.
      inversion_clear Hrhss. rename H into Hrhs, H0 into Hrhss.
      inversion_clear Hfreshs. rename H into Hfresh_v, H0 into Hfreshs.
      simpl in *.
      rewrite extendVarSetList_cons in Hbase.
      split; only 1: apply Hrhs.
      apply IHexits'.
      - assumption.
      - repeat split.
        + rewrite Forall_forall.
          rewrite Forall_forall in Hfreshs.
          rewrite in_map_iff in Hfresh.
          intros [v' rhs'] HIn.
          rewrite elemVarSet_extendVarSet.
          simpl_bool.
          split.
          ** simpl.
             destruct (Eq_eq (varUnique v') (varUnique v)); (reflexivity || exfalso).
             contradict Hfresh.
             exists (v', rhs'). split; assumption.
             admit.
          ** apply Hfreshs. assumption.
        + assumption.
        + rewrite Forall_forall.
          rewrite Forall_forall in Hrhss.
          intros pair HIn. simpl.
          rewrite WellScoped_extendVarSet_fresh.
          apply Hrhss; assumption.
          eapply subVarSet_elemVarSet_false; only 2: eassumption.
          apply WellScoped_subset.
          apply Hrhss; assumption.
  Admitted.

  (* the [addExit] function ensures that the new exit floats are well-scoped
     where we are going to put them.
   *)
  Lemma addExit_all_WellScopedFloats:
    forall captured ja e,
    WellScoped e isvs ->
    StateInvariant WellScopedFloats
                   (addExit (extendInScopeSetList in_scope2 captured) ja e).
  Proof.
    intros.
    (* This is much easier to prove by breaking the State abstraction and turning
       it into a simple function. *)
    unfold addExit, mkExitJoinId.
    unfold StateInvariant, SP,
           op_zgzgze__, return_, State.Monad__State, op_zgzgze____, return___,
           State.Monad__State_op_zgzgze__,
           State.Monad__State_return_,
           pure, State.Applicative__State , pure__,
           State.Applicative__State_pure,
           State.runState', State.get, State.put.
    simpl.
    intros floats Hfloats.
    set (v := uniqAway _ _).
    constructor; only 2: trivial.
    constructor; only 2: constructor; simpl.
    * constructor; only 2: apply Hfloats; simpl.
      unfold isvs, in_scope2 in *.
      apply elemVarSet_uniqAway.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      repeat apply subVarSet_extendVarSetList_l.
      apply subVarSet_refl.
    * constructor; only 2: apply Hfloats; simpl.
      rewrite <- map_map.
      rewrite <- elemVarSet_mkVarset_iff_In.
      rewrite not_true_iff_false.
      apply elemVarSet_uniqAway.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      apply subVarSet_extendVarSetList_r.
      apply subVarSet_refl.
    * constructor; only 2: apply Hfloats; simpl.
      assumption.
  Qed.


  (** in [go_exit], we [pick] variables to abstract over and [zap] them.
      That is somewhat involved, ([pick] is weird mix between a left-fold
      and a right fold) so extract their definitions to the top level
      and state lemmas about them.
   *)
  Definition zap := ltac:(
    let rhs := eval cbv beta delta [go_exit] in (go_exit [] (Type_ tt)  emptyVarSet) in
    lazymatch rhs with (let zap := ?rhs in ?body) =>
      exact rhs
    end
   ).

   Definition pick := ltac:(
    let rhs := eval cbv beta delta [go_exit] in (go_exit [] (Type_ tt)  emptyVarSet) in
    lazymatch rhs with (let zap' := _ in let abs_vars := let pick := @?rhs zap' in _ in _) =>
      let e' := eval cbv beta in (rhs zap) in
      exact e'
    end
    ).

  Lemma zap_ae: forall x, almostEqual x (zap x).
  Proof. intro v; unfold zap; destruct v; simpl; constructor. Qed.

  Lemma fst_pick_list:
    forall fvs vs xs,
    fst (fold_right pick (fvs,vs) xs) = fst (fold_right pick (fvs,[]) xs).
  Proof.
    induction xs.
    * reflexivity.
    * simpl. unfold pick at 1 3. do 2 expand_pairs.
      rewrite !IHxs. destruct_match; simpl; reflexivity.
  Qed.
  Lemma snd_pick_list: 
    forall fvs vs xs,
    snd (fold_right pick (fvs,vs) xs) = snd (fold_right pick (fvs,[]) xs) ++ vs.
  Proof.
    induction xs.
    * reflexivity.
    * simpl. unfold pick at 1 3. do 2 expand_pairs.
      rewrite !fst_pick_list. simpl. destruct_match; simpl.
      + rewrite IHxs. reflexivity. 
      + rewrite IHxs. reflexivity. 
  Qed.
  
  Lemma WellScoped_picked:
    forall fvs captured e,
    WellScoped e (extendVarSetList fvs captured) ->
    WellScoped e (extendVarSetList fvs (snd (fold_right pick (exprFreeVars e, []) captured))).
  Proof.
    induction captured using rev_ind; intros e HWSe; simpl.
    * simpl. assumption.
    * simpl.
      rewrite fold_right_app.
      rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil in HWSe.
      simpl.
      destruct_match; simpl.
      + rewrite snd_pick_list.
        rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
        rewrite <- WellScoped_Lam.
        erewrite delVarSet_ae by (apply zap_ae).
        rewrite <- exprFreeVars_Lam.
        apply IHcaptured.
        rewrite -> WellScoped_Lam.
        rewrite <- WellScoped_extendVarSet_ae by apply zap_ae.
        assumption.
      + apply IHcaptured.
        rewrite WellScoped_extendVarSet_fresh in HWSe; assumption.
  Qed.
  
  Lemma Forall_app:
    forall a P (xs ys : list a),
    Forall P xs -> Forall P ys ->
    Forall P (xs ++ ys).
  Proof.
    intros. induction xs; try assumption. constructor.
    inversion H; assumption.
    apply IHxs. inversion H; assumption.
  Qed.

  (* This following lemma verifies the bugfix of #15110 *)
  Lemma WellScopedVar_picked_aux:
    forall vsis captured fvs,
    Forall (fun v => WellScopedVar v (extendVarSetList vsis captured))
           (snd (fold_right pick (fvs, []) captured)) /\
    Forall (fun v => elemVarSet v fvs = true)
           (snd (fold_right pick (fvs, []) captured)).
  Proof.
    induction captured using rev_ind; intros.
    * constructor; constructor.
    * simpl.
      rewrite fold_right_app.
      simpl.
      rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
      destruct_match.
      + rewrite snd_pick_list.
        specialize (IHcaptured (delVarSet fvs x)).
        destruct IHcaptured as [IH1 IH2].
        split; apply Forall_app.
        - rewrite Forall_forall in *.
          intros v HIn. specialize (IH1 v HIn). specialize (IH2 v HIn).
          change (WellScoped (Mk_Var v) (extendVarSet (extendVarSetList vsis captured) x)).
          apply WellScoped_extendVarSet_fresh; only 2: apply IH1.
          rewrite exprFreeVars_Var.
          apply not_true_is_false.
          rewrite elemVarSet_unitVarSet.
          rewrite elemVarSet_delVarSet in *.
          intuition.
          admit.
        - constructor; only 2: constructor.
          change (WellScoped (Mk_Var (zap x)) (extendVarSet (extendVarSetList vsis captured) x)).
          rewrite WellScoped_extendVarSet_ae by (apply zap_ae).
          apply WellScopedVar_extendVarSet.
        - rewrite Forall_forall in *.
          intros v HIn. specialize (IH1 v HIn). specialize (IH2 v HIn).
          rewrite elemVarSet_delVarSet in *.
          intuition.
        - constructor; only 2: constructor.
          erewrite <- elemVarSet_ae by (apply zap_ae).
          assumption.
       + specialize (IHcaptured fvs).
         destruct IHcaptured as [IH1 IH2].
         split.
        - rewrite Forall_forall in *.
          intros v HIn. specialize (IH1 v HIn). specialize (IH2 v HIn).
          change (WellScoped (Mk_Var v) (extendVarSet (extendVarSetList vsis captured) x)).
          apply WellScoped_extendVarSet_fresh; only 2: apply IH1.
          rewrite exprFreeVars_Var.
          apply not_true_is_false.
          rewrite elemVarSet_unitVarSet.
          eapply elemVarSet_false_true; eassumption.
          admit.
        - rewrite Forall_forall in *.
          intros v HIn. specialize (IH1 v HIn). specialize (IH2 v HIn).
          assumption.
  Admitted.

  Lemma WellScopedVar_picked:
    forall vsis captured fvs,
    Forall (fun v => WellScopedVar v (extendVarSetList vsis captured))
           (snd (fold_right pick (fvs, []) captured)).
  Proof. intros. apply WellScopedVar_picked_aux. Qed.


  Lemma go_exit_all_WellScopedFloats captured e : 
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    disjointVarSet (exprFreeVars (toExpr e)) recursive_calls = true ->
    StateInvariant WellScopedFloats (go_exit captured (toExpr e) (exprFreeVars (toExpr e))).
  Proof.
    intros HWSe Hdisjoint.
    set (P := WellScopedFloats).
    cbv beta delta [go_exit]. (* No [zeta]! *)
    repeat float_let.

    (* First case *)
    enough (Hnext: StateInvariant P j_16__). {
      clearbody j_16__; cleardefs.
      destruct (collectArgs _) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Second case *)
    subst j_16__.
    enough (Hnext: StateInvariant P j_15__). {
      destruct (negb is_interesting) ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Third case *)
    subst j_15__.
    enough (Hnext: StateInvariant P j_14__). {
      destruct captures_join_points ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Third case: Actual exitification *)
    subst j_14__.
    unfold recursive_calls in Hdisjoint.
    apply StateInvariant_bind_return.
    apply addExit_all_WellScopedFloats.
    rewrite WellScoped_mkLams.
    subst abs_vars.
    float_let.
    cleardefs.

    rewrite Foldable.hs_coq_foldr_list.
    apply WellScoped_picked.

    (* [e] captures nothing in [fs] *)
    rewrite <- WellScoped_mkLams.
    rewrite <- WellScoped_mkLams in HWSe.
    unfold isvsp in HWSe.
    rewrite WellScoped_extendVarSetList_fresh in HWSe; only 1: assumption.
    rewrite hs_coq_map in Hdisjoint.
    rewrite map_map in Hdisjoint.
    rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in Hdisjoint
         by (intros; repeat expand_pairs; destruct a; reflexivity).
    fold fs in Hdisjoint.
    eapply disjointVarSet_subVarSet_l; only 1 : eassumption.
    replace captured with (rev (rev captured)).
    rewrite exprFreeVars_mkLams.
    apply subVarSet_delVarSetList.
    apply rev_involutive.
  Qed.

  Lemma go_all_WellScopedFloats captured e: 
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    StateInvariant WellScopedFloats (go captured (freeVars (toExpr e))).
  Proof.
    revert e captured.
    refine (go_ind (fun _ _ => _) _ _ _ _ _ _ _ ); intros.
    * apply go_exit_all_WellScopedFloats; assumption.
    * apply StateInvariant_bind_return.
      apply IHe.
    * apply StateInvariant_bind; only 1: apply IHrhs.
      intros. apply StateInvariant_bind_return. apply IHe.
    * apply StateInvariant_bind_return.
      apply IHe.
    * apply StateInvariant_bind.
      - apply StateInvariant_forM.
        intros [j params rhs] HIn.
        simpl.
        erewrite idJoinArity_join by eassumption.
        rewrite collectNAnnBndrs_freeVars_mkLams.
        apply StateInvariant_bind_return.
        apply (IHpairs _ _ _ _ HIn).
      - intro x.
        apply StateInvariant_bind_return.
        apply IHe.
    * (* Case [Case] *)
      simpl in *.
      apply StateInvariant_bind_return.
      apply StateInvariant_forM.
      intros [[dc pats] rhs] HIn.
      apply StateInvariant_bind_return.
      apply (IHalts _ _ _ HIn).
    * apply StateInvariant_return.
  Qed.

  (* Clearly we expect the input pairs be well-scoped *)
  Variable pairs_WS :
    Forall (fun p => WellScoped (snd p) isvsp) (map toJPair pairs) .

  Lemma all_exists_WellScoped:
    WellScopedFloats exits.
  Proof.
    unfold exits.
    unfold pairs'_exits.
    unfold ann_pairs.
    rewrite hs_coq_map.
    do 2 rewrite forM_map.
    eapply SP_snd_runState.
    * apply StateInvariant_forM.
      intros [v params rhs HisJoin] HIn.
      do 2 expand_pairs. simpl.
      erewrite idJoinArity_join by eassumption.
      rewrite collectNAnnBndrs_freeVars_mkLams.
      apply StateInvariant_bind_return.
      apply go_all_WellScopedFloats.
      + rewrite <- WellScoped_mkLams.
        rewrite Forall_map in pairs_WS.
        rewrite Forall_forall in pairs_WS.
        unfold in_scope2.
        apply (pairs_WS _ HIn).
    * repeat split; constructor.
  Qed.

  Definition sublistOf {a} (xs ys : list a) := incl ys xs.

  Lemma sublistOf_cons {a} x (xs ys : list a):
    sublistOf ys (x :: xs) <-> (In x ys /\ sublistOf ys xs).
  Proof.
    intros.
    unfold sublistOf, incl.
    intuition.
    destruct H; subst; auto.
  Qed.

  Lemma isvs_to_isvs':
     forall e, WellScoped e isvs -> WellScoped e isvs'.
  Proof.
    intros.
    apply WellScoped_extendVarSetList.
    rewrite disjointVarSet_mkVarSet.
    rewrite Forall_map. simpl.
    apply all_exists_WellScoped.
    assumption.
  Qed.

  Lemma isvsp_to_isvsp':
     forall e, WellScoped e isvsp -> WellScoped e isvsp'.
  Proof.
    intros.
    unfold isvsp, isvsp' in *.
    rewrite <- WellScoped_mkLams.
    rewrite <- WellScoped_mkLams in H.
    apply isvs_to_isvs'.
    assumption.
  Qed.

  Lemma isvsp_to_isvsp'_extended:
     forall e vs, WellScoped e (extendVarSetList isvsp vs) -> WellScoped e (extendVarSetList isvsp' vs).
  Proof.
    intros.
    rewrite <- WellScoped_mkLams.
    rewrite <- WellScoped_mkLams in H.
    apply isvsp_to_isvsp'.
    assumption.
  Qed.

  Lemma isvsp_to_isvsp'_extended_Var:
     forall v vs, WellScopedVar v (extendVarSetList isvsp vs) -> WellScopedVar v (extendVarSetList isvsp' vs).
  Proof.
    intros.
    change (WellScoped (Mk_Var v) (extendVarSetList isvsp' vs)).
    apply isvsp_to_isvsp'_extended.
    assumption.
  Qed.


  Lemma isvsp_to_isvsp'_extended2:
     forall e vs1 vs2,
     WellScoped e (extendVarSetList (extendVarSetList isvsp vs1) vs2) ->
     WellScoped e (extendVarSetList (extendVarSetList isvsp' vs1) vs2).
  Proof.
    intros.
    rewrite <- WellScoped_mkLams.
    rewrite <- WellScoped_mkLams in H.
    apply isvsp_to_isvsp'_extended.
    assumption.
  Qed.

  Lemma addExit_all_WellScopedVar:
    forall captured ja e,
    let after := extendVarSetList isvsp' captured in
    RevStateInvariant (sublistOf exits) 
         (addExit (extendInScopeSetList in_scope2 captured) ja e)
         (fun v => WellScopedVar v after).
  Proof.
    intros.
    (* This is much easier to prove by breaking the State abstraction and turning
       it into a simple function. *)
    unfold addExit, mkExitJoinId.
    unfold RevStateInvariant, SP,
           op_zgzgze__, return_, State.Monad__State, op_zgzgze____, return___,
           State.Monad__State_op_zgzgze__,
           State.Monad__State_return_,
           pure, State.Applicative__State , pure__,
           State.Applicative__State_pure,
           State.runState', State.get, State.put.
    simpl.
    intros floats Hfloats.
    set (v := uniqAway _ _) in *.
    apply sublistOf_cons in Hfloats.
    destruct Hfloats as [HIn HsublistOf].
    apply in_map with (f := fst) in HIn. simpl in HIn.
    split; only 1: assumption.
    subst after.
    apply WellScopedVar_extendVarSetList_l; only 1: apply WellScopedVar_extendVarSetList_l.
    * apply WellScopedVar_extendVarSetList_r; only 1: assumption.
      rewrite map_map.
      apply all_exists_WellScoped.
    * apply elemVarSet_uniqAway.
      unfold in_scope2.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      apply subVarSet_extendVarSetList_l.
      apply subVarSet_extendVarSetList_l.
      apply subVarSet_extendVarSetList_r.
      apply subVarSet_refl.
    * apply elemVarSet_uniqAway.
      unfold in_scope2.
      rewrite getInScopeVars_extendInScopeSet, !getInScopeVars_extendInScopeSetList.
      apply subVarSet_extendVarSet.
      apply subVarSet_extendVarSetList_l.
      apply subVarSet_extendVarSetList_r.
      apply subVarSet_refl.
  Qed.

  (* No we go through [go] again and see that pairs' is well-scoped.
     We start assuming that the result of the computation is a subset of exits'
     for which we already know [WellScopedFloats]. By going backwards,
     we will recover that [mkExit] produces a name of this set.
  *)

  Lemma go_exit_res_WellScoped captured e : 
    let orig := extendVarSetList isvsp captured in
    let after := extendVarSetList isvsp' captured in
    WellScoped (toExpr e) orig ->
    disjointVarSet (exprFreeVars (toExpr e)) recursive_calls = true ->
    RevStateInvariant (sublistOf exits) (go_exit captured (toExpr e) (exprFreeVars (toExpr e))) (fun e' => WellScoped e' after).
  Proof.
    intros ?? HWSe Hdisjoint.

    set (P := fun x => RevStateInvariant (sublistOf exits) x (fun e' => WellScoped e' after)).
    change (P (go_exit captured (toExpr e) (exprFreeVars (toExpr e)))).

    cbv beta delta [go_exit]. (* No [zeta]! *)
    repeat float_let.

    (* Common case *)
    assert (Hreturn : P (return_ (toExpr e))). {
       apply RevStateInvariant_return. cleardefs.
       apply isvsp_to_isvsp'_extended; assumption.
    } 

    (* First case *)
    enough (Hnext: P j_16__). {
      clearbody j_16__; cleardefs.
      destruct (collectArgs _) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply Hreturn.
    }
    cleardefs.

    (* Second case *)
    subst j_16__.
    enough (Hnext: P j_15__). {
      destruct (negb is_interesting) ; try apply Hnext.
      apply Hreturn.
    }
    cleardefs.

    (* Third case *)
    subst j_15__.
    enough (Hnext: P j_14__). {
      destruct (captures_join_points) ; try apply Hnext.
      apply Hreturn.
    }
    cleardefs.

    (* Third case: Actual exitification *)
    subst j_14__.
    subst P. cleardefs. 
    unfold recursive_calls in Hdisjoint.
    eapply RevStateInvariant_bind; only 1: apply addExit_all_WellScopedVar.
    intro v.
    apply RevStateInvariant_return.
    intro HWSv.
    apply WellScoped_mkVarApps; only 1 : apply HWSv.
    subst abs_vars.
    eapply Forall_impl.
    * intros v' HWSv'.
      apply isvsp_to_isvsp'_extended_Var.
      apply HWSv'.
    * subst zap0. fold zap. fold pick. simpl.
      rewrite Foldable.hs_coq_foldr_list.
      apply WellScopedVar_picked.
  Qed.

  Lemma go_res_WellScoped captured e: 
    let orig := extendVarSetList isvsp captured in
    let after := extendVarSetList isvsp' captured in
    WellScoped (toExpr e) orig ->
    RevStateInvariant (sublistOf exits) (go captured (freeVars (toExpr e))) (fun e' => WellScoped e' after).
  Proof.
    revert e captured.
    apply (go_ind (fun captured _ r => RevStateInvariant (sublistOf exits) r (fun e' => WellScoped e' (extendVarSetList isvsp' captured))));
      intros; set (after := extendVarSetList isvsp' captured).
    * apply go_exit_res_WellScoped; assumption.
    * eapply RevStateInvariant_bind.
      - apply IHe.
      - intro e'; apply RevStateInvariant_return; intro He'.
        rewrite  extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil in He'.
        simpl.
        rewrite deAnnotate_freeVars.
        split.
        ++ apply isvsp_to_isvsp'_extended. apply HWS.
        ++ apply He'.
    * unfold CoreBndr in *.
      eapply RevStateInvariant_bind; only 2: (intro body'; eapply RevStateInvariant_bind; only 2: intro hs').
      - apply IHrhs.
      - apply IHe.
      - apply RevStateInvariant_return; intros Hrhs' Hbody'.
        split.
        ** simpl.
           rewrite WellScoped_mkLams.
           rewrite extendVarSetList_append in Hbody'.
           apply Hbody'.
        ** rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil in Hrhs'.
           apply Hrhs'.
   *  eapply RevStateInvariant_bind; only 1: apply IHe.
      intro body'. apply RevStateInvariant_return; intros Hbody'.
      rewrite extendVarSetList_append in Hbody'.
      split; only 1: split.
      ++ rewrite !map_map.
         rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => varUnique x)
           by (intros; repeat expand_pairs; destruct a; reflexivity).
         apply HNoDup.
      ++ rewrite Forall'_Forall.
         rewrite !map_map. 
         rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x)
           by (intros; repeat expand_pairs; destruct a; reflexivity).
         rewrite Forall_map.
         eapply Forall_impl; only 2: apply HWSpairs.
         intros [v rhs] HWSv. simpl in *.
         rewrite deAnnotate_freeVars.
         apply isvsp_to_isvsp'_extended2; assumption.
      ++ rewrite bindersOf_Rec.
         rewrite !map_map.
         rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x)
            by (intros; repeat expand_pairs; destruct a; reflexivity).
         apply Hbody'.
     * eapply RevStateInvariant_bind.
       - apply RevStateInvariant_forM2 with
              (R := fun p p' =>
                  (fun '(Mk_NJPair x _ _ _) => x) p = fst p' /\
                  WellScoped (snd p') (extendVarSetList after (map (fun '(Mk_NJPair x _ _ _) => x) (Vector.to_list pairs'0)))).
         intros [j rhs] HIn.
         simpl.
         erewrite idJoinArity_join by eassumption.
         rewrite collectNAnnBndrs_freeVars_mkLams.
         eapply RevStateInvariant_bind.
         ++ apply (IHpairs _ _ _ _ HIn).
         ++ intro e'; apply RevStateInvariant_return; intro He'.
            simpl.
            rewrite WellScoped_mkLams.
            rewrite !extendVarSetList_append in He'.
            split; only 1: reflexivity.
            apply He'.
      - intro pairs''.
        eapply RevStateInvariant_bind; only 1: apply IHe.
        intro e'; apply RevStateInvariant_return; intros He' Hpairs''.
        apply Forall2_and in Hpairs''.
        destruct Hpairs'' as [Hfst Hpairs''].
        apply Forall2_const_Forall in Hpairs''.
        eapply Forall2_eq with (f := (fun '(Mk_NJPair x _ _ _) => x)) (g := fst) in Hfst.
        symmetry in Hfst.
        change ((@map (CoreBndr * Expr CoreBndr) CoreBndr (@fst CoreBndr (Expr CoreBndr)) pairs'') = map (fun '(Mk_NJPair x _ _ _) => x) (Vector.to_list pairs'0)) in Hfst.
        simpl.
        rewrite bindersOf_Rec_cleanup.
        rewrite Hfst.
        split; only 1: split.
        -- simpl in HNoDup.
           rewrite map_map.
           rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => varUnique x)
             by (intros; repeat expand_pairs; destruct a; reflexivity).
           apply HNoDup.
        -- rewrite Forall'_Forall.
           apply Hpairs''.
        -- rewrite !extendVarSetList_append in He'.
           apply He'.
      * (* [Case] *)
        simpl.
        eapply RevStateInvariant_bind.
        + apply RevStateInvariant_forM with (R := fun alt => WellScopedAlt v alt after).
          intros [[dc pats] rhs] HIn.
          eapply RevStateInvariant_bind.
          - apply (IHalts _ _ _  HIn).
          - intro e'; apply RevStateInvariant_return; intro He'.
            rewrite extendVarSetList_append in He'.
            apply He'.
        + intros alts'; apply RevStateInvariant_return; intro He.
          simpl. split.
          - rewrite deAnnotate_freeVars.
            apply isvsp_to_isvsp'_extended; assumption.
          - rewrite Forall'_Forall.
            apply He.
  * apply RevStateInvariant_return.
    apply isvsp_to_isvsp'_extended.
    assumption.
  Qed.

  Lemma pairs'_WS:
    Forall (fun p => WellScoped (snd p) isvsp') pairs'.
  Proof.
    unfold pairs', pairs'_exits, ann_pairs.
    eapply RevStateInvariant_runState with (P := sublistOf exits).
    * rewrite hs_coq_map, !map_map, forM_map.
      apply RevStateInvariant_forM.
      intros [v param rhs HisJoin] HIn.
      unfold id.
      simpl.
      erewrite idJoinArity_join by eassumption.
      rewrite collectNAnnBndrs_freeVars_mkLams.
      eapply RevStateInvariant_bind.
      ++ apply go_res_WellScoped.
         ** rewrite <- WellScoped_mkLams.
            rewrite Forall_map in pairs_WS.
            rewrite Forall_forall in pairs_WS.
            apply (pairs_WS _ HIn).
        ++ intro e'; apply RevStateInvariant_return; intro He'.
           simpl.
           rewrite WellScoped_mkLams.
           apply He'.
    * change (sublistOf exits exits).
      intro. auto.
  Qed.

  Lemma map_fst_pairs':
    map (@fst CoreBndr (Expr CoreBndr)) pairs' = fs.
  Proof.
    intros.
    unfold fs.
    unfold pairs', pairs'_exits, ann_pairs.
    unfold Traversable.forM, flip.
    unfold Traversable.mapM, Traversable.Traversable__list, Traversable.mapM__, Traversable.Traversable__list_mapM.
    unfold Traversable.Traversable__list_traverse.
    unfold liftA2, State.Applicative__State, liftA2__, State.Applicative__State_liftA2.
    unfold State.Applicative__State_op_zlztzg__.
    unfold State.runState.
    expand_pairs; simpl.
    unfold pure, pure__, State.Applicative__State_pure.
    unfold op_zgzgze__, State.Monad__State, op_zgzgze____,State.Monad__State_op_zgzgze__.
    unfold Bifunctor.second, Bifunctor.Bifunctor__pair_type, Bifunctor.second__,
           Bifunctor.Bifunctor__pair_type_second, Bifunctor.Bifunctor__pair_type_bimap.
    unfold id.
    generalize (@nil (prod JoinId CoreExpr)) as s.
    clear pairs_WS.
    induction pairs.
    * reflexivity.
    * intro.
      simpl. repeat (expand_pairs; simpl); destruct a; simpl.
      f_equal.
      apply IHl.
  Qed.

  (** Main well-scopedness theorem:
      If the input is well-scoped, then so is the output of [exitifyRec].*)
  Theorem exitifyRec_WellScoped:
    forall body,
    NoDup (map varUnique fs) ->
    WellScoped body isvsp ->
    WellScoped (mkLets (exitifyRec (extendInScopeSetList in_scope fs) (map toJPair pairs)) body) isvs.
  Proof.
    intros ? HNoDup HWSbody.
    cbv beta delta [exitifyRec].
    zeta_with go_exit.
    zeta_with recursive_calls.
    zeta_with go.
    zeta_with ann_pairs.
    fold pairs'_exits.
    expand_pairs.
    fold pairs'.
    fold exits.
    rewrite flat_map_unpack_cons_f.
    change (WellScoped (mkLets (map (fun '(x, y) => NonRec x y) exits ++ [Rec pairs']) body) isvs).
    rewrite mkLets_append, mkLets_cons, mkLets_nil.
    apply mkLets_WellScoped.
    * rewrite WellScoped_MkLet.
      simpl in *.
      rewrite bindersOf_Rec_cleanup.
      fold (@fst CoreBndr CoreExpr).
      rewrite map_fst_pairs'.
      repeat split.
      + assumption.
      + rewrite Forall'_Forall in *.
        apply pairs'_WS.
      + apply isvsp_to_isvsp'.
        assumption.
    * apply all_exists_WellScoped.
  Qed.

(* Join point stuff commented after updating Exitify.hs to GHC HEAD


  (** ** Join point validity *)

  (** When is the result of [mkExitLets] valid? *)
  
  Lemma mkExitLets_JPI:
    forall exits' e jps',
    isJoinPointsValid e 0 (updJPSs jps' (map fst exits')) = true ->
    forallb (fun '(v,rhs) => isJoinId v) exits' = true ->
    forallb (fun '(v,rhs) => isJoinPointsValidPair v rhs jps') exits' = true ->
    isJoinPointsValid (mkExitLets exits' e) 0 jps' = true.
  Proof.
    intros ??.
    induction exits' as [|[v rhs] exits']; intros jps' Hbase HiJI Hpairs.
    * simpl. unfold Base.id. assumption.
    * simpl in *; fold isJoinPointsValidPair in *.
      simpl_bool.
      destruct HiJI as [HiJIv HiJIvs].
      destruct Hpairs as [Hpair Hpairs].
      split.
      - assumption. 
      - apply IHexits'.
        + assumption.
        + assumption.
        + eapply forallb_imp. apply Hpairs.
          intros [v' rhs'].
          unfold updJPS. rewrite HiJIv.
          apply isJoinPointValidPair_extendVarSet.
  Qed.


  Lemma addExit_all_joinIds:
    forall in_scope_set ty ja e,
    StateInvariant (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)
                   (addExit in_scope_set ty ja e).
  Proof.
    set (P := (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)).
    intros.
    unfold addExit.
    eapply SP_bind with (R := fun v => isJoinId v = true).
    * unfold mkExitJoinId.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply SP_return.
        (* Here we actually show that we only generate join ids *)
        rewrite isJoinId_eq.
        rewrite isJoinId_maybe_uniqAway.
        rewrite isJoinId_maybe_setIdOccInfo.
        rewrite isJoinId_maybe_asJoinId.
        reflexivity.
    * intros x HiJI.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply StateInvariant_bind_return.
        apply SP_put.
        subst P.
        simpl; simpl_bool. split; assumption.
  Qed.

  Lemma go_all_joinIds:
    forall captured ann_e,
    StateInvariant (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)
                   (go captured ann_e).
  Proof.
    set (P := (fun xs => forallb (fun '(v0, _) => isJoinId v0) xs = true)).
    (* This cannot be structural recursion. Will need a size on expression. *)
    fix 2. rename go_all_joinIds into IH.
    intros.
    replace go with (go_f go) by admit. (* Need to use [go_eq] here *)
    cbv beta delta [go_f]. (* No [zeta]! *)
    (* Float out lets *)
    repeat float_let.

    (* First case *)
    enough (Hnext: StateInvariant P j_37__). {
      destruct (collectArgs e) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Second case *)
    subst j_37__.
    enough (Hnext: StateInvariant P j_36__). {
      destruct (is_exit && negb is_interesting) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Third case *)
    subst j_36__.
    enough (Hnext: StateInvariant P j_35__). {
      destruct (is_exit && captures_join_points ) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Third case: Actual exitification *)
    subst j_35__.
    enough (Hnext: StateInvariant P j_22__). {
      destruct is_exit ; try apply Hnext.
      apply StateInvariant_bind_return.
      apply addExit_all_joinIds.
    }
    clear is_exit isCapturedVarArg is_interesting captures_join_points args e fvs.

    (* Fourth case: No exitification here, so descend*)
    subst j_22__.
    enough (Hnext: StateInvariant P j_4__). {
      destruct ann_e as [fvs e] eqn:Hann.
      destruct e; try apply Hnext.
      * (* Case [Case] *)
        apply StateInvariant_bind_return.
        apply StateInvariant_forM.
        intros [[dc pats] rhs] HIn.
        apply StateInvariant_bind_return.
        apply IH.
      * (* Case Let *) 
        repeat float_let.

        enough (Hnext': StateInvariant P j_18__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          destruct (isJoinId_maybe j) as [join_arity|] eqn:HiJI; try apply Hnext'.
          destruct (collectNAnnBndrs join_arity rhs) as [params join_body].
          apply StateInvariant_bind.
          + apply IH.
          + intros. apply StateInvariant_bind_return.
            apply IH.
        }

        subst j_18__.
        enough (Hnext': StateInvariant P j_10__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          destruct (isJoinId (Tuple.fst (Panic.head pairs'))); try apply Hnext'.
          + intros.
            apply StateInvariant_bind.
            - apply StateInvariant_forM.
              intros [j rhs] HIn.
              repeat float_let.
              destruct (collectNAnnBndrs join_arity rhs) as [params join_body].
              apply StateInvariant_bind_return.
              apply IH.
            - intro x.
              apply StateInvariant_bind_return.
              apply IH.
        }

        subst j_10__.
        apply StateInvariant_bind_return.
        apply IH.
    }

    subst j_4__.
    apply StateInvariant_return.

  (* Not structurally recursive *)
  Fail Guarded.
  Admitted.

  Lemma all_exists_joinIds:
    forallb (fun '(v, _) => isJoinId v) exits = true.
  Proof.
    unfold exits.
    unfold pairs'_exits.
    eapply SP_snd_runState.
    * apply StateInvariant_forM.
      intros [v rhs] HIn.
      expand_pairs.
      apply StateInvariant_bind_return.
      apply go_all_joinIds.
    * reflexivity.
  Qed.

  (* TODO: There would be less repetition if we have a 
    [isJoinPointsValidJoinPair] that implies both 
    [isJoinPointsValidPair] and [isJoinId] *)
    
  Lemma isJoinPointsValid_delVarSet_nonJP:
    forall e jps n a,
    isJoinId a = false ->
    isJoinPointsValid e n (delVarSet jps a) = isJoinPointsValid e n jps.
  Admitted.
  Lemma isJoinPointsValid_delVarSetList_mono:
    forall e jps n vs,
    isJoinPointsValid e n (delVarSetList jps vs) = true -> isJoinPointsValid e n jps = true.
  Admitted.

  Lemma isJoinPointsValid_updJPSs_irrelevant:
    forall e jps n vs,
    forallb (fun v => negb (isJoinId v) || negb (elemVarSet v (exprFreeVars e))) vs = true ->
    isJoinPointsValid e n (updJPSs jps vs) = true ->
    isJoinPointsValid e n jps = true.
  Admitted.

  Lemma isJoinPointvalid_collectNBinders:
    forall v rhs jps ja args body,
    isJoinPointsValidPair v rhs jps = true ->
    isJoinId_maybe v = Some ja ->
    collectNBinders ja rhs = (args,body) ->
    isJoinPointsValid body 0 (updJPSs jps args) = true.
  Admitted.

  Lemma addExit_all_valid:
    forall in_scope_set jps ty ja args e,
    (* The RHS needs to be valid *)
    isJoinPointsValid e 0 jps = true -> 
    (* The join arity should match the number of lambdas added *)
    ja = (length args) ->
    (* No argument may be a join point *)
    forallb (fun a => negb (isJoinId a)) args = true ->

    StateInvariant (fun xs => forallb (fun '(v, rhs) => isJoinPointsValidPair v rhs jps) xs = true)
                   (addExit in_scope_set ty ja (mkLams args e)).
  Proof.
    clear jps.
    intros.
    set (P := (fun xs => forallb _ xs = true)).
    unfold addExit.
    eapply SP_bind with (R := fun v => isJoinId_maybe v = Some ja).
    * unfold mkExitJoinId.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply SP_return.
        (* Here we actually show that we only generate join ids *)
        rewrite isJoinId_maybe_uniqAway.
        rewrite isJoinId_maybe_setIdOccInfo.
        rewrite isJoinId_maybe_asJoinId.
        reflexivity.
    * intros x HiJI.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply StateInvariant_bind_return.
        apply SP_put.
        subst P.
        simpl; simpl_bool.
        split; only 2: assumption.
        unfold isJoinPointsValidPair, isJoinPointsValidPair_aux.
        rewrite HiJI.
        subst.
        (* Zoom past the Lams *)
        clear HPxs.
        clear HiJI.
        revert dependent jps.  clear jps.
        induction args; intros jps HiJPVe.
        + simpl. cbn. assumption.
        + replace ((length (a :: args))) with (1 + (length args)) by admit.
          destruct (Nat.eqb_spec (1 + (length args)) 0); only 1: lia.
          replace (mkLams (a :: args) e) with (Lam a (mkLams args e)) by reflexivity.
          cbn -[Nat.add].
          destruct (Nat.ltb_spec (1 + (length args)) 1); only 1: lia.
          replace (1 +  (length args) =? 1) with ((length args) =? 0) by admit.
          replace (1 +  (length args) - 1) with ( (length args)) by admit.
          simpl in H1. simpl_bool. destruct H1.
          apply IHargs.
          ** apply H1.
          ** rewrite negb_true_iff in H0.
             rewrite isJoinPointsValid_delVarSet_nonJP by assumption.
             assumption.
  Admitted.

  Lemma go_all_valid:
    forall captured ann_e,
    isJoinPointsValid (deAnnotate ann_e) 0 (updJPSs jps captured) = true ->
    StateInvariant (fun xs => forallb (fun '(v, rhs) => isJoinPointsValidPair v rhs jps) xs = true)
                   (go captured ann_e).
  Proof.
    set (P := (fun xs => forallb _ xs = true)).
    (* This cannot be structural recursion. Will need a size on expression. *)
    fix 2. rename go_all_valid into IH.
    intros ?? HiJPVe.
(*     rewrite go_eq. *)
    replace go with (go_f go) by admit. (* Need to use [go_eq] here *)
    cbv beta delta [go_f]. (* No [zeta]! *)
    (* Float out lets *)
    repeat float_let.

    (* First case *)
    enough (Hnext: StateInvariant P j_37__). {
      destruct (collectArgs e) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId s && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply StateInvariant_return.
    }
    cleardefs.

    (* Second case *)
    subst j_37__.
    enough (Hnext: StateInvariant P j_36__). {
      destruct (is_exit && negb is_interesting) ; try apply Hnext.
      apply StateInvariant_return.
    }

    (* Third case *)
    subst j_36__.
    enough (Hnext: (is_exit && captures_join_points = false) ->
                   StateInvariant P j_35__). {
      destruct (is_exit && captures_join_points).
      * apply StateInvariant_return.
      * apply Hnext. reflexivity.
    }
    intro Hno_capture.

    (* Third case: Actual exitification *)
    subst j_35__.
    enough (Hnext: StateInvariant P j_22__). {
      clearbody j_22__ j_4__.
      destruct is_exit ; try apply Hnext.
      apply StateInvariant_bind_return.
      assert (HniJIargs: forallb (fun a : Var => negb (isJoinId a)) args = true)
        by admit. (* Needs to relate [any] to [forallb] *)
      apply addExit_all_valid.
      * apply isJoinPointsValid_updJPSs_irrelevant with (vs := captured).
        + admit. (* Need lemma about [forallb] and [filter] *)
        + assumption.
      * admit. (* Need Base theory here *)
      * assumption.
    }
    clear is_exit is_interesting captures_join_points args e fvs Hno_capture.

    (* Fourth case: No exitification here, so descend*)
    subst j_22__.
    enough (Hnext: StateInvariant P j_4__). {
      destruct ann_e as [fvs e] eqn:Hann.
      destruct e; try apply Hnext.
      * (* Case [Case] *)
        apply StateInvariant_bind_return.
        apply StateInvariant_forM.
        intros [[dc pats] rhs] HIn.
        apply StateInvariant_bind_return.
        apply IH.
        (* This is boring stuff here... *)
        simpl in HiJPVe. simpl_bool. destruct HiJPVe.
        rewrite forallb_forall in H0.
        specialize (H0 (dc, pats, deAnnotate rhs)).
        simpl; rewrite updJPSs_append, updJPSs_cons.
        simpl_bool.
        apply H0.
        rewrite in_map_iff.
        exists (dc, pats, rhs). split. reflexivity. assumption.

      * (* Case Let *) 
        repeat float_let.

        enough (Hnext': StateInvariant P j_18__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          destruct (isJoinId_maybe j) as [join_arity|] eqn:HiJI; try apply Hnext'.
          destruct (collectNAnnBndrs _ _) as [params join_body] eqn:Hrhs.
          assert (collectNBinders join_arity (deAnnotate rhs) = (params, deAnnotate join_body)) by admit.
          apply StateInvariant_bind.
          + apply IH.
            (* Boring stuff *)
            simpl in HiJPVe. simpl_bool. destruct HiJPVe.
            rewrite updJPSs_append.
            eapply isJoinPointvalid_collectNBinders; try eassumption.
          + intros. apply StateInvariant_bind_return.
            apply IH.
            simpl in HiJPVe. simpl_bool. destruct HiJPVe.
            rewrite updJPSs_append, updJPSs_cons, updJPSs_nil.
            apply H1.
        }

        subst j_18__.
        enough (Hnext': StateInvariant P j_10__). {
          destruct a as [j rhs|pairs']; try apply Hnext'.
          simpl deAnnotate in HiJPVe.
          replace (flat_map _ _) with (map (fun '(v,e) => (v, deAnnotate e)) pairs') in HiJPVe by admit.
          simpl in HiJPVe. simpl_bool. destruct HiJPVe. destruct H. destruct H0.
          rewrite orb_true_iff in H1.
          destruct H1.
          + (* No join ids *)
            replace (isJoinId (Tuple.fst _)) with false.
            assumption.
            symmetry.
            destruct pairs' as [|[j rhs] pairs'']; try inversion H.
            simpl in H1. simpl_bool. destruct H1. rewrite negb_true_iff in H1. simpl in H1.
            admit. (* Need to unfold Panic.head *)
          + (* All join ids *)
            replace (isJoinId (Tuple.fst _)) with true by admit. (* like above *)

            rewrite forallb_forall in H0.
            rewrite forallb_forall in H1.
            rewrite !map_map in *.
            replace (map _ _) with (map fst pairs') in H0
                  by (apply map_ext; intro; destruct a; reflexivity).
            replace (map _ _) with (map fst pairs') in H2
                  by (apply map_ext; intro; destruct a; reflexivity).

            apply StateInvariant_bind.
            - apply StateInvariant_forM.
              intros [j rhs] HIn.
              repeat float_let.
              destruct (collectNAnnBndrs join_arity rhs) as [params join_body] eqn:Hrhs.
              assert (collectNBinders join_arity (deAnnotate rhs) = (params, deAnnotate join_body)) by admit.
              apply StateInvariant_bind_return.
              apply IH.
              rewrite !updJPSs_append.
              eapply isJoinPointvalid_collectNBinders.
              ** Fail apply H0. (* ugh *)
                 specialize (H0 (j, deAnnotate rhs)).
                 simpl in H0.
                 apply H0.
                 apply in_map_iff. eexists. split; [|eassumption]. reflexivity.
              ** apply isJoinId_isJoinId_maybe.
                 specialize (H1 (j, deAnnotate rhs)). simpl in H1.
                 apply H1.
                 apply in_map_iff. eexists. split; [|eassumption]. reflexivity.
              ** apply H3.
            - intro x.
              apply StateInvariant_bind_return.
              apply IH.
              rewrite updJPSs_append.
              apply H2.
        }

        subst j_10__.
        apply StateInvariant_bind_return.
        apply IH.
        rewrite updJPSs_append.
        simpl (deAnnotate _) in HiJPVe.
        admit. (* We need to again look at both cases of Rec and NonRec,
                  deal with deAnnotate, to get to the statement about the base case.
                  (Or refactor isJoinPointsValid to not require that) *)
    }

    subst j_4__.
    apply StateInvariant_return.

  (* Not structurally recursive *)
  Fail Guarded.
  Admitted.

  Lemma all_exists_valid:
    forallb (fun '(v, rhs) => isJoinPointsValidPair v rhs jps) exits = true.
  Proof.
    unfold exits.
    unfold pairs'_exits.
    eapply SP_snd_runState.
    * apply StateInvariant_forM.
      intros [v rhs] HIn.
      expand_pairs.
      apply StateInvariant_bind_return.
      apply go_all_valid.
      eapply isJoinPointvalid_collectNBinders.
      + admit. (* Need to thread in invariant here *)
      + admit. (* Yeah, we really should also show that these are join ids here *)
      + admit. (* Lemma bout collectNBinders and collectNAnnBndrs. @lastland? *)
    * reflexivity.
  Admitted.

  (** Main result *)

  Theorem exitifyRec_JPI:
    forall body,
    pairs <> [] ->
    isJoinPointsValid (Let (Rec (map toJPair pairs)) body) 0 jps = true ->
    isJoinPointsValid (exitifyRec (extendInScopeSetList in_scope (map (fun '(Mk_NJPair v _ _ _) => v) pairs)) (map toJPair pairs) body) 0 jps = true.
  Proof.
    intros.
    cbv beta delta [exitifyRec].
    cbv zeta.
    fold recursive_calls.
    fold go.
    fold ann_pairs.
    fold pairs'_exits.
    fold mkExitLets.
    expand_pairs.
    fold pairs'.
    fold exits.
    change (isJoinPointsValid (mkExitLets exits (mkLetRec pairs' body)) 0 jps = true).
    apply mkExitLets_JPI.
    * admit.
    * apply all_exists_joinIds.
    * apply all_exists_valid.
  Admitted.
*)

End in_exitifyRec.

Definition top_go := ltac:(
  let rhs := eval cbv beta delta [exitifyProgram] in (exitifyProgram []) in
  lazymatch rhs with | (let x := ?rhs in ?body) => 
    exact rhs
  end).


(* This is incomplete; need to nail down connection between
  [in_scope] and [isvs].
*)
Theorem top_go_WellScoped:
  forall e in_scope isvs,
  WellScoped e isvs->
  WellScoped (top_go in_scope e) isvs.
Admitted.

Theorem exitifyProgram_WellScoped:
  forall pgm isvs,
  WellScopedProgram pgm isvs->
  WellScopedProgram (exitifyProgram pgm) isvs.
Proof.
  intros.
  cbv beta delta [exitifyProgram].
  fold top_go.
  zeta_one.
  do 2 float_let.

  assert (HbindersOf: forall a, bindersOf (goTopLvl a) = bindersOf a). admit.
  
  clearbody in_scope_toplvl.
  rewrite hs_coq_map.
  revert isvs0 H.
  induction pgm; intros.
  * constructor.
  * destruct H as [HWSbind HWSpgm].
    split.
    + destruct a; simpl.
      - apply top_go_WellScoped. apply HWSbind.
      - destruct HWSbind as [HNoDup Hpairs].
        split.
        ** rewrite hs_coq_map.
           rewrite !map_map.
           rewrite map_ext with (g := fun '(x, rhs) => varUnique x)
              by (intros; repeat expand_pairs; destruct a; reflexivity).
           rewrite map_map in HNoDup.
           rewrite map_ext with (g := fun '(x, rhs) => varUnique x) in HNoDup
              by (intros; repeat expand_pairs; destruct a; reflexivity).
           apply HNoDup.
        ** rewrite Forall'_Forall in *.
           rewrite Forall_map in *.
           eapply Forall_impl; only 2: apply Hpairs.
           intros [v rhs] HWSrhs.
           simpl in *.
           apply top_go_WellScoped.
           rewrite !map_map.
           rewrite map_ext with (g := fun '(x, rhs) =>  x)
              by (intros; repeat expand_pairs; destruct a; reflexivity).
           apply HWSrhs.
    + apply IHpgm.
      rewrite HbindersOf.
      apply HWSpgm.
Admitted.
