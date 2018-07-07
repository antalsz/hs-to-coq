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
Require Import Coq.Program.Equality. (* for dependent destruction *)
 
Require Import Coq.Logic.FunctionalExtensionality.

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
Require Import Proofs.NCoreExists.
Require Import Proofs.VectorUtils.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.Unique.

Set Bullet Behavior "Strict Subproofs".


Close Scope Z_scope.


(* This section reflects the context of the local definition of exitifyRec *)
Section in_exitifyRec.

  Set Default Proof Using "Type".

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

  (* The let-scope, before *)
  Definition jpsp := updJPSs jps fs .
  (* The outermost scope, including exits *)
  Definition jps' := updJPSs jps (map fst exits).
  (* The let-scope, after *)
  Definition jpsp' := updJPSs jps' fs.

  Variable jps_subset_isvs:
    subVarSet jps isvs = true.


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
                simpl in HWS.
                rewrite WellScoped_mkLams in HWS.
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
          1:{
            exfalso.
            rewrite <- not_false_iff_true in Heq_isJoinId.
            contradict Heq_isJoinId.
            dependent inversion pairs'; subst; clear.
            dependent inversion h. simpl.
            rewrite isJoinId_eq. rewrite HnotJoin. reflexivity.
          }
          clear Heq_isJoinId.

          clear IH1 IH2 IH3.

          (* Destruct well-scopedness assumption *)
          destruct HWS as [[HGLV [HNoDup HWSpairs]] HWSe].
          simpl toBind in HWSe.
          rewrite to_list_map in HGLV.
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
          revert n pairs' e captured HGLV HNoDup HWSpairs HWSe IHe.
          refine IH4.
        + clear IH1 IH2 IH3 IH4.

          expand_pairs. simpl.
          rewrite to_list_map.
          rewrite !zip_unzip_map.
          rewrite !map_map.
          rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x)
             by (intros; repeat expand_pairs; destruct a; reflexivity).

          destruct (isJoinId _) eqn:Heq_isJoinId.
          2:{
            exfalso.
            rewrite <- not_true_iff_false in Heq_isJoinId.
            contradict Heq_isJoinId.
            dependent inversion pairs'; subst; clear.
            dependent inversion h. simpl.
            rewrite isJoinId_eq. rewrite HisJoin. reflexivity.
          }
          clear Heq_isJoinId.

          (* Destruct well-scopedness assumption *)
          destruct HWS as [[HGLV [HNoDup HWSpairs]] HWSe].
          simpl toBind in HWSe.
          rewrite bindersOf_Rec in HWSe.
          rewrite to_list_map in HGLV.
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
          clear IH. revert n pairs' e captured HGLV HNoDup HWSpairs HWSe IHpairs IHe.
          refine IH5.
      * (* Case [Case] *)
        clear IH1 IH2 IH3 IH4 IH5.
        simpl in *.

        do 2 expand_pairs. simpl.
        rewrite snd_unzip, !map_map.
        rewrite forM_map.

        destruct HWS as [HWSscrut [HGLVv HWSalts]].
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
        revert e v alts captured HWSscrut HGLVv HWSalts IHalts.
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
    Forall (fun 'p => WellScoped (snd p) isvs) floats /\
    (* All are good local variables *)
    Forall (fun 'p => GoodLocalVar (fst p)) floats.

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
    clear in_scope pairs jps jps_subset_isvs.
    induction exits' as [|[v rhs] exits']; intros isvs' e Hbase Hfloats.
    * simpl. unfold Base.id. assumption.
    * simpl in *.
      rewrite extendVarSetList_cons, extendVarSetList_nil.
      destruct Hfloats as [Hfreshs [HNoDup [Hrhss HGLVs]]].
      inversion HNoDup; subst; clear HNoDup. rename H1 into Hfresh, H2 into HNoDup.
      inversion_clear Hrhss. rename H into Hrhs, H0 into Hrhss.
      inversion_clear Hfreshs. rename H into Hfresh_v, H0 into Hfreshs.
      inversion_clear HGLVs. rename H into HGLVv, H0 into HGLSVs.
      simpl in *.
      rewrite extendVarSetList_cons in Hbase.
      split; [split|]; [apply HGLVv | apply Hrhs |].
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
             unfold GHC.Base.op_zeze__, Core.Eq___Var, op_zeze____, 
             Core.Eq___Var_op_zeze__ .
             unfold GHC.Base.op_zeze__, Core.Eq___Var, op_zeze____,
             Nat.Eq_nat.
             
             apply not_true_is_false. intro h.
             apply beq_nat_true in h.

             contradict Hfresh.
             exists (v', rhs'). split. simpl. 
             unfold varUnique. rewrite h. auto.
             assumption.
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
        + assumption.
  Qed.

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
    constructor; only 2: constructor; only 3: constructor; simpl.
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
    * constructor; only 2: apply Hfloats; simpl.
      apply GoodLocalVar_uniqAway.
      apply GoodLocalVar_asJoinid.
      apply GoodLocalVar_mkSysLocal.
      apply isLocalUnique_initExitJoinUnique.
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

  Lemma Forall2_symmetric:
    forall {a} (P : a -> a -> Prop) xs,
    (forall x, P x x) -> Forall2 P xs xs.
  Proof.
    intros.
    induction xs.
    * constructor.
    * constructor; auto.
  Qed.

  Lemma Forall2_impl_Forall_r:
    forall {a b} (P : a -> b -> Prop) (Q : b -> Prop)  xs ys,
    Forall2 P xs ys ->
    (forall x y, P x y -> Q y) ->
    Forall Q ys.
  Proof.
    intros.
    induction H.
    * constructor.
    * constructor; intuition.
      eapply H0; eassumption.
  Qed.
 
  Lemma WellScoped_picked_aux:
    forall fvs captured e vs,
    WellScoped e (extendVarSetList fvs (captured ++ vs)) ->
    WellScoped e (extendVarSetList fvs (snd (fold_right pick (delVarSetList (exprFreeVars e) vs, []) captured) ++ vs)).
  Proof.
    intros.
    revert vs H.
    induction captured using rev_ind; intros vs HWSe; simpl.
    * simpl. assumption.
    * rewrite fold_right_app.
      simpl.
      destruct_match; simpl.
      + rewrite snd_pick_list.
        rewrite <- app_assoc.
        erewrite delVarSet_ae by apply zap_ae.
        rewrite <- delVarSetList_cons2.
        apply IHcaptured.
        rewrite app_assoc.
        rewrite WellScoped_extendVarSetList_ae; only 1: apply HWSe.
        repeat apply Forall2_app.
        - apply Forall2_symmetric. intro. apply almostEqual_refl.
        - constructor. apply almostEqual_sym. apply zap_ae. constructor.
        - apply Forall2_symmetric. intro. apply almostEqual_refl.
      + apply IHcaptured.
        rewrite <- WellScoped_extendVarSetList_fresh_between.
        apply HWSe.
        apply disjointVarSet_mkVarSet.
        constructor; only 2: constructor.
        assumption.
  Qed.

  Lemma WellScoped_picked:
    forall fvs captured e,
    WellScoped e (extendVarSetList fvs captured) ->
    WellScoped e (extendVarSetList fvs (snd (fold_right pick (exprFreeVars e, []) captured))).
  Proof.
    intros.
    pose proof (WellScoped_picked_aux fvs captured e []).
    rewrite !app_nil_r in *.
    rewrite delVarSetList_nil in *.
    auto.
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
          apply elemVarSet_exprFreeVars_Var_false.
          rewrite elemVarSet_delVarSet in *.
          intuition.
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
          apply elemVarSet_exprFreeVars_Var_false.
          eapply elemVarSet_false_true; eassumption.
        - rewrite Forall_forall in *.
          intros v HIn. specialize (IH1 v HIn). specialize (IH2 v HIn).
          assumption.
  Qed.

  Lemma WellScopedVar_picked:
    forall vsis captured fvs,
    Forall (fun v => WellScopedVar v (extendVarSetList vsis captured))
           (snd (fold_right pick (fvs, []) captured)).
  Proof. intros. apply WellScopedVar_picked_aux. Qed.

  Lemma Forall_picked:
    forall P captured fvs,
    Forall (fun x => P (zap x)) captured ->
    Forall P (snd (fold_right pick (fvs, []) captured)).
  Proof.
    intros.
    induction H.
    * constructor.
    * simpl. unfold pick.
      expand_pairs.
      destruct_match. clear Heq.
      - constructor.
        ** apply H.
        ** apply IHForall.
      - apply IHForall.
  Qed.

  Lemma go_exit_all_WellScopedFloats captured e : 
    Forall GoodLocalVar captured ->
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    disjointVarSet (exprFreeVars (toExpr e)) recursive_calls = true ->
    StateInvariant WellScopedFloats (go_exit captured (toExpr e) (exprFreeVars (toExpr e))).
  Proof.
    intros HGLV HWSe Hdisjoint.
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
    repeat float_let.
    replace pick0 with pick by reflexivity.
    replace pick1 with pick by reflexivity.
    cleardefs.
    rewrite Foldable.hs_coq_foldr_list.
    split.
    * apply Forall_picked.
      eapply Forall_impl; only 2: eapply HGLV.
      intros v HGLVv.
      eapply GoodLocalVar_almostEqual. apply HGLVv.
      apply zap_ae.

    * apply WellScoped_picked.
      rewrite hs_coq_map in Hdisjoint.
      rewrite map_map in Hdisjoint.
      rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in Hdisjoint
           by (intros; repeat expand_pairs; destruct a; reflexivity).
      fold fs in Hdisjoint.

      unfold isvsp in HWSe.
      rewrite WellScoped_extendVarSetList_fresh_under in HWSe; auto.
  Qed.

  Lemma go_all_WellScopedFloats captured e: 
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    Forall GoodLocalVar captured ->
    StateInvariant WellScopedFloats (go captured (freeVars (toExpr e))).
  Proof.
    revert e captured.
    refine (go_ind (fun captured _ r => impl (Forall GoodLocalVar captured) (_ r)) _ _ _ _ _ _ _);
      intros; intro HGLVcaptured.
    * apply go_exit_all_WellScopedFloats; assumption.
    * apply StateInvariant_bind_return.
      apply IHe.
      -- apply Forall_app; only 1: apply HGLVcaptured.
         constructor; only 2: constructor.
         apply HWS.
    * apply StateInvariant_bind; only 1: apply IHrhs.
      -- apply Forall_app; only 1: apply HGLVcaptured.
         simpl in HWS.
         rewrite WellScoped_mkLams in HWS.
         apply HWS.
      -- intros. apply StateInvariant_bind_return.
         apply IHe.
         ++ apply Forall_app; only 1: apply HGLVcaptured.
            constructor; only 2: constructor.
            apply HWS.
    * apply StateInvariant_bind_return.
      apply IHe.
      -- apply Forall_app; only 1: apply HGLVcaptured.
         rewrite Forall_map.
         rewrite Forall_map in HGLV.
         eapply Forall_impl; only 2: apply HGLV.
         intros [???] H. apply H.
    * apply StateInvariant_bind.
      - apply StateInvariant_forM.
        intros [j params rhs] HIn.
        simpl.
        erewrite idJoinArity_join by eassumption.
        rewrite collectNAnnBndrs_freeVars_mkLams.
        apply StateInvariant_bind_return.
        apply (IHpairs _ _ _ _ HIn).
        -- apply Forall_app; only 1: apply HGLVcaptured.
           apply Forall_app.
           ++ rewrite Forall_map.
              rewrite Forall_map in HGLV.
              eapply Forall_impl; only 2: apply HGLV.
              intros [???] H. apply H.
           ++ specialize (HWSpairs _ HIn).
              simpl in HWSpairs.
              rewrite WellScoped_mkLams in HWSpairs.
              apply HWSpairs.
      - intro x.
        apply StateInvariant_bind_return.
        apply IHe.
        ++ apply Forall_app; only 1: apply HGLVcaptured.
           rewrite Forall_map.
           rewrite Forall_map in HGLV.
           eapply Forall_impl; only 2: apply HGLV.
           intros [???] H. apply H.
    * (* Case [Case] *)
      simpl in *.
      apply StateInvariant_bind_return.
      apply StateInvariant_forM.
      intros [[dc pats] rhs] HIn.
      apply StateInvariant_bind_return.
      apply (IHalts _ _ _ HIn).
      ++ apply Forall_app; only 1: apply HGLVcaptured.
         constructor.
         -- apply HGLVv.
         -- apply (HWSalts _ HIn).
    * apply StateInvariant_return.
  Qed.

  (* Clearly we expect the input pairs be well-scoped *)
  Variable pairs_WS :
    Forall (fun p => WellScoped (snd p) isvsp) (map toJPair pairs) .
  Variable pairs_GLV:
    Forall (fun p : Var * Expr CoreBndr => GoodLocalVar (fst p)) (map toJPair pairs).
  Variable pairs_VJPP:
    Forall (fun p : Var * Expr CoreBndr => isValidJoinPointsPair (fst p) (snd p) jpsp = true) (map toJPair pairs).


  Lemma all_exits_WellScoped:
    WellScopedFloats exits.
  Proof using Type pairs_WS.
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
      rewrite Forall_map in pairs_WS.
      rewrite Forall_forall in pairs_WS.
      specialize (pairs_WS _ HIn).
      simpl in pairs_WS.
      rewrite WellScoped_mkLams in pairs_WS.
      apply go_all_WellScopedFloats; apply pairs_WS.
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

  Lemma disjoint_isvs_exits:
     disjointVarSet isvs (mkVarSet (map fst exits)) = true.
  Proof using Type pairs_WS.
    rewrite disjointVarSet_mkVarSet.
    rewrite Forall_map. simpl.
    apply all_exits_WellScoped.
  Qed.

  Lemma isvs_to_isvs':
     StrongSubset isvs isvs'.
  Proof using Type pairs_WS.
    intros.
    apply StrongSubset_extendList_fresh.
    apply disjoint_isvs_exits.
  Qed.

  Lemma isvsp_to_isvsp':
     StrongSubset isvsp isvsp'.
  Proof using Type pairs_WS.
    intros.
    apply StrongSubset_extendVarSetList.
    apply isvs_to_isvs'.
  Qed.

  Lemma isvsp_to_isvsp'_extended:
     forall vs, StrongSubset (extendVarSetList isvsp vs) (extendVarSetList isvsp' vs).
  Proof using Type pairs_WS.
    intros.
    apply StrongSubset_extendVarSetList.
    apply isvsp_to_isvsp'.
  Qed.

  Lemma isvsp_to_isvsp'_extended2:
     forall vs1 vs2,
     StrongSubset (extendVarSetList (extendVarSetList isvsp vs1) vs2)
                  (extendVarSetList (extendVarSetList isvsp' vs1) vs2).
  Proof using Type pairs_WS.
    intros.
    apply StrongSubset_extendVarSetList.
    apply isvsp_to_isvsp'_extended.
  Qed.

  Lemma addExit_all_WellScopedVar:
    forall captured ja e,
    let after := extendVarSetList isvsp' captured in
    RevStateInvariant (sublistOf exits) 
         (addExit (extendInScopeSetList in_scope2 captured) ja e)
         (fun v => WellScopedVar v after).
  Proof using Type pairs_WS.
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
      apply all_exits_WellScoped.
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
  Proof using Type pairs_WS.
    intros ?? HWSe Hdisjoint.

    set (P := fun x => RevStateInvariant (sublistOf exits) x (fun e' => WellScoped e' after)).
    change (P (go_exit captured (toExpr e) (exprFreeVars (toExpr e)))).

    cbv beta delta [go_exit]. (* No [zeta]! *)
    repeat float_let.

    (* Common case *)
    assert (Hreturn : P (return_ (toExpr e))). {
       apply RevStateInvariant_return. cleardefs.
       apply (weaken (isvsp_to_isvsp'_extended _)).
       assumption.
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
      apply (weaken (isvsp_to_isvsp'_extended _)).
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
  Proof using Type pairs_WS.
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
        split; only 1: split.
        ++ apply HWS.
        ++ apply (weaken (isvsp_to_isvsp'_extended _)). apply HWS.
        ++ apply He'.
    * unfold CoreBndr in *.
      eapply RevStateInvariant_bind; only 2: (intro body'; eapply RevStateInvariant_bind; only 2: intro hs').
      - apply IHrhs.
      - apply IHe.
      - apply RevStateInvariant_return; intros Hrhs' Hbody'.
        split; only 1: split.
        ** apply HWS.
        ** simpl.
           rewrite WellScoped_mkLams.
           split.
           -- simpl in HWS.
              rewrite WellScoped_mkLams in HWS.
              apply HWS.
           -- rewrite extendVarSetList_append in Hbody'.
              apply Hbody'.
        ** rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil in Hrhs'.
           apply Hrhs'.
   *  eapply RevStateInvariant_bind; only 1: apply IHe.
      intro body'. apply RevStateInvariant_return; intros Hbody'.
      rewrite extendVarSetList_append in Hbody'.
      split; only 1: split; only 2: split.
      ++ rewrite Forall_map.
         rewrite Forall_map in HGLV.
         eapply Forall_impl; only 2: apply HGLV.
         intros [???] H. assumption.
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
         apply (weaken (isvsp_to_isvsp'_extended2 _ _)); assumption.
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
         intros [j params rhs] HIn.
         simpl.
         erewrite idJoinArity_join by eassumption.
         rewrite collectNAnnBndrs_freeVars_mkLams.
         eapply RevStateInvariant_bind.
         ++ apply (IHpairs _ _ _ _ HIn).
         ++ intro e'; apply RevStateInvariant_return; intro He'.
            simpl.
            rewrite WellScoped_mkLams.
            rewrite !extendVarSetList_append in He'.
            split; only 2: split.
            -- reflexivity.
            -- specialize (HWSpairs _ HIn).
               simpl in HWSpairs.
               rewrite WellScoped_mkLams in HWSpairs.
               apply HWSpairs.
            -- apply He'.
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
        repeat apply conj.
        -- rewrite <- Forall_map.
           rewrite <- Forall_map in HGLV.
           unfold CoreBndr in *.
           rewrite Hfst.
           rewrite Forall_map.
           rewrite map_map in HGLV.
           rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in HGLV
             by (intros; repeat expand_pairs; destruct a; reflexivity).
           rewrite Forall_map in HGLV.
           apply HGLV.
        -- clear IHpairs IHe He'.
           simpl in HNoDup.
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
            split.
            -- apply (HWSalts _ HIn).
            -- apply He'.
        + intros alts'; apply RevStateInvariant_return; intro He.
          simpl. split; only 2: split.
          - rewrite deAnnotate_freeVars.
            apply (weaken (isvsp_to_isvsp'_extended _)); assumption.
          - apply HGLVv.
          - rewrite Forall'_Forall.
            apply He.
  * apply RevStateInvariant_return.
    apply (weaken (isvsp_to_isvsp'_extended _)).
    assumption.
  Qed.

  Lemma pairs'_WS:
    Forall (fun p => WellScoped (snd p) isvsp') pairs'.
  Proof using Type pairs_WS.
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
         ** apply WellScoped_mkLams.
            rewrite Forall_map in pairs_WS.
            rewrite Forall_forall in pairs_WS.
            apply (pairs_WS _ HIn).
        ++ intro e'; apply RevStateInvariant_return; intro He'.
           simpl.
           rewrite WellScoped_mkLams.
           split.
           -- rewrite Forall_map in pairs_WS.
              rewrite Forall_forall in pairs_WS.
              specialize (pairs_WS _ HIn).
              simpl in pairs_WS.
              rewrite WellScoped_mkLams in pairs_WS.
              apply pairs_WS.
           -- apply He'.
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
    clear pairs_WS pairs_GLV pairs_VJPP.
    induction pairs.
    * reflexivity.
    * intro.
      simpl. repeat (expand_pairs; simpl); destruct a; simpl.
      f_equal.
      apply IHl.
  Qed.

  Lemma map_fst_pairs'':
    map (@fst Var (Expr CoreBndr)) pairs' = fs.
  Proof. exact map_fst_pairs'. Qed.

  (** Main well-scopedness theorem:
      If the input is well-scoped, then so is the output of [exitifyRec].*)
  Theorem exitifyRec_WellScoped:
    forall body,
    NoDup (map varUnique fs) ->
    WellScoped body isvsp ->
    WellScoped (mkLets (exitifyRec (extendInScopeSetList in_scope fs) (map toJPair pairs)) body) isvs.
  Proof using Type pairs_GLV pairs_WS.
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
      rewrite <- Forall_map.
      rewrite map_fst_pairs'.
      rewrite map_fst_pairs''.
      repeat apply conj.
      + rewrite <- Forall_map in pairs_GLV.
        rewrite map_map in pairs_GLV.
        rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in pairs_GLV
                     by (intros; repeat expand_pairs; destruct a; reflexivity).
        apply pairs_GLV.
      + assumption.
      + rewrite Forall'_Forall in *.
        apply pairs'_WS.
      + apply (weaken isvsp_to_isvsp').
        assumption.
    * apply all_exits_WellScoped.
  Qed.

  (** ** Join point validity *)


  (** When is the result of [mkExitLets] valid? *)
  
  Lemma mkLets_JPI:
    forall floats e jps',
    (* All added bindings are fresh with regard to the environment *)
    disjointVarSet jps' (mkVarSet (map fst floats)) = true ->
    (* The body is valid in the extended environment *)
    isJoinPointsValid e 0 (updJPSs jps' (map fst floats)) = true ->
    (* Each thing is valid in its environment *)
    forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps') floats = true ->
    isJoinPointsValid (mkLets (map (fun '(v,rhs) => NonRec v rhs) floats) e) 0 jps' = true.
  Proof.
    intros ???.
    revert e.
    induction floats as [|[v rhs] floats] using rev_ind; intros jps' Hdisjoint Hbase Hpairs.
    * simpl. unfold Base.id. assumption.
    * simpl in *; fold isJoinPointsValidPair in *.
      rewrite forallb_app in Hpairs.
      rewrite map_append, disjointVarSet_mkVarSet_append in Hdisjoint.
      simpl_bool.
      destruct Hpairs as [Hpairs Hpair].
      destruct Hdisjoint as [Hdisjoint _].
      simpl in Hpair. rewrite andb_true_r in Hpair.
      rewrite map_append, mkLets_append. simpl.
      rewrite mkLets_cons, mkLets_nil.
      apply IHfloats.
      - apply Hdisjoint.
      - simpl. fold isJoinPointsValidPair.
        simpl_bool. split.
        + apply isValidJoinPointsPair_isJoinPointsValidPair.
          refine (weakenb (StrongSubset_updJPSs_fresh _ _ _) _).
          -- apply Hdisjoint.
          -- assumption.
        + rewrite map_append in Hbase. simpl in Hbase.
          rewrite updJPSs_append, updJPSs_cons, updJPSs_nil in Hbase. 
          apply Hbase.
      - assumption.
  Qed.

  Lemma addExit_all_joinIds:
    forall jps' captured ja e,
    isJoinRHS e ja jps' = true ->
    StateInvariant (fun xs => forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps') xs = true)
                   (addExit (extendInScopeSetList in_scope2 captured) ja e).
  Proof.
    intros jps'.
    set (P := (fun xs => forallb (fun '(v, rhs) => isValidJoinPointsPair v rhs jps') xs = true)).
    intros.
    unfold addExit.
    eapply SP_bind with (R := fun v => isJoinId_maybe v = Some ja).
    * unfold mkExitJoinId.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply SP_return.
        (* Here we actually show that we only generate join ids *)
        rewrite isJoinId_maybe_uniqAway.
        rewrite isJoinId_maybe_asJoinId.
        reflexivity.
    * intros x HiJI.
      eapply SP_bind.
      - apply SP_get.
      - intros xs HPxs.
        apply StateInvariant_bind_return.
        apply SP_put.
        subst P.
        simpl; simpl_bool. split.
        + unfold isValidJoinPointsPair.
          rewrite HiJI.
          assumption.
        + assumption.
  Qed.

  Lemma isJoinPointsValid_picked_aux:
    forall jps captured e vs,
    isJoinPointsValid e 0 (updJPSs jps (captured ++ vs)) = true ->
    let abs_vars := snd (fold_right pick (delVarSetList (exprFreeVars e) vs, []) captured) in
    forallb (fun x : Var => negb (isJoinId x)) abs_vars = true ->
    isJoinPointsValid e 0 (updJPSs (delVarSetList jps abs_vars) vs) = true.
  Proof.
    intros.
    revert vs abs_vars H H0.
    induction captured using rev_ind; intros vs abs_vars HIJPVe HnotJoinId; simpl.
    * subst abs_vars. simpl. rewrite delVarSetList_nil. assumption.
    * subst abs_vars. rewrite fold_right_app. rewrite fold_right_app in HnotJoinId.
      simpl in *.
      destruct_match; simpl.
      + rewrite snd_pick_list. rewrite snd_pick_list in HnotJoinId.
        rewrite forallb_app in HnotJoinId. simpl_bool. destruct HnotJoinId as [HnotJoinId HnotJoinx].
        simpl in HnotJoinx. simpl_bool. rewrite negb_true_iff in HnotJoinx.
        rewrite delVarSetList_app, delVarSetList_cons, delVarSetList_nil.
        (* remove all mentions of [zap] *)
        erewrite delVarSet_ae by (apply almostEqual_sym; apply zap_ae).
        erewrite isJoinId_ae in HnotJoinx  by (apply almostEqual_sym; apply zap_ae).
        rewrite <- updJPS_not_joinId by assumption.
        rewrite <- updJPSs_cons.
        rewrite <- delVarSetList_cons2.
        rewrite <- delVarSetList_cons2 in HnotJoinId.
        apply IHcaptured.
        - rewrite <- app_assoc in HIJPVe.
          apply HIJPVe.
        - apply HnotJoinId.
      + apply IHcaptured.
        - rewrite isJoinPointsValid_fresh_between in HIJPVe.
          assumption.
          apply disjointVarSet_mkVarSet.
          constructor; only 2: constructor.
          assumption.
        - apply HnotJoinId.
  Qed.

  Lemma isJoinPointsValid_picked:
    forall jps captured e,
    isJoinPointsValid e 0 (updJPSs jps captured) = true ->
    let abs_vars := snd (fold_right pick (exprFreeVars e, []) captured) in
    forallb (fun x : Var => negb (isJoinId x)) abs_vars = true ->
    isJoinPointsValid e 0 (delVarSetList jps abs_vars) = true.
  Proof.
    intros.
    pose proof (isJoinPointsValid_picked_aux jps0 captured e []).
    rewrite !app_nil_r in *.
    rewrite delVarSetList_nil in *.
    specialize (H1 H H0).
    rewrite updJPSs_nil in H1.
    assumption.
  Qed.

  Lemma existsb_morgan:
    forall a p (xs : list a),
    existsb p xs = negb (forallb (fun x => negb (p x)) xs).
  Proof.
    intros.
    induction xs.
    * simpl. intuition congruence.
    * simpl. rewrite IHxs, negb_andb, negb_involutive.
      reflexivity.
  Qed.

  (* TODO: Remove this *)
  Lemma existsb_false_iff_forallb:
    forall a p (xs : list a),
    existsb p xs = false <-> forallb (fun x => negb (p x)) xs = true.
  Proof.
    intros.
    induction xs.
    * simpl. intuition congruence.
    * simpl. rewrite orb_false_iff, andb_true_iff, negb_true_iff, IHxs.
      reflexivity.
  Qed.
  


  Lemma go_exit_all_ValidJoinPairs captured e : 
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    isJoinPointsValid (toExpr e) 0 (updJPSs jpsp captured) = true ->
    disjointVarSet (exprFreeVars (toExpr e)) recursive_calls = true ->
    StateInvariant (fun xs => forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps) xs = true)
                   (go_exit captured (toExpr e) (exprFreeVars (toExpr e))).
  Proof.
    intros HWS HIJPV Hdisjoint.
    set (P := (fun xs => forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps) xs = true)).
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
    enough (Hnext: captures_join_points = false -> StateInvariant P j_14__). {
      destruct captures_join_points ; try (apply Hnext; auto).
      apply StateInvariant_return.
    }
    cleardefs.

    (* Third case: Actual exitification *)
    subst j_14__.
    intro Hno_capture_jp.
    unfold recursive_calls in Hdisjoint.
    subst captures_join_points.
    rewrite HSUtil.Foldable_any_existsb in Hno_capture_jp.
    rewrite existsb_false_iff_forallb in Hno_capture_jp.
    apply StateInvariant_bind_return.
    apply addExit_all_joinIds.
    apply isJoinRHS_mkLams.
    * rewrite Forall_forall.
      rewrite forallb_forall in Hno_capture_jp.
      intros v HIn.
      specialize (Hno_capture_jp v HIn).
      rewrite negb_true_iff in Hno_capture_jp.
      assumption.
    * apply isJoinPointsValid_picked.
      - unfold jpsp in *.
        rewrite <- updJPSs_append in HIJPV.
        erewrite <- isJoinPointsValid_fresh_updJPSs; only 1: eassumption.
        rewrite map_map in Hdisjoint.
        rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in Hdisjoint
            by (intros; repeat expand_pairs; destruct a; reflexivity).
        fold fs in Hdisjoint.
        eapply disjointVarSet_subVarSet_l; only 1: apply Hdisjoint.
        apply subVarSet_delVarSetList.
      - apply Hno_capture_jp.
  Qed.

  (* Now we need to do induction on go over a well-scoped _and_ join-point-valid term.
     And actually we need that twice. So hence I define a new induction principle, based on the old one, to be used twice.
  *)
  
  Lemma go_ind2_aux:
    forall (P : _ -> _ -> _ -> Prop),
    { IHs : Prop | 
    IHs ->
    forall e captured,
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    isJoinPointsValid (toExpr e) 0 (updJPSs jpsp captured) = true ->
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
    refine (go_ind (fun captured e r => impl (isJoinPointsValid (toExpr e) 0 (updJPSs jpsp captured) = true) (P captured e r)) _ _ _ _ _ _ _);
      intros; intro HIJPV.
    * revert e captured fvs HWS Hdisjoint HIJPV.
      eapply IH1.
    * simpl in HIJPV. simpl_bool. destruct HIJPV as [HIJPVrhs HIJPVe].
      fold isJoinPointsValidPair in HIJPVrhs.
      lapply IHe; only 1: (clear IHe; intro IHe).
      + revert captured x rhs e HnotJoin HWS HIJPVrhs HIJPVe IHe.
        eapply IH2.
      + rewrite updJPSs_append.
        rewrite updJPSs_cons.
        rewrite updJPSs_nil.
        assumption.
    * clear IH1 IH2.
      simpl in HIJPV. simpl_bool. destruct HIJPV as [HIJPVrhs HIJPVe].
      fold isJoinPointsValidPair in HIJPVrhs.
      lapply IHe; only 1: (clear IHe; intro IHe).
      lapply IHrhs; only 1: (clear IHrhs; intro IHrhs).
      + revert captured j params rhs e HisJoin HWS HIJPVrhs HIJPVe IHrhs IHe.
        eapply IH3.
      + rewrite updJPSs_append.
        eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS in HIJPVrhs; try eassumption.
        apply isJoinRHS_mkLams2 in HIJPVrhs.
        destruct HIJPVrhs as [Hno_isJoinId_params HIJPVrhs].
        assumption.
      + rewrite updJPSs_append.
        rewrite updJPSs_cons.
        rewrite updJPSs_nil.
        assumption.
    * clear IH1 IH2 IH3.
      simpl in HIJPV.
      simpl_bool.
      destruct HIJPV as [[HnotNull HjoinOrNotJoin] [HIJPVrhs HIJPVe]].
      fold isJoinPointsValidPair in HIJPVrhs.
      lapply IHe; only 1: (clear IHe; intro IHe).
      + clear HnotNull HjoinOrNotJoin.
        revert n pairs'0 e captured HGLV HNoDup HWSpairs HWSe HIJPVrhs HIJPVe IHe.
        eapply IH4.
      + rewrite updJPSs_append.
        rewrite to_list_map, map_map in HIJPVe.
        rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x) in HIJPVe
            by (intros; repeat expand_pairs; destruct a; reflexivity).
        assumption.
    * clear IH1 IH2 IH4.
      simpl in HIJPV. simpl_bool.
      destruct HIJPV as [[HnotNull HjoinOrNotJoin] [HIJPVrhs HIJPVe]].
      fold isJoinPointsValidPair in HIJPVrhs.
      lapply IHe; only 1: (clear IHe; intro IHe).
      match type of IHpairs with (forall (j:?T1) (params:?T2) (join_body:?T3) (HisJoin : ?T4), ?HIn -> impl ?A ?B) =>
       assert (forall (j:T1) (params:T2) (join_body:T3) (HisJoin : T4), HIn -> B) end.
      + intros ???? HIn.
        refine (IHpairs _ _ _ _ HIn _).
        rewrite to_list_map in HIJPVrhs.
        rewrite forallb_forall in HIJPVrhs.
        rewrite <- Forall_forall  in HIJPVrhs.
        rewrite Forall_map in HIJPVrhs.
        rewrite -> Forall_forall  in HIJPVrhs.
        specialize (HIJPVrhs _ HIn).
        fold isJoinPointsValidPair in HIJPVrhs.
        simpl in HIJPVrhs.
        rewrite map_map in HIJPVrhs.
        rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in HIJPVrhs
            by (intros; repeat expand_pairs; destruct a; reflexivity).
        pose proof (isJoinPointsValidPair_isJoinPoints_isJoinRHS _ _ _ _ HIJPVrhs HisJoin).
        apply isJoinRHS_mkLams2 in H.
        destruct H as [Hno_isJoinId_params H].
        rewrite !updJPSs_append.
        assumption.
      + clear HnotNull HjoinOrNotJoin.
        clear IHpairs. rename H into IHpairs.
        revert n pairs'0 e captured HGLV HNoDup HWSpairs HWSe HIJPVrhs HIJPVe IHpairs IHe.
        eapply IH5.
      + rewrite updJPSs_append.
        rewrite to_list_map, map_map in HIJPVe.
        rewrite map_ext with (g := fun '(Mk_NJPair x _ _ _) => x) in HIJPVe
            by (intros; repeat expand_pairs; destruct a; reflexivity).
        assumption. 
    * clear IH1 IH2 IH4 IH5.
      simpl in HIJPV. simpl_bool.
      destruct HIJPV as [[HnotJoin HIJPVe] HIJPValts].
      match type of IHalts with (forall (dc:?T1) (pats:?T2) (rhs:?T3), ?HIn -> impl ?A ?B) =>
        assert (forall (dc:T1) (pats:T2) (rhs:T3), HIn -> B) end.
      + intros ??? HIn.
        refine (IHalts  _ _ _ HIn _).
        rewrite forallb_forall in HIJPValts.
        rewrite <- Forall_forall  in HIJPValts.
        rewrite Forall_map in HIJPValts.
        rewrite -> Forall_forall  in HIJPValts.
        specialize (HIJPValts _ HIn).
        simpl in HIJPValts.
        simpl_bool.
        destruct HIJPValts as [Hno_isJoinId_pats HIJPValts].
        rewrite updJPSs_append, updJPSs_cons.
        rewrite updJPSs_not_joinId by assumption.
        rewrite negb_true_iff in HnotJoin.
        rewrite updJPS_not_joinId by assumption.
        assumption.
      + clear IHalts. rename H into IHalts.
        revert e v alts captured HWSscrut HGLVv HWSalts HnotJoin HIJPVe HIJPValts IHalts.
        eapply IH6.
    * clear IH1 IH2 IH4 IH5 IH6.
      revert e captured HWS HIJPV.
      eapply IH7.
  Defined.

  Definition go_ind2 P
    := ltac:(let x := uncurryN 6 (proj2_sig (go_ind2_aux P)) in exact x).
  Opaque go_ind2 go_ind2_aux.


  Lemma go_all_ValidJoinPairs captured e: 
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    isJoinPointsValid (toExpr e) 0 (updJPSs jpsp captured) = true ->
    StateInvariant (fun xs => forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps) xs = true)
                   (go captured (freeVars (toExpr e))).
  Proof.
    revert e captured.
    refine (go_ind2 (fun captured e r => _ r) _ _ _ _ _ _ _);
      intros.
    * apply go_exit_all_ValidJoinPairs.
      -- apply HWS.
      -- apply HIJPV.
      -- apply Hdisjoint.
    * apply StateInvariant_bind_return.
      apply IHe.
    * apply StateInvariant_bind; only 1: apply IHrhs.
      -- intros. apply StateInvariant_bind_return.
         apply IHe.
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
      apply StateInvariant_bind_return.
      apply StateInvariant_forM.
      intros [[dc pats] rhs] HIn.
      apply StateInvariant_bind_return.
      apply (IHalts _ _ _ HIn).
    * apply StateInvariant_return.
  Qed.


  Lemma all_exits_ValidJoinPairs:
    forallb (fun '(v,rhs) => isValidJoinPointsPair v rhs jps) exits = true.
  Proof using Type pairs_VJPP pairs_WS.
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
      pose proof pairs_WS as HWS_pairs.
      rewrite Forall_map in HWS_pairs.
      rewrite Forall_forall in HWS_pairs.
      specialize (HWS_pairs _ HIn).
      simpl in HWS_pairs.
      rewrite WellScoped_mkLams in HWS_pairs.
      apply go_all_ValidJoinPairs.
      + apply HWS_pairs.
      + simpl.
        rewrite Forall_map in pairs_VJPP.
        rewrite Forall_forall in pairs_VJPP.
        specialize (pairs_VJPP _ HIn).
        simpl in pairs_VJPP.
        unfold isValidJoinPointsPair in pairs_VJPP.
        rewrite HisJoin in pairs_VJPP.
        apply isJoinRHS_mkLams2 in pairs_VJPP.
        destruct pairs_VJPP as [Hno_isJoinId_params H].
        apply H.
    * repeat split; constructor.
  Qed.

  Lemma all_exits_isJoinId:
    forallb isJoinId (map fst exits) = true.
  Proof using Type pairs_VJPP pairs_WS.
    rewrite forallb_forall.
    rewrite <- Forall_forall.
    rewrite Forall_map.
    rewrite Forall_forall.
    intros [v e] HIn.
    pose proof all_exits_ValidJoinPairs.
    rewrite forallb_forall in H.
    specialize (H _ HIn).
    apply isValidJoinPointsPair_isJoinId in H.
    assumption.
  Qed.

  Lemma disjoint_jps_exits:
     disjointVarSet jps (mkVarSet (map fst exits)) = true.
  Proof using Type pairs_WS jps_subset_isvs.
    eapply disjointVarSet_subVarSet_l.
    apply disjoint_isvs_exits.
    apply jps_subset_isvs.
  Qed.

  Lemma jps_to_jps':
     StrongSubset jps jps'.
  Proof using Type pairs_WS jps_subset_isvs.
    intros.
    apply StrongSubset_updJPSs_fresh.
    apply disjoint_jps_exits.
  Qed.

  Lemma jpsp_to_jpsp':
     StrongSubset jpsp jpsp'.
  Proof using Type pairs_WS jps_subset_isvs.
    intros.
    apply StrongSubset_updJPSs.
    apply jps_to_jps'.
  Qed.

  Lemma jpsp_to_jpsp'_extended:
     forall vs, StrongSubset (updJPSs jpsp vs) (updJPSs jpsp' vs).
  Proof using Type pairs_WS jps_subset_isvs.
    intros.
    apply StrongSubset_updJPSs.
    apply jpsp_to_jpsp'.
  Qed.

  Lemma jpsp_to_jpsp'_extended2:
     forall vs1 vs2,
     StrongSubset (updJPSs (updJPSs jpsp vs1) vs2)
                  (updJPSs (updJPSs jpsp' vs1) vs2).
  Proof using Type pairs_WS jps_subset_isvs.
    intros.
    apply StrongSubset_updJPSs.
    apply jpsp_to_jpsp'_extended.
  Qed.


  (* Again, we go through [go] again and see that pairs' is join-point valid.
  *)

  Lemma addExit_isJoinPointsValid:
    forall captured ja e,
    let after := updJPSs jpsp' captured in
    RevStateInvariant (sublistOf exits) 
         (addExit (extendInScopeSetList in_scope2 captured) ja e)
         (fun v => isJoinPointsValid (Mk_Var v) ja after = true).
  Proof using Type pairs_WS pairs_VJPP.
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
    assert (isJoinId_maybe v = Some ja). {
      subst v.
      rewrite isJoinId_maybe_uniqAway, isJoinId_maybe_asJoinId.
      reflexivity.
    } 
    rewrite H; clear H.
    rewrite Nat.leb_refl. simpl.
    unfold jpsp', jps'.
    (* There is again a lot of repetition to above *)
    apply elemVarSet_updJPSs_l; only 1: apply elemVarSet_updJPSs_l.
    * rewrite updJPSs_joinId by apply all_exits_isJoinId.
      apply elemVarSet_extendVarSetList_r.
      apply elemVarSet_mkVarset_iff_In.
      apply in_map.
      assumption.
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


  Lemma go_exit_res_isJoinPointsValid captured e : 
    let orig := updJPSs jpsp captured in
    let after := updJPSs jpsp' captured in
    isJoinPointsValid (toExpr e) 0 orig = true ->
    RevStateInvariant (sublistOf exits) (go_exit captured (toExpr e) (exprFreeVars (toExpr e)))
                      (fun e' => isJoinPointsValid e' 0 after = true).
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs.
    intros ?? HJPVe.

    set (P := fun x => RevStateInvariant (sublistOf exits) x (fun e' => isJoinPointsValid e' 0 after = true)).
    change (P (go_exit captured (toExpr e) (exprFreeVars (toExpr e)))).

    cbv beta delta [go_exit]. (* No [zeta]! *)
    repeat float_let.

    (* Common case *)
    assert (Hreturn : P (return_ (toExpr e))). {
       apply RevStateInvariant_return. cleardefs.
       apply (weakenb (jpsp_to_jpsp'_extended _)).
       assumption.
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
    enough (Hnext: captures_join_points = false ->  P j_14__). {
      destruct (captures_join_points) ; try (apply Hnext; auto).
      apply Hreturn.
    }
    cleardefs.

    (* Third case: Actual exitification *)
    subst j_14__.

    intro Hno_capture_jp.
    subst captures_join_points.
    rewrite HSUtil.Foldable_any_existsb in Hno_capture_jp.
    rewrite existsb_false_iff_forallb in Hno_capture_jp.
    rewrite forallb_forall in Hno_capture_jp.
    setoid_rewrite negb_true_iff in Hno_capture_jp.
    rewrite <- Forall_forall in Hno_capture_jp.

    subst P. cleardefs. simpl.
    eapply RevStateInvariant_bind; only 1: apply addExit_isJoinPointsValid.
    intro v.
    apply RevStateInvariant_return.
    intro HJPVv.
    apply isJoinPointsValid_mkVarApps; only 1: apply Hno_capture_jp.
    simpl (0 + _).
    assumption.
  Qed.

  Lemma go_res_isJoinPointsValid captured e: 
    let orig := updJPSs jpsp captured in
    let after := updJPSs jpsp' captured in
    WellScoped (toExpr e) (extendVarSetList isvsp captured) ->
    isJoinPointsValid (toExpr e) 0 orig = true ->
    RevStateInvariant (sublistOf exits) (go captured (freeVars (toExpr e)))
                      (fun e' => isJoinPointsValid e' 0 after = true).
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs.
    revert e captured.
    refine (go_ind2 (fun captured e r => RevStateInvariant (sublistOf exits) r (fun e' => isJoinPointsValid e' 0 (updJPSs jpsp' captured) = true)) _ _ _ _ _ _ _);
      intros.
    * apply go_exit_res_isJoinPointsValid; assumption.
    * eapply RevStateInvariant_bind.
      - apply IHe.
      - intro e'; apply RevStateInvariant_return; intro He'.
        rewrite  updJPSs_append, updJPSs_cons, updJPSs_nil in He'.
        rewrite deAnnotate_freeVars.
        simpl; simpl_bool; split.
        ++ fold isJoinPointsValidPair.
           rewrite isJoinPointsValidPair_isJoinPointsValid by apply HnotJoin.
           rewrite isJoinPointsValidPair_isJoinPointsValid in HIJPVrhs by apply HnotJoin.
           assumption.
        ++ apply He'.
    * unfold CoreBndr in *.
      eapply RevStateInvariant_bind; only 2: (intro body'; eapply RevStateInvariant_bind; only 2: intro rhs').
      - apply IHrhs.
      - apply IHe.
      - apply RevStateInvariant_return; intros Hrhs' Hbody'.
        simpl; simpl_bool; split.
        ** fold isJoinPointsValidPair.
           rewrite isJoinPointsValidPair_isJoinRHS by (apply HisJoin).
           rewrite isJoinPointsValidPair_isJoinRHS in HIJPVrhs by (apply HisJoin).
           apply isJoinRHS_mkLams2 in HIJPVrhs.
           destruct HIJPVrhs as [HnotIsJoinID_params HIJPVrhs].
           rewrite <- isJoinRHS_mkLams by assumption.
           rewrite <- updJPSs_not_joinId
             by (rewrite forallb_forall; setoid_rewrite negb_true_iff; rewrite <- Forall_forall; assumption).
           rewrite updJPSs_append in Hbody'.
           assumption.
        ** simpl.
           rewrite updJPSs_append, updJPSs_cons, updJPSs_nil in Hrhs'.
           assumption.
   *  eapply RevStateInvariant_bind; only 1: apply IHe.
      intro body'. apply RevStateInvariant_return; intros Hbody'.
      rewrite updJPSs_append in Hbody'.
      simpl; simpl_bool; repeat apply conj.
      ++ dependent destruction pairs'0.
         reflexivity.
      ++ simpl_bool. left.
         rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall.
         intros [v rhs] HIn. simpl.
         rewrite isJoinId_eq. rewrite HnotJoin. reflexivity.
      ++ rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall.
         intros [v rhs] HIn. simpl.
         fold isJoinPointsValidPair.
         rewrite isJoinPointsValidPair_isJoinPointsValid by assumption.
         rewrite deAnnotate_freeVars.

         rewrite to_list_map, forallb_forall, <- Forall_forall, Forall_map, Forall_forall in HIJPVrhs.
         specialize (HIJPVrhs _ HIn).
         simpl in HIJPVrhs.
         rewrite isJoinPointsValidPair_isJoinPointsValid in HIJPVrhs by assumption.
         assumption.
      ++ rewrite !map_map.
         rewrite map_ext with (g := fun '(Mk_NPair x rhs _) => x)
            by (intros; repeat expand_pairs; destruct a; reflexivity).
         apply Hbody'.
     * eapply RevStateInvariant_bind.
       - apply RevStateInvariant_forM2 with
              (R := fun p p' =>
                  (fun '(Mk_NJPair x _ _ _) => x) p = fst p' /\
                  isJoinRHS (snd p') (length ((fun '(Mk_NJPair _ a _ _) => a) p)) (updJPSs (updJPSs jpsp' captured) (map (fun '(Mk_NJPair x _ _ _) => x) (Vector.to_list pairs'0))) = true).
         intros [j params rhs] HIn.
         simpl.
         erewrite idJoinArity_join by eassumption.
         rewrite collectNAnnBndrs_freeVars_mkLams.
         eapply RevStateInvariant_bind.
         ++ apply (IHpairs _ _ _ _ HIn).
         ++ intro e'; apply RevStateInvariant_return; intro He'.
            simpl.
            rewrite !updJPSs_append in He'.
            split.
            -- reflexivity.
            -- rewrite to_list_map, forallb_forall, <- Forall_forall, Forall_map, Forall_forall in HIJPVrhs.
               specialize (HIJPVrhs _ HIn).
               simpl in HIJPVrhs.
               rewrite isJoinPointsValidPair_isJoinRHS in HIJPVrhs by eassumption.

               apply isJoinRHS_mkLams2 in HIJPVrhs.
               destruct HIJPVrhs as [HnotIsJoinID_params HIJPVrhs].
               rewrite <- isJoinRHS_mkLams by assumption.
               rewrite <- updJPSs_not_joinId
                 by (rewrite forallb_forall; setoid_rewrite negb_true_iff; rewrite <- Forall_forall; assumption).
               assumption.
      - intro pairs''.
        eapply RevStateInvariant_bind; only 1: apply IHe.
        intro e'; apply RevStateInvariant_return; intros He' Hpairs''.
        pose proof Hpairs'' as Hfst.
        apply Forall2_and in Hfst.
        destruct Hfst as [Hfst _].
        eapply Forall2_eq with (f := (fun '(Mk_NJPair x _ _ _) => x)) (g := fst) in Hfst.
        symmetry in Hfst.
        change ((@map (CoreBndr * Expr CoreBndr) CoreBndr (@fst CoreBndr (Expr CoreBndr)) pairs'') = map (fun '(Mk_NJPair x _ _ _) => x) (Vector.to_list pairs'0)) in Hfst.
        simpl.
        rewrite Hfst.
        simpl_bool. repeat apply conj.
        -- dependent destruction pairs'0.
           rewrite to_list_cons in Hfst. simpl in Hfst.
           destruct pairs''; simpl in Hfst; try congruence.
           reflexivity.
        -- simpl_bool. right.
           rewrite forallb_forall, <- Forall_forall.
           apply Forall_map with (P := fun x : CoreBndr => isJoinId x = true) (f := (@fst CoreBndr (Expr CoreBndr))) (xs := pairs'').
           rewrite Hfst.
           rewrite Forall_map.
           rewrite Forall_forall.
           intros [x params rhs HisJoinId] HIn.
           rewrite isJoinId_eq. rewrite HisJoinId. reflexivity.
        -- rewrite forallb_forall, <- Forall_forall.
           eapply Forall2_impl_Forall_r; only 1: apply Hpairs''.
           intros [v' params rhs' HisJoinId] [v rhs] [Heq isJoinRHS]. simpl.
           fold isJoinPointsValidPair.
           simpl in Heq. subst.
           rewrite isJoinPointsValidPair_isJoinRHS by apply HisJoinId.
           eassumption.
        -- rewrite updJPSs_append in He'.
           apply He'.
      * (* [Case] *)
        simpl.
        eapply RevStateInvariant_bind.
        + apply RevStateInvariant_forM with
            (R := fun alt => isjoinPointsAlt alt (delVarSet (updJPSs jpsp' captured) v) = true).
          intros [[dc pats] rhs] HIn.
          eapply RevStateInvariant_bind.
          - apply (IHalts _ _ _  HIn).
          - clear IHalts.
            intro e'; apply RevStateInvariant_return; intro He'.
            rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall in HIJPValts.
            specialize (HIJPValts _ HIn). simpl in HIJPValts. simpl.
            simpl_bool. destruct HIJPValts as [Hnot_joinId _].
            split.
            -- assumption.
            -- rewrite <- updJPSs_not_joinId by assumption.
               rewrite negb_true_iff in HnotJoin.
               rewrite <- updJPS_not_joinId by assumption.
               rewrite <- updJPSs_cons.
               rewrite <- updJPSs_append.
               assumption.
        + intros alts'; apply RevStateInvariant_return; intro Halts.
          simpl. simpl_bool. split; only 1: split.
          - assumption.
          - rewrite deAnnotate_freeVars.
            assumption.
          - rewrite forallb_forall. rewrite  Forall_forall in Halts.
            intros [[dc params] rhs] HIn.
            specialize (Halts _  HIn).
            simpl in Halts.
            apply Halts.
  * apply RevStateInvariant_return.
    apply (weakenb (jpsp_to_jpsp'_extended _)).
    assumption.
  Qed.

  Lemma pairs'_JPV:
    Forall (fun '(v,rhs) => isValidJoinPointsPair v rhs jpsp' = true) pairs'.
  Proof using Type pairs_WS pairs_VJPP jps_subset_isvs.
    unfold pairs', pairs'_exits, ann_pairs.
    eapply RevStateInvariant_runState with (P := sublistOf exits).
    * rewrite hs_coq_map, !map_map, forM_map.
      apply RevStateInvariant_forM.
      intros [v param rhs HisJoin] HIn.
      
      pose proof pairs_VJPP as Hpairs.
      rewrite Forall_map in Hpairs.
      rewrite Forall_forall in Hpairs.
      specialize (Hpairs _ HIn).
      simpl in Hpairs.
      unfold isValidJoinPointsPair in Hpairs.
      rewrite HisJoin in Hpairs.
      apply isJoinRHS_mkLams2 in Hpairs.
      destruct Hpairs as [Hno_joinId_param HJPVrhs].

      unfold id.
      simpl.
      erewrite idJoinArity_join by eassumption.
      rewrite collectNAnnBndrs_freeVars_mkLams.
      eapply RevStateInvariant_bind.
      ++ apply go_res_isJoinPointsValid.
         ** apply WellScoped_mkLams.
            rewrite Forall_map in pairs_WS.
            rewrite Forall_forall in pairs_WS.
            apply (pairs_WS _ HIn).
         ** assumption.
        ++ intro e'; apply RevStateInvariant_return; intro He'.
           simpl.
           unfold isValidJoinPointsPair.
           rewrite HisJoin.
           rewrite <- isJoinRHS_mkLams by assumption.
           rewrite <- updJPSs_not_joinId
             by (rewrite forallb_forall; setoid_rewrite negb_true_iff; rewrite <- Forall_forall; assumption).
           assumption.
    * change (sublistOf exits exits).
      intro. auto.
  Qed.


  (** Main result *)

  Theorem exitifyRec_JPI:
    forall body,
    pairs <> [] ->
    let jps' := updJPSs jps fs in
    isJoinPointsValid body 0 jps' = true ->
    isJoinPointsValid (mkLets (exitifyRec (extendInScopeSetList in_scope fs) (map toJPair pairs)) body) 0 jps = true.
  Proof using Type jps_subset_isvs pairs_VJPP pairs_WS.
    intros.
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
    change (isJoinPointsValid (mkLets (map (fun '(x, y) => NonRec x y) exits ++ [Rec pairs']) body) 0 jps = true).
    rewrite mkLets_append, mkLets_cons, mkLets_nil.
    apply mkLets_JPI.
    * eapply disjointVarSet_subVarSet_l.
      + apply disjointVarSet_mkVarSet.
        rewrite Forall_map.
        apply all_exits_WellScoped.
      + apply jps_subset_isvs.
    * rewrite isJoinPointsValid_MkLet_Rec.
      subst jps'0.
      float_let. subst jps'0.
      rewrite map_fst_pairs'.
      simpl_bool; repeat apply conj.
      -- simpl_bool. right.
         rewrite forallb_forall.
         intros [v e] HIn.
         pose proof pairs'_JPV.
         rewrite Forall_forall in H1.
         specialize (H1 _ HIn).
         simpl in HIn.
         apply isValidJoinPointsPair_isJoinId in H1.
         assumption.
      -- fold isJoinPointsValidPair.
         rewrite forallb_forall.
         intros [v e] HIn.
         pose proof pairs'_JPV.
         rewrite Forall_forall in H1.
         specialize (H1 _ HIn).
         simpl in HIn.
         apply isValidJoinPointsPair_isJoinPointsValidPair in H1.
         assumption.
      -- apply (weakenb jpsp_to_jpsp').
         assumption.
    * apply all_exits_ValidJoinPairs.
  Qed.


End in_exitifyRec.

(* This re-formulates the main lemma about [exitifyRec] without using [NCore] stuff. *)
(* Also, introduce some equalities for easier application *)
Lemma exitifyRec_WellScoped':
  forall (in_scope : InScopeSet) (pairs : list (CoreBndr * CoreExpr)) fst_pairs jps,
  fst_pairs = map fst pairs -> 
  forallb (fun p : Var * Expr CoreBndr => isJoinId (fst p)) pairs = true ->
  forallb (fun '(v, e) => isJoinPointsValidPair v e (updJPSs jps (map fst pairs))) pairs = true -> 
  Forall (fun p : CoreBndr * CoreExpr => WellScoped (snd p) (extendVarSetList (isvs in_scope) fst_pairs)) pairs ->
  Forall (fun p : Var * Expr CoreBndr => GoodLocalVar (fst p)) pairs ->
  forall body : CoreExpr,
  NoDup (map varUnique fst_pairs) ->
  WellScoped body (extendVarSetList (isvs in_scope) fst_pairs) ->
  WellScoped
    (mkLets (exitifyRec (extendInScopeSetList in_scope fst_pairs) pairs) body)
    (isvs in_scope).
Proof.
  intros ???? Heq Hall_join HiJP.
  subst.
  assert (exists npairs, pairs = map toJPair npairs) as Hex.
  { eapply isJoinPointsValid_to_NCore_join_pairs.
    * apply Hall_join.
    * apply HiJP.
  } 
  destruct Hex as [npairs ?]. subst.
  replace (map fst _) with (fs npairs).
  2: {
    unfold fs. rewrite map_map.
    apply map_ext. destruct a. reflexivity.
  }
  apply (exitifyRec_WellScoped in_scope  npairs).
Qed.


Definition top_go := ltac:(
  let rhs := eval cbv beta delta [exitifyProgram] in (exitifyProgram []) in
  lazymatch rhs with | (let x := ?rhs in ?body) => 
    exact rhs
  end).

Lemma mapSnd_map:
  forall {a b c} (f : b -> c) (xs : list (a * b)),
  Util.mapSnd f xs = map (fun x => (fst x, f (snd x))) xs.
Proof. intros. induction xs. reflexivity. simpl. destruct a0. rewrite <- IHxs.  reflexivity. Qed.

Lemma extendInScopeSetList_nil:
  forall in_scope,
  extendInScopeSetList in_scope [] = in_scope.
Admitted.

Lemma extendInScopeSetList_cons:
  forall in_scope x xs,
  extendInScopeSetList in_scope (x::xs) = extendInScopeSetList (extendInScopeSet in_scope x) xs.
Admitted.


Lemma top_go_WellScoped_mkLams:
  forall in_scope body vs,
  Forall GoodLocalVar vs ->
  WellScoped (top_go (extendInScopeSetList in_scope vs) body)
      (getInScopeVars (extendInScopeSetList in_scope vs)) ->
  WellScoped (top_go in_scope (mkLams vs body)) (getInScopeVars in_scope).
Proof.
  intros ??? H HWS.
  revert in_scope HWS. induction H; intros.
  * rewrite extendInScopeSetList_nil in HWS.
    apply HWS.
  * replace (mkLams _ _) with (Lam x (mkLams l body)) in * by reflexivity.
    simpl in *.
    split; only 1: assumption.
    rewrite <- getInScopeVars_extendInScopeSet.
    apply IHForall.
    rewrite <- extendInScopeSetList_cons.
    assumption.
Qed.

Program Fixpoint top_go_WellScoped
  e in_scope n jps {measure e (CoreLT)} :
  WellScoped e (getInScopeVars in_scope)->
  isJoinPointsValid e n jps = true ->
  WellScoped (top_go in_scope e) (getInScopeVars in_scope) := _.
Next Obligation.
  rename top_go_WellScoped into IH.
  rename H into HWS.
  rename H0 into HJPV.
  destruct e; simpl in HJPV; simpl_bool; simpl.
  * (* Var *)
    assumption.
  * (* Lit *)
    apply I.
  * (* App *)
    inversion HWS as [HWSe1 HWSe2].
    inversion HJPV as [HJPVe1 HJPVe2].
    epose proof (IH _ _ _ _ _ HWSe1 HJPVe1).
    epose proof (IH _ _ _ _ _ HWSe2 HJPVe2).
    intuition.
  * (* Lam *)
    inversion HWS as [HGoodVar HWSe].
    simpl in HJPV. simpl_bool. destruct HJPV as [_ HJPVe].
    split; only 1: assumption.
    rewrite <- getInScopeVars_extendInScopeSet.
    rewrite <- getInScopeVars_extendInScopeSet in HWSe.
    epose proof (IH _ _ _ _ _ HWSe HJPVe).
    eassumption.
  * (* Let *)
    destruct HWS as [HBind HWSe].
    destruct b as [v rhs|pairs]; simpl in *.
    + (* NonRec *)
      destruct HBind as [HGoodVar Hrhs].
      simpl_bool. destruct HJPV as [HJPV_pair HJPVe].
      fold isJoinPointsValidPair in HJPV_pair.
      split; only 1: split.
      - assumption.
      - destruct (isJoinId_maybe v) eqn:HiJI.
        ** eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS in HJPV_pair; only 2: apply HiJI.
           pose proof (isJoinRHS_mkLams3 _ _ _ HJPV_pair).
           destruct H as [body [vs [Heq1 Heq2]]]. subst.
           pose proof (isJoinRHS_mkLams2 _ _ _ HJPV_pair).
           destruct H as [Hnot_join_params HJPVbody].
           clear HGoodVar.
           rewrite WellScoped_mkLams in Hrhs.
           destruct Hrhs as [HGoodVars HWSbody].
           rewrite <- getInScopeVars_extendInScopeSetList in HWSbody.
           epose proof (IH _ _ _ _ _ HWSbody HJPVbody).
           apply top_go_WellScoped_mkLams; assumption.
        ** eapply isJoinPointsValidPair_isJoinPointsValid in HJPV_pair; only 2: apply HiJI.
           epose proof (IH _ _ _ _ _ Hrhs HJPV_pair).
           assumption.
      - rewrite <- getInScopeVars_extendInScopeSetList.
        rewrite <- getInScopeVars_extendInScopeSetList in HWSe.
        epose proof (IH _ _ _ _ _ HWSe HJPVe).
        assumption.
    + (* Rec *)
      destruct HBind as [HGoodVars [HNoDup Hpairs]].
      simpl_bool. destruct HJPV as [[Hnot_null Hall_or_none] [HJPVpairs HJPVe]].
      clear Hnot_null.
      fold isJoinPointsValidPair in HJPVpairs.
      destruct_match.
      - (* join points *)
        rewrite HSUtil.Foldable_any_existsb in Heq.
        rewrite existsb_morgan in Heq.
        rewrite negb_true_iff in Heq.
        rewrite orb_true_iff in Hall_or_none.
        destruct Hall_or_none as [Hnone | Hall].
        1 : { exfalso. apply (eq_true_false_abs _ Hnone Heq). }

        rewrite bindersOf_Rec_cleanup in *.
        eapply exitifyRec_WellScoped'.
        ** rewrite mapSnd_map, map_map.
           apply map_ext.
           intros. reflexivity.
        ** rewrite mapSnd_map.
           rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall.
           rewrite forallb_forall in Hall.
           intros [v rhs] HIn.
           specialize (Hall _ HIn).
           apply Hall.
        ** rewrite mapSnd_map.
           rewrite forallb_forall, <- Forall_forall, Forall_map, Forall_forall.
           rewrite forallb_forall in HJPVpairs.
           intros [v rhs] HIn.
           specialize (HJPVpairs _ HIn).
           simpl in *.
           admit. (* Here we need that the output of top_go is a isJoinPointsValidPair *)
        ** rewrite Forall'_Forall in Hpairs.
           rewrite mapSnd_map, Forall_map.
           rewrite Forall_forall in *.
           intros [v rhs] HIn.
           simpl.
           rewrite forallb_forall in HJPVpairs.
           specialize (Hpairs _ HIn).
           specialize (HJPVpairs _ HIn).
           simpl in HJPVpairs.
           destruct (isJoinId_maybe v) eqn:HiJI.
           2: {
             exfalso.
             rewrite forallb_forall in Hall.
             specialize (Hall _ HIn). simpl in Hall.
             rewrite isJoinId_eq in Hall. rewrite HiJI in Hall. congruence.
           } 
           eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS in HJPVpairs; only 2: apply HiJI.
           pose proof (isJoinRHS_mkLams3 _ _ _ HJPVpairs).
           destruct H as [body [vs [Heq1 Heq2]]]. subst.
           pose proof (isJoinRHS_mkLams2 _ _ _ HJPVpairs).
           destruct H as [Hnot_join_params HJPVbody].
           simpl in Hpairs.
           rewrite WellScoped_mkLams in Hpairs.
           clear HGoodVars.
           destruct Hpairs as [HGoodVars HWSbody].
           rewrite <- !getInScopeVars_extendInScopeSetList in HWSbody.
           rewrite <- !getInScopeVars_extendInScopeSetList.
           epose proof (IH _ _ _ _ _ HWSbody HJPVbody).
           apply top_go_WellScoped_mkLams; assumption.
        ** rewrite mapSnd_map, Forall_map.
           rewrite Forall_forall in *.
           intros [v rhs] HIn.
           apply (HGoodVars _ HIn).
        ** assumption.
        ** rewrite <- getInScopeVars_extendInScopeSetList in HWSe.
           rewrite <- getInScopeVars_extendInScopeSetList.
           epose proof (IH _ _ _ _ _ HWSe HJPVe).
           assumption.
      - (* non-join points *)
        simpl.
        repeat apply conj.
        ** rewrite mapSnd_map.
           rewrite Forall_map.
           eapply Forall_impl; only 2: apply HGoodVars. simpl.
           intros [v rhs] HGoodVar.
           apply HGoodVar.
        ** rewrite mapSnd_map.
           repeat rewrite map_map.
           rewrite map_map in HNoDup.
           apply HNoDup.
        ** clear HWSe HJPVe.
           rewrite Forall'_Forall in *.
           rewrite bindersOf_Rec_cleanup in *.
           rewrite mapSnd_map.
           rewrite !Forall_map.
           rewrite Forall_forall.
           intros [v rhs] HIn.
           rewrite Forall_forall in Hpairs.
           rewrite forallb_forall in HJPVpairs.
           specialize (Hpairs _ HIn).
           specialize (HJPVpairs _ HIn).
           simpl in *.
           rewrite <- getInScopeVars_extendInScopeSetList.
           rewrite map_map. simpl.
           rewrite <- getInScopeVars_extendInScopeSetList in Hpairs.
           destruct (isJoinId_maybe v) eqn:HiJI.
           1: {
             exfalso.
             rewrite HSUtil.Foldable_any_existsb in Heq.
             rewrite existsb_morgan in Heq.
             rewrite negb_false_iff in Heq.
             rewrite forallb_forall in Heq.
             specialize (Heq _ HIn). simpl in Heq.
             rewrite isJoinId_eq in Heq. rewrite HiJI in Heq. simpl in Heq. congruence.
           }
           eapply isJoinPointsValidPair_isJoinPointsValid in HJPVpairs; only 2: apply HiJI.
           epose proof (IH _ _ _ _ _ Hpairs HJPVpairs).
           apply H.
        ** rewrite !bindersOf_Rec_cleanup in *.
           rewrite mapSnd_map.
           rewrite map_map. simpl.
           rewrite <- getInScopeVars_extendInScopeSetList.
           rewrite <- getInScopeVars_extendInScopeSetList in *.
           epose proof (IH _ _ _ _ _ HWSe HJPVe).
           apply H.
  * (* Case *)
    destruct HWS as [HWSscrut [HGoodVar HWSalts]].
    rewrite Forall'_Forall in *.
    destruct HJPV as [[Hnot_join HJPVscrut] HJPValts].
    split; only 2: split.
    + epose proof (IH _ _ _ _ _ HWSscrut HJPVscrut).
      assumption.
    + assumption.
    + unfold Base.map.
      rewrite Forall_map. simpl.
      rewrite Forall_forall in *.
      rewrite forallb_forall in *.
      intros [[dc pats] rhs] HIn.
      specialize (HWSalts _ HIn). simpl in HWSalts.
      specialize (HJPValts _ HIn). simpl in HJPValts.
      simpl_bool.
      destruct HWSalts as [HGoodVars HWSrhs].
      destruct HJPValts as [Hnot_joins HJPVrhs].
      split.
      - apply HGoodVars. 
      - simpl.
        rewrite extendVarSetList_cons.
        rewrite <- getInScopeVars_extendInScopeSet.
        rewrite <- getInScopeVars_extendInScopeSetList.
        rewrite <- extendInScopeSetList_cons.
        rewrite <- getInScopeVars_extendInScopeSetList in HWSrhs.
        epose proof (IH _ _ _ _ _ HWSrhs HJPVrhs).
        assumption.
  * (* Cast *)
    simpl in *.
    epose proof (IH _ _ _ _ _ HWS HJPV).
    assumption.
  * (* Tick *)
    simpl in *.
    epose proof (IH _ _ _ _ _ HWS HJPV).
    assumption.
  * (* Type *)
    intuition.
  * (* Coercion *)
    intuition.
Unshelve.
  all: Core_termination || (unfold CoreLT; simpl; lia). (* phew *)
Admitted.

Lemma Forall_flattenBinds:
  forall {b} P (binds : list (Bind b)),
  Forall P (flattenBinds binds) <->
  Forall (fun bind => Forall P (flattenBinds [bind])) binds.
Admitted.

Theorem exitifyProgram_WellScoped:
  forall pgm,
  WellScopedProgram pgm->
  WellScopedProgram (exitifyProgram pgm).
Proof.
  intros.
  cbv beta delta [exitifyProgram].
  fold top_go.
  zeta_one.
  do 2 float_let.

  assert (HbindersOf: forall a, bindersOf (goTopLvl a) = bindersOf a). admit.
  
  assert (HbindersOfBinds: bindersOfBinds (Base.map goTopLvl pgm) = bindersOfBinds pgm). admit.

  destruct H as [HNoDup HWS].

  unfold WellScopedProgram.
  split.
  * rewrite HbindersOfBinds.
    apply HNoDup.
  * rewrite Forall'_Forall.
    rewrite Forall'_Forall in HWS.
    rewrite Forall_flattenBinds.
    rewrite Forall_flattenBinds in HWS.
    rewrite HbindersOfBinds.
    rewrite Forall_map.

    eapply Forall_impl; only 2: apply HWS; clear HWS.
    intros bind HWS. simpl.
    destruct bind.
    + unfold goTopLvl.
      inversion_clear HWS. clear H0.
      constructor; only 2: constructor.
      simpl.
      eapply top_go_WellScoped.
      -- assumption.
      -- admit.
    + unfold goTopLvl.
      simpl in *.
      rewrite app_nil_r in *.
      rewrite Forall_map.
      eapply Forall_impl; only 2: apply HWS; clear HWS.
      intros [v e] HWS.
      eapply top_go_WellScoped.
      -- assumption.
      -- admit.
Admitted.