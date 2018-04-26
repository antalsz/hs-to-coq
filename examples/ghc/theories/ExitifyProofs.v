Require Import GHC.Base.

Require Import Exitify.
Require Import CoreSyn.
Require Import CoreFVs.
Require Import Var.
Require Import VarEnv.
Require Import VarSet.
Require Import Id.
Require Import IdInfo.


Require Import Psatz.
Require Import Coq.Lists.List.

Import ListNotations.

Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

Require Import JoinPointInvariants.
Require Import StateLogic.


(** Tactics *)

Ltac expand_pairs :=
match goal with
  |- context[let (_,_) := ?e in _] =>
  rewrite (surjective_pairing e)
end.

Ltac simpl_bool :=
  rewrite ?orb_true_l, ?orb_true_r, ?orb_false_l, ?orb_false_r,
          ?andb_true_l, ?andb_true_r, ?andb_false_l, ?andb_false_r,
          ?orb_true_iff, ?andb_true_iff
          in *.

(** This tactic finds a [let x := rhs in body] anywhere in the goal,
    and moves it into the context, without zeta-reducing it. *)
Ltac find_let e k :=
  lazymatch e with 
    | let x := ?rhs in ?body => k x rhs body
    | ?e1 ?e2 =>
      find_let e1 ltac:(fun x rhs body => k x rhs uconstr:(body e2)) ||
      find_let e2 ltac:(fun x rhs body => k x rhs uconstr:(e1 body))
    | _ => fail
  end.
Ltac float_let :=
  lazymatch goal with |- ?goal =>
    find_let goal ltac:(fun x rhs body =>
      let goal' := uconstr:(let x := rhs in body) in
      (change goal'; intro) || fail 1000 "Failed to change to" goal'
    )
  end.

(* NB, this does not work:
Ltac float_let :=
  lazymatch goal with |-  context C [let x := ?rhs in ?body] =>
    let goal' := context C[body] in
    change (let x := rhs in goal'); intro
  end.
*)



(** ** Punted-on lemmas about GHC functions *)

Axiom isJoinId_eq : forall v,
  isJoinId v = match isJoinId_maybe v with | None => false |Some _ => true end.

Axiom isJoinId_isJoinId_maybe: forall v,
  isJoinId v = true ->
  isJoinId_maybe v = Some (idJoinArity v).

Axiom isJoinId_maybe_uniqAway:
  forall s v, 
  isJoinId_maybe (uniqAway s v) = isJoinId_maybe v.

Axiom isJoinId_maybe_setIdOccInfo:
  forall v occ_info, 
  isJoinId_maybe (setIdOccInfo v occ_info) = isJoinId_maybe v.

Axiom isJoinId_maybe_asJoinId:
  forall v a,
  isJoinId_maybe (asJoinId v a) = Some a.

Axiom dVarSet_freeVarsOf_Ann:
  (* @lastland, this is one spec that you might want to do *)
  forall ann_e, dVarSetToVarSet (freeVarsOf ann_e) = exprFreeVars (deAnnotate ann_e).

Axiom extendVarSetList_cons:
  forall s v vs,
  extendVarSetList s (v :: vs) = extendVarSetList (extendVarSet s v) vs.

Axiom isJoinPointValidPair_extendVarSet:
  forall v rhs jps v',
  isJoinPointsValidPair v rhs jps = true ->
  isJoinPointsValidPair v rhs (extendVarSet jps v') = true.

Axiom forallb_imp:
  forall a P Q (xs : list a),
  forallb P xs = true ->
  (forall x, P x = true -> Q x = true) ->
  forallb Q xs = true.


(* This section reflects the context of the local definition of exitify *)
Section in_exitify.
  (* Parameters of exitify *)
  Variable in_scope : InScopeSet.
  Variable pairs : list (Var * CoreExpr).

  (* Parameters and assumptions of the proof *)
  Variable jps : VarSet.
  
  (* Local function of exitify. Automation here would be great! 
     We can use Ltac to get the outermost let.
   *)
  Definition recursive_calls := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope pairs) in
    lazymatch rhs with | (let x := ?rhs in ?body) => 
      exact rhs
    end).

  Definition go := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope pairs) in
    lazymatch rhs with | (let x := _ in let y := @?rhs x in _) => 
      let def := eval cbv beta in (rhs recursive_calls) in
      exact def
    end).

  Definition ann_pairs := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope pairs) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let y := ?rhs in _) => 
      exact rhs
    end).

  Definition pairs'_exits := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope pairs) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let '(pairs',exits) := @?rhs x2 x3 in ?body) => 
      let def := eval cbv beta in (rhs go ann_pairs) in
      exact def
    end).
  Definition pairs' := fst pairs'_exits.
  Definition exits := snd pairs'_exits.
  
  Definition mkExitLets := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope pairs) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let '(pairs',exits) := _ in let y := ?rhs in ?body) => 
      exact rhs
    end).
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

  Axiom unsafe_deferredFix2_eq: forall {a b c} `{GHC.Err.Default c} (f : (a -> b -> c) -> (a -> b -> c)),
    forall x y, DeferredFix.deferredFix2 f x y = f (DeferredFix.deferredFix2 f) x y.

  Definition go_f := ltac:(
    let rhs := eval cbv delta [go] in go in
    lazymatch rhs with
      | @DeferredFix.deferredFix2 ?a ?b ?r ?HDefault ?f =>
      exact f
    end).

  Lemma go_eq : forall x y, go x y = go_f go x y.
  Proof. apply unsafe_deferredFix2_eq. Qed.

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
    rewrite go_eq.
    cbv beta delta [go_f]. (* No [zeta]! *)
    (* Float out lets *)
    repeat float_let.

    (* First case *)
    enough (Hnext: StateInvariant P j_37__). {
      destruct (collectArgs e) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId i && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
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
    ja = Z.of_nat (length args) ->
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
        + replace (Z.of_nat (length (a :: args))) with (1 + Z.of_nat (length args)) by admit.
          destruct (Z.eqb_spec (1 + Z.of_nat (length args)) 0); only 1: lia.
          replace (mkLams (a :: args) e) with (Lam a (mkLams args e)) by reflexivity.
          cbn -[Z.add].
          destruct (Z.ltb_spec (1 + Z.of_nat (length args)) 1); only 1: lia.
          replace (1 + Z.of_nat (length args) =? 1) with (Z.of_nat (length args) =? 0) by admit.
          replace (1 + Z.of_nat (length args) - 1) with (Z.of_nat (length args)) by admit.
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
    rewrite go_eq.
    cbv beta delta [go_f]. (* No [zeta]! *)
    (* Float out lets *)
    repeat float_let.

    (* First case *)
    enough (Hnext: StateInvariant P j_37__). {
      destruct (collectArgs e) as [rhs fun_args] eqn:HcA.
      destruct rhs; try apply Hnext.
      destruct (isJoinId i && Foldable.all isCapturedVarArg fun_args) ; try apply Hnext.
      apply StateInvariant_return.
    }
    clear isCapturedVarArg.

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

  Theorem exitify_JPI:
    forall body,
    pairs <> [] ->
    isJoinPointsValid (Let (Rec pairs) body) 0 jps = true ->
    isJoinPointsValid (exitify in_scope pairs body) 0 jps = true.
  Proof.
    intros.
    cbv beta delta [exitify].
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

End in_exitify.