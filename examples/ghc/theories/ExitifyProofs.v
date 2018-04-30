Require Import GHC.Base.
Require Import Id.
Require Import Exitify.
Require Import Core.


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

Axiom isJoinId_uniqAway:
  forall s v, 
  isJoinId (uniqAway s v) = isJoinId v.

Axiom isJoinId_setIdOccInfo:
  forall v occ_info, 
  isJoinId (setIdOccInfo v occ_info) = isJoinId v.

Axiom isJoinId_asJoinId:
  forall v a,
  isJoinId (asJoinId v a) = true.

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
    lazymatch rhs with | (let x := _ in let y := ?rhs in ?body) => 
      exact (let x := recursive_calls in rhs)
    end).

  Definition ann_pairs := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope pairs) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let y := ?rhs in ?body) => 
      let def := constr:(let x1 := recursive_calls in let x2 := go in rhs) in
      exact def
    end).

  Definition pairs'_exits := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope pairs) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let '(pairs',exits) := ?rhs in ?body) => 
      let def := constr:(let x1 := recursive_calls in let x2 := go in let x3 := ann_pairs in rhs) in
      exact def
    end).
  Definition pairs' := fst pairs'_exits.
  Definition exits := snd pairs'_exits.
  
  Definition mkExitLets := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope pairs) in
    lazymatch rhs with | (let x1 := _ in let x2 := _ in let x3 := _ in let '(pairs',exits) := _ in let y := ?rhs in ?body) => 
      let def := constr:(rhs) in (* Aha, we only have to abstract over the actually captured variables here. *)
      exact def
    end).
  (** When is the result of [mkExitLets] valid? *)
  
  Lemma mkExitLets_JPI:
    forall exits' e jps',
    isJoinPointsValid e 0 (extendVarSetList jps' (map fst exits')) = true ->
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
        + rewrite HiJIv. rewrite extendVarSetList_cons in Hbase. assumption.
        + assumption.
        + rewrite HiJIv.
          eapply forallb_imp. apply Hpairs.
          intros [v' rhs'].
          apply isJoinPointValidPair_extendVarSet.
  Qed.

  Axiom unsafe_deferredFix2_eq: forall {a b c} `{GHC.Err.Default c} (f : (a -> b -> c) -> (a -> b -> c)),
    forall x y, DeferredFix.deferredFix2 f x y = f (DeferredFix.deferredFix2 f) x y.

  Definition go_f := ltac:(
    let rhs := eval cbv delta [go] in go in
    lazymatch rhs with
      | let x := recursive_calls in  @DeferredFix.deferredFix2 ?a ?b ?r ?HDefault ?f =>
      let f' := constr:(let x := recursive_calls in f) in
      exact f'
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
        rewrite isJoinId_uniqAway.
        rewrite isJoinId_setIdOccInfo.
        apply isJoinId_asJoinId.
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
    cbv delta [go_f]. (* No [zeta]! *)
    (* Float out lets *)
    float_let. cbv beta. repeat float_let.

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
      apply StateInvariant_bind.
      + apply go_all_joinIds.
      + intro x.
        apply StateInvariant_return.
    * reflexivity.
  Qed.

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
    * admit.
  Admitted.

End in_exitify.
