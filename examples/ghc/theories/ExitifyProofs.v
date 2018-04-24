Require Import GHC.Base.

Require Import Exitify.
Require Import CoreSyn.
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



(** ** Punted-on lemmas about GHC functions *)

Axiom isJoinId_eq : forall v,
  isJoinId v = match isJoinId_maybe v with | None => false |Some _ => true end.

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

Definition StateInvariant {a} {s} (P : s -> Prop) (act : State.State s a) :=
  forall s, P s -> P (snd (State.runState act s)).

Lemma StateInvariant_return:
  forall {a s} (P : s -> Prop) (x : a),
  StateInvariant P (return_ x).
Proof.
  intros.
  intros s0 H. apply H.
Qed.

Lemma StateInvariant_bind:
  forall {a b s} P (act1 : State.State s a) (act2 : a -> State.State s b),
  StateInvariant P act1 ->
  (forall x, StateInvariant P (act2 x)) ->
  StateInvariant P (act1 >>= act2).
Proof.
  intros ?????? H1 H2.
  intros s0 H.
  unfold State.runState.
  expand_pairs; simpl.
  expand_pairs; simpl.
  enough (P (snd (State.runState (act2 (fst (State.runState act1 s0))) (snd (State.runState act1 s0))))) by admit.
  eapply H2.
  eapply H1.
  assumption.
Admitted.

Lemma StateInvariant_bind_return: (*  acommon pattern *)
  forall {a b s} P (act1 : State.State s a) (f : a -> b),
  StateInvariant P act1 ->
  StateInvariant P (act1 >>= (fun x => return_ (f x))).
Proof.
  intros.
  apply StateInvariant_bind.
  * apply H.
  * intro. apply StateInvariant_return.
Qed.

Lemma StateInvariant_forM:
  forall {a b s} P (act : a -> State.State s b) (xs : list a),
  (forall x, In x xs -> StateInvariant P (act x)) ->
  StateInvariant P (Traversable.forM xs act).
Proof.
  intros ?????? Hact.
  induction xs.
  * intros s0 H. apply H.
  * admit.
Admitted.

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
  Admitted.

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
    repeat lazymatch goal with | |- StateInvariant ?P ((let x := ?rhs in ?body) ?a ?b ?c) =>
      change (let x := rhs in StateInvariant P (body a b c)); intro
    end.
    cbv beta. (* Do some beta reduction *)
    (* Flout out more lets *)
    repeat lazymatch goal with | |- StateInvariant ?P ((let x := ?rhs in ?body)) =>
      change (let x := rhs in StateInvariant P body); intro
    end.

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
        (* Flout out more lets *)
        repeat lazymatch goal with | |- StateInvariant ?P ((let x := ?rhs in ?body)) =>
          change (let x := rhs in StateInvariant P body); intro
        end.

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
              cbv zeta.
              destruct (collectNAnnBndrs (idJoinArity j) rhs) as [params join_body].
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
    apply StateInvariant_forM.
    * intros [v rhs] HIn.
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
    * admit.
    * admit.
  Admitted.

End in_exitify.