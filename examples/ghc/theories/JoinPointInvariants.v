Require Import Id.
Require Import Core.
Require Import BasicTypes.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.
Require Import Psatz.

Import ListNotations.

Require Import Proofs.Forall.
Require Import Proofs.Core.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.GhcTactics.

Set Bullet Behavior "Strict Subproofs".

Open Scope nat_scope.

Notation "a =? b" := (Nat.eqb a b).
Notation "a <=? b" := (Nat.leb a b).
Notation "a <? b" := (Nat.ltb a b).

(*
Note [Invariants on join points]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Join points must follow these invariants:

  1. All occurrences must be tail calls. Each of these tail calls must pass the
     same number of arguments, counting both types and values; we call this the
     "join arity" (to distinguish from regular arity, which only counts values).

  2. For join arity n, the right-hand side must begin with at least n lambdas.
     No ticks, no casts, just lambdas!  C.f. CoreUtils.joinRhsArity.

  2a. Moreover, this same constraint applies to any unfolding of the binder.
     Reason: if we want to push a continuation into the RHS we must push it
     into the unfolding as well.

  3. If the binding is recursive, then all other bindings in the recursive group
     must also be join points.

  4. The binding's type must not be polymorphic in its return type (as defined
     in Note [The polymorphism rule of join points]).
*)

(* We can check 1, 2, 3.

We will be able to check 2a when we translate more of IdInfo.

We will be able to check 4 when we translate types.

Additionally, we have the invariant:

 * The join arity must be non-negative.
 * A lambda-, case- or pattern-bound variable is not a join point
*)


Definition isJoinPointsValidPair_aux
  isJoinPointsValid isJoinRHS_aux
  (v : CoreBndr) (rhs : CoreExpr) (jps : VarSet) : bool :=
    match isJoinId_maybe v with
    | None => isJoinPointsValid rhs 0 emptyVarSet  (* Non-tail-call position *)
    | Some a => 
      if (a =? 0) (* Uh, all for the termination checker *)
      then isJoinPointsValid rhs 0 jps (* tail-call position *)
      else isJoinRHS_aux a rhs jps                   (* tail-call position *)
    end.

Definition updJPS jps v :=
   if isJoinId v
   then extendVarSet jps v
   else delVarSet    jps v.

Definition updJPSs jps vs :=
  fold_left updJPS vs jps.

Lemma updJPSs_nil:
  forall jps, updJPSs jps [] = jps.
Proof. intros. reflexivity. Qed.

Lemma updJPSs_cons:
  forall jps v vs, updJPSs jps (v :: vs) = updJPSs (updJPS jps v) vs.
Proof. intros. reflexivity. Qed.

Lemma updJPSs_append:
  forall jps vs1 vs2, updJPSs jps (vs1 ++ vs2) = updJPSs (updJPSs jps vs1) vs2.
Proof. intros. apply fold_left_app. Qed.

Lemma updJPS_not_joinId:
  forall jps v,
  isJoinId v = false ->
  updJPS jps v = delVarSet jps v.
Proof. intros. unfold updJPS. rewrite H. reflexivity. Qed.

Lemma updJPS_joinId:
  forall jps v,
  isJoinId v = true ->
  updJPS jps v = extendVarSet jps v.
Proof. intros. unfold updJPS. rewrite H. reflexivity. Qed.

Lemma updJPSs_not_joinId:
  forall jps vs,
  forallb (fun v => negb (isJoinId v)) vs = true ->
  updJPSs jps vs = delVarSetList jps vs.
Proof. 
  intros. induction vs using rev_ind.
  * rewrite delVarSetList_nil. reflexivity.
  * rewrite updJPSs_append, updJPSs_cons, updJPSs_nil.
    rewrite delVarSetList_app, delVarSetList_cons, delVarSetList_nil.
    rewrite forallb_app in H. simpl in H. rewrite andb_true_r, andb_true_iff, negb_true_iff in H. 
    rewrite IHvs by intuition.
    rewrite updJPS_not_joinId by intuition.
    reflexivity.
Qed.

Lemma updJPSs_joinId:
  forall jps vs,
  forallb isJoinId vs = true ->
  updJPSs jps vs = extendVarSetList jps vs.
Proof. 
  intros. induction vs using rev_ind.
  * rewrite extendVarSetList_nil. reflexivity.
  * rewrite updJPSs_append, updJPSs_cons, updJPSs_nil.
    rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
    rewrite forallb_app in H. simpl in H. rewrite andb_true_r, andb_true_iff in H. 
    rewrite IHvs by intuition.
    rewrite updJPS_joinId by intuition.
    reflexivity.
Qed.


Lemma elemVarSet_updJPSs_l:
  forall v jps vs,
  elemVarSet v jps  = true  ->
  elemVarSet v (mkVarSet vs) = false ->
  elemVarSet v (updJPSs jps vs) = true .
Admitted.


Lemma subVarSet_updJPS_extendVarSet:
  forall jps isvs v,
  subVarSet jps isvs = true ->
  subVarSet (updJPS jps v) (extendVarSet isvs v) = true.
Admitted.

Lemma subVarSet_updJPSs_extendVarSetList:
  forall jps isvs vs,
  subVarSet jps isvs = true ->
  subVarSet (updJPSs jps vs) (extendVarSetList isvs vs) = true.
Admitted.

Lemma subVarSet_delVarSet_extendVarSet:
  forall jps isvs v,
  subVarSet jps isvs = true ->
  subVarSet (delVarSet jps v) (extendVarSet isvs v) = true.
Admitted.

Lemma subVarSet_delVarSetList_extendVarSetList:
  forall jps isvs vs,
  subVarSet jps isvs = true ->
  subVarSet (delVarSetList jps vs) (extendVarSetList isvs vs) = true.
Admitted.




Fixpoint isJoinPointsValid (e : CoreExpr) (n : nat) (jps : VarSet) {struct e} : bool :=
  match e with
  | Mk_Var v => match isJoinId_maybe v with
    | None => true
    | Some a => (a <=? n) && elemVarSet v jps
    end
  | Lit l => true
  | App e1 e2 =>
    isJoinPointsValid e1 (n+1) jps &&   (* Tail-call-position *)
    isJoinPointsValid e2 0 emptyVarSet    (* Non-tail-call position *)
  | Lam v e =>
    negb (isJoinId v) &&
    isJoinPointsValid e 0 emptyVarSet     (* Non-tail-call position *)
  | Let (NonRec v rhs) body => 
      isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v rhs jps &&
      let jps' := updJPS jps v in
      isJoinPointsValid body 0 jps'
  | Let (Rec pairs) body => 
      negb (List.null pairs) &&  (* Not join-point-specific, could be its own invariant *)
      (forallb (fun p => negb (isJoinId (fst p))) pairs ||
       forallb (fun p =>       isJoinId (fst p))  pairs) &&
      let jps' := updJPSs jps (map fst pairs) in
      forallb (fun '(v,e) => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v e jps') pairs &&
      isJoinPointsValid body 0 jps'
  | Case scrut bndr ty alts  => 
    negb (isJoinId bndr) &&
    isJoinPointsValid scrut 0 emptyVarSet &&  (* Non-tail-call position *)
    let jps' := delVarSet jps bndr in
    forallb (fun '(dc,pats,rhs) =>
      let jps'' := delVarSetList jps' pats  in
      forallb (fun v => negb (isJoinId v)) pats &&
      isJoinPointsValid rhs 0 jps'') alts  (* Tail-call position *)
  | Cast e _ =>    isJoinPointsValid e 0 jps
  | Tick _ e =>    isJoinPointsValid e 0 jps
  | Type_ _  =>   true
  | Coercion _ => true
  end
with isJoinRHS_aux (a : JoinArity) (rhs : CoreExpr) (jps : VarSet) {struct rhs} : bool :=
  if a <? 1 then false else
  match rhs with
    | Lam v e => negb (isJoinId v) &&
                 if a =? 1
                 then isJoinPointsValid e 0 (delVarSet jps v) (* tail-call position *)
                 else isJoinRHS_aux (a-1) e (delVarSet jps v)
    | _ => false
    end.

Definition isjoinPointsAlt : CoreAlt -> VarSet -> bool :=
  fun '(dc,pats,rhs) jps =>
      let jps'' := delVarSetList jps pats  in
      forallb (fun v => negb (isJoinId v)) pats &&
      isJoinPointsValid rhs 0 jps''.

Definition isJoinPointsValidPair := isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux.

(* Top-level binders are never join-points *)
Definition isJoinPointsValidProgram (pgm : CoreProgram)  :=
  Forall (fun '(v,e) =>
    isJoinId v = false /\
    isJoinPointsValid e 0 emptyVarSet = true) (flattenBinds pgm).

Lemma isJoinPointsValid_more_args:
  forall e n n' jps,
  n <= n' ->
  isJoinPointsValid e n jps = true ->
  isJoinPointsValid e n' jps = true.
Admitted.

(* Conjuction of [isJoinId] and [isJoinPointsValidPair] *)

Definition isJoinRHS rhs a jps :=
      if (a =? 0)
      then isJoinPointsValid rhs 0 jps
      else isJoinRHS_aux a rhs jps.

Definition isValidJoinPointsPair
  (v : CoreBndr) (rhs : CoreExpr) (jps : VarSet) : bool :=
    match isJoinId_maybe v with
    | None => false (* NB *)
    | Some a => isJoinRHS rhs a jps
    end.


Lemma isJoinPointsValidPair_isJoinPoints_isJoinRHS:
  forall v rhs jps a,
  isJoinPointsValidPair v rhs jps = true ->
  isJoinId_maybe v = Some a ->
  isJoinRHS rhs a jps = true.
Proof.
  intros.
  unfold isJoinPointsValidPair,isJoinPointsValidPair_aux in H.
  rewrite H0 in H.
  apply H.
Qed.

Lemma isJoinPointsValidPair_isJoinRHS:
  forall v rhs jps a,
  isJoinId_maybe v = Some a ->
  isJoinPointsValidPair v rhs jps = true <->
  isJoinRHS rhs a jps = true.
Proof.
  intros.
  unfold isJoinPointsValidPair,isJoinPointsValidPair_aux.
  rewrite H.
  unfold isJoinRHS.
  reflexivity.
Qed.

Lemma isJoinPointsValidPair_isJoinPointsValid:
  forall v rhs jps,
  isJoinId_maybe v = None ->
  isJoinPointsValidPair v rhs jps = true <->
  isJoinPointsValid rhs 0 emptyVarSet = true.
Proof.
  intros.
  unfold isJoinPointsValidPair,isJoinPointsValidPair_aux.
  rewrite H.
  unfold isJoinRHS.
  reflexivity.
Qed.



Lemma isValidJoinPointsPair_isJoinPointsValidPair:
  forall v rhs jps,
  isValidJoinPointsPair v rhs jps = true -> isJoinPointsValidPair v rhs jps = true.
Proof.
  intros.
  unfold isValidJoinPointsPair, isJoinPointsValidPair, isJoinPointsValidPair_aux in *.
  destruct_match.
  * assumption.
  * congruence.
Qed.

Lemma isValidJoinPointsPair_isJoinId:
  forall v rhs jps,
  isValidJoinPointsPair v rhs jps = true -> isJoinId v = true.
Proof.
  intros.
  unfold isValidJoinPointsPair in *.
  rewrite isJoinId_eq.
  destruct_match; congruence.
Qed.

Lemma Forall_isValidJoinPointsPair_forallb_isJoinId_isJoinPointsValidPair:
  forall pairs jps,
  Forall (fun p => isValidJoinPointsPair (fst p) (snd p) jps = true) pairs <->
  forallb (fun p : Var * Expr CoreBndr => isJoinId (fst p)) pairs = true /\
  forallb (fun '(v, e) => isJoinPointsValidPair v e jps) pairs = true.
Proof.
  intros.
  rewrite Forall_forall, !forallb_forall.
  split; intro; only 1: split.
  * intros [v e] HIn.
    specialize (H _ HIn).
    simpl in *.
    eapply isValidJoinPointsPair_isJoinId; eassumption.
  * intros [v e] HIn.
    specialize (H _ HIn).
    simpl in *.
    eapply isValidJoinPointsPair_isJoinPointsValidPair; eassumption.
  * intros [v e] HIn.
    destruct H.
    specialize (H _ HIn).
    specialize (H0 _ HIn).
    simpl in *.
    unfold isValidJoinPointsPair in *.
    rewrite isJoinId_eq in H.
    destruct_match; auto.
    eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS; eassumption.
Qed.

Lemma isJoinPointsValid_subVarSet:
  forall e jps1 jps2,
  subVarSet jps1 jps2 = true ->
  isJoinPointsValid e 0 jps1 = true ->
  isJoinPointsValid e 0 jps2 = true.
Admitted.

Lemma isJoinRHS_mkLams:
  forall vs e jps,
  Forall (fun v => isJoinId v = false) vs ->
  isJoinPointsValid e 0 (delVarSetList jps vs) = true <->
  isJoinRHS (mkLams vs e) (length vs) jps = true.
Proof.
  intros. revert jps H.
  induction vs; intros jps Hdisjoint.
  * rewrite delVarSetList_nil.
    reflexivity.
  * simpl.
    replace (mkLams _ _) with (Lam a (mkLams vs e)) by reflexivity.
    rewrite delVarSetList_cons.
    unfold isJoinRHS.
    destruct_match.
    + apply EqNat.beq_nat_true in Heq. congruence.
    + clear Heq.
      inversion_clear Hdisjoint.
      rewrite IHvs by assumption.
      simpl.
      rewrite PeanoNat.Nat.sub_0_r.
      unfold isJoinRHS.
      rewrite H.
      reflexivity.
Qed.

Lemma isJoinRHS_mkLams2:
  forall vs e jps,
  isJoinRHS (mkLams vs e) (length vs) jps = true ->
  Forall (fun v => isJoinId v = false) vs /\ isJoinPointsValid e 0 (updJPSs jps vs) = true.
Proof.
  intros. revert jps H.
  induction vs; intros jps H.
  * rewrite updJPSs_nil.
    intuition.
  * simpl.
    replace (mkLams _ _) with (Lam a (mkLams vs e)) in H by reflexivity.
    unfold isJoinRHS in H.
    destruct_match.
    + apply EqNat.beq_nat_true in Heq. simpl in Heq. congruence.
    + clear Heq.
      simpl in H.
      rewrite PeanoNat.Nat.sub_0_r in H.
      rewrite andb_true_iff, negb_true_iff in H.
      destruct H as [Hnot_isJoin H].
      change (isJoinRHS (mkLams vs e) (length vs) (delVarSet jps a) = true) in H.
      specialize (IHvs _ H).
      unfold updJPS. rewrite Hnot_isJoin.
      intuition.
Qed.

Lemma isJoinRHS_mkLams3:
  forall e ja jps,
  isJoinRHS e ja jps = true ->
  exists body vs,
  e = mkLams vs body /\ ja = length vs.
Proof.
  intros. revert e jps H. induction ja; intros.
  * exists e. exists nil.
    repeat apply conj.
    + reflexivity.
    + reflexivity.
  * unfold isJoinRHS in H.
    destruct (PeanoNat.Nat.eqb_spec (S ja) 0); only 1: (exfalso; lia). clear n.
    destruct e; simpl in H; try congruence.
    simpl_bool.
    destruct H as [HnotJoinId H].
    rewrite negb_true_iff in HnotJoinId.
    rewrite PeanoNat.Nat.sub_0_r in H.
    change (isJoinRHS e ja (delVarSet jps c) = true) in H.
    specialize (IHja _ _ H).
    destruct IHja as [body [vs [Heq1 Heq2]]].
    subst.
    exists body. exists (c :: vs).
    repeat apply conj.
    + reflexivity.
    + reflexivity.
Qed.

Lemma isJoinPointsValid_mkVarApps:
  forall e n vs jps,
  Forall (fun v => isJoinId v = false) vs ->
  isJoinPointsValid e (n + length vs) jps = true ->
  isJoinPointsValid (mkVarApps e vs) n jps = true.
Proof.
  intros ???? Hnot_iJI HiJPV.
  unfold mkVarApps.
  rewrite Foldable.hs_coq_foldl_list.
  revert e HiJPV.
  induction Hnot_iJI; intros.
  * simpl.
    simpl in HiJPV. rewrite PeanoNat.Nat.add_0_r in HiJPV.
    assumption.
  * simpl.
    apply IHHnot_iJI; clear IHHnot_iJI.
    simpl.
    rewrite andb_true_iff. split.
    - simpl in HiJPV.
      replace (_ + _ + _) with (n + S (length l)) by lia. 
      assumption.
    - unfold varToCoreExpr.
      repeat destruct_match; try reflexivity.
      simpl. rewrite isJoinId_eq in H.
      destruct_match; congruence.
Qed.

Lemma isJoinPointsValid_MkLetRec: forall pairs body jps,
  isJoinPointsValid (mkLetRec pairs body) 0 jps = true <->
  ( (forallb (fun p => negb (isJoinId (fst p))) pairs ||
     forallb (fun p =>       isJoinId (fst p))  pairs) &&
     let jps' := updJPSs jps (map fst pairs) in
     forallb (fun '(v,e) => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v e jps') pairs &&
     isJoinPointsValid body 0 jps'
  ) = true.
Proof.
  intros.
  unfold mkLetRec.
  destruct pairs; try reflexivity.
Qed.

Lemma isJoinPointsValid_MkLet_Rec: forall pairs body jps,
  isJoinPointsValid (mkLet (Rec pairs) body) 0 jps = true <->
  ( (forallb (fun p => negb (isJoinId (fst p))) pairs ||
     forallb (fun p =>       isJoinId (fst p))  pairs) &&
     let jps' := updJPSs jps (map fst pairs) in
     forallb (fun '(v,e) => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v e jps') pairs &&
     isJoinPointsValid body 0 jps'
  ) = true.
Proof.
  intros.
  destruct pairs; try reflexivity.
Qed.



Require Import CoreFVs.

(* There is some worrying duplication/similarity with
[WellScoped_extendVarSetList_fresh_between] *)
Lemma isJoinPointsValid_fresh_updJPSs:
  forall (vs2 vs3 : list Var) (e : CoreExpr) (jps : VarSet),
  disjointVarSet (delVarSetList (exprFreeVars e) vs3) (mkVarSet vs2) = true ->
  isJoinPointsValid e 0 (updJPSs jps (vs2 ++ vs3)) =
  isJoinPointsValid e 0 (updJPSs jps vs3).
Admitted.


Lemma isJoinPointsValid_fresh_between:
  forall (vs1 vs2 vs3 : list Var) (e : CoreExpr) (jps : VarSet),
  disjointVarSet (delVarSetList (exprFreeVars e) vs3) (mkVarSet vs2) = true ->
  isJoinPointsValid e 0 (updJPSs jps ((vs1 ++ vs2) ++ vs3)) =
  isJoinPointsValid e 0 (updJPSs jps (vs1 ++ vs3)).
Admitted.

(* I had to do two things to make this pass the termination checker that I would
   have done differently otherwise:
    - isJoinRHS is structured so that *always* destructs the expression,
      and calls isJoinPointsValid on the subexpression.
      This requires some duplication, namely checking the case a=0 in 
      isJoinPointsValidPair.
      Normally, I would count down a, and if a=0, call isJoinPointsValid on rhs,
      which is more natural.
    - isJoinPointsValidPair does not actually recurse, so it cannot be one
      of the top-level recursive functions. Instead, it is a local let and
      I repeat the defininition later to give it a name.
*)

Lemma StrongSubset_updJPSs:
  forall (vs3 : list Var) (vs1 vs2 : VarSet),
  StrongSubset vs1 vs2 ->
  StrongSubset (updJPSs vs1 vs3) (updJPSs vs2 vs3).
Admitted.


Lemma StrongSubset_updJPS_fresh :
  forall vs v,
  elemVarSet v vs = false ->
  StrongSubset vs (updJPS vs v).
Admitted.

Lemma StrongSubset_updJPSs_fresh :
  forall vs vs2,
  disjointVarSet vs (mkVarSet vs2) = true ->
  StrongSubset vs (updJPSs vs vs2).
Admitted.



Instance Respects_StrongSubset_isJoinPointsValid e n : Respects_StrongSubset (fun jps => isJoinPointsValid e n jps = true).
Proof.
  admit.
Admitted.

Instance Respects_StrongSubset_isValidJoinPointsPair x e : Respects_StrongSubset (fun jps => isValidJoinPointsPair x e jps = true).
Proof.
  admit.
Admitted.