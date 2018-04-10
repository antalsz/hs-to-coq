Require Import CoreSyn.
Require Import Id.
Require Import IdInfo.
Require Import VarSet.
Require Import BasicTypes.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

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
*)


(* Attempt one: An inductive predicate *)
Inductive JoinPointsValid : CoreExpr -> Z -> VarSet -> Prop :=
  | JPV_Var     : forall v n jps,
    isJoinId v = false ->
    JoinPointsValid (Var v) n jps
  | JPV_JoinVar : forall v a n jps,
    isJoinId_maybe v = Some a ->
    a <= n ->
    elemVarSet v jps = true ->
    JoinPointsValid (Var v) n jps
  | JPV_List    : forall l n jps, JoinPointsValid (Lit l) n jps
  | JPV_App     : forall e1 e2 n jps,
    JoinPointsValid e1 (n+1) jps ->     (* Tail-call-position *)
    JoinPointsValid e2 0 emptyVarSet -> (* Non-tail-call position *)
    JoinPointsValid (App e1 e2) n jps
  | JPV_Lam     : forall v e n jps,
    JoinPointsValid e 0 emptyVarSet -> (* Non-tail-call position *)
    JoinPointsValid (Lam v e) n jps
  | JPV_LetNonRec  : forall v rhs body n jps, 
    isJoinId v = false ->
    JoinPointsValid rhs 0 emptyVarSet ->            (* Non-tail-call position *)
    JoinPointsValid body 0 (delVarSet jps v) ->     (* Tail-call-position *)
    JoinPointsValid (Let (NonRec v rhs) body) n jps
  | JPV_LetNonRecJP  : forall v a rhs body n jps, (* Shadowing *)
    isJoinId_maybe v = Some a ->
    GoodJoinRHS a rhs jps ->
    JoinPointsValid body 0 (extendVarSet jps v) ->     (* Tail-call-position *)
    JoinPointsValid (Let (NonRec v rhs) body) n jps
  | JPV_LetRec  : forall pairs body n jps,
    (forall v rhs, In (v,rhs) pairs -> isJoinId v = false) ->
    (forall v rhs, In (v,rhs) pairs -> JoinPointsValid rhs 0 emptyVarSet)  -> (* Non-tail-call position *)
    let jps' := delVarSetList jps (map fst pairs) in
    JoinPointsValid body 0 jps' ->     (* Tail-call-position *)
    JoinPointsValid (Let (Rec pairs) body) n jps
  | JPV_LetRecJP  : forall pairs body n jps, 
    (forall v rhs, In (v,rhs) pairs -> isJoinId v = true) ->
    let jps' := extendVarSetList jps (map fst pairs) in
    (forall v rhs a, In (v,rhs) pairs ->
                     isJoinId_maybe v = Some a ->
                     GoodJoinRHS a rhs jps')  -> (* Non-tail-call position *)
    JoinPointsValid body 0 jps' ->     (* Tail-call-position *)
    JoinPointsValid (Let (Rec pairs) body) n jps
  | JPV_Case  : forall scrut bndr ty alts n jps, 
    JoinPointsValid scrut 0 emptyVarSet -> (* Non-tail-call position *)
    let jps' := delVarSet jps bndr in
    (forall dc pats rhs, In (dc,pats,rhs) alts ->
                         let jps' := delVarSetList jps pats in
                         JoinPointsValid rhs 0 jps')  -> (* Tail-call position *)
    JoinPointsValid (Case scrut bndr ty alts) n jps
  | JPV_Cast  : forall e co n jps, 
    JoinPointsValid e 0 jps ->
    JoinPointsValid (Cast e co) n jps
  | JPV_Tick  : forall tickish e n jps, 
    JoinPointsValid e 0 jps ->
    JoinPointsValid (Tick tickish e) n jps
  | JPV_Type  : forall ty n jps, 
    JoinPointsValid (Type_ ty) n jps
  | JPV_Coercion  : forall co n jps, 
    JoinPointsValid (Coercion co) n jps
 with
  GoodJoinRHS : Z -> CoreExpr -> VarSet -> Prop :=
  | GJR_Lam : forall a v e jps,
    0 < a ->
    GoodJoinRHS (a - 1) e (delVarSet jps v) ->
    GoodJoinRHS a (Lam v e) jps
  | GJR_RHS: forall a e jps,
    a = 0 ->
    JoinPointsValid e 0 jps->     (* Tail-call-position *)
    GoodJoinRHS a e jps
  .

(* Attempt two: An executable checker *)
Fixpoint isJoinPointsValid (e : CoreExpr) (n : Z) (jps : VarSet) {struct e} : bool :=
  let isJoinPointsValidPair (v : CoreBndr) (rhs : CoreExpr) (jps : VarSet) : bool :=
    match isJoinId_maybe v with
    | None => isJoinPointsValid rhs 0 emptyVarSet  (* Non-tail-call position *)
    | Some a => 
      if a =? 0 (* Uh, all for the termination checker *)
      then isJoinPointsValid rhs 0 jps (* tail-call position *)
      else isJoinRHS a rhs jps                   (* tail-call position *)
    end
  in
  match e with
  | Var v => match isJoinId_maybe v with
    | None => true
    | Some a => a <=? n
    end
  | Lit l => true
  | App e1 e2 =>
    isJoinPointsValid e1 (n+1) jps &&   (* Tail-call-position *)
    isJoinPointsValid e2 0 emptyVarSet    (* Non-tail-call position *)
  | Lam v e =>
    isJoinPointsValid e 0 emptyVarSet     (* Non-tail-call position *)
  | Let (NonRec v rhs) body => 
      isJoinPointsValidPair v rhs jps &&
      let jps' := if isJoinId v
                  then extendVarSet jps v
                  else delVarSet    jps v in
      isJoinPointsValid body 0 jps'
  | Let (Rec pairs) body => 
      (forallb (fun p => negb (isJoinId (fst p))) pairs ||
       forallb (fun p =>       isJoinId (fst p))  pairs) &&
      let jps' := if forallb (fun p => isJoinId (fst p)) pairs 
                  then extendVarSetList jps (map fst pairs)
                  else delVarSetList    jps (map fst pairs) in
      forallb (fun '(v,e) => isJoinPointsValidPair v e jps') pairs &&
      isJoinPointsValid body 0 jps'
  | Case scrut bndr ty alts  => 
    isJoinPointsValid scrut 0 emptyVarSet &&  (* Non-tail-call position *)
    let jps' := delVarSet jps bndr in
    forallb (fun '(dc,pats,rhs) =>
      let jps' := delVarSetList jps pats in
      isJoinPointsValid rhs 0 jps') alts  (* Tail-call position *)
  | Cast e _ =>    isJoinPointsValid e 0 jps
  | Tick _ e =>    isJoinPointsValid e 0 jps
  | Type_ _  =>   true
  | Coercion _ => true
  end
with isJoinRHS (a : JoinArity) (rhs : CoreExpr) (jps : VarSet) {struct rhs} : bool :=
  if a <? 1 then false else
  match rhs with
    | Lam v e => if a =? 1
                 then isJoinPointsValid e 0 jps (* tail-call position *)
                 else isJoinRHS (a-1) e jps
    | _ => false
    end.

Definition isJoinPointsValidPair (v : CoreBndr) (rhs : CoreExpr) (jps : VarSet) : bool :=
    match isJoinId_maybe v with
    | None => isJoinPointsValid rhs 0 emptyVarSet  (* Non-tail-call position *)
    | Some a => 
      if a =? 0 (* Uh, all for the termination checker *)
      then isJoinPointsValid rhs 0 jps (* tail-call position *)
      else isJoinRHS a rhs jps                   (* tail-call position *)
    end.

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


(* Relating the two definitions (may not be needed or useful) *)


Scheme JPV_mut := Induction for JoinPointsValid Sort Prop
with GJR_mut := Induction for GoodJoinRHS Sort Prop.

Axiom isJoinId_eq : forall v,
  isJoinId v = match isJoinId_maybe v with | None => false |Some _ => true end.

Axiom delVarList_singleton: forall jps v,
  delVarSetList jps (v :: nil) = delVarSet jps v.

Axiom extendVarList_singleton: forall jps v,
  extendVarSetList jps (v :: nil) = extendVarSet jps v.

Lemma bindersOf_cleanup:
  forall {a b} (pairs : list (a * b)),
  flat_map (fun '(binder, _) => binder :: nil) pairs = map fst pairs.
Proof. intros.  induction pairs. reflexivity. destruct a0. simpl. rewrite IHpairs. reflexivity. Qed.

Lemma JoinPointsValid_isJoinPointsValid:
  forall e n jps,
  JoinPointsValid e n jps -> isJoinPointsValid e n jps = true.
Proof.
  eapply JPV_mut with
    (P0 := fun a rhs jps _ => 
      (if a =? 0
        then isJoinPointsValid rhs 0 jps 
        else isJoinRHS a rhs jps) = true);
  intros; simpl;
  rewrite ?isJoinId_eq in *;
  rewrite ?orb_true_iff, ?andb_true_iff in *;
  rewrite ?bindersOf_cleanup.
  * destruct (isJoinId_maybe v); congruence.
  * rewrite e, Z.leb_le. assumption.
  * reflexivity.
  * split; assumption.
  * assumption.
  * destruct (isJoinId_maybe v); inversion_clear e.
    split; assumption.
  * rewrite e in *; clear e.
    split; assumption.
  * split; only 2: split.
    - rewrite orb_true_iff. left.
      rewrite forallb_forall.
      intros [v rhs] HIn.
      erewrite e by eassumption.
      reflexivity.
    - rewrite forallb_forall.
      intros [v rhs] HIn.
      specialize (e _ _ HIn).
      rewrite isJoinId_eq in e.
      destruct (isJoinId_maybe v); inversion_clear e.
      specialize (H _ _ HIn).
      assumption.
    - rewrite ?orb_true_iff, ?andb_true_iff in *.
      admit. (* need to handle pairs = [] separately *)
      (*
      replace (forallb (fun p : Var.Var * Expr CoreBndr => isJoinId (fst p)) pairs) with false.
      assumption.
      symmetry.
      *)
  * assert (forallb (fun p : Var.Var * Expr CoreBndr => isJoinId (fst p)) pairs = true).
    { rewrite forallb_forall.
      intros [v rhs] HIn.
      erewrite e by eassumption.
      reflexivity. }
    rewrite H1. clear H1.
    split; only 2: split.
    - rewrite orb_true_iff. right.
      reflexivity.
    - rewrite forallb_forall.
      intros [v rhs] HIn.
      specialize (e _ _ HIn).
      rewrite isJoinId_eq in e.
      destruct (isJoinId_maybe v) eqn:HiJI; inversion_clear e.
      specialize (H _ _ _ HIn HiJI).
      assumption.
    - rewrite ?orb_true_iff, ?andb_true_iff in *.
      assumption.
Admitted.