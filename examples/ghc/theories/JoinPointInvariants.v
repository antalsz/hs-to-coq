Require Import CoreSyn.
Require Import Id.
Require Import IdInfo.
Require Import VarSet.
Require Import BasicTypes.

Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.

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
    JoinPointsValid (Let (Rec pairs) body) n jps'
  | JPV_LetRecJP  : forall pairs body n jps, 
    (forall v rhs, In (v,rhs) pairs -> isJoinId v = true) ->
    let jps' := extendVarSetList jps (map fst pairs) in
    (forall v rhs a, In (v,rhs) pairs ->
                     isJoinId_maybe v = Some a ->
                     GoodJoinRHS a rhs jps')  -> (* Non-tail-call position *)
    JoinPointsValid body 0 jps' ->     (* Tail-call-position *)
    JoinPointsValid (Let (Rec pairs) body) n jps'
  | JPV_Case  : forall scrut bndr ty alts n jps, 
    JoinPointsValid scrut 0 jps ->
    let jps' := delVarSet jps bndr in
    (forall dc pats rhs, In (dc,pats,rhs) alts ->
                         let jps' := delVarSetList jps pats in
                         JoinPointsValid rhs 0 jps')  -> (* Tail-call position *)
    JoinPointsValid (Case scrut bndr ty alts) n jps'
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
