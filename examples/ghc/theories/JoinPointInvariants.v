
Require Import Id.
Require Import Core.
Require Import BasicTypes.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Psatz.

Import ListNotations.

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

Additionally, we have the invariant:

 * The join arity must be non-negative.
*)


Definition isJoinPointsValidPair_aux
  isJoinPointsValid isJoinRHS
  (v : CoreBndr) (rhs : CoreExpr) (jps : VarSet) : bool :=
    match isJoinId_maybe v with
    | None => isJoinPointsValid rhs 0 emptyVarSet  (* Non-tail-call position *)
    | Some a => 
      if a =? 0 (* Uh, all for the termination checker *)
      then isJoinPointsValid rhs 0 jps (* tail-call position *)
      else isJoinRHS a rhs jps                   (* tail-call position *)
    end.


Fixpoint isJoinPointsValid (e : CoreExpr) (n : Z) (jps : VarSet) {struct e} : bool :=
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
    isJoinPointsValid e 0 emptyVarSet     (* Non-tail-call position *)
  | Let (NonRec v rhs) body => 
      isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS v rhs jps &&
      let jps' := if isJoinId v
                  then extendVarSet jps v
                  else delVarSet    jps v in
      isJoinPointsValid body 0 jps'
  | Let (Rec pairs) body => 
      negb (List.null pairs) &&  (* Not join-point-specific, could be its own invariant *)
      (forallb (fun p => negb (isJoinId (fst p))) pairs ||
       forallb (fun p =>       isJoinId (fst p))  pairs) &&
      let jps' := if forallb (fun p => isJoinId (fst p)) pairs 
                  then extendVarSetList jps (map fst pairs)
                  else delVarSetList    jps (map fst pairs) in
      forallb (fun '(v,e) => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS v e jps') pairs &&
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
                 then isJoinPointsValid e 0 (delVarSet jps v) (* tail-call position *)
                 else isJoinRHS (a-1) e (delVarSet jps v)
    | _ => false
    end.

Definition isJoinPointsValidPair := isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS.
    
    
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
