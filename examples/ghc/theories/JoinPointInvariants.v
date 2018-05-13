Require Import Id.
Require Import Core.
Require Import BasicTypes.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.
Require Import Psatz.

Import ListNotations.

Require Import Forall.
Require Import CoreLemmas.

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

TODO are these invariants:

 * A lambda-, case- or pattern-bound variable is not a join point
*)



(** Invariant 2 is special: It is local (does not need a context),
    and it is crucial to make AST traversals, that use [collectNBinders],
    total. This means that many functions will have that as a precondition.
    So lets isolate that.
*)

Definition HasJoinLamsPair {v : Type} x (e : Expr v) :=
  match isJoinId_maybe x with
  | Some n => HasNLams n e
  | None   => True
  end.
  

Fixpoint HasJoinLams (e : CoreExpr) {struct e} : Prop :=
  match e with
  | Mk_Var v => True
  | Lit l => True
  | App e1 e2 => HasJoinLams e1 /\  HasJoinLams e2
  | Lam v e => HasJoinLams e
  | Let (NonRec v rhs) body => 
      HasJoinLamsPair v rhs /\ HasJoinLams rhs /\ HasJoinLams body
  | Let (Rec pairs) body => 
      Forall' (fun p => HasJoinLamsPair (fst p) (snd p)) pairs /\
      Forall' (fun p => HasJoinLams (snd p)) pairs /\
      HasJoinLams body
  | Case scrut bndr ty alts  => 
    HasJoinLams scrut /\
      Forall' (fun alt => HasJoinLams (snd alt)) alts
  | Cast e _ =>   HasJoinLams e
  | Tick _ e =>   HasJoinLams e
  | Type_ _  =>   True
  | Coercion _ => True
  end.

Definition AnnHasJoinLamsPair {a v : Type} (x : Id) (e : AnnExpr v a) :=
  match isJoinId_maybe x with
  | Some n => AnnHasNLams n e
  | None   => True
  end.


(* With AnnExpr, [Fixpoint] is too confused *)
Inductive AnnHasJoinLams {a : Type} : AnnExpr Id a -> Prop :=
  | AnnHasJoinLams_Var : forall fvs v,  AnnHasJoinLams (fvs, AnnVar v)
  | AnnHasJoinLams_Lit : forall fvs l,  AnnHasJoinLams (fvs, AnnLit l)
  | AnnHasJoinLams_App : forall fvs e1 e2,
      AnnHasJoinLams e1 -> AnnHasJoinLams e2 -> AnnHasJoinLams (fvs, AnnApp e1 e2)
  | AnnHasJoinLams_Lam : forall fvs v e,
      AnnHasJoinLams e -> AnnHasJoinLams (fvs, AnnLam v e)
  | AnnHasJoinLams_LetNonRec : forall fvs v rhs body,
      AnnHasJoinLamsPair v rhs ->
      AnnHasJoinLams rhs ->
      AnnHasJoinLams body ->
      AnnHasJoinLams (fvs, AnnLet (AnnNonRec v rhs) body)
  | AnnHasJoinLams_LetRec : forall fvs pairs body,
      Forall (fun p => AnnHasJoinLamsPair (fst p) (snd p)) pairs ->
      Forall (fun p => AnnHasJoinLams (snd p)) pairs ->
      AnnHasJoinLams body ->
      AnnHasJoinLams (fvs, AnnLet (AnnRec pairs) body)
  | AnnHasJoinLams_Case : forall fvs scrut bndr ty alts,
      AnnHasJoinLams scrut ->
      Forall (fun alt => AnnHasJoinLams (snd alt)) alts ->
      AnnHasJoinLams (fvs, AnnCase scrut bndr ty alts)
  | AnnHasJoinLams_Cast : forall fvs e co,
        AnnHasJoinLams e -> AnnHasJoinLams (fvs, AnnCast e co)
  | AnnHasJoinLams_Tick: forall fvs t e,
        AnnHasJoinLams e -> AnnHasJoinLams (fvs, AnnTick t e)
  | AnnHasJoinLams_Type :    forall fvs t,  AnnHasJoinLams (fvs, AnnType t)
  | AnnHasJoinLams_Coercion: forall fvs co, AnnHasJoinLams (fvs, AnnCoercion co)
  .


Lemma HasJoinLams_deAnnotate:
  forall { a : Type} (e : AnnExpr Id a),
  HasJoinLams (deAnnotate e) <-> AnnHasJoinLams e.
Admitted.

(** And now the full join point invariants *)


Definition isJoinPointsValidPair_aux
  isJoinPointsValid isJoinRHS
  (v : CoreBndr) (rhs : CoreExpr) (jps : VarSet) : bool :=
    match isJoinId_maybe v with
    | None => isJoinPointsValid rhs 0 emptyVarSet  (* Non-tail-call position *)
    | Some a => 
      if (a =? 0) (* Uh, all for the termination checker *)
      then isJoinPointsValid rhs 0 jps (* tail-call position *)
      else isJoinRHS a rhs jps                   (* tail-call position *)
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
      isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS v rhs jps &&
      let jps' := updJPS jps v in
      isJoinPointsValid body 0 jps'
  | Let (Rec pairs) body => 
      negb (List.null pairs) &&  (* Not join-point-specific, could be its own invariant *)
      (forallb (fun p => negb (isJoinId (fst p))) pairs ||
       forallb (fun p =>       isJoinId (fst p))  pairs) &&
      let jps' := updJPSs jps (map fst pairs) in
      forallb (fun '(v,e) => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS v e jps') pairs &&
      isJoinPointsValid body 0 jps'
  | Case scrut bndr ty alts  => 
    negb (isJoinId bndr) &&
    isJoinPointsValid scrut 0 emptyVarSet &&  (* Non-tail-call position *)
    let jps' := updJPS jps bndr in
    forallb (fun '(dc,pats,rhs) =>
      let jps'' := updJPSs jps' pats  in
      forallb (fun v => negb (isJoinId v)) pats &&
      isJoinPointsValid rhs 0 jps'') alts  (* Tail-call position *)
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
