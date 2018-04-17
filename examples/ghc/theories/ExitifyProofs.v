Require Import Exitify.
Require Import CoreSyn.
Require Import Var.
Require Import VarEnv.
Require Import VarSet.

Require Import Psatz.
Require Import Coq.Lists.List.

Import ListNotations.

Open Scope Z_scope.

Set Bullet Behavior "Strict Subproofs".

Require Import JoinPointInvariants.

Ltac get_let n e :=
 lazymatch e with 
 | (let x := ?rhs in ?body) => 
  let n' := eval cbv in n in
  lazymatch n' with
  | O => rhs
  | S ?nsub1 => get_let nsub1 body
  end
 | _ => fail "expression" e "is not a let-binding"
 end.

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
    let def := get_let 0%nat rhs in
    exact def).

  (* But for the next nested let we have a problem. *)
  Fail Definition go := ltac:(
    let rhs := eval cbv beta delta [exitify] in (exitify in_scope pairs) in
    let def := get_let 1%nat rhs in
    let ty := type of def in
    exact ty).
    (* 
    In nested Ltac calls to "get_let" and "get_let", last call failed.
    Must evaluate to a closed term
    offending expression: 
    e
    this is an object of type constr_under_binders
    *)
    (* We cannot go under a binder with ltac, this way it seems. *)

  (* It works for every given depths if 
     we pattern-match on the nested [let]s in one go,
     and abstract over the free variables correctly:
  *)
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

  (* This is tedious, but doable. Maybe some not too big ML hacking
     can give us a
     [Lift Local Definition (exitify in_scope pairs body)]
     command that does precisely that?
   *)

  Ltac expand_pairs :=
  match goal with
    |- context[let (_,_) := ?e in _] =>
    rewrite (surjective_pairing e)
  end.

  Theorem exitify_JPI:
    forall body jps,
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
    change (isJoinPointsValid (mkExitLets exits (mkLetRec pairs' body)) 0 jps0 = true).
  Abort.

End in_exitify.