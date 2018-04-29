Require Import CoreSyn.
Require Import Var.
Require Import VarSet.

Require Import Coq.Lists.List.
Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

(*
This file describes an invariant of Core files that
 * all variables must be in scope
 * and be structurally equal to their binder
*)

(* This returns a [Prop] rather than a bool because
   we do not have a function that determines structural
   equality.
*)

(* The termination checker does not like recursion through [Forall], but
   through [map] is fine... oh well. *)
Definition Forall' {a} (P : a -> Prop) xs := Forall id (map P xs).

Fixpoint WellScoped (e : CoreExpr) (in_scope : VarSet) {struct e} : Prop :=
  match e with
  | CoreSyn.Var v => match lookupVarSet in_scope v with
    | None => False
    | Some v' => v = v'
    end
  | Lit l => True
  | App e1 e2 => WellScoped e1 in_scope /\  WellScoped e2 in_scope
  | Lam v e => WellScoped e (extendVarSet in_scope v)
  | Let (NonRec v rhs) body => 
      WellScoped rhs in_scope /\ WellScoped body (extendVarSet in_scope v)
  | Let (Rec pairs) body => 
      NoDup (map varUnique (map fst pairs)) /\
      let in_scope' := extendVarSetList in_scope (map fst pairs) in
      Forall' (fun p => WellScoped (snd p) in_scope') pairs /\
      WellScoped body in_scope'
  | Case scrut bndr ty alts  => 
    WellScoped scrut in_scope /\
    Forall' (fun alt =>
      let in_scope' := extendVarSetList in_scope (bndr :: snd (fst alt)) in
      WellScoped (snd alt) in_scope') alts
  | Cast e _ =>   WellScoped e in_scope
  | Tick _ e =>   WellScoped e in_scope
  | Type_ _  =>   True
  | Coercion _ => True
  end.
