Require Import Id.
Require Import Core.
Require Import BasicTypes.

Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import Coq.Bool.Bool.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

(** * Nice core

This module defines a variant of [Expr] where more of the invariant
that various code needs are baked in. The idea is that if
[f : CoreExpr -> …], then, in general, [f (toCore e)] does not call [error].
*)

(* The use of [Vector] here is just to be able to restrict the lengths.
   Infortunately, one cannot just write [length pairs <> 0] or such,
   because the implicit paramter of [length] is a non-positive occurence of [NExpr].
*)
Inductive NExpr : Type :=
  | NVar : Var -> NExpr
  | NLit : Literal.Literal -> NExpr
  | NApp : NExpr -> NExpr -> NExpr
  | NLam : Var -> NExpr -> NExpr
  | NLet : NBind -> NExpr -> NExpr
  | NCase : NExpr -> Var -> list (AltCon * list Var * NExpr) -> NExpr
  | NCast : NExpr -> NExpr
  | NTick : Tickish Id -> NExpr -> NExpr
  | NType : NExpr
  | NCoercion : NExpr
with  NBind : Type :=
  | NNonRec :     NPair ->     NBind
  | NNonRecJoin : NJPair -> NBind
  | NRec :   forall n (pairs : Vector.t NPair     (S n)),  NBind
  | NRecJoin : forall n (pairs : Vector.t NJPair (S n)),  NBind
with NPair :=
  | Mk_NPair : forall (v : Var) (rhs : NExpr)
      (HnotJoin : isJoinId_maybe v = None),
      NPair
with NJPair :=
  | Mk_NJPair : forall (v : Var) (params: list Var) (rhs : NExpr)
      (HnotJoin : isJoinId_maybe v = Some (length params)),
      NJPair
.

Fixpoint toExpr (e : NExpr) : CoreExpr := match e with
  | NVar v => Mk_Var v
  | NLit l => Lit l
  | NApp e1 e2 => App (toExpr e1) (toExpr e2)
  | NLam v e => Lam v (toExpr e)
  | NLet bind e => Let (toBind bind) (toExpr e)
  | NCase scrut bndr alts => Case (toExpr scrut) bndr tt (List.map (fun '(dc,pats,rhs) => (dc, pats, toExpr rhs)) alts)
  | NCast e => Cast (toExpr e) tt
  | NTick t e => Tick t (toExpr e)
  | NType  => Type_ tt
  | NCoercion  => Coercion tt
end with toBind (b : NBind) : CoreBind := match b with
  | NNonRec     (Mk_NPair     v rhs _)       => NonRec v (toExpr rhs)
  | NNonRecJoin (Mk_NJPair v params rhs _) => NonRec v (mkLams params (toExpr rhs))
  | NRec     _ pairs => Rec (to_list (Vector.map (fun '(Mk_NPair v rhs _) => (v, toExpr rhs)) pairs))
  | NRecJoin _ pairs =>
      Rec (to_list (Vector.map (fun '(Mk_NJPair v params rhs _) => (v, (mkLams params (toExpr rhs)))) pairs))
end.
 