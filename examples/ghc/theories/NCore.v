Require Import Id.
Require Import Core.
Require Import BasicTypes.

Require Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Psatz.

Require Import VectorUtils.

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
      (HisJoin : isJoinId_maybe v = Some (length params)),
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
  | NNonRec     (Mk_NPair  v rhs _)        => NonRec v (toExpr rhs)
  | NNonRecJoin (Mk_NJPair v params rhs _) => NonRec v (mkLams params (toExpr rhs))
  | NRec     _ pairs => Rec (Vector.to_list (Vector.map toPair  pairs))
  | NRecJoin _ pairs => Rec (Vector.to_list (Vector.map toJPair pairs))
end with toJPair (p : NJPair) := match p with
  | Mk_NJPair v params rhs _ => (v, (mkLams params (toExpr rhs)))
end with toPair (p : NPair) := match p with
  | Mk_NPair v  rhs _ => (v, toExpr rhs)
end.


Section NCoreLT.
  Fixpoint ncore_size (e : NExpr) : nat :=
    match e with
    | NVar v => 0
    | NLit l => 0
    | NApp e1 e2 => S (ncore_size e1 + ncore_size e2)
    | NLam v e => S (ncore_size e)
    | NLet bind body => S (nbind_size bind + ncore_size body)
    | NCase scrut bndr alts  => 
        S (ncore_size scrut +
           List.fold_right plus 0 (List.map (fun p => ncore_size (snd p)) alts))
    | NCast e   => S (ncore_size e)
    | NTick _ e => S (ncore_size e)
    | NType     => 0
    | NCoercion => 0
    end
  with nbind_size (b : NBind) : nat :=
    match b with
    | NNonRec     p    => npair_size  p
    | NNonRecJoin jp   => njpair_size jp
    | NRec     _ pairs => fold_right plus 0 (Vector.to_list (Vector.map npair_size  pairs))
    | NRecJoin _ pairs => fold_right plus 0 (Vector.to_list (Vector.map njpair_size pairs))
    end
  with npair_size (p : NPair) : nat :=
    match p with
    | Mk_NPair _ rhs _ => ncore_size rhs
    end
  with njpair_size (jp : NJPair) : nat :=
    match jp with
    | Mk_NJPair _ _ rhs _ => ncore_size rhs
    end.

  (* We use the size only for comparisons. So lets
     make a definition here that we never unfold otherwise,
     and isntead create a tactic that handles all cases.
  *)
  Definition NCoreLT := fun x y => ncore_size x < ncore_size y.

  Lemma NCoreLT_wf : well_founded NCoreLT.
  Proof.
    apply Wf_nat.well_founded_ltof. 
  Qed.

  Lemma NCoreLT_case_alts:
    forall scrut b alts dc pats rhs,
    In (dc, pats, rhs) alts ->
    NCoreLT rhs (NCase scrut b alts).
  Proof.
    intros.
    unfold NCoreLT. simpl.
    apply Lt.le_lt_n_Sm.
    etransitivity; only 2: apply Plus.le_plus_r.
    induction alts; inversion H.
    * subst. simpl. lia.
    * intuition. simpl. lia.
  Qed.


  Lemma NCoreLT_let_rhs:
    forall v rhs e H,
    NCoreLT rhs (NLet (NNonRec (Mk_NPair v rhs H)) e).
  Proof.
    intros.
    unfold NCoreLT. simpl.
    apply Lt.le_lt_n_Sm.
    etransitivity; only 2: apply Plus.le_plus_l.
    lia.
  Qed.


  Lemma NCoreLT_let_join_rhs:
    forall v rhs params e H,
    NCoreLT rhs (NLet (NNonRecJoin (Mk_NJPair v params rhs H)) e).
  Proof.
    intros.
    unfold NCoreLT. simpl.
    apply Lt.le_lt_n_Sm.
    etransitivity; only 2: apply Plus.le_plus_l.
    lia.
  Qed.

  Lemma NCoreLT_let_pairs:
    forall v rhs H n pairs e,
    In (Mk_NPair v rhs H) (Vector.to_list pairs) ->
    NCoreLT rhs (NLet (NRec n pairs) e).
  Proof.
    intros.
    unfold NCoreLT. simpl.
    apply Lt.le_lt_n_Sm.
    etransitivity; only 2: apply Plus.le_plus_l.
    induction pairs;  rewrite ?to_list_map, ?to_list_nil, ?to_list_cons in *; inversion H0.
    * subst. simpl. lia.
    * intuition. simpl. rewrite to_list_map in H2. lia.
  Qed.

  Lemma NCoreLT_let_join_pairs:
    forall v params rhs H n pairs e,
    In (Mk_NJPair v params rhs H) (Vector.to_list pairs) ->
    NCoreLT rhs (NLet (NRecJoin n pairs) e).
  Proof.
    intros.
    unfold NCoreLT. simpl.
    apply Lt.le_lt_n_Sm.
    etransitivity; only 2: apply Plus.le_plus_l.
    induction pairs;  rewrite ?to_list_map, ?to_list_nil, ?to_list_cons in *; inversion H0.
    * subst. simpl. lia.
    * intuition. simpl. rewrite to_list_map in H2. lia.
  Qed.

  Lemma NCoreLT_let_body:
    forall binds e,
    NCoreLT e (NLet binds e).
  Proof. intros. unfold NCoreLT. simpl. lia. Qed.


End NCoreLT.

Opaque NCoreLT.

(* For less obligations from [Program Fixpoint]: *)
Hint Resolve NCoreLT_wf : arith.

(* This is a bit plump yet *)
Ltac NCore_termination :=
(*   try (apply CoreLT_collectNBinders; only 1: assumption);  *)
  first
    [ apply  NCoreLT_let_rhs
    | apply  NCoreLT_let_join_rhs
    | apply  NCoreLT_let_body
    | eapply NCoreLT_let_pairs;      eassumption
    | eapply NCoreLT_let_join_pairs; eassumption
    | eapply NCoreLT_case_alts;      eassumption
    ].
