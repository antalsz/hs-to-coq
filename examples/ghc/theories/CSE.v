From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat.
Set Bullet Behavior "Strict Subproofs".

Require Import Coq.Lists.List.

Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Data.Foldable.
Require Import Data.Traversable.

Require Import Proofs.GHC.Base.
Require Import Proofs.Data.Foldable.
Require Import Proofs.Data.Traversable.

Require Import BasicTypes.
Require Import Id.
Require Import Core.
Require Import CoreUtils.
Require Import CoreSubst.

Require Import Proofs.Core.
Require Import Proofs.CoreInduct.
Require Import Proofs.CoreSubst.
Require Import Proofs.ScopeInvariant.
Require Import Proofs.Forall.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.VarEnv.

Require Import CSE.
Require Import TrieMap.
Require Import Proofs.TrieMap.

Opaque GHC.Base.hs_string__.

(* Well-scoped *)

(* Lemma lookupIdSubst_ok (vars : VarSet) (doc : String) (csubst : Subst) (v : Id) : *)
(*   WellScoped_Subst csubst vars -> *)
(*   exists v', lookupIdSubst doc csubst v = Mk_Var v'. *)
(* Proof. *)
(*   case: csubst => [in_scope ids [] []] /= [SUBSET VARS]. *)
(*   case locality_v: (isLocalId v) => /=; last by exists v. *)
(*   case lookup_v: (lookupVarEnv ids v) => [e |]. *)

Theorem foldr_id {A B} (a : A) (bs : list B) : foldr (fun _ => id) a bs = a.
Proof. by elim: bs. Qed.

Theorem stripTicksE_id {b} p (e : Expr b) :
  stripTicksE p e = e.
Proof.
  rewrite /stripTicksE.
  match goal with |- ?go_def ?e = ?e => set go := go_def end.
  
  elim/(@core_induct' b): e =>
    [ v | lit
    | e1 e2 IH1 IH2 | v e IH
    | [v rhs | pairs] body IHbind IHbody | scrut bndr [] alts IHscrut IHalts
    | e [] IH | tickish e IH
    | [] | [] ]
    //=; rewrite -/go;
    try by repeat f_equal.
  
  - admit.
  - admit.
  - case: (p tickish); rewrite IH=> //.
Abort.

Lemma mkTicks_id ticks e : mkTicks ticks e = e.
Proof. apply foldr_id. Qed.

(* vars = set of variables in scope AFTER `cs_subst` is applied *)
Record WellScopedCSEnv (env : CSEnv) (vars : VarSet) : Prop :=
 IsWellScopedCSEnv
   { ws_subst   : WellScoped_Subst (cs_subst env) vars
   ; ws_map     : const True (cs_map env)
   ; ws_rec_map : const True (cs_rec_map env) }.

(* Lemma WS_addBinder vars env v : *)
(*   WellScopedVar v vars -> *)
(*   WellScopedCSEnv env vars -> *)
(*   WellScopedVar (addBinder env v).2 vars. *)
(* Proof. *)
(*   case: env => [cs_subst cs_map cs_rec_map] /=. *)
(*   rewrite /addBinder /=. *)
(*   move=> WSV [ws_subst ws_map ws_rec_map]. *)
(* Abort. *)

(* We really ought to be able to automate these things *)
Lemma cseExpr_App env f a :
  cseExpr env (App f a) = App (cseExpr env f) (tryForCSE env a).
Proof. done. Qed.
Hint Rewrite cseExpr_App : hs_simpl.

Definition WS_cseExpr vars env e :
  WellScopedCSEnv env             vars ->
  WellScoped      e               vars ->
  WellScoped      (cseExpr env e) (getSubstInScopeVars (cs_subst env)).
Proof.
  elim/core_induct: e vars env => 
    [ v | lit
    | e1 e2 IH1 IH2 | v e IH
    | [v rhs | pairs] body IHbind IHbody | scrut bndr [] alts IHscrut IHalts
    | e [] IH | tickish e IH
    | [] | [] ]
    vars
    [[in_scope id_env [] []] cs_map cs_rec_map]
    //; hs_simpl;
    move=> WSenv; move: (WSenv) => [WSsubst _ _];
    rewrite /cs_subst in WSsubst.
  
  - rewrite /cseExpr /lookupSubst => WSv.
    eapply lookupIdSubst_ok; eassumption.

  - move=> /= [WSe1 WSe2]; split; first by apply (IH1 vars).
    rewrite /tryForCSE /=.
    rewrite /lookupCoreMap /=.
    rewrite /TrieMap.TrieMap__CoreMap_lookupTM.
    case: cs_map WSenv WSsubst => [cs_map_guts] /= WSenv WSsubst.
    admit.

  - rewrite /= /addBinder /= => -[GLV WSe].
    case SB: (substBndr _ _) => [sub' v'] /=.
    move: (WellScoped_Subst_substBndr _ _ _ _ _ SB GLV WSsubst) => [SE WSsubst'].
    move: (GoodLocalVar_substBndr _ _ _ _ GLV SB) => GLV'.
    split=> //.
    specialize (IH (extendVarSet vars v) (CS sub' cs_map cs_rec_map)).
    lapply IH; first move=> {IH} IH.
    + move: IH; rewrite /cs_subst => /(_ WSe) IH.
      apply WellScoped_StrongSubset with (vs1 := getSubstInScopeVars sub') => //.
      destruct sub' as [in_scope' id_env' [] []] => /=.
      move: SE; rewrite /SubstExtends; move=> [_ [_ [_ [_ [[// _] _]]]]].
    + constructor=> //; rewrite /cs_subst //.

  - 

(* Definition WS_cseExpr_cseBind vars env toplevel e b : *)
(*   WellScoped     e vars -> *)
(*   WellScopedBind b vars -> *)
(*   WellScoped (cseExpr env e) vars /\ WellScopedBind (cseBind toplevel env b).2 vars. *)
(* Proof. *)
(*   elim/core_induct: e vars env toplevel b =>  *)
(*     [ v | lit *)
(*     | e1 e2 IH1 IH2 | v e IH *)
(*     | [v rhs | pairs] body IHbind IHbody | scrut bndr [] alts IHscrut IHalts *)
(*     | e [] IH | tickish e IH *)
(*     | [] | [] ] *)
(*     vars env toplevel b //=. *)
(*   - admit. *)
(*   -  *)
  
Definition WS_cseExpr_stmt vars env e :=
  WellScoped e vars ->
  WellScoped (cseExpr env e) vars.

Definition WS_cseBind_stmt vars toplevel env b :=
  WellScopedBind b vars ->
  WellScopedBind (cseBind toplevel env b).2 vars.

Definition WS_cse_bind_stmt vars toplevel env in_info out_id :=
  WellScopedVar in_info.1 vars ->
  WellScoped    in_info.2 vars ->
  WellScopedVar out_id    vars ->
  let: (_, (out_id', out_rhs)) := cse_bind toplevel env in_info out_id
  in WellScopedVar out_id' vars /\ WellScoped out_rhs vars.

Definition WS_tryForCSE_stmt vars env e :=
  WellScoped e vars ->
  WellScoped (tryForCSE env e) vars.

Definition WS_cseCase_stmt vars env e v ty alts :=
  WellScoped    e vars ->
  WellScopedVar v vars ->
  Forall (fun alt => WellScopedAlt v alt vars) alts ->
  WellScoped (cseCase env e v ty alts) vars.

(* Theorem WS_cse_all vars e b : *)
(*   and5 (forall env, WS_cseExpr_stmt vars env e) *)
(*        (forall toplevel env, WS_cseBind_stmt vars toplevel env b) *)
(*        ( *)
        

Theorem WS_cse_all vars
                   env1 e1
                   toplevel2 env2 b2
                   toplevel3 env3 in_info3 out_id3
                   env4 e4
                   env5 e5 v5 ty5 alts5 :
  and5 (WellScoped e1 vars ->
        WellScoped (cseExpr env1 e1) vars)
       (WellScopedBind b2 vars ->
        WellScopedBind (cseBind toplevel2 env2 b2).2 vars)
       (WellScopedVar in_info3.1 vars ->
        WellScoped    in_info3.2 vars ->
        WellScopedVar out_id3    vars ->
        let: (_, (out_id', out_rhs)) := cse_bind toplevel3 env3 in_info3 out_id3
        in WellScopedVar out_id' vars /\ WellScoped out_rhs vars)
       (WellScoped e4 vars ->
        WellScoped (tryForCSE env4 e4) vars)
       (WellScoped    e5 vars ->
        WellScopedVar v5 vars ->
        Forall (fun alt => WellScopedAlt v5 alt vars) alts5 ->
        WellScoped (cseCase env5 e5 v5 ty5 alts5) vars).
Proof.
  
Admitted.

Theorem WS_cse_1 vars env e :
  WellScoped e vars -> WellScoped (cseExpr env e) vars.
Proof.
  apply WS_cse_all; try exact BasicTypes.TopLevel; try exact emptyCSEnv; try exact tt; try exact nil; try exact (Type_ tt).
  
Abort.  
  
  


Ltac WS_unstmt :=
  rewrite /WS_cseExpr_stmt /WS_cseBind_stmt /WS_cse_bind_stmt /WS_tryForCSE_stmt /WS_cseCase_stmt.


(* Theorem WellScoped_cse vars : *)
(*   and4 (WS_cseBind_stmt   vars) *)
(*        (WS_cse_bind_stmt  vars) *)
(*        (WS_tryForCSE_stmt vars) *)
(*        (WS_cseCase_stmt   vars) *)
(*   -> WS_cseExpr_stmt vars. *)
(* Proof. *)
(*   WS_unstmt; move=> [WS_cseBind WS_cse_bind WS_tryForCSE WS_cseCase] env. *)
 
(* Axiom WellScoped_cseExpr : forall vars, *)
(*   and4 (WS_cseBind_stmt   vars) *)
(*        (WS_cse_bind_stmt  vars) *)
(*        (WS_tryForCSE_stmt vars) *)
(*        (WS_cseCase_stmt   vars) *)
(*   -> WS_cseExpr_stmt vars. *)
 
(* Axiom WellScoped_cseBind : forall vars, *)
(*   and4 (WS_cseExpr_stmt   vars) *)
(*        (WS_cse_bind_stmt  vars) *)
(*        (WS_tryForCSE_stmt vars) *)
(*        (WS_cseCase_stmt   vars) *)
(*   -> WS_cseBind_stmt vars. *)
 
(* Axiom WellScoped_cse_bind : forall vars, *)
(*   and4 (WS_cseExpr_stmt   vars) *)
(*        (WS_cseBind_stmt   vars) *)
(*        (WS_tryForCSE_stmt vars) *)
(*        (WS_cseCase_stmt   vars) *)
(*   -> WS_cse_bind_stmt vars. *)
 
(* Axiom WellScoped_tryForCSE : forall vars, *)
(*   and4 (WS_cseExpr_stmt  vars) *)
(*        (WS_cseBind_stmt  vars) *)
(*        (WS_cse_bind_stmt vars) *)
(*        (WS_cseCase_stmt  vars) *)
(*   -> WS_tryForCSE_stmt vars. *)
 
(* Axiom WellScoped_cseCase : forall vars, *)
(*   and4 (WS_cseExpr_stmt   vars) *)
(*        (WS_cseBind_stmt   vars) *)
(*        (WS_cse_bind_stmt  vars) *)
(*        (WS_tryForCSE_stmt vars) *)
(*   -> WS_cseCase_stmt vars. *)

(* Theorem WellScoped_cse vars : *)
(*   and4 (WS_cseBind_stmt   vars) *)
(*        (WS_cse_bind_stmt  vars) *)
(*        (WS_tryForCSE_stmt vars) *)
(*        (WS_cseCase_stmt   vars) *)
(*   -> WS_cseExpr_stmt vars. *)
(* Proof. *)
(*   WS_unstmt; move=> [WS_cseBind WS_cse_bind WS_tryForCSE WS_cseCase] env. *)
(*   elim/core_induct =>  *)
(*     [ v | lit *)
(*     | e1 e2 IH1 IH2 | v e IH *)
(*     | [v rhs | pairs] body IHbind IHbody | scrut bndr [] alts IHscrut IHalts *)
(*     | e [] IH | tickish e IH *)
(*     | [] | [] ] *)
(*     //=; unrec. *)
(*   - move => WSV. *)
(*     admit. (* AXIOM *) *)

(*   - move=> [WS1 WS2]; split; [by apply IH1 | by apply WS_tryForCSE]. *)
  
(*   -  *)

(*   - case: env => [csubst omap1 omap2] /=. *)
(*     rewrite /CoreSubst.lookupIdSubst /=. *)
(*     case: csubst => [in_scope ids [] []] /=. *)

(*   elim/core_induct: e => *)
(*     [ v | lit *)
(*     | e1 e2 IH1 IH2 | v e IH *)
(*     | [v rhs | pairs] body IHbind IHbody | scrut bndr [] alts IHscrut IHalts *)
(*     | e [] IH | tickish e IH *)
(*     | [] | [] ] *)
(*     //=; unrec. *)
(*   - admit. *)
(*   - move=> [WS1 WS2]; split; first by apply IH1. *)
(*     admit. *)
(*   - move=> [GLV WS]. *)
(*     admit. *)
(*   - move=> [[GLV WSrhs] WSbody]. *)
(*     admit. *)
(*   - move=> [[GLVpairs [NDpairs WSpairs]] WSbody]. *)
(*     admit. *)
(*   - move=> [WSscrut [GLV OKalts]]. *)
(*     admit. *)
(*   - move=> WS. *)
(*     admit. *)
(* Admitted.     *)


(* Theorem WellScoped_cseExpr vars env e : *)
(*   WellScoped e vars -> WellScoped (cseExpr env e) vars. *)
(* Proof. *)
(*   elim/core_induct: e => *)
(*     [ v | lit *)
(*     | e1 e2 IH1 IH2 | v e IH *)
(*     | [v rhs | pairs] body IHbind IHbody | scrut bndr [] alts IHscrut IHalts *)
(*     | e [] IH | tickish e IH *)
(*     | [] | [] ] *)
(*     //=; unrec. *)
(*   - admit. *)
(*   - move=> [WS1 WS2]; split; first by apply IH1. *)
(*     admit. *)
(*   - move=> [GLV WS]. *)
(*     admit. *)
(*   - move=> [[GLV WSrhs] WSbody]. *)
(*     admit. *)
(*   - move=> [[GLVpairs [NDpairs WSpairs]] WSbody]. *)
(*     admit. *)
(*   - move=> [WSscrut [GLV OKalts]]. *)
(*     admit. *)
(*   - move=> WS. *)
(*     admit. *)
(* Admitted.     *)
