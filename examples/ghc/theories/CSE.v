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
Require Import Proofs.VarSetStrong.
Require Import Proofs.VarEnv.

Require Import CSE.
Require Import TrieMap.
Require Import Proofs.TrieMap.

Opaque GHC.Base.hs_string__.

(* Well-scoped *)

Lemma stripTicksE_id {b} p (e : Expr b) :
  stripTicksE p e = e.
Proof.
  rewrite /stripTicksE.
  match goal with |- ?go_def ?e = ?e => set go := go_def end.
  elim/(@core_induct' b): e =>
    [ v | lit
    | e1 e2 IH1 IH2 | v e IH
    | [v rhs | pairs] body IHbind IHbody | scrut bndr bty alts IHscrut IHalts
    | e co IH
    | ty | co ]
    //=; rewrite -/go;
    repeat f_equal => //.
  - rewrite -{2}(map_id pairs).
    replace @map with @List.map by done.
    apply map_ext_in => [[v e] IN].
    by rewrite (IHbind v).
  - rewrite -{2}(map_id alts).
    replace @map with @List.map by done.
    apply map_ext_in => [[[c bs] e] IN].
    by rewrite (IHalts c bs).
Qed.

Hint Rewrite @stripTicksE_id : hs_simpl.
Hint Rewrite (@stripTicksE_id CoreBndr) : hs_simpl.

Lemma WellScoped_Subst_implies_StrongSubset subst vars :
  WellScoped_Subst subst vars ->
  vars {<=} getSubstInScopeVars subst.
Proof.
  case: subst => [in_scope id_env vs cs] /= [SS lookup_WS].
  move=> var; move /(_ var) in lookup_WS.
  case LVS:  (lookupVarSet _ _) => [v|//].
  move: (SS var).
  case LVS': (lookupVarSet _ _) => [v'|].
  - case LVS'': (lookupVarSet _ _) => [v''|//].
    apply almostEqual_trans.
    admit.
  
  - case LVS'': (lookupVarSet _ _) => [v''|] _.
    + admit.
    + 
Abort.

(* vars = set of variables in scope AFTER `cs_subst` is applied *)
Record WellScopedCSEnv (env : CSEnv) (vars : VarSet) : Prop :=
 IsWellScopedCSEnv
   { ws_subst   : WellScoped_Subst (cs_subst env) vars
   ; ws_map     : const True (cs_map env)
   ; ws_rec_map : const True (cs_rec_map env) }.

(* We really ought to be able to automate these things *)
Lemma cseExpr_App env f a :
  cseExpr env (App f a) = App (cseExpr env f) (tryForCSE env a).
Proof. done. Qed.
Hint Rewrite cseExpr_App : hs_simpl.

Lemma cseExpr_Let env bind e :
  cseExpr env (Let bind e) = let: (env', bind') := cseBind NotTopLevel env bind
                             in Let bind' (cseExpr env' e).
Proof. done. Qed.
Hint Rewrite cseExpr_Let : hs_simpl.

Lemma cseExpr_NonRec toplevel env b e :
  cseBind toplevel env (NonRec b e) =
    let: (env1, b1)       := addBinder env b in
    let: (env2, (b2, e2)) := cse_bind toplevel env1 (b,e) b1 in
    (env2, NonRec b2 e2).
Proof. done. Qed.
Hint Rewrite cseExpr_NonRec : hs_simpl.

Lemma fromOL_nilOL_nil {a} : OrdList.fromOL OrdList.nilOL = nil :> list a.
Proof. done. Qed.

Lemma appOL_nilOL_right {a} (ol : OrdList.OrdList a) : OrdList.appOL ol OrdList.nilOL = ol.
Proof. by rewrite /OrdList.appOL /=; case: ol. Qed.

Lemma concatOL_map_nilOL_nilOL {a b} (xs : list a) (f : a -> OrdList.OrdList b) :
  (forall x, In x xs -> f x = OrdList.nilOL) -> 
  OrdList.concatOL (map f xs) = OrdList.nilOL.
Proof.
  rewrite /OrdList.concatOL.
  elim: xs => [|x xs IH] //= NIL; hs_simpl.
  rewrite NIL /=; last by left.
  rewrite IH //.
  by move=> y IN; apply NIL; right.
Qed.

Lemma stripTicksT_nil {b} p (e : Expr b) :
  stripTicksT p e = nil.
Proof.
  rewrite /stripTicksT.
  rewrite -fromOL_nilOL_nil; f_equal.
  match goal with |- ?go_def ?e = _ => set go := go_def end.
  elim/(@core_induct' b): e => 
    [ v | lit
    | e1 e2 IH1 IH2 | v e IH
    | [v rhs | pairs] body IHbind IHbody | scrut bndr bty alts IHscrut IHalts
    | e co IH
    | ty | co ]
    //=;
    rewrite -/go.
  - by rewrite IH1 IH2.
  - by rewrite IHbind IHbody.
  - rewrite IHbody.
    rewrite concatOL_map_nilOL_nilOL //.
    move=> [v rhs]; apply IHbind.
  - rewrite IHscrut /=.
    rewrite concatOL_map_nilOL_nilOL //.
    move=> [[dc pats] rhs]; apply IHalts.
Qed.
Hint Rewrite @stripTicksT_nil : hs_simpl.
Hint Rewrite (@stripTicksT_nil CoreBndr) : hs_simpl.

Lemma tryForCSE_simpl env expr :
  tryForCSE env expr = match lookupCSEnv env (cseExpr env expr) with
                       | Some e => e
                       | None   => cseExpr env expr
                       end.
Proof.
  rewrite /tryForCSE; hs_simpl.
  by case: (lookupCSEnv _ _) => [e|//]; hs_simpl.
Qed.

Definition WS_cseExpr vars env e :
  WellScopedCSEnv env             vars ->
  WellScoped      e               vars ->
  WellScoped      (cseExpr env e) (getSubstInScopeVars (cs_subst env)).
Proof.
  elim/core_induct: e vars env => 
    [ v | lit
    | e1 e2 IH1 IH2 | v e IH
    | [v rhs | pairs] body IHbind IHbody | scrut bndr bty alts IHscrut IHalts
    | e ty IH
    | co | ty ]
    vars
    [[in_scope id_env tm cm] cs_map cs_rec_map]
    //; hs_simpl;
    move=> WSenv; move: (WSenv) => [WSsubst _ _];
    rewrite /cs_subst in WSsubst.
  
  - rewrite /cseExpr /lookupSubst => WSv.
    eapply lookupIdSubst_ok; eassumption.

  - move=> /= [WSe1 WSe2]; split; first by apply (IH1 vars).
    rewrite tryForCSE_simpl /=.
    case LOOKUP: (lookupCoreMap _ _) => [e|]; last by apply (IH2 vars).
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

  - rewrite (lock cse_bind) /= -(lock cse_bind) => -[[GLV WS_rhs] WS_ext].
    rewrite /addBinder /substBndr isn'tTyVar isn'tCoVar.
    case def_sub'_v': (substIdBndr _ _ _ _) => [sub' v'].
    have GLV': GoodLocalVar v' by eapply GoodLocalVar_substIdBndr; eassumption.
    move: (WellScoped_Subst_substIdBndr _ _ _ _ _ _ _ def_sub'_v' GLV WSsubst)
      => [subst_ext WSsubst'].
    
    (* cse_bind *)
    simpl.
    case def_env'_out_id': (addBinding _ _ _ _) => [env' out_id'].
    case join_v: (isJoinId_maybe v) => [arity|].
    + admit.
    + rewrite tryForCSE_simpl /=.
      case LOOKUP: (lookupCoreMap _ _) => [e|]; hs_simpl.
      * admit.
      * split; first split.
        -- admit.
        -- admit. (* IHbind *)
        -- (* ? *)
           suff <-: getSubstInScopeVars (cs_subst env') = extendVarSet (getInScopeVars in_scope) out_id'. {
             eapply IHbody; last eassumption; hs_simpl.
             constructor => //.
             admit.
           }
           admit.

  - rewrite (lock cseBind) /= -(lock cseBind).
    case: pairs IHbind => [|[in_id rhs] [|[in_id' rhs'] pairs]] IHbind [[GLVs [Uniq WS_pairs]] WS_body] /=.
    + repeat split=> //.
      by eapply IHbody; last eassumption.
    + case checkCSE: (noCSE in_id).
      * simpl; hs_simpl.
        repeat split; try constructor=> //=.
        -- apply GoodLocalVar_uniqAway.
           by inversion_clear GLVs.
        -- admit. (* IHbind *)
        -- admit. (* IHbody *)
      * case LOOKUP: (lookupCoreMap _ _) => [e|]; hs_simpl.
        -- admit.
        -- admit.
    + admit.

  - admit.

  - simpl; hs_simpl.
    case def_e': (lookupCoreMap _ _) => [e'|]; hs_simpl; last by apply IH.
    admit.
Admitted.

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
