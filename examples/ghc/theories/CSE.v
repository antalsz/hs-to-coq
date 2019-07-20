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
Require Import Proofs.OrdList.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.StrongVarSet.
Require Import Proofs.VarEnv.
Require Proofs.StrongCoreFVs.

Require Import CSE.
Require Import TrieMap.
Require Import Proofs.TrieMap.

Opaque GHC.Base.hs_string__.

(** * Evaluating CSE *)
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

Lemma cseBind_NonRec toplevel env b e :
  cseBind toplevel env (NonRec b e) =
    let: (env1, b1)       := addBinder env b in
    let: (env2, (b2, e2)) := cse_bind toplevel env1 (b,e) b1 in
    (env2, NonRec b2 e2).
Proof. done. Qed.
Hint Rewrite cseBind_NonRec : hs_simpl.

(** * Stripping ticks *)

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

(** * Well-scopedness for CSE *)

(* vars = set of variables in scope AFTER `cs_subst` is applied *)
Record WellScopedCSEnv (env : CSEnv) (vars : VarSet) : Prop :=
 IsWellScopedCSEnv
   { ws_subst   : WellScoped_Subst (cs_subst env) vars
   ; ws_map     : const True (cs_map env)
   ; ws_rec_map : const True (cs_rec_map env) }.

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
      apply StrongCoreFVs.WellScoped_StrongSubset with (vs1 := getSubstInScopeVars sub') => //.
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
