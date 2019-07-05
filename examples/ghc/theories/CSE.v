From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype.
Set Bullet Behavior "Strict Subproofs".

Generalizable All Variables.

Require Import Coq.Lists.List.

Require Import GHC.Base.
Import GHC.Base.Notations.
Require Import Data.Foldable.
Require Import Data.Traversable.
Require Import Data.Maybe.

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
Require Import Proofs.VarEnv.

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

Lemma cseExpr_Case env e bndr ty alts :
  cseExpr env (Case e bndr ty alts) = cseCase env e bndr ty alts.
Proof. done. Qed.
Hint Rewrite cseExpr_Case : hs_simpl.

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

Definition getCSEnvInScopeVars : CSEnv -> VarSet := getSubstInScopeVars ∘ cs_subst.
Arguments getCSEnvInScopeVars !env /.

(* vars = set of variables in scope AFTER `cs_subst` is applied *)
Record WellScopedCSEnv (env : CSEnv) (vars : VarSet) : Prop :=
 IsWellScopedCSEnv
   { ws_subst   : WellScoped_Subst (cs_subst env) vars
   ; ws_map     : TrieMap_All (WellScoped^~ (getCSEnvInScopeVars env)) (cs_map env)
   ; ws_rec_map : TrieMap_All (WellScoped^~ (getCSEnvInScopeVars env)) (cs_rec_map env) }.
   (* `WellScoped^~ vars` or `WellScoped (getSubstInScopeVars (cs_subst env)`? *)

Lemma tryForCSE_simpl env expr :
  tryForCSE env expr = match lookupCSEnv env (cseExpr env expr) with
                       | Some e => e
                       | None   => cseExpr env expr
                       end.
Proof.
  rewrite /tryForCSE; hs_simpl.
  by case: (lookupCSEnv _ _) => [e|//]; hs_simpl.
Qed.

Ltac simpl_Key := rewrite /Key /TrieMap__CoreMap /TrieMap.TrieMap__CoreMap_Key.

Lemma WellScoped_SetEq vars1 vars2 expr :
  vars1 {=} vars2 ->
  WellScoped expr vars1 <-> WellScoped expr vars2.
Proof. by case=> ss12 ss21; split=> WS; eapply WellScoped_StrongSubset; eassumption. Qed.

Lemma SubstExtends_WellScoped_iff sub v sub' v' expr :
  SubstExtends sub (v :: nil) sub' (v' :: nil) ->
  WellScoped expr (getSubstInScopeVars sub') <-> WellScoped expr (extendVarSet (getSubstInScopeVars sub) v').
Proof.
  case: sub => [in_scope id_env tm cm]; case: sub' => [in_scope' id_env' tm' cm'].
  rewrite /SubstExtends /=; hs_simpl; move=> [_ [_ [_ [FL [inScopeVars_eq [minusDom_subst VEE]]]]]].
  by rewrite (WellScoped_SetEq (_ in_scope')); last eassumption.
Qed.

Lemma SubstExtends_WellScoped_iff_eta1 in_scope id_env tm cm v sub' v' expr :
  SubstExtends (Mk_Subst in_scope id_env tm cm) (v :: nil) sub' (v' :: nil) ->
  WellScoped expr (getSubstInScopeVars sub') <-> WellScoped expr (extendVarSet (getInScopeVars in_scope) v').
Proof. apply SubstExtends_WellScoped_iff. Qed.

Lemma SubstExtends_WellScoped_preserved sub v sub' v' expr :
  SubstExtends sub (v :: nil) sub' (v' :: nil) ->
  WellScoped expr (getSubstInScopeVars sub) -> WellScoped expr (getSubstInScopeVars sub').
Proof.
  move=> SE.
  rewrite (SubstExtends_WellScoped_iff _ _ sub'); last eassumption.
  move=> /WellScoped_StrongSubset; apply.
  apply StrongSubset_extend_fresh.
  by move: sub sub' SE => [? ? ? ?] [? ? ? ?] [_ [_ [_ [/freshList_cons[? ?] _]]]].
Qed.  

Ltac do_Expand_substBndr def_subst'_v' subst' v' def_subst' in_scope' id_env' tm' cm' :=
  match goal with
  | |- context[substBndr ?subst ?v] => case def_subst'_v': (substBndr subst v) => [subst' v']
  end;
  let H := fresh in
  case H: subst' => [in_scope' id_env' tm' cm']; rewrite -H; rename H into def_subst'.
  (* For some reason, if `def_subst'` is passed in as an `ident`, it can't be
     used in `rewrite`, so we go through an intermediate `H` *)

Tactic Notation "Expand_substBndr" "=>"
                ident(def_subst'_v') "[" ident(subst') ident(v') "]"
                ident(def_subst')    "[" ident(in_scope') ident(id_env') ident(tm') ident(cm') "]" :=
  do_Expand_substBndr def_subst'_v' subst' v' def_subst' in_scope' id_env' tm' cm'.

Ltac GoodLocalVar_WellScoped_substBndr :=
  match goal with
  | SB  : substBndr ?subst ?v = (?subst',?bndr')
  , GLV : GoodLocalVar ?v
  , WSS : WellScoped_Subst ?subst ?vs
    |- _ => move: (GoodLocalVar_substBndr     v bndr' subst subst' GLV SB)
                  (WellScoped_Subst_substBndr subst subst' bndr'  v vs SB GLV WSS)
  end. 

Inductive Expr_Var_View {b} : Expr b -> Type :=
| EVV_IsVar  v : Expr_Var_View (Mk_Var v)
| EVV_NotVar e : ~ (exists v, e = Mk_Var v) -> Expr_Var_View e.

Definition case_if_Var {b} (e : Expr b) : Expr_Var_View e :=
  match e with
  | Mk_Var v => EVV_IsVar  v
  | e'       => EVV_NotVar e' ltac:(by subst e'; move=> [v ?])
  end.

Ltac lapply_all H :=
  match type of H with
  | (_ -> _) => lapply H; try clear H; first (let G := fresh in move=> G; lapply_all G)
  | _        => move: H
  end.

Lemma GoodLocalVar_zapIdOccInfo v :
  GoodLocalVar v ->
  GoodLocalVar (zapIdOccInfo v).
Proof.
  case: v => [varName realUnique varType idScope id_details id_info].
  by move=> []; repeat move=> [] ?; repeat split.
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
    [cs_sub cs_map cs_rec_map]
    //; hs_simpl;
    move=> WSenv; move: (WSenv) => [WSsubst WSmap WSrec];
    rewrite /cs_subst in WSsubst; rewrite /CSE.cs_map in WSmap; rewrite /CSE.cs_rec_map in WSrec.
  
  - rewrite /cseExpr /lookupSubst => WSv.
    eapply lookupIdSubst_ok; eassumption.

  - move=> /= [WSe1 WSe2]; split; first by apply (IH1 vars).
    rewrite tryForCSE_simpl /=.
    case LOOKUP: (lookupCoreMap _ _) => [e|]; last by apply (IH2 vars).
    by eapply TrieMap_All_lookup_Some in LOOKUP => //.
  
  - rewrite /= /addBinder /= => -[GLV WSe].
    case SB: (substBndr _ _) => [sub' v'].
    GoodLocalVar_WellScoped_substBndr => GLV' [SE WSsubst'].
    split=> //.
    specialize (IH (extendVarSet vars v) (CS sub' cs_map cs_rec_map)).
    lapply_all IH => //.
    + by rewrite -SubstExtends_WellScoped_iff; last eassumption; apply.
    + constructor=> //; rewrite /cs_subst //=.
      all: by eapply TrieMap_All_impl_lookup => // *; eauto using SubstExtends_WellScoped_preserved.

  - rewrite (lock cse_bind) /= -(lock cse_bind) => -[[GLV WS_rhs] WS_ext].
    rewrite /addBinder.
    case def_sub'_v': (substBndr _ _) => [sub' v'].
    GoodLocalVar_WellScoped_substBndr => GLV' [SE WSsubst'].
    
    (* cse_bind *)
    simpl.
    rewrite tryForCSE_simpl.
    case def_env'_out_id': (addBinding _ _ _ _) => [env' out_id'].
    case join_v: (isJoinId_maybe v) => [arity|].
    + admit.
    + move: def_env'_out_id' => /=.
      case LOOKUP: (lookupCoreMap _ _) => [e|]; hs_simpl.
      * rewrite /addBinding; hs_simpl => /=.
        case testCSE: (noCSE v).
        -- move=> [? ?]; subst env' out_id'.
           split; first split=> //.
           ++ by eapply TrieMap_All_lookup_Some in LOOKUP; last eassumption.
           ++ lapply_all (IHbody (extendVarSet vars v) (CS sub' cs_map cs_rec_map)) => //=.
              ** by rewrite -SubstExtends_WellScoped_iff; last eassumption.
              ** constructor => //=.
                 all: eapply TrieMap_All_impl_lookup; last eassumption;
                      eauto using SubstExtends_WellScoped_preserved.
        -- destruct (case_if_Var e) as [ev|e e_nonvar] => //=; hs_simpl.
           ++ move=> [<-{env'} <-{out_id'}].
              split; first split=> //.
              ** by eapply TrieMap_All_lookup_Some in LOOKUP; last eassumption.
              ** move: (WSsubst'); rewrite (lock WellScoped_Subst); case: sub' def_sub'_v' SE WSsubst' LOOKUP
                   => [in_scope' id_env' tm' cm'] //= def_sub'_v' SE [WSsubst'_SS WSsubst'_lookup] LOOKUP;
                   hs_simpl; rewrite -(lock WellScoped_Subst) => WSsubst'.
                 rewrite -SubstExtends_WellScoped_iff; last eassumption.
                 eapply IHbody; last eassumption; hs_simpl.
                 constructor.
                 all: try by eapply TrieMap_All_impl_lookup; last eassumption;
                             move=> ? ? ? H; eapply SubstExtends_WellScoped_preserved in H; last eassumption.
                 rewrite /cs_subst.
                 split.
                 --- etransitivity; first by apply StrongSubset_minusDom_extend_extend.
                     etransitivity; last by apply WSsubst'_SS.
                     
                     (*destruct cs_sub as [in_scope id_env tm cm] eqn:def_cs_sub.
                     move: (SE)
                       => [/= _ [_ [_ [/freshList_cons [fresh_v _] [inScopeVars_eq [minusDom_subst VEE]]]]]].
                     move: minusDom_subst.
                     replace (getInScopeVars in_scope')
                       with  (extendVarSetList (getInScopeVars in_scope) (v' :: nil))
                       by admit.
                     hs_simpl.
                     
                     etransitivity; first by apply StrongSubset_minusDom_extend_extend.
                     etransitivity; last by apply WSsubst'_SS.
                     
                     destruct cs_sub as [in_scope id_env tm cm] eqn:def_cs_sub.
                     move: (SE)
                       => [/= _ [_ [_ [/freshList_cons [fresh_v _] [inScopeVars_eq [minusDom_subst VEE]]]]]].
                     replace (getInScopeVars in_scope')
                       with  (extendVarSetList (getInScopeVars in_scope) (v' :: nil))
                       by admit.
                     hs_simpl.
                     etransitivity; first by apply StrongSubset_minusDom_extend_extend.
                     etransitivity; last by apply WSsubst'_SS.
                     setoid_rewrite inScopeVars_eq.
                     
                     etransitivity; first by apply StrongSubset_minusDom_extend_extend.
                     etransitivity; last by apply WSsubst'_SS.
                     

                     apply StrongSubset_extendVarSet_fresh.
                     move: WS_ext; hs_simpl.
                     rewrite /WellScoped*)
                   admit.
                     
                 --- move=> var; specialize (WSsubst'_lookup var).
                     case CMP: (v == var); [ rewrite lookupVarEnv_extendVarEnv_eq //
                                           | rewrite lookupVarEnv_extendVarEnv_neq // CMP // ].
                     eapply TrieMap_All_lookup_Some in LOOKUP; last eassumption.
                     by eapply SubstExtends_WellScoped_preserved in LOOKUP; last eassumption.
                 
           ++ replace (match e with Mk_Var _ => _ | _ => false end) with false by
                by case: e {LOOKUP} e_nonvar => //= ev []; exists ev.
              move=> [<-{env'} <-{out_id'}].
              split; first split.
              ** by destruct v'.
              ** by eapply TrieMap_All_lookup_Some in LOOKUP; last eassumption.
              ** (*suff: forall expr vars var, WellScoped expr (extendVarSet vars var) -> WellScoped expr (extendVarSet vars (zapIdUsageInfo var)).
                 {
                   apply.
                   eapply SubstExtends_WellScoped_iff; first eassumption.
                   eapply IHbody; last eassumption.
                   hs_simpl.
                   constructor=> //.
                   eapply TrieMap_All_impl_lookup.
                   2: { simpl.
                        apply TrieMap_All_insert; last eassumption.
                        - admit.
                        - rewrite /= /varToCoreExpr; hs_simpl=> /=.
                          suff: (forall subst subst' v v',
                                    GoodLocalVar v ->
                                    substBndr subst v = (subst',v') ->
                                    WellScopedVar v' (getSubstInScopeVars subst)).
                          {
                            by apply; last eassumption.
                          }
                            
                          {
                            clear=> -[in_scope id_env tm cm] subst' v v' GLV.
                            rewrite /= /substBndr; hs_simpl => /=; hs_simpl=> /=.
                            case CMP: (_ == _) => /=.
                            - move=> [_ <-{v'}].
                              rewrite Axioms.uniqAway_eq_same //.
                              admit.
                            - move=> [_ <-{v'}].
                              red.
                              case ILV: (isLocalVar _).
                              + case LOOKUP: (lookupVarSet _ _) => [v'|].
                                * split; last by apply GoodLocalVar_uniqAway.
                                  destruct v; simpl in *.
                                  rewrite /uniqAway.
                                  case EISS: (elemInScopeSet _ _).
                                  -- rewrite /uniqAway'.
                                     rewrite /setVarUnique.
                                     rewrite /Name.setNameUnique.
                                     rewrite /Core.varName.
                              + by apply GoodLocalVar_uniqAway.
                            

                          apply SubstExtends_WellScoped_iff.
                          
                          simpl in SE.
                          case: SE => //= [_ [_ [_ X]]].
                          destruct cs_sub as [in_scope id_env tm cm], sub' as [in_scope' id_env' tm' cm'].
                          simpl.
                          apply 
                          
                 all: try by eapply TrieMap_All_impl_lookup; last eassumption
                             move=> ? ? ? H; SubstExtends_WellScoped_preserved in H; last eassumption.
                 }
              *)
                admit.
      * rewrite /addBinding; hs_simpl=> /=.
        case testCSE: (noCSE v).
        -- move => [<-{env'} <-{out_id'}].
           split; first split=> //.
           ++ (* suff: WellScoped (cseExpr (CS sub' cs_map cs_rec_map) rhs) (getSubstInScopeVars sub') ->
                    WellScoped (cseExpr (CS sub' cs_map cs_rec_map) rhs) (getSubstInScopeVars cs_sub).
              {
                apply.
                eapply IHbind; last eassumption.
                constructor=> //=.
                all: try (eapply TrieMap_All_impl_lookup; last eassumption; simpl).
                all: try by move=> *; eapply SubstExtends_WellScoped_preserved; first eassumption.
                
              }
              *)
             admit.
           ++ eapply SubstExtends_WellScoped_iff; first eassumption.
              eapply IHbody; last eassumption.
              hs_simpl; constructor=> //.
              all: eapply TrieMap_All_impl_lookup; last eassumption.
              all: move=> ? ? LOOKUP' ?; eapply SubstExtends_WellScoped_preserved; first eassumption.
              all: by eapply TrieMap_All_lookup_Some in LOOKUP'; last eassumption.
        -- move def_rhs': (cseExpr (CS sub' cs_map cs_rec_map) rhs) => rhs'.
           destruct (case_if_Var rhs') as [rhs'_v|rhs' rhs'_nonvar] => //=; hs_simpl;
             last replace (match rhs' with Mk_Var _ => _ | _ => false end) with false by
                    (by case: rhs' {def_rhs'} rhs'_nonvar => //= rhs'_v []; exists rhs'_v);
             move=> [<-{env'} <-{out_id'}].
           ++ split; first split=> //.
              ** admit.
              ** admit.
           ++ admit.

  - rewrite (lock cseBind) /= -(lock cseBind).
    case: pairs IHbind => [|[in_id rhs] [|[in_id' rhs'] pairs]] IHbind [[GLVs [Uniq WS_pairs]] WS_body] /=.
    + repeat split=> //.
      by eapply IHbody; last eassumption.
    + case checkCSE: (noCSE in_id).
      * simpl; hs_simpl.
        repeat split; try constructor=> //=.
        -- (*apply GoodLocalVar_uniqAway.
           by inversion_clear GLVs.*)
          admit.
      * admit. (*case LOOKUP: (lookupCoreMap _ _) => [e|]; hs_simpl.*)
    + admit.

  - rewrite /= /cseCase => -[WS_scrut [GLV_bndr All_alts]].
    rewrite /addBinder /=.
    case def_sub'_v': (substBndr _ _) => [sub' v'].
    move: (GoodLocalVar_zapIdOccInfo bndr GLV_bndr) => GLV_zap.
    GoodLocalVar_WellScoped_substBndr => GLV' [SE WSsubst'].
    admit.

  - simpl; hs_simpl.
    case def_e': (lookupCoreMap _ _) => [e'|]; hs_simpl; last by apply IH.
    by eapply TrieMap_All_lookup_Some in def_e'; last eassumption; simpl in def_e'.
Admitted.
