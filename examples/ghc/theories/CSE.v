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

Theorem foldr_id {A B} (a : A) (bs : list B) : foldr (fun _ => id) a bs = a.
Proof. by elim: bs. Qed.

(*
Theorem stripTicksE_id {b} p (e : Expr b) :
  stripTicksE p e = e.
Proof.
  rewrite /stripTicksE.
  match goal with |- ?go_def ?e = ?e => set go := go_def end.
  
  elim/(@core_induct' b): e =>
    [ v | lit
    | e1 e2 IH1 IH2 | v e IH
    | [v rhs | pairs] body IHbind IHbody | scrut bndr ty alts IHscrut IHalts
    | e ty IH | tickish e IH
    | co | ty ]
    //=; rewrite -/go;
    try by repeat f_equal.
  
  - admit.
  - admit.
  - case: (p tickish); rewrite IH=> //.
Abort.

Lemma mkTicks_id ticks e : mkTicks ticks e = e.
Proof. apply foldr_id. Qed.
*)
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

(*
Lemma stripTicksE_App {b} p (e1 e2 : Expr b) :
  stripTicksE p (App e1 e2) = App (stripTicksE p e1) (stripTicksE p e2).
Proof. done. Qed.
Hint Rewrite @stripTicksE_App : hs_simpl.
Hint Rewrite (@stripTicksE_App CoreBndr) : hs_simpl.

Lemma stripTicksE_Lam {b} p (bndr : b) e :
  stripTicksE p (Lam bndr e) = Lam bndr (stripTicksE p e).
Proof. done. Qed.
Hint Rewrite @stripTicksE_Lam : hs_simpl.
Hint Rewrite (@stripTicksE_Lam CoreBndr) : hs_simpl.

Lemma stripTicksE_Let_NonRec {b} p (bndr : b) rhs body :
  stripTicksE p (Let (NonRec bndr rhs) body) =
  Let (NonRec bndr (stripTicksE p rhs)) (stripTicksE p body).
Proof. done. Qed.
Hint Rewrite @stripTicksE_Let_NonRec : hs_simpl.
Hint Rewrite (@stripTicksE_Let_NonRec CoreBndr) : hs_simpl.

Lemma stripTicksE_Let_Rec {b} p (bndrs : list (b * Expr b)) body :
  stripTicksE p (Let (Rec bndrs) body) =
  Let (Rec (map (fun '(b',e') => (b', stripTicksE p e')) bndrs)) (stripTicksE p body).
Proof. done. Qed.
Hint Rewrite @stripTicksE_Let_Rec : hs_simpl.
Hint Rewrite (@stripTicksE_Let_Rec CoreBndr) : hs_simpl.

Lemma stripTicksE_Case {b} p e (bndr : b) t alts :
  stripTicksE p (Case e bndr t alts) =
  Case (stripTicksE p e) bndr t (map (fun '(c, bs, e) => (c, bs, stripTicksE p e)) alts).
Proof. done. Qed.
Hint Rewrite @stripTicksE_Case : hs_simpl.
Hint Rewrite (@stripTicksE_Case CoreBndr) : hs_simpl.

Lemma stripTicksE_Cast {b} p (e : Expr b) t :
  stripTicksE p (Cast e t) =
  Cast (stripTicksE p e) t.
Proof. done. Qed.
Hint Rewrite @stripTicksE_Cast : hs_simpl.
Hint Rewrite (@stripTicksE_Cast CoreBndr) : hs_simpl.

Lemma stripTicksE_Tick {b} p t (e : Expr b) :
  stripTicksE p (Tick t e) =
  if p t
  then stripTicksE p e
  else Tick t (stripTicksE p e).
Proof. done. Qed. 
Hint Rewrite @stripTicksE_Tick : hs_simpl.
Hint Rewrite (@stripTicksE_Tick CoreBndr) : hs_simpl.
*)

Theorem flat_map_ext {A B} (f g : A -> list B) xs :
  f =1 g ->
  flat_map f xs = flat_map g xs.
Proof.
  move=> EQ1.
  elim: xs => [|x xs IH] //=.
  by rewrite EQ1 IH.
Qed.

Theorem Forall_In_impl {A} {P : A -> Prop} (Q : A -> Prop) :
  forall l,
  (forall a, In a l -> P a -> Q a) ->
  Forall P l -> Forall Q l.
Proof.
  move=> l; rewrite !Forall_forall => IMPL In__P x IN.
  by apply IMPL; last apply In__P.
Qed.

(*
Lemma stripTicksE_map_fst {a b} p (pairs : list (a * Expr b)) :
  List.map fst (List.map (fun '(b', e') => (b', stripTicksE p e')) pairs) = List.map fst pairs.
Proof. by rewrite List.map_map; apply map_ext; case. Qed.

Theorem WellScoped_stripTicksE p e vars :
  WellScoped e vars <-> WellScoped (stripTicksE p e) vars.
Proof.
  elim/core_induct: e vars => 
    [ v | lit
    | e1 e2 IH1 IH2 | v e IH
    | [v rhs | pairs] body IHbind IHbody | scrut bndr ty alts IHscrut IHalts
    | e ty IH | tickish e IH
    | co | ty ]
    vars
    //;
    hs_simpl.
  - by rewrite /= IH1 IH2.
  - by rewrite /= IH.
  - by rewrite /= IHbind IHbody.
  - rewrite /= IHbody.
    repeat match goal with |- context[flat_map (fun '(b,_) => b :: nil) ?ps] =>
      replace (flat_map (fun '(b,_) => b :: nil) ps) with (map fst ps)
        by (rewrite -flat_map_cons_f; apply flat_map_ext; by case)
    end.
    replace @map with @List.map by done.
    rewrite !Forall'_Forall !Forall_map.
    rewrite !stripTicksE_map_fst.
    split; move=> [[GLV_pairs [ND_pairs WS_ext_pairs]] WS_pairs]; repeat split=> //.
    + by eapply Forall_impl => [[b e]|]; last by apply GLV_pairs.
    + eapply Forall_In_impl => [[b e]|]; last by apply WS_ext_pairs.
      by move=> /= /IHbind ->.
    + by eapply Forall_impl => [[b e]|]; last by apply GLV_pairs.
    + eapply Forall_In_impl => [[b e]|]; last by apply WS_ext_pairs.
      by move=> /= /IHbind ->.
  - rewrite /= IHscrut.
    replace @map with @List.map by done.
    rewrite !Forall'_Forall !Forall_map.
    split; move=> [WS_vars [GLV OK_alts]]; repeat split=> //.
    all: eapply Forall_In_impl; last by apply OK_alts.
    all: move=> [[c bs] e] IN /=.
    all: by rewrite -IHalts; last by apply IN.
  - by rewrite /= IH.
  - case: (p tickish) => //=.
Qed.
*)

(* TODO freeVars/freeVarsBind *)

Definition WS_cseExpr vars env e :
  WellScopedCSEnv env             vars ->
  WellScoped      e               vars ->
  WellScoped      (cseExpr env e) (getSubstInScopeVars (cs_subst env)).
Proof.
  elim/core_induct: e vars env => 
    [ v | lit
    | e1 e2 IH1 IH2 | v e IH
    | [v rhs | pairs] body IHbind IHbody | scrut bndr ty alts IHscrut IHalts
    | e ty IH (* | tickish e IH *)
    | co | ty ]
    vars
    [[in_scope id_env tm cm] cs_map cs_rec_map]
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

  - admit. (* rewrite /= /addBinder /= => -[GLV WSe].
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
    + constructor=> //; rewrite /cs_subst //. *)

  - admit. (* rewrite (lock cse_bind) /= -(lock cse_bind) => -[[GLV WS_rhs] WS_ext].
    have NTV: isTyVar v = false. admit.
    have NCV: isCoVar v = false. admit.
    rewrite /addBinder /substBndr /cs_subst. rewrite NTV NCV.
    case def_sub'_v': (substIdBndr _ _ _ _) => [sub' v'].
    have GLV': GoodLocalVar v' by eapply GoodLocalVar_substIdBndr; eassumption.
    move: (WellScoped_Subst_substIdBndr _ _ _ _ _ _ _ def_sub'_v' GLV WSsubst)
        => [subst_ext WSsubst'].      
    (* cse_bind *)
    simpl.
    case def_env'_out_id': (addBinding _ _ _ _) => [env' out_id'].
    case join_v: (isJoinId_maybe v) => [arity|].
    * admit.
    * rewrite /tryForCSE.
    *)

(*       case def_env2_b2_e2: (cse_bind _ _ _ _) => [env2 [b2 e2]]. *)
      
      
                                
    
    
(*     have not_tv: ~~ isTyVar v. *)
(*     move: GLV => [] _ {WS_ext}. *)
(*     case: v => //=. simpl.  *)
(*     move=> ? ? ?. *)
(*     rewrite /isLocalVar. simpl *)
                             

(* case: v GLV {WS_ext} => [? ? ? | ? ? ? ? | ? ? ? ? ? ?]. *)
    
(*     have not_cv: ~~ isCoVar v. *)
    
(*     rewrite {1}/WellScoped -/WellScoped. *)
(*     rewrite /bindersOf extendVarSetList_singleton. *)
(*     rewrite /cs_subst /getSubstInScopeVars. *)
(*     move=> . *)
(*     rewrite /cseExpr -/cseExpr -/cse_bind. *)

  - admit.

  - admit.

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
