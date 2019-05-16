(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require Core.
Require CoreFVs.
Require CoreSubst.
Require CoreUtils.
Require Data.Foldable.
Require Data.Traversable.
Require Data.Tuple.
Require Datatypes.
Require GHC.Base.
Require GHC.Err.
Require Id.
Require NestedRecursionHelpers.
Require TrieMap.
Require Util.

(* Converted type declarations: *)

Inductive CSEnv : Type
  := CS (cs_subst : CoreSubst.Subst) (cs_map : TrieMap.CoreMap Core.OutExpr)
  (cs_rec_map : TrieMap.CoreMap Core.OutExpr)
   : CSEnv.

Definition cs_map (arg_0__ : CSEnv) :=
  let 'CS _ cs_map _ := arg_0__ in
  cs_map.

Definition cs_rec_map (arg_0__ : CSEnv) :=
  let 'CS _ _ cs_rec_map := arg_0__ in
  cs_rec_map.

Definition cs_subst (arg_0__ : CSEnv) :=
  let 'CS cs_subst _ _ := arg_0__ in
  cs_subst.

(* Midamble *)

Require NestedRecursionHelpers.

(* default = emptyCSEnv *)
Instance Default__CSEnv : GHC.Err.Default CSEnv := {| GHC.Err.default := CS CoreSubst.emptySubst TrieMap.emptyCoreMap TrieMap.emptyCoreMap |}.

(* Converted value declarations: *)

Definition noCSE : Core.InId -> bool :=
  fun id =>
    orb (andb (negb (BasicTypes.isAlwaysActive (Id.idInlineActivation id))) (negb
               (BasicTypes.noUserInlineSpec (BasicTypes.inlinePragmaSpec (Id.idInlinePragma
                                                                          id))))) (orb (BasicTypes.isAnyInlinePragma
                                                                                        (Id.idInlinePragma id))
                                                                                       (Id.isJoinId id)).

Definition lookupSubst : CSEnv -> Core.Var -> Core.OutExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CS sub _ _, x =>
        CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "CSE.lookupSubst"))
        sub x
    end.

Definition lookupCSRecEnv
   : CSEnv -> Core.OutId -> Core.OutExpr -> option Core.OutExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | CS _ _ csmap, bndr, expr => TrieMap.lookupCoreMap csmap (Core.Lam bndr expr)
    end.

Definition lookupCSEnv : CSEnv -> Core.OutExpr -> option Core.OutExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CS _ csmap _, expr => TrieMap.lookupCoreMap csmap expr
    end.

Definition extendCSSubst : CSEnv -> Core.Var -> Core.CoreExpr -> CSEnv :=
  fun cse x rhs =>
    let 'CS cs_subst_0__ cs_map_1__ cs_rec_map_2__ := cse in
    CS (CoreSubst.extendSubst (cs_subst cse) x rhs) cs_map_1__ cs_rec_map_2__.

Definition extendCSRecEnv
   : CSEnv -> Core.OutId -> Core.OutExpr -> Core.OutExpr -> CSEnv :=
  fun cse bndr expr triv_expr =>
    let 'CS cs_subst_0__ cs_map_1__ cs_rec_map_2__ := cse in
    CS cs_subst_0__ cs_map_1__ (TrieMap.extendCoreMap (cs_rec_map cse) (Core.Lam
                                                                        bndr expr) triv_expr).

Definition extendCSEnv : CSEnv -> Core.OutExpr -> Core.OutExpr -> CSEnv :=
  fun cse expr triv_expr =>
    let sexpr := CoreUtils.stripTicksE Core.tickishFloatable expr in
    let 'CS cs_subst_1__ cs_map_2__ cs_rec_map_3__ := cse in
    CS cs_subst_1__ (TrieMap.extendCoreMap (cs_map cse) sexpr triv_expr)
       cs_rec_map_3__.

Definition emptyCSEnv : CSEnv :=
  CS CoreSubst.emptySubst TrieMap.emptyCoreMap TrieMap.emptyCoreMap.

Definition csEnvSubst : CSEnv -> CoreSubst.Subst :=
  cs_subst.

Definition combineAlts : CSEnv -> list Core.InAlt -> list Core.InAlt :=
  fun arg_0__ arg_1__ =>
    let j_2__ := match arg_0__, arg_1__ with | _, alts => alts end in
    match arg_0__, arg_1__ with
    | env, cons (pair (pair _ bndrs1) rhs1) rest_alts =>
        let in_scope := CoreSubst.substInScope (csEnvSubst env) in
        let ok :=
          fun bndr =>
            orb (Id.isDeadBinder bndr) (negb (Core.elemInScopeSet bndr in_scope)) in
        let identical :=
          fun '(pair (pair _con bndrs) rhs) =>
            andb (Data.Foldable.all ok bndrs) (CoreUtils.eqExpr in_scope rhs1 rhs) in
        let filtered_alts := Util.filterOut identical rest_alts in
        if Data.Foldable.all Id.isDeadBinder bndrs1 : bool
        then cons (pair (pair Core.DEFAULT nil) rhs1) filtered_alts else
        j_2__
    | _, _ => j_2__
    end.

Definition addRecBinders
   : CSEnv -> list Core.Var -> (CSEnv * list Core.Var)%type :=
  fun cse vs =>
    let 'pair sub' vs' := CoreSubst.substRecBndrs (cs_subst cse) vs in
    pair (let 'CS cs_subst_1__ cs_map_2__ cs_rec_map_3__ := cse in
          CS sub' cs_map_2__ cs_rec_map_3__) vs'.

Definition addBinding
   : CSEnv ->
     Core.InVar -> Core.OutId -> Core.OutExpr -> (CSEnv * Core.OutId)%type :=
  fun env in_id out_id rhs' =>
    let use_subst := match rhs' with | Core.Mk_Var _ => true | _ => false end in
    let zapped_id := Id.zapIdUsageInfo out_id in
    let id_expr' := Core.varToCoreExpr out_id in
    if negb (Core.isId in_id) : bool
    then pair (extendCSSubst env in_id rhs') out_id else
    if noCSE in_id : bool then pair env out_id else
    if use_subst : bool then pair (extendCSSubst env in_id rhs') out_id else
    pair (extendCSEnv env rhs' id_expr') zapped_id.

Definition addBinders
   : CSEnv -> list Core.Var -> (CSEnv * list Core.Var)%type :=
  fun cse vs =>
    let 'pair sub' vs' := CoreSubst.substBndrs (cs_subst cse) vs in
    pair (let 'CS cs_subst_1__ cs_map_2__ cs_rec_map_3__ := cse in
          CS sub' cs_map_2__ cs_rec_map_3__) vs'.

Definition addBinder : CSEnv -> Core.Var -> (CSEnv * Core.Var)%type :=
  fun cse v =>
    let 'pair sub' v' := CoreSubst.substBndr (cs_subst cse) v in
    pair (let 'CS cs_subst_1__ cs_map_2__ cs_rec_map_3__ := cse in
          CS sub' cs_map_2__ cs_rec_map_3__) v'.

Definition cseBind
   : BasicTypes.TopLevelFlag ->
     CSEnv -> Core.CoreBind -> (CSEnv * Core.CoreBind)%type :=
  fix cseExpr arg_0__ arg_1__
        := let tryForCSE env expr :=
             let expr' := cseExpr env expr in
             let expr'' := CoreUtils.stripTicksE Core.tickishFloatable expr' in
             let ticks := CoreUtils.stripTicksT Core.tickishFloatable expr' in
             match lookupCSEnv env expr'' with
             | Some e => CoreUtils.mkTicks ticks e
             | _ => expr'
             end in
           let cseCase env scrut bndr ty alts :=
             let bndr1 := Id.zapIdOccInfo bndr in
             let 'pair env1 bndr2 := addBinder env bndr1 in
             let scrut1 := tryForCSE env scrut in
             let 'pair alt_env bndr3 := addBinding env1 bndr bndr2 scrut1 in
             let con_target : Core.OutExpr := lookupSubst alt_env bndr in
             let arg_tys : list Core.OutType := nil in
             let cse_alt :=
               fun arg_5__ =>
                 let j_8__ :=
                   let 'pair (pair con args) rhs := arg_5__ in
                   let 'pair env' args' := addBinders alt_env args in
                   pair (pair con args') (tryForCSE env' rhs) in
                 match arg_5__ with
                 | pair (pair (Core.DataAlt con) args) rhs =>
                     let 'pair env' args' := addBinders alt_env args in
                     let con_expr := CoreUtils.mkAltExpr (Core.DataAlt con) args' arg_tys in
                     let new_env := extendCSEnv env' con_expr con_target in
                     if negb (Data.Foldable.null args) : bool
                     then pair (pair (Core.DataAlt con) args') (tryForCSE new_env rhs) else
                     j_8__
                 | _ => j_8__
                 end in
             let ty' := tt in
             Core.Case scrut1 bndr3 ty' (combineAlts alt_env (GHC.Base.map cse_alt alts)) in
           match arg_0__, arg_1__ with
           | env, Core.Type_ t => Core.Type_ (tt)
           | env, Core.Coercion c => Core.Coercion (tt)
           | _, Core.Lit lit => Core.Lit lit
           | env, Core.Mk_Var v => lookupSubst env v
           | env, Core.App f a => Core.App (cseExpr env f) (tryForCSE env a)
           | env, Core.Tick t e => Core.Tick t (cseExpr env e)
           | env, Core.Cast e co => Core.Cast (tryForCSE env e) (tt)
           | env, Core.Lam b e =>
               let 'pair env' b' := addBinder env b in
               Core.Lam b' (cseExpr env' e)
           | env, Core.Let bind e =>
               let 'pair env' bind' := cseBind BasicTypes.NotTopLevel env bind in
               Core.Let bind' (cseExpr env' e)
           | env, Core.Case e bndr ty alts => cseCase env e bndr ty alts
           end with cseBind arg_0__ arg_1__ arg_2__
                      := let tryForCSE env expr :=
                           let expr' := cseExpr env expr in
                           let expr'' := CoreUtils.stripTicksE Core.tickishFloatable expr' in
                           let ticks := CoreUtils.stripTicksT Core.tickishFloatable expr' in
                           match lookupCSEnv env expr'' with
                           | Some e => CoreUtils.mkTicks ticks e
                           | _ => expr'
                           end in
                         let cse_bind arg_0__ arg_1__ arg_2__ arg_3__ :=
                           match arg_0__, arg_1__, arg_2__, arg_3__ with
                           | toplevel, env, pair in_id in_rhs, out_id =>
                               let out_rhs := tryForCSE env in_rhs in
                               let 'pair env' out_id' := addBinding env in_id out_id out_rhs in
                               if andb (BasicTypes.isTopLevel toplevel) (CoreUtils.exprIsTickedString
                                        in_rhs) : bool
                               then pair env' (pair out_id in_rhs) else
                               match Id.isJoinId_maybe in_id with
                               | Some arity =>
                                   NestedRecursionHelpers.collectNBinders_k arity in_rhs (fun params in_body =>
                                                                               let 'pair env' params' := addBinders env
                                                                                                           params in
                                                                               let out_body := tryForCSE env' in_body in
                                                                               pair env (pair out_id (Core.mkLams
                                                                                               params' out_body)))
                               | _ => pair env' (pair out_id' out_rhs)
                               end
                           end in
                         match arg_0__, arg_1__, arg_2__ with
                         | toplevel, env, Core.NonRec b e =>
                             let 'pair env1 b1 := addBinder env b in
                             let 'pair env2 (pair b2 e2) := cse_bind toplevel env1 (pair b e) b1 in
                             pair env2 (Core.NonRec b2 e2)
                         | _, env, Core.Rec (cons (pair in_id rhs) nil) =>
                             match addRecBinders env (cons in_id nil) with
                             | pair env1 (cons out_id nil) =>
                                 let rhs' := cseExpr env1 rhs in
                                 let rhs'' := CoreUtils.stripTicksE Core.tickishFloatable rhs' in
                                 let ticks := CoreUtils.stripTicksT Core.tickishFloatable rhs' in
                                 let id_expr' := Core.varToCoreExpr out_id in
                                 let zapped_id := Id.zapIdUsageInfo out_id in
                                 if noCSE in_id : bool
                                 then pair env1 (Core.Rec (cons (pair out_id rhs') nil)) else
                                 match lookupCSRecEnv env out_id rhs'' with
                                 | Some previous =>
                                     let previous' := CoreUtils.mkTicks ticks previous in
                                     pair (extendCSSubst env1 in_id previous') (Core.NonRec out_id previous')
                                 | _ =>
                                     pair (extendCSRecEnv env1 out_id rhs'' id_expr') (Core.Rec (cons (pair zapped_id
                                                                                                            rhs') nil))
                                 end
                             | _ => GHC.Err.patternFailure
                             end
                         | _, _, _ =>
                             match arg_0__, arg_1__, arg_2__ with
                             | toplevel, env, Core.Rec pairs =>
                                 let do_one :=
                                   fun arg_3__ arg_4__ =>
                                     match arg_3__, arg_4__ with
                                     | env, pair pr b1 => cse_bind toplevel env pr b1
                                     end in
                                 let 'pair env1 bndrs1 := addRecBinders env (GHC.Base.map Data.Tuple.fst
                                                                             pairs) in
                                 let 'pair env2 pairs' := NestedRecursionHelpers.zipMapAccumL do_one env1 pairs
                                                                                              bndrs1 in
                                 pair env2 (Core.Rec pairs')
                             | _, _, _ => GHC.Err.patternFailure
                             end
                         end for cseBind.

Definition cseProgram : Core.CoreProgram -> Core.CoreProgram :=
  fun binds =>
    Data.Tuple.snd (Data.Traversable.mapAccumL (cseBind BasicTypes.TopLevel)
                    emptyCSEnv binds).

Definition cseExpr : CSEnv -> Core.InExpr -> Core.OutExpr :=
  fix cseExpr arg_0__ arg_1__
        := let tryForCSE env expr :=
             let expr' := cseExpr env expr in
             let expr'' := CoreUtils.stripTicksE Core.tickishFloatable expr' in
             let ticks := CoreUtils.stripTicksT Core.tickishFloatable expr' in
             match lookupCSEnv env expr'' with
             | Some e => CoreUtils.mkTicks ticks e
             | _ => expr'
             end in
           let cseCase env scrut bndr ty alts :=
             let bndr1 := Id.zapIdOccInfo bndr in
             let 'pair env1 bndr2 := addBinder env bndr1 in
             let scrut1 := tryForCSE env scrut in
             let 'pair alt_env bndr3 := addBinding env1 bndr bndr2 scrut1 in
             let con_target : Core.OutExpr := lookupSubst alt_env bndr in
             let arg_tys : list Core.OutType := nil in
             let cse_alt :=
               fun arg_5__ =>
                 let j_8__ :=
                   let 'pair (pair con args) rhs := arg_5__ in
                   let 'pair env' args' := addBinders alt_env args in
                   pair (pair con args') (tryForCSE env' rhs) in
                 match arg_5__ with
                 | pair (pair (Core.DataAlt con) args) rhs =>
                     let 'pair env' args' := addBinders alt_env args in
                     let con_expr := CoreUtils.mkAltExpr (Core.DataAlt con) args' arg_tys in
                     let new_env := extendCSEnv env' con_expr con_target in
                     if negb (Data.Foldable.null args) : bool
                     then pair (pair (Core.DataAlt con) args') (tryForCSE new_env rhs) else
                     j_8__
                 | _ => j_8__
                 end in
             let ty' := tt in
             Core.Case scrut1 bndr3 ty' (combineAlts alt_env (GHC.Base.map cse_alt alts)) in
           match arg_0__, arg_1__ with
           | env, Core.Type_ t => Core.Type_ (tt)
           | env, Core.Coercion c => Core.Coercion (tt)
           | _, Core.Lit lit => Core.Lit lit
           | env, Core.Mk_Var v => lookupSubst env v
           | env, Core.App f a => Core.App (cseExpr env f) (tryForCSE env a)
           | env, Core.Tick t e => Core.Tick t (cseExpr env e)
           | env, Core.Cast e co => Core.Cast (tryForCSE env e) (tt)
           | env, Core.Lam b e =>
               let 'pair env' b' := addBinder env b in
               Core.Lam b' (cseExpr env' e)
           | env, Core.Let bind e =>
               let 'pair env' bind' := cseBind BasicTypes.NotTopLevel env bind in
               Core.Let bind' (cseExpr env' e)
           | env, Core.Case e bndr ty alts => cseCase env e bndr ty alts
           end with cseBind arg_0__ arg_1__ arg_2__
                      := let tryForCSE env expr :=
                           let expr' := cseExpr env expr in
                           let expr'' := CoreUtils.stripTicksE Core.tickishFloatable expr' in
                           let ticks := CoreUtils.stripTicksT Core.tickishFloatable expr' in
                           match lookupCSEnv env expr'' with
                           | Some e => CoreUtils.mkTicks ticks e
                           | _ => expr'
                           end in
                         let cse_bind arg_0__ arg_1__ arg_2__ arg_3__ :=
                           match arg_0__, arg_1__, arg_2__, arg_3__ with
                           | toplevel, env, pair in_id in_rhs, out_id =>
                               let out_rhs := tryForCSE env in_rhs in
                               let 'pair env' out_id' := addBinding env in_id out_id out_rhs in
                               if andb (BasicTypes.isTopLevel toplevel) (CoreUtils.exprIsTickedString
                                        in_rhs) : bool
                               then pair env' (pair out_id in_rhs) else
                               match Id.isJoinId_maybe in_id with
                               | Some arity =>
                                   NestedRecursionHelpers.collectNBinders_k arity in_rhs (fun params in_body =>
                                                                               let 'pair env' params' := addBinders env
                                                                                                           params in
                                                                               let out_body := tryForCSE env' in_body in
                                                                               pair env (pair out_id (Core.mkLams
                                                                                               params' out_body)))
                               | _ => pair env' (pair out_id' out_rhs)
                               end
                           end in
                         match arg_0__, arg_1__, arg_2__ with
                         | toplevel, env, Core.NonRec b e =>
                             let 'pair env1 b1 := addBinder env b in
                             let 'pair env2 (pair b2 e2) := cse_bind toplevel env1 (pair b e) b1 in
                             pair env2 (Core.NonRec b2 e2)
                         | _, env, Core.Rec (cons (pair in_id rhs) nil) =>
                             match addRecBinders env (cons in_id nil) with
                             | pair env1 (cons out_id nil) =>
                                 let rhs' := cseExpr env1 rhs in
                                 let rhs'' := CoreUtils.stripTicksE Core.tickishFloatable rhs' in
                                 let ticks := CoreUtils.stripTicksT Core.tickishFloatable rhs' in
                                 let id_expr' := Core.varToCoreExpr out_id in
                                 let zapped_id := Id.zapIdUsageInfo out_id in
                                 if noCSE in_id : bool
                                 then pair env1 (Core.Rec (cons (pair out_id rhs') nil)) else
                                 match lookupCSRecEnv env out_id rhs'' with
                                 | Some previous =>
                                     let previous' := CoreUtils.mkTicks ticks previous in
                                     pair (extendCSSubst env1 in_id previous') (Core.NonRec out_id previous')
                                 | _ =>
                                     pair (extendCSRecEnv env1 out_id rhs'' id_expr') (Core.Rec (cons (pair zapped_id
                                                                                                            rhs') nil))
                                 end
                             | _ => GHC.Err.patternFailure
                             end
                         | _, _, _ =>
                             match arg_0__, arg_1__, arg_2__ with
                             | toplevel, env, Core.Rec pairs =>
                                 let do_one :=
                                   fun arg_3__ arg_4__ =>
                                     match arg_3__, arg_4__ with
                                     | env, pair pr b1 => cse_bind toplevel env pr b1
                                     end in
                                 let 'pair env1 bndrs1 := addRecBinders env (GHC.Base.map Data.Tuple.fst
                                                                             pairs) in
                                 let 'pair env2 pairs' := NestedRecursionHelpers.zipMapAccumL do_one env1 pairs
                                                                                              bndrs1 in
                                 pair env2 (Core.Rec pairs')
                             | _, _, _ => GHC.Err.patternFailure
                             end
                         end for cseExpr.

Definition cseOneExpr : Core.InExpr -> Core.OutExpr :=
  fun e =>
    let env :=
      let 'CS cs_subst_0__ cs_map_1__ cs_rec_map_2__ := emptyCSEnv in
      CS (CoreSubst.mkEmptySubst (Core.mkInScopeSet (CoreFVs.exprFreeVars e)))
         cs_map_1__ cs_rec_map_2__ in
    cseExpr env e.

Definition tryForCSE : CSEnv -> Core.InExpr -> Core.OutExpr :=
  fun env expr =>
    let expr' := cseExpr env expr in
    let expr'' := CoreUtils.stripTicksE Core.tickishFloatable expr' in
    let ticks := CoreUtils.stripTicksT Core.tickishFloatable expr' in
    match lookupCSEnv env expr'' with
    | Some e => CoreUtils.mkTicks ticks e
    | _ => expr'
    end.

Definition cseCase
   : CSEnv ->
     Core.InExpr -> Core.InId -> Core.InType -> list Core.InAlt -> Core.OutExpr :=
  fun env scrut bndr ty alts =>
    let bndr1 := Id.zapIdOccInfo bndr in
    let 'pair env1 bndr2 := addBinder env bndr1 in
    let scrut1 := tryForCSE env scrut in
    let 'pair alt_env bndr3 := addBinding env1 bndr bndr2 scrut1 in
    let con_target : Core.OutExpr := lookupSubst alt_env bndr in
    let arg_tys : list Core.OutType := nil in
    let cse_alt :=
      fun arg_5__ =>
        let j_8__ :=
          let 'pair (pair con args) rhs := arg_5__ in
          let 'pair env' args' := addBinders alt_env args in
          pair (pair con args') (tryForCSE env' rhs) in
        match arg_5__ with
        | pair (pair (Core.DataAlt con) args) rhs =>
            let 'pair env' args' := addBinders alt_env args in
            let con_expr := CoreUtils.mkAltExpr (Core.DataAlt con) args' arg_tys in
            let new_env := extendCSEnv env' con_expr con_target in
            if negb (Data.Foldable.null args) : bool
            then pair (pair (Core.DataAlt con) args') (tryForCSE new_env rhs) else
            j_8__
        | _ => j_8__
        end in
    let ty' := tt in
    Core.Case scrut1 bndr3 ty' (combineAlts alt_env (GHC.Base.map cse_alt alts)).

Definition cse_bind
   : BasicTypes.TopLevelFlag ->
     CSEnv ->
     (Core.InId * Core.InExpr)%type ->
     Core.OutId -> (CSEnv * (Core.OutId * Core.OutExpr)%type)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | toplevel, env, pair in_id in_rhs, out_id =>
        let out_rhs := tryForCSE env in_rhs in
        let 'pair env' out_id' := addBinding env in_id out_id out_rhs in
        if andb (BasicTypes.isTopLevel toplevel) (CoreUtils.exprIsTickedString
                 in_rhs) : bool
        then pair env' (pair out_id in_rhs) else
        match Id.isJoinId_maybe in_id with
        | Some arity =>
            NestedRecursionHelpers.collectNBinders_k arity in_rhs (fun params in_body =>
                                                        let 'pair env' params' := addBinders env params in
                                                        let out_body := tryForCSE env' in_body in
                                                        pair env (pair out_id (Core.mkLams params' out_body)))
        | _ => pair env' (pair out_id' out_rhs)
        end
    end.

(* External variables:
     Some andb bool cons false list negb nil op_zt__ option orb pair true tt
     BasicTypes.NotTopLevel BasicTypes.TopLevel BasicTypes.TopLevelFlag
     BasicTypes.inlinePragmaSpec BasicTypes.isAlwaysActive
     BasicTypes.isAnyInlinePragma BasicTypes.isTopLevel BasicTypes.noUserInlineSpec
     Core.App Core.Case Core.Cast Core.Coercion Core.CoreBind Core.CoreExpr
     Core.CoreProgram Core.DEFAULT Core.DataAlt Core.InAlt Core.InExpr Core.InId
     Core.InType Core.InVar Core.Lam Core.Let Core.Lit Core.Mk_Var Core.NonRec
     Core.OutExpr Core.OutId Core.OutType Core.Rec Core.Tick Core.Type_ Core.Var
     Core.elemInScopeSet Core.isId Core.mkInScopeSet Core.mkLams
     Core.tickishFloatable Core.varToCoreExpr CoreFVs.exprFreeVars CoreSubst.Subst
     CoreSubst.emptySubst CoreSubst.extendSubst CoreSubst.lookupIdSubst
     CoreSubst.mkEmptySubst CoreSubst.substBndr CoreSubst.substBndrs
     CoreSubst.substInScope CoreSubst.substRecBndrs CoreUtils.eqExpr
     CoreUtils.exprIsTickedString CoreUtils.mkAltExpr CoreUtils.mkTicks
     CoreUtils.stripTicksE CoreUtils.stripTicksT Data.Foldable.all Data.Foldable.null
     Data.Traversable.mapAccumL Data.Tuple.fst Data.Tuple.snd Datatypes.id
     GHC.Base.map GHC.Err.patternFailure Id.idInlineActivation Id.idInlinePragma
     Id.isDeadBinder Id.isJoinId Id.isJoinId_maybe Id.zapIdOccInfo Id.zapIdUsageInfo
     NestedRecursionHelpers.collectNBinders_k NestedRecursionHelpers.zipMapAccumL
     TrieMap.CoreMap TrieMap.emptyCoreMap TrieMap.extendCoreMap TrieMap.lookupCoreMap
     Util.filterOut
*)
