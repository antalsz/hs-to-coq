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
Require Coq.Init.Datatypes.
Require Core.
Require CoreArity.
Require CoreFVs.
Require CoreSubst.
Require CoreUtils.
Require Data.Foldable.
Require Data.Traversable.
Require Data.Tuple.
Require Datatypes.
Require DynFlags.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require Literal.
Require Maybes.
Require Module.
Require Panic.
Require PrelNames.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive SimpleOptEnv : Type
  := | SOE (soe_inl : Core.IdEnv (SimpleOptEnv * Core.InExpr)%type%type)
  (soe_subst : CoreSubst.Subst)
   : SimpleOptEnv.

Definition SimpleClo :=
  (SimpleOptEnv * Core.InExpr)%type%type.

Inductive ConCont : Type := | CC : list Core.CoreExpr -> unit -> ConCont.

Instance Default__SimpleOptEnv : GHC.Err.Default SimpleOptEnv :=
  GHC.Err.Build_Default _ (SOE GHC.Err.default GHC.Err.default).

Definition soe_inl (arg_0__ : SimpleOptEnv) :=
  let 'SOE soe_inl _ := arg_0__ in
  soe_inl.

Definition soe_subst (arg_0__ : SimpleOptEnv) :=
  let 'SOE _ soe_subst := arg_0__ in
  soe_subst.

(* Converted value declarations: *)

Definition wrapLet
   : option (Core.Id * Core.CoreExpr)%type -> Core.CoreExpr -> Core.CoreExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | None, body => body
    | Some (pair b r), body => Core.Let (Core.NonRec b r) body
    end.

Definition subst_opt_id_bndr
   : SimpleOptEnv -> Core.InId -> (SimpleOptEnv * Core.OutId)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | SOE inl_ subst, old_id =>
        let new_inl := Core.delVarEnv inl_ old_id in
        let 'CoreSubst.Mk_Subst in_scope id_subst tv_subst cv_subst := subst in
        let id1 := Core.uniqAway in_scope old_id in
        let id2 := id1 in
        let new_id := Id.zapFragileIdInfo id2 in
        let no_change := new_id GHC.Base.== old_id in
        let new_in_scope := Core.extendInScopeSet in_scope new_id in
        let new_id_subst :=
          if no_change : bool then Core.delVarEnv id_subst old_id else
          Core.extendVarEnv id_subst old_id (Core.Mk_Var new_id) in
        let new_subst :=
          CoreSubst.Mk_Subst new_in_scope new_id_subst tv_subst cv_subst in
        pair (SOE new_inl new_subst) new_id
    end.

Definition subst_opt_bndr
   : SimpleOptEnv -> Core.InVar -> (SimpleOptEnv * Core.OutVar)%type :=
  fun env bndr =>
    let subst := soe_subst env in
    let 'pair subst_tv tv' := CoreSubst.substTyVarBndr subst bndr in
    let 'pair subst_cv cv' := CoreSubst.substCoVarBndr subst bndr in
    if Core.isTyVar bndr : bool
    then pair (let 'SOE soe_inl_9__ soe_subst_10__ := env in
               SOE soe_inl_9__ subst_tv) tv' else
    if Core.isCoVar bndr : bool
    then pair (let 'SOE soe_inl_4__ soe_subst_5__ := env in
               SOE soe_inl_4__ subst_cv) cv' else
    subst_opt_id_bndr env bndr.

Definition subst_opt_bndrs
   : SimpleOptEnv -> list Core.InVar -> (SimpleOptEnv * list Core.OutVar)%type :=
  fun env bndrs => Data.Traversable.mapAccumL subst_opt_bndr env bndrs.

Definition soeZapSubst : SimpleOptEnv -> SimpleOptEnv :=
  fun '(SOE _ subst) => SOE Core.emptyVarEnv (CoreSubst.zapSubstEnv subst).

Definition soeSetInScope : SimpleOptEnv -> SimpleOptEnv -> SimpleOptEnv :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | SOE _ subst1, (SOE _ subst2 as env2) =>
        let 'SOE soe_inl_2__ soe_subst_3__ := env2 in
        SOE soe_inl_2__ (CoreSubst.setInScope subst2 (CoreSubst.substInScope subst1))
    end.

Definition simpleUnfoldingFun : Core.IdUnfoldingFun :=
  fun id =>
    if BasicTypes.isAlwaysActive (Id.idInlineActivation id) : bool
    then Id.idUnfolding id else
    Core.noUnfolding.

Axiom pushCoercionIntoLambda : Core.InScopeSet ->
                               Core.Var -> Core.CoreExpr -> unit -> option (Core.Var * Core.CoreExpr)%type.

Axiom pushCoValArg : unit -> option (unit * unit)%type.

Axiom pushCoTyArg : unit -> unit -> option (unit * unit)%type.

Axiom pushCoDataCon : Core.DataCon ->
                      list Core.CoreExpr ->
                      unit -> option (Core.DataCon * list unit * list Core.CoreExpr)%type.

Axiom pushCoArgs : unit ->
                   list Core.CoreArg -> option (list Core.CoreArg * unit)%type.

Axiom pushCoArg : unit -> Core.CoreArg -> option (Core.CoreArg * unit)%type.

Definition joinPointBinding_maybe
   : Core.InBndr -> Core.InExpr -> option (Core.InBndr * Core.InExpr)%type :=
  fun bndr rhs =>
    if negb (Core.isId bndr) : bool then None else
    if Id.isJoinId bndr : bool then Some (pair bndr rhs) else
    match BasicTypes.tailCallInfo (Id.idOccInfo bndr) with
    | BasicTypes.AlwaysTailCalled join_arity =>
        let 'pair bndrs body := CoreArity.etaExpandToJoinPoint join_arity rhs in
        Some (pair (Id.asJoinId bndr join_arity) (Core.mkLams bndrs body))
    | _ => None
    end.

Definition joinPointBindings_maybe
   : list (Core.InBndr * Core.InExpr)%type ->
     option (list (Core.InBndr * Core.InExpr)%type) :=
  fun bndrs =>
    Data.Traversable.mapM (Data.Tuple.uncurry joinPointBinding_maybe) bndrs.

Definition exprIsLiteral_maybe
   : Core.InScopeEnv -> Core.CoreExpr -> option Literal.Literal :=
  fix exprIsLiteral_maybe (arg_0__ : Core.InScopeEnv) (arg_1__ : Core.CoreExpr)
        : option Literal.Literal
        := match arg_0__, arg_1__ with
           | (pair _ id_unf as env), e =>
               match e with
               | Core.Lit l => Some l
               | Core.Tick _ e' => exprIsLiteral_maybe env e'
               | Core.Mk_Var v =>
                   match None with
                   | Some rhs => exprIsLiteral_maybe env rhs
                   | _ => None
                   end
               | _ => None
               end
           end.

Axiom exprIsConApp_maybe : Core.InScopeEnv ->
                           Core.CoreExpr -> option (Core.DataCon * list unit * list Core.CoreExpr)%type.

Definition emptyEnv : SimpleOptEnv :=
  SOE Core.emptyVarEnv CoreSubst.emptySubst.

Axiom dealWithStringLiteral : Core.Var ->
                              GHC.Base.String ->
                              unit -> option (Core.DataCon * list unit * list Core.CoreExpr)%type.

Axiom collectBindersPushingCo : Core.CoreExpr ->
                                (list Core.Var * Core.CoreExpr)%type.

Definition add_info
   : SimpleOptEnv -> Core.InVar -> Core.OutVar -> Core.OutVar :=
  fun env old_bndr new_bndr =>
    let subst := soe_subst env in
    let mb_new_info :=
      CoreSubst.substIdInfo subst new_bndr ((@Core.idInfo tt old_bndr)) in
    if Core.isTyVar old_bndr : bool then new_bndr else
    Id.maybeModifyIdInfo mb_new_info new_bndr.

Definition simple_out_bind_pair
   : SimpleOptEnv ->
     Core.InId ->
     option Core.OutId ->
     Core.OutExpr ->
     BasicTypes.OccInfo ->
     bool ->
     bool -> (SimpleOptEnv * option (Core.OutVar * Core.OutExpr)%type)%type :=
  fun env in_bndr mb_out_bndr out_rhs occ_info active stable_unf =>
    let coercible_hack :=
      match Core.collectArgs out_rhs with
      | pair (Core.Mk_Var fun_) args =>
          match Id.isDataConWorkId_maybe fun_ with
          | Some dc =>
              if orb (Unique.hasKey dc PrelNames.heqDataConKey) (Unique.hasKey dc
                                                                               PrelNames.coercibleDataConKey) : bool
              then Data.Foldable.all CoreUtils.exprIsTrivial args else
              false
          | _ => false
          end
      | _ => false
      end in
    let post_inline_unconditionally : bool :=
      if negb active : bool then false else
      if BasicTypes.isWeakLoopBreaker occ_info : bool then false else
      if stable_unf : bool then false else
      if Core.isExportedId in_bndr : bool then false else
      if CoreUtils.exprIsTrivial out_rhs : bool then true else
      if coercible_hack : bool then true else
      false in
    let 'pair env' bndr1 := (match mb_out_bndr with
                               | Some out_bndr => pair env out_bndr
                               | None => subst_opt_bndr env in_bndr
                               end) in
    let out_bndr := add_info env' in_bndr bndr1 in
    if post_inline_unconditionally : bool
    then pair (let 'SOE soe_inl_13__ soe_subst_14__ := env' in
               SOE soe_inl_13__ (CoreSubst.extendIdSubst (soe_subst env) in_bndr out_rhs))
              None else
    pair env' (Some (pair out_bndr out_rhs)).

Definition simple_out_bind
   : SimpleOptEnv ->
     (Core.InVar * Core.OutExpr)%type ->
     (SimpleOptEnv * option (Core.OutVar * Core.OutExpr)%type)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (SOE _ subst as env), pair in_bndr out_rhs =>
        match out_rhs with
        | Core.Type_ out_ty =>
            if andb Util.debugIsOn (negb (Core.isTyVar in_bndr)) : bool
            then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreOpt.hs")
                  #390)
            else pair (let 'SOE soe_inl_8__ soe_subst_9__ := env in
                       SOE soe_inl_8__ (CoreSubst.extendTvSubst subst in_bndr out_ty)) None
        | _ =>
            match out_rhs with
            | Core.Coercion out_co =>
                if andb Util.debugIsOn (negb (Core.isCoVar in_bndr)) : bool
                then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreOpt.hs")
                      #394)
                else pair (let 'SOE soe_inl_3__ soe_subst_4__ := env in
                           SOE soe_inl_3__ (CoreSubst.extendCvSubst subst in_bndr out_co)) None
            | _ =>
                simple_out_bind_pair env in_bndr None out_rhs (Id.idOccInfo in_bndr) true false
            end
        end
    end.

Definition finish_app
   : SimpleOptEnv -> Core.OutExpr -> list SimpleClo -> Core.OutExpr :=
  fix simple_opt_expr (env : SimpleOptEnv) (expr : Core.InExpr) : Core.OutExpr
        := let fix go_lam arg_0__ arg_1__ arg_2__
                     := match arg_0__, arg_1__, arg_2__ with
                        | env, bs', Core.Lam b e =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            go_lam env' (cons b' bs') e
                        | env, bs', e =>
                            let e' := simple_opt_expr env e in
                            let bs := GHC.List.reverse bs' in
                            match CoreUtils.tryEtaReduce bs e' with
                            | Some etad_e => etad_e
                            | _ => Core.mkLams bs e'
                            end
                        end in
           let go_alt :=
             fun arg_10__ arg_11__ =>
               match arg_10__, arg_11__ with
               | env, pair (pair con bndrs) rhs =>
                   let 'pair env' bndrs' := subst_opt_bndrs env bndrs in
                   pair (pair con bndrs') (simple_opt_expr env' rhs)
               end in
           let subst := soe_subst env in
           let in_scope := CoreSubst.substInScope subst in
           let in_scope_env := pair in_scope simpleUnfoldingFun in
           let fix go arg_18__
                     := 
                     match arg_18__ with
                        | Core.Mk_Var v =>
                            match Core.lookupVarEnv (soe_inl env) v with
                            | Some clo => simple_opt_clo env clo
                            | _ =>
                                CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simpleOptExpr"))
                                (soe_subst env) v
                            end
                        | Core.App e1 e2 => simple_app env e1 (cons (pair env e2) nil)
                        | Core.Type_ ty => Core.Type_ (CoreSubst.substTy subst ty)
                        | Core.Coercion co => Core.Coercion (tt)
                        | Core.Lit lit => Core.Lit lit
                        | Core.Tick tickish e =>
                            CoreUtils.mkTick (CoreSubst.substTickish subst tickish) (go e)
                        | Core.Cast e co => let co' := tt in Core.Cast (go e) co'
                        | Core.Let bind body =>
                            match simple_opt_bind env bind with
                            | pair env' None => simple_opt_expr env' body
                            | pair env' (Some bind) => Core.Let bind (simple_opt_expr env' body)
                            end
                        | (Core.Lam _ _ as lam) => go_lam env nil lam
                        | Core.Case e b ty as_ =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            let e' := go e in
                            let j_35__ :=
                              Core.Case e' b' (CoreSubst.substTy subst ty) (GHC.Base.map (go_alt env') as_) in
                            let j_36__ :=
                              if Id.isDeadBinder b : bool
                              then match as_ with
                                   | cons (pair (pair Core.DEFAULT _) rhs) nil =>
                                       if Core.isCoercionType (Core.varType b) : bool
                                       then match Core.collectArgs e with
                                            | pair (Core.Mk_Var fun_) _args =>
                                                if Unique.hasKey fun_ PrelNames.coercibleSCSelIdKey : bool
                                                then go rhs else
                                                j_35__
                                            | _ => j_35__
                                            end else
                                       j_35__
                                   | _ => j_35__
                                   end else
                              j_35__ in
                            if Id.isDeadBinder b : bool
                            then match exprIsConApp_maybe in_scope_env e' with
                                 | Some (pair (pair con _tys) es) =>
                                     match CoreUtils.findAlt (Core.DataAlt con) as_ with
                                     | Some (pair (pair altcon bs) rhs) =>
                                         match altcon with
                                         | Core.DEFAULT => go rhs
                                         | _ =>
                                             let 'pair env' mb_prs := Data.Traversable.mapAccumL simple_out_bind env
                                                                        (Util.zipEqual (GHC.Base.hs_string__
                                                                                        "simpleOptExpr") bs es) in
                                             Data.Foldable.foldr wrapLet (simple_opt_expr env' rhs) mb_prs
                                         end
                                     | _ => j_36__
                                     end
                                 | _ => j_36__
                                 end else
                            j_36__
                        end in
           go expr with simple_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.InExpr)
                                   (arg_2__ : list SimpleClo) : Core.CoreExpr
                          := let j_4__ :=
                               match arg_0__, arg_1__, arg_2__ with
                               | env, e, as_ => finish_app env (simple_opt_expr env e) as_
                               end in
                             match arg_0__, arg_1__, arg_2__ with
                             | env, Core.Mk_Var v, as_ =>
                                 match Core.lookupVarEnv (soe_inl env) v with
                                 | Some (pair env' e) => simple_app (soeSetInScope env env') e as_
                                 | _ =>
                                     let j_6__ :=
                                       let out_fn :=
                                         CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simple_app"))
                                         (soe_subst env) v in
                                       finish_app env out_fn as_ in
                                     let unf := Id.idUnfolding v in
                                     if andb (Core.isCompulsoryUnfolding (Id.idUnfolding v))
                                             (BasicTypes.isAlwaysActive (Id.idInlineActivation v)) : bool
                                     then simple_app (soeZapSubst env) (Core.unfoldingTemplate unf) as_ else
                                     j_6__
                                 end
                             | env, Core.App e1 e2, as_ => simple_app env e1 (cons (pair env e2) as_)
                             | env, Core.Lam b e, cons a as_ =>
                                 let 'pair env' mb_pr := simple_bind_pair env b None a in
                                 wrapLet mb_pr (simple_app env' e as_)
                             | env, Core.Tick t e, as_ =>
                                 if Core.tickishScopesLike t Core.SoftScope : bool
                                 then CoreUtils.mkTick t (simple_app env e as_) else
                                 j_4__
                             | _, _, _ => j_4__
                             end with finish_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.OutExpr) (arg_2__
                                                   : list SimpleClo) : Core.OutExpr
                                        := match arg_0__, arg_1__, arg_2__ with
                                           | _, fun_, nil => fun_
                                           | env, fun_, cons arg args =>
                                               finish_app env (Core.App fun_ (simple_opt_clo env arg)) args
                                           end with simple_opt_clo (arg_0__ : SimpleOptEnv) (arg_1__ : SimpleClo)
                                                      : Core.OutExpr
                                                      := match arg_0__, arg_1__ with
                                                         | env, pair e_env e =>
                                                             simple_opt_expr (soeSetInScope env e_env) e
                                                         end with simple_bind_pair (arg_0__ : SimpleOptEnv) (arg_1__
                                                                                     : Core.InVar) (arg_2__
                                                                                     : option Core.OutVar) (arg_3__
                                                                                     : SimpleClo) : (SimpleOptEnv *
                                                                                                     option (Core.OutVar
                                                                                                             *
                                                                                                             Core.OutExpr)%type)%type
                                                                    := match arg_0__, arg_1__, arg_2__, arg_3__ with
                                                                       | (SOE inl_env subst as env)
                                                                       , in_bndr
                                                                       , mb_out_bndr
                                                                       , (pair rhs_env in_rhs as clo) =>
                                                                           let safe_to_inline
                                                                            : BasicTypes.OccInfo -> bool :=
                                                                             fun arg_4__ =>
                                                                               match arg_4__ with
                                                                               | BasicTypes.IAmALoopBreaker _ _ => false
                                                                               | BasicTypes.IAmDead => true
                                                                               | (BasicTypes.OneOcc _ _ _ _ as occ) =>
                                                                                   andb (negb (BasicTypes.occ_in_lam
                                                                                               occ))
                                                                                        (BasicTypes.occ_one_br occ)
                                                                               | BasicTypes.ManyOccs _ => false
                                                                               end in
                                                                           let occ := Id.idOccInfo in_bndr in
                                                                           let active :=
                                                                             BasicTypes.isAlwaysActive
                                                                             (Id.idInlineActivation in_bndr) in
                                                                           let stable_unf :=
                                                                             Core.isStableUnfolding (Id.idUnfolding
                                                                                                     in_bndr) in
                                                                           let pre_inline_unconditionally : bool :=
                                                                             if Core.isCoVar in_bndr : bool
                                                                             then false else
                                                                             if Core.isExportedId in_bndr : bool
                                                                             then false else
                                                                             if stable_unf : bool then false else
                                                                             if negb active : bool then false else
                                                                             if negb (safe_to_inline occ) : bool
                                                                             then false else
                                                                             true in
                                                                           match in_rhs with
                                                                           | Core.Type_ ty =>
                                                                               let out_ty :=
                                                                                 CoreSubst.substTy (soe_subst rhs_env)
                                                                                 ty in
                                                                               if andb Util.debugIsOn (negb
                                                                                        (Core.isTyVar in_bndr)) : bool
                                                                               then (Panic.assertPanic
                                                                                     (GHC.Base.hs_string__
                                                                                      "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                     #348)
                                                                               else pair (let 'SOE soe_inl_26__
                                                                                             soe_subst_27__ := env in
                                                                                          SOE soe_inl_26__
                                                                                              (CoreSubst.extendTvSubst
                                                                                               subst in_bndr out_ty))
                                                                                         None
                                                                           | _ =>
                                                                               match in_rhs with
                                                                               | Core.Coercion co =>
                                                                                   let out_co := tt in
                                                                                   if andb Util.debugIsOn (negb
                                                                                            (Core.isCoVar
                                                                                             in_bndr)) : bool
                                                                                   then (Panic.assertPanic
                                                                                         (GHC.Base.hs_string__
                                                                                          "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                         #353)
                                                                                   else pair (let 'SOE soe_inl_21__
                                                                                                 soe_subst_22__ :=
                                                                                                env in
                                                                                              SOE soe_inl_21__
                                                                                                  (CoreSubst.extendCvSubst
                                                                                                   subst in_bndr
                                                                                                   out_co)) None
                                                                               | _ =>
                                                                                   if pre_inline_unconditionally : bool
                                                                                   then pair (let 'SOE soe_inl_16__
                                                                                                 soe_subst_17__ :=
                                                                                                env in
                                                                                              SOE (Core.extendVarEnv
                                                                                                   inl_env in_bndr clo)
                                                                                                  soe_subst_17__)
                                                                                             None else
                                                                                   simple_out_bind_pair env in_bndr
                                                                                   mb_out_bndr (simple_opt_clo env clo)
                                                                                   occ active stable_unf
                                                                               end
                                                                           end
                                                                       end with simple_opt_bind (arg_0__ : SimpleOptEnv)
                                                                                                (arg_1__ : Core.InBind)
                                                                                  : (SimpleOptEnv *
                                                                                     option Core.OutBind)%type
                                                                                  := match arg_0__, arg_1__ with
                                                                                     | env, Core.NonRec b r =>
                                                                                         let 'pair b' r' :=
                                                                                           Maybes.orElse
                                                                                             (joinPointBinding_maybe b
                                                                                              r) (pair b r) in
                                                                                         let 'pair env' mb_pr :=
                                                                                           simple_bind_pair env b' None
                                                                                             (pair env r') in
                                                                                         pair env' (match mb_pr with
                                                                                               | None => None
                                                                                               | Some (pair b r) =>
                                                                                                   Some (Core.NonRec b
                                                                                                         r)
                                                                                               end)
                                                                                     | env, Core.Rec prs =>
                                                                                         let do_pr :=
                                                                                           fun arg_7__ arg_8__ =>
                                                                                             match arg_7__, arg_8__ with
                                                                                             | pair env prs
                                                                                             , pair (pair b r) b' =>
                                                                                                 let 'pair env' mb_pr :=
                                                                                                   simple_bind_pair env
                                                                                                     b (Some b') (pair
                                                                                                                  env
                                                                                                                  r) in
                                                                                                 pair env'
                                                                                                      (match mb_pr with
                                                                                                       | Some pr =>
                                                                                                           cons pr prs
                                                                                                       | None => prs
                                                                                                       end)
                                                                                             end in
                                                                                         let prs' :=
                                                                                           Maybes.orElse
                                                                                           (joinPointBindings_maybe prs)
                                                                                           prs in
                                                                                         let 'pair env' bndrs' :=
                                                                                           subst_opt_bndrs env
                                                                                             (GHC.Base.map
                                                                                              Data.Tuple.fst prs') in
                                                                                         let 'pair env'' rev_prs' :=
                                                                                           Data.Foldable.foldl do_pr
                                                                                             (pair env' nil)
                                                                                             (GHC.List.zip prs'
                                                                                                           bndrs') in
                                                                                         let res_bind :=
                                                                                           Some (Core.Rec
                                                                                                 (GHC.List.reverse
                                                                                                  rev_prs')) in
                                                                                         pair env'' res_bind
                                                                                     end for finish_app.

Definition simple_app
   : SimpleOptEnv -> Core.InExpr -> list SimpleClo -> Core.CoreExpr :=
  fix simple_opt_expr (env : SimpleOptEnv) (expr : Core.InExpr) : Core.OutExpr
        := let fix go_lam arg_0__ arg_1__ arg_2__
                     := match arg_0__, arg_1__, arg_2__ with
                        | env, bs', Core.Lam b e =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            go_lam env' (cons b' bs') e
                        | env, bs', e =>
                            let e' := simple_opt_expr env e in
                            let bs := GHC.List.reverse bs' in
                            match CoreUtils.tryEtaReduce bs e' with
                            | Some etad_e => etad_e
                            | _ => Core.mkLams bs e'
                            end
                        end in
           let go_alt :=
             fun arg_10__ arg_11__ =>
               match arg_10__, arg_11__ with
               | env, pair (pair con bndrs) rhs =>
                   let 'pair env' bndrs' := subst_opt_bndrs env bndrs in
                   pair (pair con bndrs') (simple_opt_expr env' rhs)
               end in
           let subst := soe_subst env in
           let in_scope := CoreSubst.substInScope subst in
           let in_scope_env := pair in_scope simpleUnfoldingFun in
           let fix go arg_18__
                     := match arg_18__ with
                        | Core.Mk_Var v =>
                            match Core.lookupVarEnv (soe_inl env) v with
                            | Some clo => simple_opt_clo env clo
                            | _ =>
                                CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simpleOptExpr"))
                                (soe_subst env) v
                            end
                        | Core.App e1 e2 => simple_app env e1 (cons (pair env e2) nil)
                        | Core.Type_ ty => Core.Type_ (CoreSubst.substTy subst ty)
                        | Core.Coercion co => Core.Coercion (tt)
                        | Core.Lit lit => Core.Lit lit
                        | Core.Tick tickish e =>
                            CoreUtils.mkTick (CoreSubst.substTickish subst tickish) (go e)
                        | Core.Cast e co => let co' := tt in Core.Cast (go e) co'
                        | Core.Let bind body =>
                            match simple_opt_bind env bind with
                            | pair env' None => simple_opt_expr env' body
                            | pair env' (Some bind) => Core.Let bind (simple_opt_expr env' body)
                            end
                        | (Core.Lam _ _ as lam) => go_lam env nil lam
                        | Core.Case e b ty as_ =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            let e' := go e in
                            let j_35__ :=
                              Core.Case e' b' (CoreSubst.substTy subst ty) (GHC.Base.map (go_alt env') as_) in
                            let j_36__ :=
                              if Id.isDeadBinder b : bool
                              then match as_ with
                                   | cons (pair (pair Core.DEFAULT _) rhs) nil =>
                                       if Core.isCoercionType (Core.varType b) : bool
                                       then match Core.collectArgs e with
                                            | pair (Core.Mk_Var fun_) _args =>
                                                if Unique.hasKey fun_ PrelNames.coercibleSCSelIdKey : bool
                                                then go rhs else
                                                j_35__
                                            | _ => j_35__
                                            end else
                                       j_35__
                                   | _ => j_35__
                                   end else
                              j_35__ in
                            if Id.isDeadBinder b : bool
                            then match exprIsConApp_maybe in_scope_env e' with
                                 | Some (pair (pair con _tys) es) =>
                                     match CoreUtils.findAlt (Core.DataAlt con) as_ with
                                     | Some (pair (pair altcon bs) rhs) =>
                                         match altcon with
                                         | Core.DEFAULT => go rhs
                                         | _ =>
                                             let 'pair env' mb_prs := Data.Traversable.mapAccumL simple_out_bind env
                                                                        (Util.zipEqual (GHC.Base.hs_string__
                                                                                        "simpleOptExpr") bs es) in
                                             Data.Foldable.foldr wrapLet (simple_opt_expr env' rhs) mb_prs
                                         end
                                     | _ => j_36__
                                     end
                                 | _ => j_36__
                                 end else
                            j_36__
                        end in
           go expr with simple_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.InExpr)
                                   (arg_2__ : list SimpleClo) : Core.CoreExpr
                          := let j_4__ :=
                               match arg_0__, arg_1__, arg_2__ with
                               | env, e, as_ => finish_app env (simple_opt_expr env e) as_
                               end in
                             match arg_0__, arg_1__, arg_2__ with
                             | env, Core.Mk_Var v, as_ =>
                                 match Core.lookupVarEnv (soe_inl env) v with
                                 | Some (pair env' e) => simple_app (soeSetInScope env env') e as_
                                 | _ =>
                                     let j_6__ :=
                                       let out_fn :=
                                         CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simple_app"))
                                         (soe_subst env) v in
                                       finish_app env out_fn as_ in
                                     let unf := Id.idUnfolding v in
                                     if andb (Core.isCompulsoryUnfolding (Id.idUnfolding v))
                                             (BasicTypes.isAlwaysActive (Id.idInlineActivation v)) : bool
                                     then simple_app (soeZapSubst env) (Core.unfoldingTemplate unf) as_ else
                                     j_6__
                                 end
                             | env, Core.App e1 e2, as_ => simple_app env e1 (cons (pair env e2) as_)
                             | env, Core.Lam b e, cons a as_ =>
                                 let 'pair env' mb_pr := simple_bind_pair env b None a in
                                 wrapLet mb_pr (simple_app env' e as_)
                             | env, Core.Tick t e, as_ =>
                                 if Core.tickishScopesLike t Core.SoftScope : bool
                                 then CoreUtils.mkTick t (simple_app env e as_) else
                                 j_4__
                             | _, _, _ => j_4__
                             end with finish_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.OutExpr) (arg_2__
                                                   : list SimpleClo) : Core.OutExpr
                                        := match arg_0__, arg_1__, arg_2__ with
                                           | _, fun_, nil => fun_
                                           | env, fun_, cons arg args =>
                                               finish_app env (Core.App fun_ (simple_opt_clo env arg)) args
                                           end with simple_opt_clo (arg_0__ : SimpleOptEnv) (arg_1__ : SimpleClo)
                                                      : Core.OutExpr
                                                      := match arg_0__, arg_1__ with
                                                         | env, pair e_env e =>
                                                             simple_opt_expr (soeSetInScope env e_env) e
                                                         end with simple_bind_pair (arg_0__ : SimpleOptEnv) (arg_1__
                                                                                     : Core.InVar) (arg_2__
                                                                                     : option Core.OutVar) (arg_3__
                                                                                     : SimpleClo) : (SimpleOptEnv *
                                                                                                     option (Core.OutVar
                                                                                                             *
                                                                                                             Core.OutExpr)%type)%type
                                                                    := match arg_0__, arg_1__, arg_2__, arg_3__ with
                                                                       | (SOE inl_env subst as env)
                                                                       , in_bndr
                                                                       , mb_out_bndr
                                                                       , (pair rhs_env in_rhs as clo) =>
                                                                           let safe_to_inline
                                                                            : BasicTypes.OccInfo -> bool :=
                                                                             fun arg_4__ =>
                                                                               match arg_4__ with
                                                                               | BasicTypes.IAmALoopBreaker _ _ => false
                                                                               | BasicTypes.IAmDead => true
                                                                               | (BasicTypes.OneOcc _ _ _ _ as occ) =>
                                                                                   andb (negb (BasicTypes.occ_in_lam
                                                                                               occ))
                                                                                        (BasicTypes.occ_one_br occ)
                                                                               | BasicTypes.ManyOccs _ => false
                                                                               end in
                                                                           let occ := Id.idOccInfo in_bndr in
                                                                           let active :=
                                                                             BasicTypes.isAlwaysActive
                                                                             (Id.idInlineActivation in_bndr) in
                                                                           let stable_unf :=
                                                                             Core.isStableUnfolding (Id.idUnfolding
                                                                                                     in_bndr) in
                                                                           let pre_inline_unconditionally : bool :=
                                                                             if Core.isCoVar in_bndr : bool
                                                                             then false else
                                                                             if Core.isExportedId in_bndr : bool
                                                                             then false else
                                                                             if stable_unf : bool then false else
                                                                             if negb active : bool then false else
                                                                             if negb (safe_to_inline occ) : bool
                                                                             then false else
                                                                             true in
                                                                           match in_rhs with
                                                                           | Core.Type_ ty =>
                                                                               let out_ty :=
                                                                                 CoreSubst.substTy (soe_subst rhs_env)
                                                                                 ty in
                                                                               if andb Util.debugIsOn (negb
                                                                                        (Core.isTyVar in_bndr)) : bool
                                                                               then (Panic.assertPanic
                                                                                     (GHC.Base.hs_string__
                                                                                      "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                     #348)
                                                                               else pair (let 'SOE soe_inl_26__
                                                                                             soe_subst_27__ := env in
                                                                                          SOE soe_inl_26__
                                                                                              (CoreSubst.extendTvSubst
                                                                                               subst in_bndr out_ty))
                                                                                         None
                                                                           | _ =>
                                                                               match in_rhs with
                                                                               | Core.Coercion co =>
                                                                                   let out_co := tt in
                                                                                   if andb Util.debugIsOn (negb
                                                                                            (Core.isCoVar
                                                                                             in_bndr)) : bool
                                                                                   then (Panic.assertPanic
                                                                                         (GHC.Base.hs_string__
                                                                                          "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                         #353)
                                                                                   else pair (let 'SOE soe_inl_21__
                                                                                                 soe_subst_22__ :=
                                                                                                env in
                                                                                              SOE soe_inl_21__
                                                                                                  (CoreSubst.extendCvSubst
                                                                                                   subst in_bndr
                                                                                                   out_co)) None
                                                                               | _ =>
                                                                                   if pre_inline_unconditionally : bool
                                                                                   then pair (let 'SOE soe_inl_16__
                                                                                                 soe_subst_17__ :=
                                                                                                env in
                                                                                              SOE (Core.extendVarEnv
                                                                                                   inl_env in_bndr clo)
                                                                                                  soe_subst_17__)
                                                                                             None else
                                                                                   simple_out_bind_pair env in_bndr
                                                                                   mb_out_bndr (simple_opt_clo env clo)
                                                                                   occ active stable_unf
                                                                               end
                                                                           end
                                                                       end with simple_opt_bind (arg_0__ : SimpleOptEnv)
                                                                                                (arg_1__ : Core.InBind)
                                                                                  : (SimpleOptEnv *
                                                                                     option Core.OutBind)%type
                                                                                  := match arg_0__, arg_1__ with
                                                                                     | env, Core.NonRec b r =>
                                                                                         let 'pair b' r' :=
                                                                                           Maybes.orElse
                                                                                             (joinPointBinding_maybe b
                                                                                              r) (pair b r) in
                                                                                         let 'pair env' mb_pr :=
                                                                                           simple_bind_pair env b' None
                                                                                             (pair env r') in
                                                                                         pair env' (match mb_pr with
                                                                                               | None => None
                                                                                               | Some (pair b r) =>
                                                                                                   Some (Core.NonRec b
                                                                                                         r)
                                                                                               end)
                                                                                     | env, Core.Rec prs =>
                                                                                         let do_pr :=
                                                                                           fun arg_7__ arg_8__ =>
                                                                                             match arg_7__, arg_8__ with
                                                                                             | pair env prs
                                                                                             , pair (pair b r) b' =>
                                                                                                 let 'pair env' mb_pr :=
                                                                                                   simple_bind_pair env
                                                                                                     b (Some b') (pair
                                                                                                                  env
                                                                                                                  r) in
                                                                                                 pair env'
                                                                                                      (match mb_pr with
                                                                                                       | Some pr =>
                                                                                                           cons pr prs
                                                                                                       | None => prs
                                                                                                       end)
                                                                                             end in
                                                                                         let prs' :=
                                                                                           Maybes.orElse
                                                                                           (joinPointBindings_maybe prs)
                                                                                           prs in
                                                                                         let 'pair env' bndrs' :=
                                                                                           subst_opt_bndrs env
                                                                                             (GHC.Base.map
                                                                                              Data.Tuple.fst prs') in
                                                                                         let 'pair env'' rev_prs' :=
                                                                                           Data.Foldable.foldl do_pr
                                                                                             (pair env' nil)
                                                                                             (GHC.List.zip prs'
                                                                                                           bndrs') in
                                                                                         let res_bind :=
                                                                                           Some (Core.Rec
                                                                                                 (GHC.List.reverse
                                                                                                  rev_prs')) in
                                                                                         pair env'' res_bind
                                                                                     end for simple_app.

Definition simple_bind_pair
   : SimpleOptEnv ->
     Core.InVar ->
     option Core.OutVar ->
     SimpleClo -> (SimpleOptEnv * option (Core.OutVar * Core.OutExpr)%type)%type :=
  fix simple_opt_expr (env : SimpleOptEnv) (expr : Core.InExpr) : Core.OutExpr
        := let fix go_lam arg_0__ arg_1__ arg_2__
                     := match arg_0__, arg_1__, arg_2__ with
                        | env, bs', Core.Lam b e =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            go_lam env' (cons b' bs') e
                        | env, bs', e =>
                            let e' := simple_opt_expr env e in
                            let bs := GHC.List.reverse bs' in
                            match CoreUtils.tryEtaReduce bs e' with
                            | Some etad_e => etad_e
                            | _ => Core.mkLams bs e'
                            end
                        end in
           let go_alt :=
             fun arg_10__ arg_11__ =>
               match arg_10__, arg_11__ with
               | env, pair (pair con bndrs) rhs =>
                   let 'pair env' bndrs' := subst_opt_bndrs env bndrs in
                   pair (pair con bndrs') (simple_opt_expr env' rhs)
               end in
           let subst := soe_subst env in
           let in_scope := CoreSubst.substInScope subst in
           let in_scope_env := pair in_scope simpleUnfoldingFun in
           let fix go arg_18__
                     := match arg_18__ with
                        | Core.Mk_Var v =>
                            match Core.lookupVarEnv (soe_inl env) v with
                            | Some clo => simple_opt_clo env clo
                            | _ =>
                                CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simpleOptExpr"))
                                (soe_subst env) v
                            end
                        | Core.App e1 e2 => simple_app env e1 (cons (pair env e2) nil)
                        | Core.Type_ ty => Core.Type_ (CoreSubst.substTy subst ty)
                        | Core.Coercion co => Core.Coercion (tt)
                        | Core.Lit lit => Core.Lit lit
                        | Core.Tick tickish e =>
                            CoreUtils.mkTick (CoreSubst.substTickish subst tickish) (go e)
                        | Core.Cast e co => let co' := tt in Core.Cast (go e) co'
                        | Core.Let bind body =>
                            match simple_opt_bind env bind with
                            | pair env' None => simple_opt_expr env' body
                            | pair env' (Some bind) => Core.Let bind (simple_opt_expr env' body)
                            end
                        | (Core.Lam _ _ as lam) => go_lam env nil lam
                        | Core.Case e b ty as_ =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            let e' := go e in
                            let j_35__ :=
                              Core.Case e' b' (CoreSubst.substTy subst ty) (GHC.Base.map (go_alt env') as_) in
                            let j_36__ :=
                              if Id.isDeadBinder b : bool
                              then match as_ with
                                   | cons (pair (pair Core.DEFAULT _) rhs) nil =>
                                       if Core.isCoercionType (Core.varType b) : bool
                                       then match Core.collectArgs e with
                                            | pair (Core.Mk_Var fun_) _args =>
                                                if Unique.hasKey fun_ PrelNames.coercibleSCSelIdKey : bool
                                                then go rhs else
                                                j_35__
                                            | _ => j_35__
                                            end else
                                       j_35__
                                   | _ => j_35__
                                   end else
                              j_35__ in
                            if Id.isDeadBinder b : bool
                            then match exprIsConApp_maybe in_scope_env e' with
                                 | Some (pair (pair con _tys) es) =>
                                     match CoreUtils.findAlt (Core.DataAlt con) as_ with
                                     | Some (pair (pair altcon bs) rhs) =>
                                         match altcon with
                                         | Core.DEFAULT => go rhs
                                         | _ =>
                                             let 'pair env' mb_prs := Data.Traversable.mapAccumL simple_out_bind env
                                                                        (Util.zipEqual (GHC.Base.hs_string__
                                                                                        "simpleOptExpr") bs es) in
                                             Data.Foldable.foldr wrapLet (simple_opt_expr env' rhs) mb_prs
                                         end
                                     | _ => j_36__
                                     end
                                 | _ => j_36__
                                 end else
                            j_36__
                        end in
           go expr with simple_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.InExpr)
                                   (arg_2__ : list SimpleClo) : Core.CoreExpr
                          := let j_4__ :=
                               match arg_0__, arg_1__, arg_2__ with
                               | env, e, as_ => finish_app env (simple_opt_expr env e) as_
                               end in
                             match arg_0__, arg_1__, arg_2__ with
                             | env, Core.Mk_Var v, as_ =>
                                 match Core.lookupVarEnv (soe_inl env) v with
                                 | Some (pair env' e) => simple_app (soeSetInScope env env') e as_
                                 | _ =>
                                     let j_6__ :=
                                       let out_fn :=
                                         CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simple_app"))
                                         (soe_subst env) v in
                                       finish_app env out_fn as_ in
                                     let unf := Id.idUnfolding v in
                                     if andb (Core.isCompulsoryUnfolding (Id.idUnfolding v))
                                             (BasicTypes.isAlwaysActive (Id.idInlineActivation v)) : bool
                                     then simple_app (soeZapSubst env) (Core.unfoldingTemplate unf) as_ else
                                     j_6__
                                 end
                             | env, Core.App e1 e2, as_ => simple_app env e1 (cons (pair env e2) as_)
                             | env, Core.Lam b e, cons a as_ =>
                                 let 'pair env' mb_pr := simple_bind_pair env b None a in
                                 wrapLet mb_pr (simple_app env' e as_)
                             | env, Core.Tick t e, as_ =>
                                 if Core.tickishScopesLike t Core.SoftScope : bool
                                 then CoreUtils.mkTick t (simple_app env e as_) else
                                 j_4__
                             | _, _, _ => j_4__
                             end with finish_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.OutExpr) (arg_2__
                                                   : list SimpleClo) : Core.OutExpr
                                        := match arg_0__, arg_1__, arg_2__ with
                                           | _, fun_, nil => fun_
                                           | env, fun_, cons arg args =>
                                               finish_app env (Core.App fun_ (simple_opt_clo env arg)) args
                                           end with simple_opt_clo (arg_0__ : SimpleOptEnv) (arg_1__ : SimpleClo)
                                                      : Core.OutExpr
                                                      := match arg_0__, arg_1__ with
                                                         | env, pair e_env e =>
                                                             simple_opt_expr (soeSetInScope env e_env) e
                                                         end with simple_bind_pair (arg_0__ : SimpleOptEnv) (arg_1__
                                                                                     : Core.InVar) (arg_2__
                                                                                     : option Core.OutVar) (arg_3__
                                                                                     : SimpleClo) : (SimpleOptEnv *
                                                                                                     option (Core.OutVar
                                                                                                             *
                                                                                                             Core.OutExpr)%type)%type
                                                                    := match arg_0__, arg_1__, arg_2__, arg_3__ with
                                                                       | (SOE inl_env subst as env)
                                                                       , in_bndr
                                                                       , mb_out_bndr
                                                                       , (pair rhs_env in_rhs as clo) =>
                                                                           let safe_to_inline
                                                                            : BasicTypes.OccInfo -> bool :=
                                                                             fun arg_4__ =>
                                                                               match arg_4__ with
                                                                               | BasicTypes.IAmALoopBreaker _ _ => false
                                                                               | BasicTypes.IAmDead => true
                                                                               | (BasicTypes.OneOcc _ _ _ _ as occ) =>
                                                                                   andb (negb (BasicTypes.occ_in_lam
                                                                                               occ))
                                                                                        (BasicTypes.occ_one_br occ)
                                                                               | BasicTypes.ManyOccs _ => false
                                                                               end in
                                                                           let occ := Id.idOccInfo in_bndr in
                                                                           let active :=
                                                                             BasicTypes.isAlwaysActive
                                                                             (Id.idInlineActivation in_bndr) in
                                                                           let stable_unf :=
                                                                             Core.isStableUnfolding (Id.idUnfolding
                                                                                                     in_bndr) in
                                                                           let pre_inline_unconditionally : bool :=
                                                                             if Core.isCoVar in_bndr : bool
                                                                             then false else
                                                                             if Core.isExportedId in_bndr : bool
                                                                             then false else
                                                                             if stable_unf : bool then false else
                                                                             if negb active : bool then false else
                                                                             if negb (safe_to_inline occ) : bool
                                                                             then false else
                                                                             true in
                                                                           match in_rhs with
                                                                           | Core.Type_ ty =>
                                                                               let out_ty :=
                                                                                 CoreSubst.substTy (soe_subst rhs_env)
                                                                                 ty in
                                                                               if andb Util.debugIsOn (negb
                                                                                        (Core.isTyVar in_bndr)) : bool
                                                                               then (Panic.assertPanic
                                                                                     (GHC.Base.hs_string__
                                                                                      "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                     #348)
                                                                               else pair (let 'SOE soe_inl_26__
                                                                                             soe_subst_27__ := env in
                                                                                          SOE soe_inl_26__
                                                                                              (CoreSubst.extendTvSubst
                                                                                               subst in_bndr out_ty))
                                                                                         None
                                                                           | _ =>
                                                                               match in_rhs with
                                                                               | Core.Coercion co =>
                                                                                   let out_co := tt in
                                                                                   if andb Util.debugIsOn (negb
                                                                                            (Core.isCoVar
                                                                                             in_bndr)) : bool
                                                                                   then (Panic.assertPanic
                                                                                         (GHC.Base.hs_string__
                                                                                          "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                         #353)
                                                                                   else pair (let 'SOE soe_inl_21__
                                                                                                 soe_subst_22__ :=
                                                                                                env in
                                                                                              SOE soe_inl_21__
                                                                                                  (CoreSubst.extendCvSubst
                                                                                                   subst in_bndr
                                                                                                   out_co)) None
                                                                               | _ =>
                                                                                   if pre_inline_unconditionally : bool
                                                                                   then pair (let 'SOE soe_inl_16__
                                                                                                 soe_subst_17__ :=
                                                                                                env in
                                                                                              SOE (Core.extendVarEnv
                                                                                                   inl_env in_bndr clo)
                                                                                                  soe_subst_17__)
                                                                                             None else
                                                                                   simple_out_bind_pair env in_bndr
                                                                                   mb_out_bndr (simple_opt_clo env clo)
                                                                                   occ active stable_unf
                                                                               end
                                                                           end
                                                                       end with simple_opt_bind (arg_0__ : SimpleOptEnv)
                                                                                                (arg_1__ : Core.InBind)
                                                                                  : (SimpleOptEnv *
                                                                                     option Core.OutBind)%type
                                                                                  := match arg_0__, arg_1__ with
                                                                                     | env, Core.NonRec b r =>
                                                                                         let 'pair b' r' :=
                                                                                           Maybes.orElse
                                                                                             (joinPointBinding_maybe b
                                                                                              r) (pair b r) in
                                                                                         let 'pair env' mb_pr :=
                                                                                           simple_bind_pair env b' None
                                                                                             (pair env r') in
                                                                                         pair env' (match mb_pr with
                                                                                               | None => None
                                                                                               | Some (pair b r) =>
                                                                                                   Some (Core.NonRec b
                                                                                                         r)
                                                                                               end)
                                                                                     | env, Core.Rec prs =>
                                                                                         let do_pr :=
                                                                                           fun arg_7__ arg_8__ =>
                                                                                             match arg_7__, arg_8__ with
                                                                                             | pair env prs
                                                                                             , pair (pair b r) b' =>
                                                                                                 let 'pair env' mb_pr :=
                                                                                                   simple_bind_pair env
                                                                                                     b (Some b') (pair
                                                                                                                  env
                                                                                                                  r) in
                                                                                                 pair env'
                                                                                                      (match mb_pr with
                                                                                                       | Some pr =>
                                                                                                           cons pr prs
                                                                                                       | None => prs
                                                                                                       end)
                                                                                             end in
                                                                                         let prs' :=
                                                                                           Maybes.orElse
                                                                                           (joinPointBindings_maybe prs)
                                                                                           prs in
                                                                                         let 'pair env' bndrs' :=
                                                                                           subst_opt_bndrs env
                                                                                             (GHC.Base.map
                                                                                              Data.Tuple.fst prs') in
                                                                                         let 'pair env'' rev_prs' :=
                                                                                           Data.Foldable.foldl do_pr
                                                                                             (pair env' nil)
                                                                                             (GHC.List.zip prs'
                                                                                                           bndrs') in
                                                                                         let res_bind :=
                                                                                           Some (Core.Rec
                                                                                                 (GHC.List.reverse
                                                                                                  rev_prs')) in
                                                                                         pair env'' res_bind
                                                                                     end for simple_bind_pair.

Definition simple_opt_bind
   : SimpleOptEnv -> Core.InBind -> (SimpleOptEnv * option Core.OutBind)%type :=
  fix simple_opt_expr (env : SimpleOptEnv) (expr : Core.InExpr) : Core.OutExpr
        := let fix go_lam arg_0__ arg_1__ arg_2__
                     := match arg_0__, arg_1__, arg_2__ with
                        | env, bs', Core.Lam b e =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            go_lam env' (cons b' bs') e
                        | env, bs', e =>
                            let e' := simple_opt_expr env e in
                            let bs := GHC.List.reverse bs' in
                            match CoreUtils.tryEtaReduce bs e' with
                            | Some etad_e => etad_e
                            | _ => Core.mkLams bs e'
                            end
                        end in
           let go_alt :=
             fun arg_10__ arg_11__ =>
               match arg_10__, arg_11__ with
               | env, pair (pair con bndrs) rhs =>
                   let 'pair env' bndrs' := subst_opt_bndrs env bndrs in
                   pair (pair con bndrs') (simple_opt_expr env' rhs)
               end in
           let subst := soe_subst env in
           let in_scope := CoreSubst.substInScope subst in
           let in_scope_env := pair in_scope simpleUnfoldingFun in
           let fix go arg_18__
                     := match arg_18__ with
                        | Core.Mk_Var v =>
                            match Core.lookupVarEnv (soe_inl env) v with
                            | Some clo => simple_opt_clo env clo
                            | _ =>
                                CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simpleOptExpr"))
                                (soe_subst env) v
                            end
                        | Core.App e1 e2 => simple_app env e1 (cons (pair env e2) nil)
                        | Core.Type_ ty => Core.Type_ (CoreSubst.substTy subst ty)
                        | Core.Coercion co => Core.Coercion (tt)
                        | Core.Lit lit => Core.Lit lit
                        | Core.Tick tickish e =>
                            CoreUtils.mkTick (CoreSubst.substTickish subst tickish) (go e)
                        | Core.Cast e co => let co' := tt in Core.Cast (go e) co'
                        | Core.Let bind body =>
                            match simple_opt_bind env bind with
                            | pair env' None => simple_opt_expr env' body
                            | pair env' (Some bind) => Core.Let bind (simple_opt_expr env' body)
                            end
                        | (Core.Lam _ _ as lam) => go_lam env nil lam
                        | Core.Case e b ty as_ =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            let e' := go e in
                            let j_35__ :=
                              Core.Case e' b' (CoreSubst.substTy subst ty) (GHC.Base.map (go_alt env') as_) in
                            let j_36__ :=
                              if Id.isDeadBinder b : bool
                              then match as_ with
                                   | cons (pair (pair Core.DEFAULT _) rhs) nil =>
                                       if Core.isCoercionType (Core.varType b) : bool
                                       then match Core.collectArgs e with
                                            | pair (Core.Mk_Var fun_) _args =>
                                                if Unique.hasKey fun_ PrelNames.coercibleSCSelIdKey : bool
                                                then go rhs else
                                                j_35__
                                            | _ => j_35__
                                            end else
                                       j_35__
                                   | _ => j_35__
                                   end else
                              j_35__ in
                            if Id.isDeadBinder b : bool
                            then match exprIsConApp_maybe in_scope_env e' with
                                 | Some (pair (pair con _tys) es) =>
                                     match CoreUtils.findAlt (Core.DataAlt con) as_ with
                                     | Some (pair (pair altcon bs) rhs) =>
                                         match altcon with
                                         | Core.DEFAULT => go rhs
                                         | _ =>
                                             let 'pair env' mb_prs := Data.Traversable.mapAccumL simple_out_bind env
                                                                        (Util.zipEqual (GHC.Base.hs_string__
                                                                                        "simpleOptExpr") bs es) in
                                             Data.Foldable.foldr wrapLet (simple_opt_expr env' rhs) mb_prs
                                         end
                                     | _ => j_36__
                                     end
                                 | _ => j_36__
                                 end else
                            j_36__
                        end in
           go expr with simple_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.InExpr)
                                   (arg_2__ : list SimpleClo) : Core.CoreExpr
                          := let j_4__ :=
                               match arg_0__, arg_1__, arg_2__ with
                               | env, e, as_ => finish_app env (simple_opt_expr env e) as_
                               end in
                             match arg_0__, arg_1__, arg_2__ with
                             | env, Core.Mk_Var v, as_ =>
                                 match Core.lookupVarEnv (soe_inl env) v with
                                 | Some (pair env' e) => simple_app (soeSetInScope env env') e as_
                                 | _ =>
                                     let j_6__ :=
                                       let out_fn :=
                                         CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simple_app"))
                                         (soe_subst env) v in
                                       finish_app env out_fn as_ in
                                     let unf := Id.idUnfolding v in
                                     if andb (Core.isCompulsoryUnfolding (Id.idUnfolding v))
                                             (BasicTypes.isAlwaysActive (Id.idInlineActivation v)) : bool
                                     then simple_app (soeZapSubst env) (Core.unfoldingTemplate unf) as_ else
                                     j_6__
                                 end
                             | env, Core.App e1 e2, as_ => simple_app env e1 (cons (pair env e2) as_)
                             | env, Core.Lam b e, cons a as_ =>
                                 let 'pair env' mb_pr := simple_bind_pair env b None a in
                                 wrapLet mb_pr (simple_app env' e as_)
                             | env, Core.Tick t e, as_ =>
                                 if Core.tickishScopesLike t Core.SoftScope : bool
                                 then CoreUtils.mkTick t (simple_app env e as_) else
                                 j_4__
                             | _, _, _ => j_4__
                             end with finish_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.OutExpr) (arg_2__
                                                   : list SimpleClo) : Core.OutExpr
                                        := match arg_0__, arg_1__, arg_2__ with
                                           | _, fun_, nil => fun_
                                           | env, fun_, cons arg args =>
                                               finish_app env (Core.App fun_ (simple_opt_clo env arg)) args
                                           end with simple_opt_clo (arg_0__ : SimpleOptEnv) (arg_1__ : SimpleClo)
                                                      : Core.OutExpr
                                                      := match arg_0__, arg_1__ with
                                                         | env, pair e_env e =>
                                                             simple_opt_expr (soeSetInScope env e_env) e
                                                         end with simple_bind_pair (arg_0__ : SimpleOptEnv) (arg_1__
                                                                                     : Core.InVar) (arg_2__
                                                                                     : option Core.OutVar) (arg_3__
                                                                                     : SimpleClo) : (SimpleOptEnv *
                                                                                                     option (Core.OutVar
                                                                                                             *
                                                                                                             Core.OutExpr)%type)%type
                                                                    := match arg_0__, arg_1__, arg_2__, arg_3__ with
                                                                       | (SOE inl_env subst as env)
                                                                       , in_bndr
                                                                       , mb_out_bndr
                                                                       , (pair rhs_env in_rhs as clo) =>
                                                                           let safe_to_inline
                                                                            : BasicTypes.OccInfo -> bool :=
                                                                             fun arg_4__ =>
                                                                               match arg_4__ with
                                                                               | BasicTypes.IAmALoopBreaker _ _ => false
                                                                               | BasicTypes.IAmDead => true
                                                                               | (BasicTypes.OneOcc _ _ _ _ as occ) =>
                                                                                   andb (negb (BasicTypes.occ_in_lam
                                                                                               occ))
                                                                                        (BasicTypes.occ_one_br occ)
                                                                               | BasicTypes.ManyOccs _ => false
                                                                               end in
                                                                           let occ := Id.idOccInfo in_bndr in
                                                                           let active :=
                                                                             BasicTypes.isAlwaysActive
                                                                             (Id.idInlineActivation in_bndr) in
                                                                           let stable_unf :=
                                                                             Core.isStableUnfolding (Id.idUnfolding
                                                                                                     in_bndr) in
                                                                           let pre_inline_unconditionally : bool :=
                                                                             if Core.isCoVar in_bndr : bool
                                                                             then false else
                                                                             if Core.isExportedId in_bndr : bool
                                                                             then false else
                                                                             if stable_unf : bool then false else
                                                                             if negb active : bool then false else
                                                                             if negb (safe_to_inline occ) : bool
                                                                             then false else
                                                                             true in
                                                                           match in_rhs with
                                                                           | Core.Type_ ty =>
                                                                               let out_ty :=
                                                                                 CoreSubst.substTy (soe_subst rhs_env)
                                                                                 ty in
                                                                               if andb Util.debugIsOn (negb
                                                                                        (Core.isTyVar in_bndr)) : bool
                                                                               then (Panic.assertPanic
                                                                                     (GHC.Base.hs_string__
                                                                                      "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                     #348)
                                                                               else pair (let 'SOE soe_inl_26__
                                                                                             soe_subst_27__ := env in
                                                                                          SOE soe_inl_26__
                                                                                              (CoreSubst.extendTvSubst
                                                                                               subst in_bndr out_ty))
                                                                                         None
                                                                           | _ =>
                                                                               match in_rhs with
                                                                               | Core.Coercion co =>
                                                                                   let out_co := tt in
                                                                                   if andb Util.debugIsOn (negb
                                                                                            (Core.isCoVar
                                                                                             in_bndr)) : bool
                                                                                   then (Panic.assertPanic
                                                                                         (GHC.Base.hs_string__
                                                                                          "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                         #353)
                                                                                   else pair (let 'SOE soe_inl_21__
                                                                                                 soe_subst_22__ :=
                                                                                                env in
                                                                                              SOE soe_inl_21__
                                                                                                  (CoreSubst.extendCvSubst
                                                                                                   subst in_bndr
                                                                                                   out_co)) None
                                                                               | _ =>
                                                                                   if pre_inline_unconditionally : bool
                                                                                   then pair (let 'SOE soe_inl_16__
                                                                                                 soe_subst_17__ :=
                                                                                                env in
                                                                                              SOE (Core.extendVarEnv
                                                                                                   inl_env in_bndr clo)
                                                                                                  soe_subst_17__)
                                                                                             None else
                                                                                   simple_out_bind_pair env in_bndr
                                                                                   mb_out_bndr (simple_opt_clo env clo)
                                                                                   occ active stable_unf
                                                                               end
                                                                           end
                                                                       end with simple_opt_bind (arg_0__ : SimpleOptEnv)
                                                                                                (arg_1__ : Core.InBind)
                                                                                  : (SimpleOptEnv *
                                                                                     option Core.OutBind)%type
                                                                                  := match arg_0__, arg_1__ with
                                                                                     | env, Core.NonRec b r =>
                                                                                         let 'pair b' r' :=
                                                                                           Maybes.orElse
                                                                                             (joinPointBinding_maybe b
                                                                                              r) (pair b r) in
                                                                                         let 'pair env' mb_pr :=
                                                                                           simple_bind_pair env b' None
                                                                                             (pair env r') in
                                                                                         pair env' (match mb_pr with
                                                                                               | None => None
                                                                                               | Some (pair b r) =>
                                                                                                   Some (Core.NonRec b
                                                                                                         r)
                                                                                               end)
                                                                                     | env, Core.Rec prs =>
                                                                                         let do_pr :=
                                                                                           fun arg_7__ arg_8__ =>
                                                                                             match arg_7__, arg_8__ with
                                                                                             | pair env prs
                                                                                             , pair (pair b r) b' =>
                                                                                                 let 'pair env' mb_pr :=
                                                                                                   simple_bind_pair env
                                                                                                     b (Some b') (pair
                                                                                                                  env
                                                                                                                  r) in
                                                                                                 pair env'
                                                                                                      (match mb_pr with
                                                                                                       | Some pr =>
                                                                                                           cons pr prs
                                                                                                       | None => prs
                                                                                                       end)
                                                                                             end in
                                                                                         let prs' :=
                                                                                           Maybes.orElse
                                                                                           (joinPointBindings_maybe prs)
                                                                                           prs in
                                                                                         let 'pair env' bndrs' :=
                                                                                           subst_opt_bndrs env
                                                                                             (GHC.Base.map
                                                                                              Data.Tuple.fst prs') in
                                                                                         let 'pair env'' rev_prs' :=
                                                                                           Data.Foldable.foldl do_pr
                                                                                             (pair env' nil)
                                                                                             (GHC.List.zip prs'
                                                                                                           bndrs') in
                                                                                         let res_bind :=
                                                                                           Some (Core.Rec
                                                                                                 (GHC.List.reverse
                                                                                                  rev_prs')) in
                                                                                         pair env'' res_bind
                                                                                     end for simple_opt_bind.

Definition simple_opt_clo : SimpleOptEnv -> SimpleClo -> Core.OutExpr :=
  fix simple_opt_expr (env : SimpleOptEnv) (expr : Core.InExpr) : Core.OutExpr
        := let fix go_lam arg_0__ arg_1__ arg_2__
                     := match arg_0__, arg_1__, arg_2__ with
                        | env, bs', Core.Lam b e =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            go_lam env' (cons b' bs') e
                        | env, bs', e =>
                            let e' := simple_opt_expr env e in
                            let bs := GHC.List.reverse bs' in
                            match CoreUtils.tryEtaReduce bs e' with
                            | Some etad_e => etad_e
                            | _ => Core.mkLams bs e'
                            end
                        end in
           let go_alt :=
             fun arg_10__ arg_11__ =>
               match arg_10__, arg_11__ with
               | env, pair (pair con bndrs) rhs =>
                   let 'pair env' bndrs' := subst_opt_bndrs env bndrs in
                   pair (pair con bndrs') (simple_opt_expr env' rhs)
               end in
           let subst := soe_subst env in
           let in_scope := CoreSubst.substInScope subst in
           let in_scope_env := pair in_scope simpleUnfoldingFun in
           let fix go arg_18__
                     := match arg_18__ with
                        | Core.Mk_Var v =>
                            match Core.lookupVarEnv (soe_inl env) v with
                            | Some clo => simple_opt_clo env clo
                            | _ =>
                                CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simpleOptExpr"))
                                (soe_subst env) v
                            end
                        | Core.App e1 e2 => simple_app env e1 (cons (pair env e2) nil)
                        | Core.Type_ ty => Core.Type_ (CoreSubst.substTy subst ty)
                        | Core.Coercion co => Core.Coercion (tt)
                        | Core.Lit lit => Core.Lit lit
                        | Core.Tick tickish e =>
                            CoreUtils.mkTick (CoreSubst.substTickish subst tickish) (go e)
                        | Core.Cast e co => let co' := tt in Core.Cast (go e) co'
                        | Core.Let bind body =>
                            match simple_opt_bind env bind with
                            | pair env' None => simple_opt_expr env' body
                            | pair env' (Some bind) => Core.Let bind (simple_opt_expr env' body)
                            end
                        | (Core.Lam _ _ as lam) => go_lam env nil lam
                        | Core.Case e b ty as_ =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            let e' := go e in
                            let j_35__ :=
                              Core.Case e' b' (CoreSubst.substTy subst ty) (GHC.Base.map (go_alt env') as_) in
                            let j_36__ :=
                              if Id.isDeadBinder b : bool
                              then match as_ with
                                   | cons (pair (pair Core.DEFAULT _) rhs) nil =>
                                       if Core.isCoercionType (Core.varType b) : bool
                                       then match Core.collectArgs e with
                                            | pair (Core.Mk_Var fun_) _args =>
                                                if Unique.hasKey fun_ PrelNames.coercibleSCSelIdKey : bool
                                                then go rhs else
                                                j_35__
                                            | _ => j_35__
                                            end else
                                       j_35__
                                   | _ => j_35__
                                   end else
                              j_35__ in
                            if Id.isDeadBinder b : bool
                            then match exprIsConApp_maybe in_scope_env e' with
                                 | Some (pair (pair con _tys) es) =>
                                     match CoreUtils.findAlt (Core.DataAlt con) as_ with
                                     | Some (pair (pair altcon bs) rhs) =>
                                         match altcon with
                                         | Core.DEFAULT => go rhs
                                         | _ =>
                                             let 'pair env' mb_prs := Data.Traversable.mapAccumL simple_out_bind env
                                                                        (Util.zipEqual (GHC.Base.hs_string__
                                                                                        "simpleOptExpr") bs es) in
                                             Data.Foldable.foldr wrapLet (simple_opt_expr env' rhs) mb_prs
                                         end
                                     | _ => j_36__
                                     end
                                 | _ => j_36__
                                 end else
                            j_36__
                        end in
           go expr with simple_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.InExpr)
                                   (arg_2__ : list SimpleClo) : Core.CoreExpr
                          := let j_4__ :=
                               match arg_0__, arg_1__, arg_2__ with
                               | env, e, as_ => finish_app env (simple_opt_expr env e) as_
                               end in
                             match arg_0__, arg_1__, arg_2__ with
                             | env, Core.Mk_Var v, as_ =>
                                 match Core.lookupVarEnv (soe_inl env) v with
                                 | Some (pair env' e) => simple_app (soeSetInScope env env') e as_
                                 | _ =>
                                     let j_6__ :=
                                       let out_fn :=
                                         CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simple_app"))
                                         (soe_subst env) v in
                                       finish_app env out_fn as_ in
                                     let unf := Id.idUnfolding v in
                                     if andb (Core.isCompulsoryUnfolding (Id.idUnfolding v))
                                             (BasicTypes.isAlwaysActive (Id.idInlineActivation v)) : bool
                                     then simple_app (soeZapSubst env) (Core.unfoldingTemplate unf) as_ else
                                     j_6__
                                 end
                             | env, Core.App e1 e2, as_ => simple_app env e1 (cons (pair env e2) as_)
                             | env, Core.Lam b e, cons a as_ =>
                                 let 'pair env' mb_pr := simple_bind_pair env b None a in
                                 wrapLet mb_pr (simple_app env' e as_)
                             | env, Core.Tick t e, as_ =>
                                 if Core.tickishScopesLike t Core.SoftScope : bool
                                 then CoreUtils.mkTick t (simple_app env e as_) else
                                 j_4__
                             | _, _, _ => j_4__
                             end with finish_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.OutExpr) (arg_2__
                                                   : list SimpleClo) : Core.OutExpr
                                        := match arg_0__, arg_1__, arg_2__ with
                                           | _, fun_, nil => fun_
                                           | env, fun_, cons arg args =>
                                               finish_app env (Core.App fun_ (simple_opt_clo env arg)) args
                                           end with simple_opt_clo (arg_0__ : SimpleOptEnv) (arg_1__ : SimpleClo)
                                                      : Core.OutExpr
                                                      := match arg_0__, arg_1__ with
                                                         | env, pair e_env e =>
                                                             simple_opt_expr (soeSetInScope env e_env) e
                                                         end with simple_bind_pair (arg_0__ : SimpleOptEnv) (arg_1__
                                                                                     : Core.InVar) (arg_2__
                                                                                     : option Core.OutVar) (arg_3__
                                                                                     : SimpleClo) : (SimpleOptEnv *
                                                                                                     option (Core.OutVar
                                                                                                             *
                                                                                                             Core.OutExpr)%type)%type
                                                                    := match arg_0__, arg_1__, arg_2__, arg_3__ with
                                                                       | (SOE inl_env subst as env)
                                                                       , in_bndr
                                                                       , mb_out_bndr
                                                                       , (pair rhs_env in_rhs as clo) =>
                                                                           let safe_to_inline
                                                                            : BasicTypes.OccInfo -> bool :=
                                                                             fun arg_4__ =>
                                                                               match arg_4__ with
                                                                               | BasicTypes.IAmALoopBreaker _ _ => false
                                                                               | BasicTypes.IAmDead => true
                                                                               | (BasicTypes.OneOcc _ _ _ _ as occ) =>
                                                                                   andb (negb (BasicTypes.occ_in_lam
                                                                                               occ))
                                                                                        (BasicTypes.occ_one_br occ)
                                                                               | BasicTypes.ManyOccs _ => false
                                                                               end in
                                                                           let occ := Id.idOccInfo in_bndr in
                                                                           let active :=
                                                                             BasicTypes.isAlwaysActive
                                                                             (Id.idInlineActivation in_bndr) in
                                                                           let stable_unf :=
                                                                             Core.isStableUnfolding (Id.idUnfolding
                                                                                                     in_bndr) in
                                                                           let pre_inline_unconditionally : bool :=
                                                                             if Core.isCoVar in_bndr : bool
                                                                             then false else
                                                                             if Core.isExportedId in_bndr : bool
                                                                             then false else
                                                                             if stable_unf : bool then false else
                                                                             if negb active : bool then false else
                                                                             if negb (safe_to_inline occ) : bool
                                                                             then false else
                                                                             true in
                                                                           match in_rhs with
                                                                           | Core.Type_ ty =>
                                                                               let out_ty :=
                                                                                 CoreSubst.substTy (soe_subst rhs_env)
                                                                                 ty in
                                                                               if andb Util.debugIsOn (negb
                                                                                        (Core.isTyVar in_bndr)) : bool
                                                                               then (Panic.assertPanic
                                                                                     (GHC.Base.hs_string__
                                                                                      "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                     #348)
                                                                               else pair (let 'SOE soe_inl_26__
                                                                                             soe_subst_27__ := env in
                                                                                          SOE soe_inl_26__
                                                                                              (CoreSubst.extendTvSubst
                                                                                               subst in_bndr out_ty))
                                                                                         None
                                                                           | _ =>
                                                                               match in_rhs with
                                                                               | Core.Coercion co =>
                                                                                   let out_co := tt in
                                                                                   if andb Util.debugIsOn (negb
                                                                                            (Core.isCoVar
                                                                                             in_bndr)) : bool
                                                                                   then (Panic.assertPanic
                                                                                         (GHC.Base.hs_string__
                                                                                          "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                         #353)
                                                                                   else pair (let 'SOE soe_inl_21__
                                                                                                 soe_subst_22__ :=
                                                                                                env in
                                                                                              SOE soe_inl_21__
                                                                                                  (CoreSubst.extendCvSubst
                                                                                                   subst in_bndr
                                                                                                   out_co)) None
                                                                               | _ =>
                                                                                   if pre_inline_unconditionally : bool
                                                                                   then pair (let 'SOE soe_inl_16__
                                                                                                 soe_subst_17__ :=
                                                                                                env in
                                                                                              SOE (Core.extendVarEnv
                                                                                                   inl_env in_bndr clo)
                                                                                                  soe_subst_17__)
                                                                                             None else
                                                                                   simple_out_bind_pair env in_bndr
                                                                                   mb_out_bndr (simple_opt_clo env clo)
                                                                                   occ active stable_unf
                                                                               end
                                                                           end
                                                                       end with simple_opt_bind (arg_0__ : SimpleOptEnv)
                                                                                                (arg_1__ : Core.InBind)
                                                                                  : (SimpleOptEnv *
                                                                                     option Core.OutBind)%type
                                                                                  := match arg_0__, arg_1__ with
                                                                                     | env, Core.NonRec b r =>
                                                                                         let 'pair b' r' :=
                                                                                           Maybes.orElse
                                                                                             (joinPointBinding_maybe b
                                                                                              r) (pair b r) in
                                                                                         let 'pair env' mb_pr :=
                                                                                           simple_bind_pair env b' None
                                                                                             (pair env r') in
                                                                                         pair env' (match mb_pr with
                                                                                               | None => None
                                                                                               | Some (pair b r) =>
                                                                                                   Some (Core.NonRec b
                                                                                                         r)
                                                                                               end)
                                                                                     | env, Core.Rec prs =>
                                                                                         let do_pr :=
                                                                                           fun arg_7__ arg_8__ =>
                                                                                             match arg_7__, arg_8__ with
                                                                                             | pair env prs
                                                                                             , pair (pair b r) b' =>
                                                                                                 let 'pair env' mb_pr :=
                                                                                                   simple_bind_pair env
                                                                                                     b (Some b') (pair
                                                                                                                  env
                                                                                                                  r) in
                                                                                                 pair env'
                                                                                                      (match mb_pr with
                                                                                                       | Some pr =>
                                                                                                           cons pr prs
                                                                                                       | None => prs
                                                                                                       end)
                                                                                             end in
                                                                                         let prs' :=
                                                                                           Maybes.orElse
                                                                                           (joinPointBindings_maybe prs)
                                                                                           prs in
                                                                                         let 'pair env' bndrs' :=
                                                                                           subst_opt_bndrs env
                                                                                             (GHC.Base.map
                                                                                              Data.Tuple.fst prs') in
                                                                                         let 'pair env'' rev_prs' :=
                                                                                           Data.Foldable.foldl do_pr
                                                                                             (pair env' nil)
                                                                                             (GHC.List.zip prs'
                                                                                                           bndrs') in
                                                                                         let res_bind :=
                                                                                           Some (Core.Rec
                                                                                                 (GHC.List.reverse
                                                                                                  rev_prs')) in
                                                                                         pair env'' res_bind
                                                                                     end for simple_opt_clo.

Definition simple_opt_expr : SimpleOptEnv -> Core.InExpr -> Core.OutExpr :=
  fix simple_opt_expr (env : SimpleOptEnv) (expr : Core.InExpr) : Core.OutExpr
        := let fix go_lam arg_0__ arg_1__ arg_2__
                     := match arg_0__, arg_1__, arg_2__ with
                        | env, bs', Core.Lam b e =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            go_lam env' (cons b' bs') e
                        | env, bs', e =>
                            let e' := simple_opt_expr env e in
                            let bs := GHC.List.reverse bs' in
                            match CoreUtils.tryEtaReduce bs e' with
                            | Some etad_e => etad_e
                            | _ => Core.mkLams bs e'
                            end
                        end in
           let go_alt :=
             fun arg_10__ arg_11__ =>
               match arg_10__, arg_11__ with
               | env, pair (pair con bndrs) rhs =>
                   let 'pair env' bndrs' := subst_opt_bndrs env bndrs in
                   pair (pair con bndrs') (simple_opt_expr env' rhs)
               end in
           let subst := soe_subst env in
           let in_scope := CoreSubst.substInScope subst in
           let in_scope_env := pair in_scope simpleUnfoldingFun in
           let fix go arg_18__
                     := match arg_18__ with
                        | Core.Mk_Var v =>
                            match Core.lookupVarEnv (soe_inl env) v with
                            | Some clo => simple_opt_clo env clo
                            | _ =>
                                CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simpleOptExpr"))
                                (soe_subst env) v
                            end
                        | Core.App e1 e2 => simple_app env e1 (cons (pair env e2) nil)
                        | Core.Type_ ty => Core.Type_ (CoreSubst.substTy subst ty)
                        | Core.Coercion co => Core.Coercion (tt)
                        | Core.Lit lit => Core.Lit lit
                        | Core.Tick tickish e =>
                            CoreUtils.mkTick (CoreSubst.substTickish subst tickish) (go e)
                        | Core.Cast e co => let co' := tt in Core.Cast (go e) co'
                        | Core.Let bind body =>
                            match simple_opt_bind env bind with
                            | pair env' None => simple_opt_expr env' body
                            | pair env' (Some bind) => Core.Let bind (simple_opt_expr env' body)
                            end
                        | (Core.Lam _ _ as lam) => go_lam env nil lam
                        | Core.Case e b ty as_ =>
                            let 'pair env' b' := subst_opt_bndr env b in
                            let e' := go e in
                            let j_35__ :=
                              Core.Case e' b' (CoreSubst.substTy subst ty) (GHC.Base.map (go_alt env') as_) in
                            let j_36__ :=
                              if Id.isDeadBinder b : bool
                              then match as_ with
                                   | cons (pair (pair Core.DEFAULT _) rhs) nil =>
                                       if Core.isCoercionType (Core.varType b) : bool
                                       then match Core.collectArgs e with
                                            | pair (Core.Mk_Var fun_) _args =>
                                                if Unique.hasKey fun_ PrelNames.coercibleSCSelIdKey : bool
                                                then go rhs else
                                                j_35__
                                            | _ => j_35__
                                            end else
                                       j_35__
                                   | _ => j_35__
                                   end else
                              j_35__ in
                            if Id.isDeadBinder b : bool
                            then match exprIsConApp_maybe in_scope_env e' with
                                 | Some (pair (pair con _tys) es) =>
                                     match CoreUtils.findAlt (Core.DataAlt con) as_ with
                                     | Some (pair (pair altcon bs) rhs) =>
                                         match altcon with
                                         | Core.DEFAULT => go rhs
                                         | _ =>
                                             let 'pair env' mb_prs := Data.Traversable.mapAccumL simple_out_bind env
                                                                        (Util.zipEqual (GHC.Base.hs_string__
                                                                                        "simpleOptExpr") bs es) in
                                             Data.Foldable.foldr wrapLet (simple_opt_expr env' rhs) mb_prs
                                         end
                                     | _ => j_36__
                                     end
                                 | _ => j_36__
                                 end else
                            j_36__
                        end in
           go expr with simple_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.InExpr)
                                   (arg_2__ : list SimpleClo) : Core.CoreExpr
                          := let j_4__ :=
                               match arg_0__, arg_1__, arg_2__ with
                               | env, e, as_ => finish_app env (simple_opt_expr env e) as_
                               end in
                             match arg_0__, arg_1__, arg_2__ with
                             | env, Core.Mk_Var v, as_ =>
                                 match Core.lookupVarEnv (soe_inl env) v with
                                 | Some (pair env' e) => simple_app (soeSetInScope env env') e as_
                                 | _ =>
                                     let j_6__ :=
                                       let out_fn :=
                                         CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "simple_app"))
                                         (soe_subst env) v in
                                       finish_app env out_fn as_ in
                                     let unf := Id.idUnfolding v in
                                     if andb (Core.isCompulsoryUnfolding (Id.idUnfolding v))
                                             (BasicTypes.isAlwaysActive (Id.idInlineActivation v)) : bool
                                     then simple_app (soeZapSubst env) (Core.unfoldingTemplate unf) as_ else
                                     j_6__
                                 end
                             | env, Core.App e1 e2, as_ => simple_app env e1 (cons (pair env e2) as_)
                             | env, Core.Lam b e, cons a as_ =>
                                 let 'pair env' mb_pr := simple_bind_pair env b None a in
                                 wrapLet mb_pr (simple_app env' e as_)
                             | env, Core.Tick t e, as_ =>
                                 if Core.tickishScopesLike t Core.SoftScope : bool
                                 then CoreUtils.mkTick t (simple_app env e as_) else
                                 j_4__
                             | _, _, _ => j_4__
                             end with finish_app (arg_0__ : SimpleOptEnv) (arg_1__ : Core.OutExpr) (arg_2__
                                                   : list SimpleClo) : Core.OutExpr
                                        := match arg_0__, arg_1__, arg_2__ with
                                           | _, fun_, nil => fun_
                                           | env, fun_, cons arg args =>
                                               finish_app env (Core.App fun_ (simple_opt_clo env arg)) args
                                           end with simple_opt_clo (arg_0__ : SimpleOptEnv) (arg_1__ : SimpleClo)
                                                      : Core.OutExpr
                                                      := match arg_0__, arg_1__ with
                                                         | env, pair e_env e =>
                                                             simple_opt_expr (soeSetInScope env e_env) e
                                                         end with simple_bind_pair (arg_0__ : SimpleOptEnv) (arg_1__
                                                                                     : Core.InVar) (arg_2__
                                                                                     : option Core.OutVar) (arg_3__
                                                                                     : SimpleClo) : (SimpleOptEnv *
                                                                                                     option (Core.OutVar
                                                                                                             *
                                                                                                             Core.OutExpr)%type)%type
                                                                    := match arg_0__, arg_1__, arg_2__, arg_3__ with
                                                                       | (SOE inl_env subst as env)
                                                                       , in_bndr
                                                                       , mb_out_bndr
                                                                       , (pair rhs_env in_rhs as clo) =>
                                                                           let safe_to_inline
                                                                            : BasicTypes.OccInfo -> bool :=
                                                                             fun arg_4__ =>
                                                                               match arg_4__ with
                                                                               | BasicTypes.IAmALoopBreaker _ _ => false
                                                                               | BasicTypes.IAmDead => true
                                                                               | (BasicTypes.OneOcc _ _ _ _ as occ) =>
                                                                                   andb (negb (BasicTypes.occ_in_lam
                                                                                               occ))
                                                                                        (BasicTypes.occ_one_br occ)
                                                                               | BasicTypes.ManyOccs _ => false
                                                                               end in
                                                                           let occ := Id.idOccInfo in_bndr in
                                                                           let active :=
                                                                             BasicTypes.isAlwaysActive
                                                                             (Id.idInlineActivation in_bndr) in
                                                                           let stable_unf :=
                                                                             Core.isStableUnfolding (Id.idUnfolding
                                                                                                     in_bndr) in
                                                                           let pre_inline_unconditionally : bool :=
                                                                             if Core.isCoVar in_bndr : bool
                                                                             then false else
                                                                             if Core.isExportedId in_bndr : bool
                                                                             then false else
                                                                             if stable_unf : bool then false else
                                                                             if negb active : bool then false else
                                                                             if negb (safe_to_inline occ) : bool
                                                                             then false else
                                                                             true in
                                                                           match in_rhs with
                                                                           | Core.Type_ ty =>
                                                                               let out_ty :=
                                                                                 CoreSubst.substTy (soe_subst rhs_env)
                                                                                 ty in
                                                                               if andb Util.debugIsOn (negb
                                                                                        (Core.isTyVar in_bndr)) : bool
                                                                               then (Panic.assertPanic
                                                                                     (GHC.Base.hs_string__
                                                                                      "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                     #348)
                                                                               else pair (let 'SOE soe_inl_26__
                                                                                             soe_subst_27__ := env in
                                                                                          SOE soe_inl_26__
                                                                                              (CoreSubst.extendTvSubst
                                                                                               subst in_bndr out_ty))
                                                                                         None
                                                                           | _ =>
                                                                               match in_rhs with
                                                                               | Core.Coercion co =>
                                                                                   let out_co := tt in
                                                                                   if andb Util.debugIsOn (negb
                                                                                            (Core.isCoVar
                                                                                             in_bndr)) : bool
                                                                                   then (Panic.assertPanic
                                                                                         (GHC.Base.hs_string__
                                                                                          "ghc/compiler/coreSyn/CoreOpt.hs")
                                                                                         #353)
                                                                                   else pair (let 'SOE soe_inl_21__
                                                                                                 soe_subst_22__ :=
                                                                                                env in
                                                                                              SOE soe_inl_21__
                                                                                                  (CoreSubst.extendCvSubst
                                                                                                   subst in_bndr
                                                                                                   out_co)) None
                                                                               | _ =>
                                                                                   if pre_inline_unconditionally : bool
                                                                                   then pair (let 'SOE soe_inl_16__
                                                                                                 soe_subst_17__ :=
                                                                                                env in
                                                                                              SOE (Core.extendVarEnv
                                                                                                   inl_env in_bndr clo)
                                                                                                  soe_subst_17__)
                                                                                             None else
                                                                                   simple_out_bind_pair env in_bndr
                                                                                   mb_out_bndr (simple_opt_clo env clo)
                                                                                   occ active stable_unf
                                                                               end
                                                                           end
                                                                       end with simple_opt_bind (arg_0__ : SimpleOptEnv)
                                                                                                (arg_1__ : Core.InBind)
                                                                                  : (SimpleOptEnv *
                                                                                     option Core.OutBind)%type
                                                                                  := match arg_0__, arg_1__ with
                                                                                     | env, Core.NonRec b r =>
                                                                                         let 'pair b' r' :=
                                                                                           Maybes.orElse
                                                                                             (joinPointBinding_maybe b
                                                                                              r) (pair b r) in
                                                                                         let 'pair env' mb_pr :=
                                                                                           simple_bind_pair env b' None
                                                                                             (pair env r') in
                                                                                         pair env' (match mb_pr with
                                                                                               | None => None
                                                                                               | Some (pair b r) =>
                                                                                                   Some (Core.NonRec b
                                                                                                         r)
                                                                                               end)
                                                                                     | env, Core.Rec prs =>
                                                                                         let do_pr :=
                                                                                           fun arg_7__ arg_8__ =>
                                                                                             match arg_7__, arg_8__ with
                                                                                             | pair env prs
                                                                                             , pair (pair b r) b' =>
                                                                                                 let 'pair env' mb_pr :=
                                                                                                   simple_bind_pair env
                                                                                                     b (Some b') (pair
                                                                                                                  env
                                                                                                                  r) in
                                                                                                 pair env'
                                                                                                      (match mb_pr with
                                                                                                       | Some pr =>
                                                                                                           cons pr prs
                                                                                                       | None => prs
                                                                                                       end)
                                                                                             end in
                                                                                         let prs' :=
                                                                                           Maybes.orElse
                                                                                           (joinPointBindings_maybe prs)
                                                                                           prs in
                                                                                         let 'pair env' bndrs' :=
                                                                                           subst_opt_bndrs env
                                                                                             (GHC.Base.map
                                                                                              Data.Tuple.fst prs') in
                                                                                         let 'pair env'' rev_prs' :=
                                                                                           Data.Foldable.foldl do_pr
                                                                                             (pair env' nil)
                                                                                             (GHC.List.zip prs'
                                                                                                           bndrs') in
                                                                                         let res_bind :=
                                                                                           Some (Core.Rec
                                                                                                 (GHC.List.reverse
                                                                                                  rev_prs')) in
                                                                                         pair env'' res_bind
                                                                                     end for simple_opt_expr.

Definition simpleOptExprWith : CoreSubst.Subst -> Core.InExpr -> Core.OutExpr :=
  fun subst expr =>
    let init_env := SOE Core.emptyVarEnv subst in
    simple_opt_expr init_env (OccurAnal.occurAnalyseExpr expr).

Definition exprIsLambda_maybe
   : Core.InScopeEnv ->
     Core.CoreExpr ->
     option (Core.Var * Core.CoreExpr * list (Core.Tickish Core.Id))%type :=
  fix exprIsLambda_maybe (arg_0__ : Core.InScopeEnv) (arg_1__ : Core.CoreExpr)
        : option (Core.Var * Core.CoreExpr * list (Core.Tickish Core.Id))%type
        := let j_2__ := match arg_0__, arg_1__ with | _, _e => None end in
           let j_6__ :=
             match arg_0__, arg_1__ with
             | pair in_scope_set id_unf, e =>
                 match Core.collectArgsTicks Core.tickishFloatable e with
                 | pair (pair (Core.Mk_Var f) as_) ts =>
                     if Id.idArity f GHC.Base.> Util.count Core.isValArg as_ : bool
                     then match None with
                          | Some rhs =>
                              let e' :=
                                simpleOptExprWith (CoreSubst.mkEmptySubst in_scope_set) (Core.mkApps rhs as_) in
                              match exprIsLambda_maybe (pair in_scope_set id_unf) e' with
                              | Some (pair (pair x' e'') ts') =>
                                  let res := Some (pair (pair x' e'') (Coq.Init.Datatypes.app ts ts')) in res
                              | _ => j_2__
                              end
                          | _ => j_2__
                          end else
                     j_2__
                 | _ => j_2__
                 end
             end in
           match arg_0__, arg_1__ with
           | _, Core.Lam x e => Some (pair (pair x e) nil)
           | pair in_scope_set id_unf, Core.Tick t e =>
               if Core.tickishFloatable t : bool
               then match exprIsLambda_maybe (pair in_scope_set id_unf) e with
                    | Some (pair (pair x e) ts) => Some (pair (pair x e) (cons t ts))
                    | _ => j_6__
                    end else
               j_6__
           | pair in_scope_set id_unf, Core.Cast casted_e co =>
               match exprIsLambda_maybe (pair in_scope_set id_unf) casted_e with
               | Some (pair (pair x e) ts) =>
                   if andb (andb (negb (Core.isTyVar x)) (negb (Core.isCoVar x))) (if andb
                                                                                      Util.debugIsOn (negb (negb
                                                                                                            (Core.elemVarSet
                                                                                                             x
                                                                                                             (TyCoRep.tyCoVarsOfCo
                                                                                                              co)))) : bool
                            then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreOpt.hs")
                                  #882)
                            else true) : bool
                   then match pushCoercionIntoLambda in_scope_set x e co with
                        | Some (pair x' e') => let res := Some (pair (pair x' e') ts) in res
                        | _ => j_6__
                        end else
                   j_6__
               | _ => j_6__
               end
           | _, _ => j_6__
           end.

Definition simpleOptExpr : Core.CoreExpr -> Core.CoreExpr :=
  fun expr =>
    let init_subst :=
      CoreSubst.mkEmptySubst (Core.mkInScopeSet (CoreFVs.exprFreeVars expr)) in
    simpleOptExprWith init_subst expr.

Definition substVect : CoreSubst.Subst -> Core.CoreVect -> Core.CoreVect :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | subst, Core.Vect v rhs => Core.Vect v (simpleOptExprWith subst rhs)
    | _subst, (Core.NoVect _ as vd) => vd
    | _subst, (Core.VectType _ _ _ as vd) => vd
    | _subst, (Core.VectClass _ as vd) => vd
    | _subst, (Core.VectInst _ as vd) => vd
    end.

Definition substVects
   : CoreSubst.Subst -> list Core.CoreVect -> list Core.CoreVect :=
  fun subst => GHC.Base.map (substVect subst).

Definition simpleOptPgm
   : DynFlags.DynFlags ->
     Module.Module ->
     Core.CoreProgram ->
     list Core.CoreRule ->
     list Core.CoreVect ->
     GHC.Types.IO (Core.CoreProgram * list Core.CoreRule *
                   list Core.CoreVect)%type :=
  fun dflags this_mod binds rules vects =>
    let do_one :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair env binds', bind =>
            match simple_opt_bind env bind with
            | pair env' None => pair env' binds'
            | pair env' (Some bind') => pair env' (cons bind' binds')
            end
        end in
    let occ_anald_binds :=
      OccurAnal.occurAnalysePgm this_mod (fun arg_8__ => false) rules vects
      Core.emptyVarSet binds in
    let 'pair final_env binds' := Data.Foldable.foldl do_one (pair emptyEnv nil)
                                    occ_anald_binds in
    let final_subst := soe_subst final_env in
    let rules' := CoreSubst.substRulesForImportedIds final_subst rules in
    let vects' := substVects final_subst vects in
    ErrUtils.dumpIfSet_dyn dflags DynFlags.Opt_D_dump_occur_anal
    (GHC.Base.hs_string__ "Occurrence analysis") (PprCore.pprCoreBindings
                                                  occ_anald_binds) GHC.Base.>>
    GHC.Base.return_ (pair (pair (GHC.List.reverse binds') rules') vects').

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreOpt.Outputable__SimpleOptEnv' *)

(* External variables:
     None Some andb bool cons false list negb nil op_zt__ option orb pair true tt
     unit BasicTypes.AlwaysTailCalled BasicTypes.IAmALoopBreaker BasicTypes.IAmDead
     BasicTypes.ManyOccs BasicTypes.OccInfo BasicTypes.OneOcc
     BasicTypes.isAlwaysActive BasicTypes.isWeakLoopBreaker BasicTypes.occ_in_lam
     BasicTypes.occ_one_br BasicTypes.tailCallInfo Coq.Init.Datatypes.app Core.App
     Core.Case Core.Cast Core.Coercion Core.CoreArg Core.CoreExpr Core.CoreProgram
     Core.CoreRule Core.CoreVect Core.DEFAULT Core.DataAlt Core.DataCon Core.Id
     Core.IdEnv Core.IdUnfoldingFun Core.InBind Core.InBndr Core.InExpr Core.InId
     Core.InScopeEnv Core.InScopeSet Core.InVar Core.Lam Core.Let Core.Lit
     Core.Mk_Var Core.NoVect Core.NonRec Core.OutBind Core.OutExpr Core.OutId
     Core.OutVar Core.Rec Core.SoftScope Core.Tick Core.Tickish Core.Type_ Core.Var
     Core.Vect Core.VectClass Core.VectInst Core.VectType Core.collectArgs
     Core.collectArgsTicks Core.delVarEnv Core.elemVarSet Core.emptyVarEnv
     Core.emptyVarSet Core.extendInScopeSet Core.extendVarEnv Core.idInfo
     Core.isCoVar Core.isCoercionType Core.isCompulsoryUnfolding Core.isExportedId
     Core.isId Core.isStableUnfolding Core.isTyVar Core.isValArg Core.lookupVarEnv
     Core.mkApps Core.mkInScopeSet Core.mkLams Core.noUnfolding Core.tickishFloatable
     Core.tickishScopesLike Core.unfoldingTemplate Core.uniqAway Core.varType
     CoreArity.etaExpandToJoinPoint CoreFVs.exprFreeVars CoreSubst.Mk_Subst
     CoreSubst.Subst CoreSubst.emptySubst CoreSubst.extendCvSubst
     CoreSubst.extendIdSubst CoreSubst.extendTvSubst CoreSubst.lookupIdSubst
     CoreSubst.mkEmptySubst CoreSubst.setInScope CoreSubst.substCoVarBndr
     CoreSubst.substIdInfo CoreSubst.substInScope CoreSubst.substRulesForImportedIds
     CoreSubst.substTickish CoreSubst.substTy CoreSubst.substTyVarBndr
     CoreSubst.zapSubstEnv CoreUtils.exprIsTrivial CoreUtils.findAlt CoreUtils.mkTick
     CoreUtils.tryEtaReduce Data.Foldable.all Data.Foldable.foldl Data.Foldable.foldr
     Data.Traversable.mapAccumL Data.Traversable.mapM Data.Tuple.fst
     Data.Tuple.uncurry Datatypes.id DynFlags.DynFlags DynFlags.Opt_D_dump_occur_anal
     ErrUtils.dumpIfSet_dyn GHC.Base.String GHC.Base.map GHC.Base.op_zeze__
     GHC.Base.op_zg__ GHC.Base.op_zgzg__ GHC.Base.return_ GHC.Err.Build_Default
     GHC.Err.Default GHC.Err.default GHC.List.reverse GHC.List.zip
     GHC.Num.fromInteger GHC.Types.IO Id.asJoinId Id.idArity Id.idInlineActivation
     Id.idOccInfo Id.idUnfolding Id.isDataConWorkId_maybe Id.isDeadBinder Id.isJoinId
     Id.maybeModifyIdInfo Id.zapFragileIdInfo Literal.Literal Maybes.orElse
     Module.Module OccurAnal.occurAnalyseExpr OccurAnal.occurAnalysePgm
     Panic.assertPanic PprCore.pprCoreBindings PrelNames.coercibleDataConKey
     PrelNames.coercibleSCSelIdKey PrelNames.heqDataConKey TyCoRep.tyCoVarsOfCo
     Unique.hasKey Util.count Util.debugIsOn Util.zipEqual
*)
