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
Require Coq.Lists.List.
Require CoreFVs.
Require CoreSubst.
Require CoreSyn.
Require CoreUtils.
Require Data.Foldable.
Require Datatypes.
Require Demand.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require Pair.
Require Panic.
Require TyCon.
Require Unique.
Require Var.
Require VarEnv.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive EtaInfo : Type
  := EtaVar : Var.Var -> EtaInfo
  |  EtaCo : unit -> EtaInfo.

Definition CheapFun :=
  (CoreSyn.CoreExpr -> option unit -> bool)%type.

Inductive ArityType : Type
  := ATop : list BasicTypes.OneShotInfo -> ArityType
  |  ABot : BasicTypes.Arity -> ArityType.

Inductive ArityEnv : Type := AE : CheapFun -> bool -> ArityEnv.

Definition ae_cheap_fn (arg_0__ : ArityEnv) :=
  let 'AE ae_cheap_fn _ := arg_0__ in
  ae_cheap_fn.

Definition ae_ped_bot (arg_0__ : ArityEnv) :=
  let 'AE _ ae_ped_bot := arg_0__ in
  ae_ped_bot.
(* Converted value declarations: *)

(* Skipping instance Outputable__EtaInfo of class Outputable *)

(* Skipping instance Outputable__ArityType of class Outputable *)

Definition andArityType : ArityType -> ArityType -> ArityType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | ABot n1, ABot n2 => ABot (GHC.Base.max n1 n2)
    | ATop as_, ABot _ => ATop as_
    | ABot _, ATop bs => ATop bs
    | ATop as_, ATop bs =>
        let fix combine arg_5__ arg_6__
                  := match arg_5__, arg_6__ with
                     | cons a as_, cons b bs => cons (BasicTypes.bestOneShot a b) (combine as_ bs)
                     | nil, bs => GHC.List.takeWhile BasicTypes.isOneShotInfo bs
                     | as_, nil => GHC.List.takeWhile BasicTypes.isOneShotInfo as_
                     end in
        ATop (combine as_ bs)
    end.

Definition arityLam : Var.Id -> ArityType -> ArityType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | id, ATop as_ => ATop (cons (Id.idStateHackOneShotInfo id) as_)
    | _, ABot n => ABot (n GHC.Num.+ #1)
    end.

Definition etaInfoAbs : list EtaInfo -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr :=
  fix etaInfoAbs arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | nil, expr => expr
           | cons (EtaVar v) eis, expr => CoreSyn.Lam v (etaInfoAbs eis expr)
           | cons (EtaCo co) eis, expr =>
               CoreSyn.Cast (etaInfoAbs eis expr) (Coercion.mkSymCo co)
           end.

Definition etaInfoAppTy : unit -> list EtaInfo -> unit :=
  fix etaInfoAppTy arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | ty, nil => ty
           | ty, cons (EtaVar v) eis =>
               etaInfoAppTy (CoreSyn.applyTypeToArg ty (CoreSyn.varToCoreExpr v)) eis
           | _, cons (EtaCo co) eis =>
               etaInfoAppTy (Pair.pSnd (Coercion.coercionKind co)) eis
           end.

Definition floatIn : bool -> ArityType -> ArityType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, ABot n => ABot n
    | true, ATop as_ => ATop as_
    | false, ATop as_ => ATop (GHC.List.takeWhile BasicTypes.isOneShotInfo as_)
    end.

Definition arityApp : ArityType -> bool -> ArityType :=
  fun arg_0__ arg_1__ =>
    let j_6__ :=
      match arg_0__, arg_1__ with
      | ABot n, _ => ABot (n GHC.Num.- #1)
      | ATop nil, _ => ATop nil
      | ATop (cons _ as_), cheap => floatIn cheap (ATop as_)
      end in
    match arg_0__, arg_1__ with
    | ABot num_2__, _ => if num_2__ GHC.Base.== #0 : bool then ABot #0 else j_6__
    | _, _ => j_6__
    end.

Definition freshEtaId : GHC.Num.Int -> unit -> unit -> (unit * Var.Id)%type :=
  fun n subst ty =>
    let ty' := TyCoRep.substTy subst ty in
    let eta_id' :=
      VarEnv.uniqAway (TyCoRep.getTCvInScope subst) (Id.mkSysLocalOrCoVar
                                                     (FastString.fsLit (GHC.Base.hs_string__ "eta"))
                                                     (Unique.mkBuiltinUnique n) ty') in
    let subst' := TyCoRep.extendTCvInScope subst eta_id' in pair subst' eta_id'.

Definition etaBodyForJoinPoint
   : GHC.Num.Int ->
     CoreSyn.CoreExpr -> (list CoreSyn.CoreBndr * CoreSyn.CoreExpr)%type :=
  fun need_args body =>
    let init_subst :=
      fun e =>
        TyCoRep.mkEmptyTCvSubst (VarEnv.mkInScopeSet (CoreFVs.exprFreeVars e)) in
    let fix go arg_1__ arg_2__ arg_3__ arg_4__ arg_5__
              := match arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
                 | num_6__, _, _, rev_bs, e =>
                     if num_6__ GHC.Base.== #0 : bool then pair (GHC.List.reverse rev_bs) e else
                     match arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
                     | n, ty, subst, rev_bs, e =>
                         match Type.splitForAllTy_maybe ty with
                         | Some (pair tv res_ty) =>
                             let 'pair subst' tv' := TyCoRep.substTyVarBndr subst tv in
                             go (n GHC.Num.- #1) res_ty subst' (cons tv' rev_bs) (CoreSyn.App e
                                                                                              (CoreSyn.Type_ (tt)))
                         | _ =>
                             match Type.splitFunTy_maybe ty with
                             | Some (pair arg_ty res_ty) =>
                                 let 'pair subst' b := freshEtaId n subst arg_ty in
                                 go (n GHC.Num.- #1) res_ty subst' (cons b rev_bs) (CoreSyn.App e (CoreSyn.Var
                                                                                                 b))
                             | _ =>
                                 Panic.panicStr (GHC.Base.hs_string__ "etaBodyForJoinPoint") Panic.someSDoc
                             end
                         end
                     end
                 end in
    go need_args (tt) (init_subst body) nil body.

Definition etaExpandToJoinPoint
   : BasicTypes.JoinArity ->
     CoreSyn.CoreExpr -> (list CoreSyn.CoreBndr * CoreSyn.CoreExpr)%type :=
  fun join_arity expr =>
    let fix go arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | num_3__, rev_bs, e =>
                     if num_3__ GHC.Base.== #0 : bool then pair (GHC.List.reverse rev_bs) e else
                     match arg_0__, arg_1__, arg_2__ with
                     | n, rev_bs, CoreSyn.Lam b e => go (n GHC.Num.- #1) (cons b rev_bs) e
                     | n, rev_bs, e =>
                         let 'pair bs e' := etaBodyForJoinPoint n e in
                         pair (Coq.Init.Datatypes.app (GHC.List.reverse rev_bs) bs) e'
                     end
                 end in
    go join_arity nil expr.

Definition etaExpandToJoinPointRule
   : BasicTypes.JoinArity -> CoreSyn.CoreRule -> CoreSyn.CoreRule :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, (CoreSyn.BuiltinRule _ _ _ _ as rule) =>
        Panic.warnPprTrace (true) (GHC.Base.hs_string__
                            "ghc/compiler/coreSyn/CoreArity.hs") #1100 ((Outputable.sep (cons (Datatypes.id
                                                                                               (GHC.Base.hs_string__
                                                                                                "Can't eta-expand built-in rule:"))
                                                                                              (cons (Panic.noString
                                                                                                     rule) nil)))) rule
    | join_arity, (CoreSyn.Rule _ _ _ _ bndrs args rhs _ _ _ _ as rule) =>
        let need_args := join_arity GHC.Num.- Data.Foldable.length args in
        let 'pair new_bndrs new_rhs := etaBodyForJoinPoint need_args rhs in
        let new_args := CoreSyn.varsToCoreExprs new_bndrs in
        if need_args GHC.Base.== #0 : bool then rule else
        if need_args GHC.Base.< #0 : bool
        then Panic.panicStr (GHC.Base.hs_string__ "etaExpandToJoinPointRule")
             (Panic.someSDoc) else
        match rule with
        | CoreSyn.Rule ru_name_6__ ru_act_7__ ru_fn_8__ ru_rough_9__ ru_bndrs_10__
        ru_args_11__ ru_rhs_12__ ru_auto_13__ ru_origin_14__ ru_orphan_15__
        ru_local_16__ =>
            CoreSyn.Rule ru_name_6__ ru_act_7__ ru_fn_8__ ru_rough_9__
                         (Coq.Init.Datatypes.app bndrs new_bndrs) (Coq.Init.Datatypes.app args new_args)
                         new_rhs ru_auto_13__ ru_origin_14__ ru_orphan_15__ ru_local_16__
        | CoreSyn.BuiltinRule _ _ _ _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        end
    end.

Definition getBotArity : ArityType -> option BasicTypes.Arity :=
  fun arg_0__ => match arg_0__ with | ABot n => Some n | _ => None end.

Definition joinRhsArity : CoreSyn.CoreExpr -> BasicTypes.JoinArity :=
  fix joinRhsArity arg_0__
        := match arg_0__ with
           | CoreSyn.Lam _ e => #1 GHC.Num.+ joinRhsArity e
           | _ => #0
           end.

Definition manifestArity : CoreSyn.CoreExpr -> BasicTypes.Arity :=
  fix manifestArity arg_0__
        := let j_3__ :=
             match arg_0__ with
             | CoreSyn.Cast e _ => manifestArity e
             | _ => #0
             end in
           match arg_0__ with
           | CoreSyn.Lam v e =>
               if Var.isId v : bool then #1 GHC.Num.+ manifestArity e else
               manifestArity e
           | CoreSyn.Tick t e =>
               if negb (CoreSyn.tickishIsCode t) : bool then manifestArity e else
               j_3__
           | _ => j_3__
           end.

Definition mk_cheap_fn
   : DynFlags.DynFlags -> CoreUtils.CheapAppFun -> CheapFun :=
  fun dflags cheap_app =>
    if negb (DynFlags.gopt DynFlags.Opt_DictsCheap dflags) : bool
    then fun arg_4__ arg_5__ =>
           match arg_4__, arg_5__ with
           | e, _ => CoreUtils.exprIsCheapX cheap_app e
           end else
    fun e mb_ty =>
      orb (CoreUtils.exprIsCheapX cheap_app e) (match mb_ty with
           | None => false
           | Some ty => Type.isDictLikeTy ty
           end).

Definition pushCoercion : unit -> list EtaInfo -> list EtaInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | co1, cons (EtaCo co2) eis =>
        let co := Coercion.mkTransCo co1 co2 in
        if Coercion.isReflCo co : bool then eis else
        cons (EtaCo co) eis
    | _, _ => match arg_0__, arg_1__ with | co, eis => cons (EtaCo co) eis end
    end.

Definition mkEtaWW
   : BasicTypes.Arity ->
     CoreSyn.CoreExpr ->
     VarEnv.InScopeSet -> unit -> (VarEnv.InScopeSet * list EtaInfo)%type :=
  fun orig_n orig_expr in_scope orig_ty =>
    let fix go n subst ty eis
              := if n GHC.Base.== #0 : bool
                 then pair (TyCoRep.getTCvInScope subst) (GHC.List.reverse eis) else
                 match Type.splitForAllTy_maybe ty with
                 | Some (pair tv ty') =>
                     let 'pair subst' tv' := TyCoRep.substTyVarBndr subst tv in
                     go n subst' ty' (cons (EtaVar tv') eis)
                 | _ =>
                     let j_0__ :=
                       Panic.warnPprTrace (true) (GHC.Base.hs_string__
                                           "ghc/compiler/coreSyn/CoreArity.hs") #1066 (Panic.someSDoc) (pair
                                                                                                        (TyCoRep.getTCvInScope
                                                                                                         subst)
                                                                                                        (GHC.List.reverse
                                                                                                         eis)) in
                     let j_1__ :=
                       match Coercion.topNormaliseNewType_maybe ty with
                       | Some (pair co ty') => go n subst ty' (pushCoercion co eis)
                       | _ => j_0__
                       end in
                     match Type.splitFunTy_maybe ty with
                     | Some (pair arg_ty res_ty) =>
                         if negb (Type.isTypeLevPoly arg_ty) : bool
                         then let 'pair subst' eta_id' := freshEtaId n subst arg_ty in
                              go (n GHC.Num.- #1) subst' res_ty (cons (EtaVar eta_id') eis) else
                         j_1__
                     | _ => j_1__
                     end
                 end in
    let empty_subst := TyCoRep.mkEmptyTCvSubst in_scope in
    go orig_n empty_subst orig_ty nil.

Definition subst_expr
   : CoreSubst.Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr :=
  CoreSubst.substExpr (Datatypes.id (GHC.Base.hs_string__ "CoreArity:substExpr")).

Definition etaInfoApp
   : CoreSubst.Subst -> CoreSyn.CoreExpr -> list EtaInfo -> CoreSyn.CoreExpr :=
  fix etaInfoApp arg_0__ arg_1__ arg_2__
        := let j_9__ :=
             match arg_0__, arg_1__, arg_2__ with
             | subst, e, eis =>
                 let fix go arg_3__ arg_4__
                           := match arg_3__, arg_4__ with
                              | e, nil => e
                              | e, cons (EtaVar v) eis => go (CoreSyn.App e (CoreSyn.varToCoreExpr v)) eis
                              | e, cons (EtaCo co) eis => go (CoreSyn.Cast e co) eis
                              end in
                 go (subst_expr subst e) eis
             end in
           let j_12__ :=
             match arg_0__, arg_1__, arg_2__ with
             | subst, CoreSyn.Tick t e, eis =>
                 CoreSyn.Tick (CoreSubst.substTickish subst t) (etaInfoApp subst e eis)
             | subst, expr, _ =>
                 match CoreSyn.collectArgs expr with
                 | pair (CoreSyn.Var fun_) _ =>
                     match CoreSubst.lookupIdSubst (GHC.Base.mappend (Datatypes.id
                                                                      (GHC.Base.hs_string__ "etaInfoApp"))
                                                                     (Panic.noString fun_)) subst fun_ with
                     | CoreSyn.Var fun' =>
                         if Id.isJoinId fun' : bool then subst_expr subst expr else
                         j_9__
                     | _ => j_9__
                     end
                 | _ => j_9__
                 end
             end in
           match arg_0__, arg_1__, arg_2__ with
           | subst, CoreSyn.Lam v1 e, cons (EtaVar v2) eis =>
               etaInfoApp (CoreSubst.extendSubstWithVar subst v1 v2) e eis
           | subst, CoreSyn.Cast e co1, eis =>
               let co' := CoreSubst.substCo subst co1 in
               etaInfoApp subst e (pushCoercion co' eis)
           | subst, CoreSyn.Case e b ty alts, eis =>
               let ty' := etaInfoAppTy (CoreSubst.substTy subst ty) eis in
               let 'pair subst1 b1 := CoreSubst.substBndr subst b in
               let subst_alt :=
                 fun '(pair (pair con bs) rhs) =>
                   let 'pair subst2 bs' := CoreSubst.substBndrs subst1 bs in
                   pair (pair con bs') (etaInfoApp subst2 rhs eis) in
               let alts' := GHC.Base.map subst_alt alts in
               CoreSyn.Case (subst_expr subst e) b1 ty' alts'
           | subst, CoreSyn.Let b e, eis =>
               let 'pair subst' b' := CoreSubst.substBindSC subst b in
               if negb (CoreUtils.isJoinBind b) : bool
               then CoreSyn.Let b' (etaInfoApp subst' e eis) else
               j_12__
           | _, _, _ => j_12__
           end.

Definition etaExpand
   : BasicTypes.Arity -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr :=
  fun n orig_expr =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | num_2__, expr =>
                     if num_2__ GHC.Base.== #0 : bool then expr else
                     match arg_0__, arg_1__ with
                     | n, CoreSyn.Lam v body =>
                         if Var.isTyVar v : bool then CoreSyn.Lam v (go n body) else
                         CoreSyn.Lam v (go (n GHC.Num.- #1) body)
                     | _, _ =>
                         match arg_0__, arg_1__ with
                         | n, CoreSyn.Cast expr co => CoreSyn.Cast (go n expr) co
                         | n, expr =>
                             let 'pair expr' args := CoreSyn.collectArgs expr in
                             let 'pair ticks expr'' := CoreUtils.stripTicksTop CoreSyn.tickishFloatable
                                                         expr' in
                             let retick := fun expr => Data.Foldable.foldr CoreUtils.mkTick expr ticks in
                             let sexpr := Data.Foldable.foldl CoreSyn.App expr'' args in
                             let in_scope := VarEnv.mkInScopeSet (CoreFVs.exprFreeVars expr) in
                             let 'pair in_scope' etas := mkEtaWW n orig_expr in_scope (tt) in
                             let subst' := CoreSubst.mkEmptySubst in_scope' in
                             retick (etaInfoAbs etas (etaInfoApp subst' sexpr etas))
                         end
                     end
                 end in
    go n orig_expr.

Definition typeArity : unit -> list BasicTypes.OneShotInfo :=
  fun ty =>
    let fix go rec_nts ty
              := match Type.splitForAllTy_maybe ty with
                 | Some (pair _ ty') => go rec_nts ty'
                 | _ =>
                     match Type.splitFunTy_maybe ty with
                     | Some (pair arg res) => cons (Id.typeOneShot arg) (go rec_nts res)
                     | _ =>
                         match Type.splitTyConApp_maybe ty with
                         | Some (pair tc tys) =>
                             match Coercion.instNewTyCon_maybe tc tys with
                             | Some (pair ty' _) =>
                                 match TyCon.checkRecTc rec_nts tc with
                                 | Some rec_nts' => go rec_nts' ty'
                                 | _ => nil
                                 end
                             | _ => nil
                             end
                         | _ => nil
                         end
                     end
                 end in
    go TyCon.initRecTc ty.

Definition exprArity : CoreSyn.CoreExpr -> BasicTypes.Arity :=
  fun e =>
    let trim_arity : BasicTypes.Arity -> unit -> BasicTypes.Arity :=
      fun arity ty => GHC.Base.min arity (Data.Foldable.length (typeArity ty)) in
    let fix go arg_1__
              := let j_3__ := #0 in
                 match arg_1__ with
                 | CoreSyn.Var v => Id.idArity v
                 | CoreSyn.Lam x e => if Var.isId x : bool then go e GHC.Num.+ #1 else go e
                 | CoreSyn.Tick t e =>
                     if negb (CoreSyn.tickishIsCode t) : bool then go e else
                     j_3__
                 | CoreSyn.Cast e co => trim_arity (go e) (Pair.pSnd (Coercion.coercionKind co))
                 | CoreSyn.App e (CoreSyn.Type_ _) => go e
                 | CoreSyn.App f a =>
                     if CoreUtils.exprIsTrivial a : bool
                     then GHC.Base.max (go f GHC.Num.- #1) #0 else
                     j_3__
                 | _ => j_3__
                 end in
    go e.

Definition vanillaArityType : ArityType :=
  ATop nil.

Definition arityType : ArityEnv -> CoreSyn.CoreExpr -> ArityType :=
  fix arityType arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | env, CoreSyn.Cast e co =>
               let co_arity :=
                 Data.Foldable.length (typeArity (Pair.pSnd (Coercion.coercionKind co))) in
               match arityType env e with
               | ATop os => ATop (GHC.List.take co_arity os)
               | ABot n => ABot (GHC.Base.min n co_arity)
               end
           | _, CoreSyn.Var v =>
               let one_shots : list BasicTypes.OneShotInfo := typeArity (tt) in
               let 'strict_sig := Id.idStrictness v in
               if negb (Demand.isTopSig strict_sig) : bool
               then let 'pair ds res := Demand.splitStrictSig strict_sig in
                    let arity := Data.Foldable.length ds in
                    if Demand.isBotRes res : bool
                    then ABot arity
                    else ATop (GHC.List.take arity one_shots) else
               ATop (GHC.List.take (Id.idArity v) one_shots)
           | env, CoreSyn.Lam x e =>
               if Var.isId x : bool then arityLam x (arityType env e) else
               arityType env e
           | env, CoreSyn.App fun_ (CoreSyn.Type_ _) => arityType env fun_
           | env, CoreSyn.App fun_ arg =>
               arityApp (arityType env fun_) (ae_cheap_fn env arg None)
           | env, CoreSyn.Case scrut _ _ alts =>
               let alts_type :=
                 Data.Foldable.foldr1 andArityType (let cont_16__ arg_17__ :=
                                                      let 'pair (pair _ _) rhs := arg_17__ in
                                                      cons (arityType env rhs) nil in
                                                    Coq.Lists.List.flat_map cont_16__ alts) in
               if orb (CoreUtils.exprIsBottom scrut) (Data.Foldable.null alts) : bool
               then ABot #0 else
               match alts_type with
               | ABot n => if n GHC.Base.> #0 : bool then ATop nil else ABot #0
               | ATop as_ =>
                   if andb (negb (ae_ped_bot env)) (ae_cheap_fn env scrut None) : bool
                   then ATop as_ else
                   if CoreUtils.exprOkForSpeculation scrut : bool then ATop as_ else
                   ATop (GHC.List.takeWhile BasicTypes.isOneShotInfo as_)
               end
           | env, CoreSyn.Let b e =>
               let is_cheap := fun '(pair b e) => ae_cheap_fn env e (Some (tt)) in
               let cheap_bind :=
                 fun arg_30__ =>
                   match arg_30__ with
                   | CoreSyn.NonRec b e => is_cheap (pair b e)
                   | CoreSyn.Rec prs => Data.Foldable.all is_cheap prs
                   end in
               floatIn (cheap_bind b) (arityType env e)
           | env, CoreSyn.Tick t e =>
               if negb (CoreSyn.tickishIsCode t) : bool then arityType env e else
               vanillaArityType
           | _, _ => vanillaArityType
           end.

Definition exprBotStrictness_maybe
   : CoreSyn.CoreExpr -> option (BasicTypes.Arity * Demand.StrictSig)%type :=
  fun e =>
    let sig :=
      fun ar =>
        Demand.mkClosedStrictSig (GHC.List.replicate ar Demand.topDmd) Demand.exnRes in
    let env := AE (fun arg_1__ arg_2__ => false) true in
    match getBotArity (arityType env e) with
    | None => None
    | Some ar => Some (pair ar (sig ar))
    end.

Definition exprEtaExpandArity
   : DynFlags.DynFlags -> CoreSyn.CoreExpr -> BasicTypes.Arity :=
  fun dflags e =>
    let env :=
      AE (mk_cheap_fn dflags CoreUtils.isCheapApp) (DynFlags.gopt
          DynFlags.Opt_PedanticBottoms dflags) in
    match (arityType env e) with
    | ATop oss => Data.Foldable.length oss
    | ABot n => n
    end.

Definition findRhsArity
   : DynFlags.DynFlags ->
     Var.Id ->
     CoreSyn.CoreExpr -> BasicTypes.Arity -> (BasicTypes.Arity * bool)%type :=
  fun dflags bndr rhs old_arity =>
    let init_cheap_app : CoreUtils.CheapAppFun :=
      fun fn n_val_args =>
        if fn GHC.Base.== bndr : bool then true else
        CoreUtils.isCheapApp fn n_val_args in
    let fix has_lam arg_2__
              := match arg_2__ with
                 | CoreSyn.Tick _ e => has_lam e
                 | CoreSyn.Lam b e => orb (Var.isId b) (has_lam e)
                 | _ => false
                 end in
    let is_lam := has_lam rhs in
    let get_arity : CoreUtils.CheapAppFun -> (BasicTypes.Arity * bool)%type :=
      fun cheap_app =>
        let env :=
          AE (mk_cheap_fn dflags cheap_app) (DynFlags.gopt DynFlags.Opt_PedanticBottoms
              dflags) in
        let scrut_8__ := (arityType env rhs) in
        let j_10__ :=
          match scrut_8__ with
          | ATop _ => pair #0 false
          | _ => GHC.Err.patternFailure
          end in
        match scrut_8__ with
        | ABot n => pair n true
        | ATop (cons os oss) =>
            if orb (BasicTypes.isOneShotInfo os) is_lam : bool
            then pair (#1 GHC.Num.+ Data.Foldable.length oss) false else
            j_10__
        | _ => j_10__
        end in
    let go : (BasicTypes.Arity * bool)%type -> (BasicTypes.Arity * bool)%type :=
      fix go arg_15__
            := let '(pair cur_arity _ as cur_info) := arg_15__ in
               let cheap_app : CoreUtils.CheapAppFun :=
                 fun fn n_val_args =>
                   if fn GHC.Base.== bndr : bool then n_val_args GHC.Base.< cur_arity else
                   CoreUtils.isCheapApp fn n_val_args in
               let '(pair new_arity _ as new_info) := get_arity cheap_app in
               if cur_arity GHC.Base.<= old_arity : bool then cur_info else
               if new_arity GHC.Base.== cur_arity : bool then cur_info else
               go new_info in
    go (get_arity init_cheap_app).

(* External variables:
     None Some andb bool cons false list negb nil op_zt__ option orb pair true tt
     unit BasicTypes.Arity BasicTypes.JoinArity BasicTypes.OneShotInfo
     BasicTypes.bestOneShot BasicTypes.isOneShotInfo Coercion.coercionKind
     Coercion.instNewTyCon_maybe Coercion.isReflCo Coercion.mkSymCo
     Coercion.mkTransCo Coercion.topNormaliseNewType_maybe Coq.Init.Datatypes.app
     Coq.Lists.List.flat_map CoreFVs.exprFreeVars CoreSubst.Subst
     CoreSubst.extendSubstWithVar CoreSubst.lookupIdSubst CoreSubst.mkEmptySubst
     CoreSubst.substBindSC CoreSubst.substBndr CoreSubst.substBndrs CoreSubst.substCo
     CoreSubst.substExpr CoreSubst.substTickish CoreSubst.substTy CoreSyn.App
     CoreSyn.BuiltinRule CoreSyn.Case CoreSyn.Cast CoreSyn.CoreBndr CoreSyn.CoreExpr
     CoreSyn.CoreRule CoreSyn.Lam CoreSyn.Let CoreSyn.NonRec CoreSyn.Rec CoreSyn.Rule
     CoreSyn.Tick CoreSyn.Type_ CoreSyn.Var CoreSyn.applyTypeToArg
     CoreSyn.collectArgs CoreSyn.tickishFloatable CoreSyn.tickishIsCode
     CoreSyn.varToCoreExpr CoreSyn.varsToCoreExprs CoreUtils.CheapAppFun
     CoreUtils.exprIsBottom CoreUtils.exprIsCheapX CoreUtils.exprIsTrivial
     CoreUtils.exprOkForSpeculation CoreUtils.isCheapApp CoreUtils.isJoinBind
     CoreUtils.mkTick CoreUtils.stripTicksTop Data.Foldable.all Data.Foldable.foldl
     Data.Foldable.foldr Data.Foldable.foldr1 Data.Foldable.length Data.Foldable.null
     Datatypes.id Demand.StrictSig Demand.exnRes Demand.isBotRes Demand.isTopSig
     Demand.mkClosedStrictSig Demand.splitStrictSig Demand.topDmd DynFlags.DynFlags
     DynFlags.Opt_DictsCheap DynFlags.Opt_PedanticBottoms DynFlags.gopt
     FastString.fsLit GHC.Base.map GHC.Base.mappend GHC.Base.max GHC.Base.min
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zl__ GHC.Base.op_zlze__
     GHC.Err.error GHC.Err.patternFailure GHC.List.replicate GHC.List.reverse
     GHC.List.take GHC.List.takeWhile GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zm__
     GHC.Num.op_zp__ Id.idArity Id.idStateHackOneShotInfo Id.idStrictness Id.isJoinId
     Id.mkSysLocalOrCoVar Id.typeOneShot Outputable.sep Pair.pSnd Panic.noString
     Panic.panicStr Panic.someSDoc Panic.warnPprTrace TyCoRep.extendTCvInScope
     TyCoRep.getTCvInScope TyCoRep.mkEmptyTCvSubst TyCoRep.substTy
     TyCoRep.substTyVarBndr TyCon.checkRecTc TyCon.initRecTc Type.isDictLikeTy
     Type.isTypeLevPoly Type.splitForAllTy_maybe Type.splitFunTy_maybe
     Type.splitTyConApp_maybe Unique.mkBuiltinUnique Var.Id Var.Var Var.isId
     Var.isTyVar VarEnv.InScopeSet VarEnv.mkInScopeSet VarEnv.uniqAway
*)
