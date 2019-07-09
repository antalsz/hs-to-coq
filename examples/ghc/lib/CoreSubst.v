(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require AxiomatizedTypes.
Require Coq.Lists.List.
Require Import Core.
Require CoreFVs.
Require CoreUtils.
Require Data.Foldable.
Require Import Data.Traversable.
Require Data.Tuple.
Require Datatypes.
Require FV.
Require Import GHC.Base.
Require GHC.Err.
Require Import GHC.List.
Require GHC.Num.
Require Id.
Require Maybes.
Require Name.
Require Panic.
Require UniqSupply.
Require Unique.
Require Util.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition IdSubstEnv :=
  (IdEnv CoreExpr)%type.

Inductive Subst : Type
  := | Mk_Subst : InScopeSet -> IdSubstEnv -> TvSubstEnv -> CvSubstEnv -> Subst.

(* Midamble *)

Instance Default_Subst : GHC.Err.Default Subst :=
  GHC.Err.Build_Default _ (Mk_Subst GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

(* Converted value declarations: *)

Definition zapSubstEnv : Subst -> Subst :=
  fun '(Mk_Subst in_scope _ _ _) =>
    Mk_Subst in_scope emptyVarEnv emptyVarEnv emptyVarEnv.

Definition substUnfolding : Subst -> Unfolding -> Unfolding :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, unf => unf end.

Definition substTyVarBndr : Subst -> TyVar -> (Subst * TyVar)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope id_env tv_env cv_env, tv =>
        let 'pair (Mk_TCvSubst in_scope' tv_env' cv_env') tv' := substTyVarBndr
                                                                   (Mk_TCvSubst in_scope tv_env cv_env) tv in
        pair (Mk_Subst in_scope' id_env tv_env' cv_env') tv'
    end.

Axiom substSpec : Subst -> Id -> RuleInfo -> RuleInfo.

Definition substInScope : Subst -> InScopeSet :=
  fun '(Mk_Subst in_scope _ _ _) => in_scope.

Definition substIdInfo : Subst -> Id -> IdInfo -> option IdInfo :=
  fun subst new_id info =>
    let old_unf := unfoldingInfo info in
    let old_rules := ruleInfo info in
    let nothing_to_do :=
      andb (isEmptyRuleInfo old_rules) (negb (isFragileUnfolding old_unf)) in
    if nothing_to_do : bool then None else
    Some (setUnfoldingInfo (setRuleInfo info (substSpec subst new_id old_rules))
                           (substUnfolding subst old_unf)).

Definition substCoVarBndr : Subst -> TyVar -> (Subst * TyVar)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope id_env tv_env cv_env, cv =>
        let 'pair (Mk_TCvSubst in_scope' tv_env' cv_env') cv' := substCoVarBndr
                                                                   (Mk_TCvSubst in_scope tv_env cv_env) cv in
        pair (Mk_Subst in_scope' id_env tv_env' cv_env') cv'
    end.

Definition setInScope : Subst -> InScopeSet -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst _ ids tvs cvs, in_scope => Mk_Subst in_scope ids tvs cvs
    end.

Definition mkSubst
   : InScopeSet -> TvSubstEnv -> CvSubstEnv -> IdSubstEnv -> Subst :=
  fun in_scope tvs cvs ids => Mk_Subst in_scope ids tvs cvs.

Definition mkOpenSubst : InScopeSet -> list (Var * CoreArg)%type -> Subst :=
  fun in_scope pairs =>
    Mk_Subst in_scope (mkVarEnv (let cont_0__ arg_1__ :=
                                   let 'pair id e := arg_1__ in
                                   if isId id : bool then cons (pair id e) nil else
                                   nil in
                                 Coq.Lists.List.flat_map cont_0__ pairs)) (mkVarEnv (let cont_2__ arg_3__ :=
                                                                                       match arg_3__ with
                                                                                       | pair tv (Mk_Type ty) =>
                                                                                           cons (pair tv ty) nil
                                                                                       | _ => nil
                                                                                       end in
                                                                                     Coq.Lists.List.flat_map cont_2__
                                                                                                             pairs))
    (mkVarEnv (let cont_4__ arg_5__ :=
                 match arg_5__ with
                 | pair v (Mk_Coercion co) => cons (pair v co) nil
                 | _ => nil
                 end in
               Coq.Lists.List.flat_map cont_4__ pairs)).

Definition mkEmptySubst : InScopeSet -> Subst :=
  fun in_scope => Mk_Subst in_scope emptyVarEnv emptyVarEnv emptyVarEnv.

Definition lookupTCvSubst : Subst -> TyVar -> AxiomatizedTypes.Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst _ _ tvs cvs, v =>
        if isTyVar v : bool then Maybes.orElse (lookupVarEnv tvs v) (mkTyVarTy v) else
        mkCoercionTy (Maybes.orElse (lookupVarEnv cvs v) (mkCoVarCo v))
    end.

Definition lookupIdSubst : String -> Subst -> Id -> CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | doc, Mk_Subst in_scope ids _ _, v =>
        if negb (isLocalId v) : bool then Mk_Var v else
        match lookupVarEnv ids v with
        | Some e => e
        | _ =>
            match lookupInScope in_scope v with
            | Some v' => Mk_Var v'
            | _ =>
                Panic.warnPprTrace (true) (GHC.Base.hs_string__
                                    "ghc/compiler/coreSyn/CoreSubst.hs") #262 (mappend (mappend (Datatypes.id
                                                                                                 (GHC.Base.hs_string__
                                                                                                  "CoreSubst.lookupIdSubst"))
                                                                                                doc) Panic.someSDoc)
                (Mk_Var v)
            end
        end
    end.

Definition substDVarSet : Subst -> DVarSet -> DVarSet :=
  fun subst fvs =>
    let subst_fv :=
      fun subst fv acc =>
        if isId fv : bool
        then CoreFVs.expr_fvs (lookupIdSubst (Datatypes.id (GHC.Base.hs_string__
                                                            "substDVarSet")) subst fv) isLocalVar emptyVarSet acc else
        FV.emptyFV (const true) emptyVarSet acc in
    mkDVarSet (Data.Tuple.fst (Data.Foldable.foldr (subst_fv subst) (pair nil
                                                                          emptyVarSet) (dVarSetElems fvs))).

Definition substIdOcc : Subst -> Id -> Id :=
  fun subst v =>
    match lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "substIdOcc")) subst
            v with
    | Mk_Var v' => v'
    | other => Panic.panicStr (GHC.Base.hs_string__ "substIdOcc") (Panic.someSDoc)
    end.

Definition substTickish : Subst -> Tickish Id -> Tickish Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | subst, Breakpoint n ids =>
        let do_one :=
          CoreUtils.getIdFromTrivialExpr ∘
          lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "subst_tickish")) subst in
        Breakpoint n (map do_one ids)
    | _subst, other => other
    end.

Definition isInScope : Var -> Subst -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, Mk_Subst in_scope _ _ _ => elemInScopeSet v in_scope
    end.

Definition isEmptySubst : Subst -> bool :=
  fun '(Mk_Subst _ id_env tv_env cv_env) =>
    andb (isEmptyVarEnv id_env) (andb (isEmptyVarEnv tv_env) (isEmptyVarEnv
                                       cv_env)).

Definition substUnfoldingSC : Subst -> Unfolding -> Unfolding :=
  fun subst unf =>
    if isEmptySubst subst : bool then unf else
    substUnfolding subst unf.

Definition getTCvSubst : Subst -> TCvSubst :=
  fun '(Mk_Subst in_scope _ tenv cenv) => Mk_TCvSubst in_scope tenv cenv.

Definition substCo
   : Subst -> AxiomatizedTypes.Coercion -> AxiomatizedTypes.Coercion :=
  fun subst co => substCo (getTCvSubst subst) co.

Definition substTy
   : Subst -> AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_ :=
  fun subst ty => substTyUnchecked (getTCvSubst subst) ty.

Definition substIdBndr : String -> Subst -> Subst -> Id -> (Subst * Id)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _doc, rec_subst, (Mk_Subst in_scope env tvs cvs as subst), old_id =>
        let old_ty := Id.idType old_id in
        let no_type_change := orb (andb (isEmptyVarEnv tvs) (isEmptyVarEnv cvs)) true in
        let id1 := uniqAway in_scope old_id in
        let id2 :=
          if no_type_change : bool then id1 else
          Id.setIdType id1 (substTy subst old_ty) in
        let mb_new_info := substIdInfo rec_subst id2 (idInfo id2) in
        let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
        let no_change := id1 == old_id in
        let new_env :=
          if no_change : bool then delVarEnv env old_id else
          extendVarEnv env old_id (Mk_Var new_id) in
        pair (Mk_Subst (extendInScopeSet in_scope new_id) new_env tvs cvs) new_id
    end.

Definition substBndr : Subst -> Var -> (Subst * Var)%type :=
  fun subst bndr =>
    if isTyVar bndr : bool then substTyVarBndr subst bndr else
    if isCoVar bndr : bool then substCoVarBndr subst bndr else
    substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr.

Definition substBndrs : Subst -> list Var -> (Subst * list Var)%type :=
  fun subst bndrs => mapAccumL substBndr subst bndrs.

Definition substRecBndrs : Subst -> list Id -> (Subst * list Id)%type :=
  fun subst bndrs =>
    let 'pair new_subst new_bndrs := mapAccumL (substIdBndr (Datatypes.id
                                                             (GHC.Base.hs_string__ "rec-bndr")) (GHC.Err.error
                                                             Panic.someSDoc)) subst bndrs in
    pair new_subst new_bndrs.

Definition substBind : Subst -> CoreBind -> (Subst * CoreBind)%type :=
  fix subst_expr (doc : String) (subst : Subst) (expr : CoreExpr) : CoreExpr
        := let go_alt :=
             fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | subst, pair (pair con bndrs) rhs =>
                   let 'pair subst' bndrs' := substBndrs subst bndrs in
                   pair (pair con bndrs') (subst_expr doc subst' rhs)
               end in
           let fix go arg_5__
                     := match arg_5__ with
                        | Mk_Var v => lookupIdSubst (doc) subst v
                        | Mk_Type ty => Mk_Type (substTy subst ty)
                        | Mk_Coercion co => Mk_Coercion (substCo subst co)
                        | Lit lit => Lit lit
                        | App fun_ arg => App (go fun_) (go arg)
                        | Cast e co => Cast (go e) (substCo subst co)
                        | Lam bndr body =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Lam bndr' (subst_expr doc subst' body)
                        | Let bind body =>
                            let 'pair subst' bind' := substBind subst bind in
                            Let bind' (subst_expr doc subst' body)
                        | Case scrut bndr ty alts =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Case (go scrut) bndr' (substTy subst ty) (map (go_alt subst') alts)
                        end in
           go expr with substBind (arg_0__ : Subst) (arg_1__ : CoreBind) : (Subst *
                                                                            CoreBind)%type
                          := match arg_0__, arg_1__ with
                             | subst, NonRec bndr rhs =>
                                 let 'pair subst' bndr' := substBndr subst bndr in
                                 pair subst' (NonRec bndr' (subst_expr (Datatypes.id (GHC.Base.hs_string__
                                                                                      "substBind")) subst rhs))
                             | subst, Rec pairs =>
                                 let 'pair bndrs rhss := unzip pairs in
                                 let 'pair subst' bndrs' := substRecBndrs subst bndrs in
                                 let rhss' :=
                                   map (fun ps =>
                                          subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBind")) subst' (snd ps))
                                       pairs in
                                 pair subst' (Rec (zip bndrs' rhss'))
                             end for substBind.

Definition substIdType : Subst -> Id -> Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_Subst _ _ tv_env cv_env as subst), id =>
        let old_ty := Id.idType id in
        if orb (andb (isEmptyVarEnv tv_env) (isEmptyVarEnv cv_env)) (noFreeVarsOfType
                old_ty) : bool
        then id else
        Id.setIdType id (substTy subst old_ty)
    end.

Definition subst_expr : String -> Subst -> CoreExpr -> CoreExpr :=
  fix subst_expr (doc : String) (subst : Subst) (expr : CoreExpr) : CoreExpr
        := let go_alt :=
             fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | subst, pair (pair con bndrs) rhs =>
                   let 'pair subst' bndrs' := substBndrs subst bndrs in
                   pair (pair con bndrs') (subst_expr doc subst' rhs)
               end in
           let fix go arg_5__
                     := match arg_5__ with
                        | Mk_Var v => lookupIdSubst (doc) subst v
                        | Mk_Type ty => Mk_Type (substTy subst ty)
                        | Mk_Coercion co => Mk_Coercion (substCo subst co)
                        | Lit lit => Lit lit
                        | App fun_ arg => App (go fun_) (go arg)
                        | Cast e co => Cast (go e) (substCo subst co)
                        | Lam bndr body =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Lam bndr' (subst_expr doc subst' body)
                        | Let bind body =>
                            let 'pair subst' bind' := substBind subst bind in
                            Let bind' (subst_expr doc subst' body)
                        | Case scrut bndr ty alts =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Case (go scrut) bndr' (substTy subst ty) (map (go_alt subst') alts)
                        end in
           go expr with substBind (arg_0__ : Subst) (arg_1__ : CoreBind) : (Subst *
                                                                            CoreBind)%type
                          := match arg_0__, arg_1__ with
                             | subst, NonRec bndr rhs =>
                                 let 'pair subst' bndr' := substBndr subst bndr in
                                 pair subst' (NonRec bndr' (subst_expr (Datatypes.id (GHC.Base.hs_string__
                                                                                      "substBind")) subst rhs))
                             | subst, Rec pairs =>
                                 let 'pair bndrs rhss := unzip pairs in
                                 let 'pair subst' bndrs' := substRecBndrs subst bndrs in
                                 let rhss' :=
                                   map (fun ps =>
                                          subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBind")) subst' (snd ps))
                                       pairs in
                                 pair subst' (Rec (zip bndrs' rhss'))
                             end for subst_expr.

Definition substBindSC : Subst -> CoreBind -> (Subst * CoreBind)%type :=
  fun subst bind =>
    if negb (isEmptySubst subst) : bool then substBind subst bind else
    match bind with
    | NonRec bndr rhs =>
        let 'pair subst' bndr' := substBndr subst bndr in
        pair subst' (NonRec bndr' rhs)
    | Rec pairs =>
        let 'pair bndrs rhss := unzip pairs in
        let 'pair subst' bndrs' := substRecBndrs subst bndrs in
        let rhss' :=
          if isEmptySubst subst' : bool then rhss else
          map (subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBindSC")) subst')
          rhss in
        pair subst' (Rec (zip bndrs' rhss'))
    end.

Definition substExpr : String -> Subst -> CoreExpr -> CoreExpr :=
  fun doc subst orig_expr => subst_expr doc subst orig_expr.

Definition substRule
   : Subst -> (Name.Name -> Name.Name) -> CoreRule -> CoreRule :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, _, (BuiltinRule _ _ _ _ as rule) => rule
    | subst
    , subst_ru_fn
    , (Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
        let 'pair subst' bndrs' := substBndrs subst bndrs in
        let doc :=
          mappend (Datatypes.id (GHC.Base.hs_string__ "subst-rule")) Panic.someSDoc in
        match rule with
        | Rule ru_name_5__ ru_act_6__ ru_fn_7__ ru_rough_8__ ru_bndrs_9__ ru_args_10__
        ru_rhs_11__ ru_auto_12__ ru_origin_13__ ru_orphan_14__ ru_local_15__ =>
            Rule ru_name_5__ ru_act_6__ (if is_local : bool
                  then subst_ru_fn fn_name
                  else fn_name) ru_rough_8__ bndrs' (map (substExpr doc subst') args) (substExpr
                  (Datatypes.id (GHC.Base.hs_string__ "foo")) subst' rhs) ru_auto_12__
                 ru_origin_13__ ru_orphan_14__ ru_local_15__
        | BuiltinRule _ _ _ _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        end
    end.

Definition substRulesForImportedIds : Subst -> list CoreRule -> list CoreRule :=
  fun subst rules =>
    let not_needed :=
      fun name =>
        Panic.panicStr (GHC.Base.hs_string__ "substRulesForImportedIds")
        (Panic.someSDoc) in
    map (substRule subst not_needed) rules.

Definition substExprSC : String -> Subst -> CoreExpr -> CoreExpr :=
  fun doc subst orig_expr =>
    if isEmptySubst subst : bool then orig_expr else
    subst_expr doc subst orig_expr.

Definition extendTvSubst : Subst -> TyVar -> AxiomatizedTypes.Type_ -> Subst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_Subst in_scope ids tvs cvs, tv, ty =>
        if andb Util.debugIsOn (negb (isTyVar tv)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/coreSyn/CoreSubst.hs") #214)
        else Mk_Subst in_scope ids (extendVarEnv tvs tv ty) cvs
    end.

Definition extendTvSubstList
   : Subst -> list (TyVar * AxiomatizedTypes.Type_)%type -> Subst :=
  fun subst vrs =>
    let extend :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | subst, pair v r => extendTvSubst subst v r
        end in
    Data.Foldable.foldl' extend subst vrs.

Definition extendInScopeList : Subst -> list Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (extendInScopeSetList in_scope vs) (delVarEnvList ids vs)
        (delVarEnvList tvs vs) (delVarEnvList cvs vs)
    end.

Definition extendInScopeIds : Subst -> list Id -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (extendInScopeSetList in_scope vs) (delVarEnvList ids vs) tvs cvs
    end.

Definition extendInScope : Subst -> Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, v =>
        Mk_Subst (extendInScopeSet in_scope v) (delVarEnv ids v) (delVarEnv tvs v)
        (delVarEnv cvs v)
    end.

Definition extendIdSubstList : Subst -> list (Id * CoreExpr)%type -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, prs =>
        if andb Util.debugIsOn (negb (Data.Foldable.all (isNonCoVarId ∘ Data.Tuple.fst)
                                      prs)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/coreSyn/CoreSubst.hs") #204)
        else Mk_Subst in_scope (extendVarEnvList ids prs) tvs cvs
    end.

Definition extendIdSubst : Subst -> Id -> CoreExpr -> Subst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_Subst in_scope ids tvs cvs, v, r =>
        if andb Util.debugIsOn (negb (isNonCoVarId v)) : bool
        then (GHC.Err.error Panic.someSDoc)
        else Mk_Subst in_scope (extendVarEnv ids v r) tvs cvs
    end.

Definition extendCvSubst
   : Subst -> CoVar -> AxiomatizedTypes.Coercion -> Subst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_Subst in_scope ids tvs cvs, v, r =>
        if andb Util.debugIsOn (negb (isCoVar v)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/coreSyn/CoreSubst.hs") #228)
        else Mk_Subst in_scope ids tvs (extendVarEnv cvs v r)
    end.

Definition extendSubst : Subst -> Var -> CoreArg -> Subst :=
  fun subst var arg =>
    match arg with
    | Mk_Type ty =>
        if andb Util.debugIsOn (negb (isTyVar var)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/coreSyn/CoreSubst.hs") #237)
        else extendTvSubst subst var ty
    | Mk_Coercion co =>
        if andb Util.debugIsOn (negb (isCoVar var)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/coreSyn/CoreSubst.hs") #238)
        else extendCvSubst subst var co
    | _ =>
        if andb Util.debugIsOn (negb (isId var)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/coreSyn/CoreSubst.hs") #239)
        else extendIdSubst subst var arg
    end.

Definition extendSubstList : Subst -> list (Var * CoreArg)%type -> Subst :=
  fix extendSubstList (arg_0__ : Subst) (arg_1__ : list (Var * CoreArg)%type)
        : Subst
        := match arg_0__, arg_1__ with
           | subst, nil => subst
           | subst, cons (pair var rhs) prs =>
               extendSubstList (extendSubst subst var rhs) prs
           end.

Definition extendSubstWithVar : Subst -> Var -> Var -> Subst :=
  fun subst v1 v2 =>
    if isTyVar v1 : bool
    then if andb Util.debugIsOn (negb (isTyVar v2)) : bool
         then (Panic.assertPanic (GHC.Base.hs_string__
                                  "ghc/compiler/coreSyn/CoreSubst.hs") #243)
         else extendTvSubst subst v1 (mkTyVarTy v2) else
    if isCoVar v1 : bool
    then if andb Util.debugIsOn (negb (isCoVar v2)) : bool
         then (Panic.assertPanic (GHC.Base.hs_string__
                                  "ghc/compiler/coreSyn/CoreSubst.hs") #244)
         else extendCvSubst subst v1 (mkCoVarCo v2) else
    if andb Util.debugIsOn (negb (isId v2)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__
                             "ghc/compiler/coreSyn/CoreSubst.hs") #245)
    else extendIdSubst subst v1 (Mk_Var v2).

Definition emptySubst : Subst :=
  Mk_Subst emptyInScopeSet emptyVarEnv emptyVarEnv emptyVarEnv.

Definition delBndrs : Subst -> list Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst in_scope (delVarEnvList ids vs) (delVarEnvList tvs vs) (delVarEnvList
                                                                         cvs vs)
    end.

Definition delBndr : Subst -> Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, v =>
        if isCoVar v : bool then Mk_Subst in_scope ids tvs (delVarEnv cvs v) else
        if isTyVar v : bool then Mk_Subst in_scope ids (delVarEnv tvs v) cvs else
        Mk_Subst in_scope (delVarEnv ids v) tvs cvs
    end.

Definition deShadowBinds : CoreProgram -> CoreProgram :=
  fun binds => Data.Tuple.snd (mapAccumL substBind emptySubst binds).

Definition clone_id
   : Subst -> Subst -> (Id * Unique.Unique)%type -> (Subst * Id)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | rec_subst, (Mk_Subst in_scope idvs tvs cvs as subst), pair old_id uniq =>
        let id1 := setVarUnique old_id uniq in
        let id2 := substIdType subst id1 in
        let new_id :=
          Id.maybeModifyIdInfo (substIdInfo rec_subst id2 (idInfo old_id)) id2 in
        let 'pair new_idvs new_cvs := (if isCoVar old_id : bool
                                       then pair idvs (extendVarEnv cvs old_id (mkCoVarCo new_id)) else
                                       pair (extendVarEnv idvs old_id (Mk_Var new_id)) cvs) in
        pair (Mk_Subst (extendInScopeSet in_scope new_id) new_idvs tvs new_cvs) new_id
    end.

Definition cloneTyVarBndr
   : Subst -> TyVar -> Unique.Unique -> (Subst * TyVar)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_Subst in_scope id_env tv_env cv_env, tv, uniq =>
        let 'pair (Mk_TCvSubst in_scope' tv_env' cv_env') tv' := cloneTyVarBndr
                                                                   (Mk_TCvSubst in_scope tv_env cv_env) tv uniq in
        pair (Mk_Subst in_scope' id_env tv_env' cv_env') tv'
    end.

Definition cloneRecIdBndrs
   : Subst -> UniqSupply.UniqSupply -> list Id -> (Subst * list Id)%type :=
  fun subst us ids =>
    let 'pair subst' ids' := mapAccumL (clone_id (GHC.Err.error Panic.someSDoc))
                               subst (zip ids (UniqSupply.uniqsFromSupply us)) in
    pair subst' ids'.

Definition cloneIdBndrs
   : Subst -> UniqSupply.UniqSupply -> list Id -> (Subst * list Id)%type :=
  fun subst us ids =>
    mapAccumL (clone_id subst) subst (zip ids (UniqSupply.uniqsFromSupply us)).

Definition cloneIdBndr
   : Subst -> UniqSupply.UniqSupply -> Id -> (Subst * Id)%type :=
  fun subst us old_id =>
    clone_id subst subst (pair old_id (UniqSupply.uniqFromSupply us)).

Definition cloneBndr : Subst -> Unique.Unique -> Var -> (Subst * Var)%type :=
  fun subst uniq v =>
    if isTyVar v : bool then cloneTyVarBndr subst v uniq else
    clone_id subst subst (pair v uniq).

Definition cloneBndrs
   : Subst -> UniqSupply.UniqSupply -> list Var -> (Subst * list Var)%type :=
  fun subst us vs =>
    mapAccumL (fun arg_0__ arg_1__ =>
                 match arg_0__, arg_1__ with
                 | subst, pair v u => cloneBndr subst u v
                 end) subst (zip vs (UniqSupply.uniqsFromSupply us)).

Definition addInScopeSet : Subst -> VarSet -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (extendInScopeSetSet in_scope vs) ids tvs cvs
    end.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreSubst.Outputable__Subst' *)

(* External variables:
     App Breakpoint BuiltinRule Case Cast CoVar CoreArg CoreBind CoreExpr CoreProgram
     CoreRule CvSubstEnv DVarSet Id IdEnv IdInfo InScopeSet Lam Let Lit Mk_Coercion
     Mk_TCvSubst Mk_Type Mk_Var NonRec None Rec Rule RuleInfo Some String TCvSubst
     Tickish TvSubstEnv TyVar Unfolding Var VarSet andb bool cloneTyVarBndr cons
     const dVarSetElems delVarEnv delVarEnvList elemInScopeSet emptyInScopeSet
     emptyVarEnv emptyVarSet extendInScopeSet extendInScopeSetList
     extendInScopeSetSet extendVarEnv extendVarEnvList idInfo isCoVar isEmptyRuleInfo
     isEmptyVarEnv isFragileUnfolding isId isLocalId isLocalVar isNonCoVarId isTyVar
     list lookupInScope lookupVarEnv map mapAccumL mappend mkCoVarCo mkCoercionTy
     mkDVarSet mkTyVarTy mkVarEnv negb nil noFreeVarsOfType op_z2218U__ op_zeze__
     op_zt__ option orb pair ruleInfo setRuleInfo setUnfoldingInfo setVarUnique snd
     substCo substCoVarBndr substTyUnchecked substTyVarBndr true unfoldingInfo
     uniqAway unzip zip AxiomatizedTypes.Coercion AxiomatizedTypes.Type_
     Coq.Lists.List.flat_map CoreFVs.expr_fvs CoreUtils.getIdFromTrivialExpr
     Data.Foldable.all Data.Foldable.foldl' Data.Foldable.foldr Data.Tuple.fst
     Data.Tuple.snd Datatypes.id FV.emptyFV GHC.Err.error GHC.Num.fromInteger
     Id.idType Id.maybeModifyIdInfo Id.setIdType Maybes.orElse Name.Name
     Panic.assertPanic Panic.panicStr Panic.someSDoc Panic.warnPprTrace
     UniqSupply.UniqSupply UniqSupply.uniqFromSupply UniqSupply.uniqsFromSupply
     Unique.Unique Util.debugIsOn
*)
