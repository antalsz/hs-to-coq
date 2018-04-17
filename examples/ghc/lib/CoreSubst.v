(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)



(* Converted imports: *)

Require CoreFVs.
Require CoreSyn.
Require CoreUtils.
Require Data.Foldable.
Require Data.Traversable.
Require Data.Tuple.
Require Datatypes.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require IdInfo.
Require Name.
Require Panic.
Require UniqSupply.
Require Unique.
Require Var.
Require VarEnv.
Require VarSet.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition IdSubstEnv :=
  (VarEnv.IdEnv CoreSyn.CoreExpr)%type.

Inductive Subst : Type
  := Mk_Subst : VarEnv.InScopeSet -> IdSubstEnv -> unit -> unit -> Subst.
(* Midamble *)

Parameter substBind1 :  Subst -> CoreSyn.CoreBind -> (Subst * CoreSyn.CoreBind)%type.
Parameter substBndrs1 : Subst -> list Var.Var -> (Subst * list Var.Var)%type.
Parameter substBndr1 : Subst -> Var.Var -> (Subst * Var.Var)%type.
Parameter substRecBndrs1 : Subst -> list Var.Id -> (Subst * list Var.Id)%type.
Parameter substIdBndr1
   : GHC.Base.String -> Subst -> Subst -> Var.Id -> (Subst * Var.Id)%type.

Parameter substIdInfo1
   : Subst -> Var.Id -> IdInfo.IdInfo -> option IdInfo.IdInfo.


Definition mkOpenSubst
   : VarEnv.InScopeSet -> (list (Var.Var * CoreSyn.CoreArg) -> Subst) :=
  fun in_scope pairs =>
    Mk_Subst in_scope (VarEnv.mkVarEnv (Coq.Lists.List.flat_map (fun arg_1__ => let 'pair id e := arg_1__ in
                                          if Var.isId id then cons (pair id e) nil else
                                          nil) pairs)) tt tt. 

(* TODO: Recursive KNOT tying!!! *)
(*
Parameter substRecBndrs : Subst -> list Var.Id -> (Subst * list Var.Id)%type.

(*
Definition substRecBndrs : Subst -> list Var.Id -> (Subst * list Var.Id)%type :=
  fun subst bndrs =>
    let 'pair new_subst new_bndrs := 
        Data.Traversable.mapAccumL (substIdBndr
                                      (Datatypes.id (GHC.Base.hs_string__ "rec-bndr"))
                                      new_subst) subst bndrs in
    pair new_subst new_bndrs.
*)

(* TODO: recursive knot *)
Parameter cloneRecIdBndrs
   : Subst ->
     UniqSupply.UniqSupply -> list Var.Id -> (Subst * list Var.Id)%type.
*)
(* Converted value declarations: *)

(* Skipping instance Outputable__Subst of class Outputable *)

Definition addInScopeSet : Subst -> VarSet.VarSet -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (VarEnv.extendInScopeSetSet in_scope vs) ids tvs cvs
    end.

Definition delBndr : Subst -> Var.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, v =>
        Mk_Subst in_scope (VarEnv.delVarEnv ids v) tvs cvs
    end.

Definition delBndrs : Subst -> list Var.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst in_scope (VarEnv.delVarEnvList ids vs) (tt) (tt)
    end.

Definition emptySubst : Subst :=
  Mk_Subst VarEnv.emptyInScopeSet VarEnv.emptyVarEnv tt tt.

Definition extendIdSubst : Subst -> Var.Id -> CoreSyn.CoreExpr -> Subst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_Subst in_scope ids tvs cvs, v, r =>
        Mk_Subst in_scope (VarEnv.extendVarEnv ids v r) tvs cvs
    end.

Definition extendSubst : Subst -> Var.Var -> CoreSyn.CoreArg -> Subst :=
  fun subst var arg =>
    match arg with
    | CoreSyn.Type_ ty => subst
    | CoreSyn.Coercion co => subst
    | _ => extendIdSubst subst var arg
    end.

Definition extendSubstList
   : Subst -> list (Var.Var * CoreSyn.CoreArg)%type -> Subst :=
  fix extendSubstList arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | subst, nil => subst
           | subst, cons (pair var rhs) prs =>
               extendSubstList (extendSubst subst var rhs) prs
           end.

Definition extendSubstWithVar : Subst -> Var.Var -> Var.Var -> Subst :=
  fun subst v1 v2 => extendIdSubst subst v1 (CoreSyn.Var v2).

Definition extendIdSubstList
   : Subst -> list (Var.Id * CoreSyn.CoreExpr)%type -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, prs =>
        Mk_Subst in_scope (VarEnv.extendVarEnvList ids prs) tvs cvs
    end.

Definition extendInScope : Subst -> Var.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, v =>
        Mk_Subst (VarEnv.extendInScopeSet in_scope v) (VarEnv.delVarEnv ids v) (tt) (tt)
    end.

Definition extendInScopeIds : Subst -> list Var.Id -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (VarEnv.extendInScopeSetList in_scope vs) (VarEnv.delVarEnvList ids vs)
        tvs cvs
    end.

Definition extendInScopeList : Subst -> list Var.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (VarEnv.extendInScopeSetList in_scope vs) (VarEnv.delVarEnvList ids vs)
        (tt) (tt)
    end.

Definition isEmptySubst : Subst -> bool :=
  fun '(Mk_Subst _ id_env tv_env cv_env) =>
    andb (VarEnv.isEmptyVarEnv id_env) (andb true true).

Definition isInScope : Var.Var -> Subst -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, Mk_Subst in_scope _ _ _ => VarEnv.elemInScopeSet v in_scope
    end.

Definition lookupIdSubst
   : GHC.Base.String -> Subst -> Var.Id -> CoreSyn.CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | doc, Mk_Subst in_scope ids _ _, v =>
        if negb (Var.isLocalId v) : bool then CoreSyn.Var v else
        match VarEnv.lookupVarEnv ids v with
        | Some e => e
        | _ =>
            match VarEnv.lookupInScope in_scope v with
            | Some v' => CoreSyn.Var v'
            | _ =>
                Panic.warnPprTrace (true) (GHC.Base.hs_string__
                                    "ghc/compiler/coreSyn/CoreSubst.hs") #262 (Panic.someSDoc) (CoreSyn.Var v)
            end
        end
    end.

Definition substDVarSet : Subst -> VarSet.DVarSet -> VarSet.DVarSet :=
  fun subst fvs =>
    let subst_fv :=
      fun subst fv acc =>
        let j_0__ := id acc in
        CoreFVs.expr_fvs (lookupIdSubst (Datatypes.id (GHC.Base.hs_string__
                                                       "substDVarSet")) subst fv) Var.isLocalVar VarSet.emptyVarSet
        acc in
    VarSet.mkDVarSet (Data.Tuple.fst (Data.Foldable.foldr (subst_fv subst) (pair nil
                                                                                 VarSet.emptyVarSet)
                                                          (VarSet.dVarSetElems fvs))).

Definition substIdOcc : Subst -> Var.Id -> Var.Id :=
  fun subst v =>
    match lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "substIdOcc")) subst
            v with
    | CoreSyn.Var v' => v'
    | other =>
        Panic.panicStr (GHC.Base.hs_string__ "substIdOcc") (Panic.noString (cons
                                                                            (GHC.Base.mappend (Panic.noString v)
                                                                                              (Panic.noString other))
                                                                            (cons (Panic.noString subst) nil)))
    end.

Definition substTickish
   : Subst -> CoreSyn.Tickish Var.Id -> CoreSyn.Tickish Var.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | subst, CoreSyn.Breakpoint n ids =>
        let do_one :=
          CoreUtils.getIdFromTrivialExpr GHC.Base.∘
          lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "subst_tickish")) subst in
        CoreSyn.Breakpoint n (GHC.Base.map do_one ids)
    | _subst, other => other
    end.

Definition mkEmptySubst : VarEnv.InScopeSet -> Subst :=
  fun in_scope => Mk_Subst in_scope VarEnv.emptyVarEnv tt tt.

Definition mkSubst : VarEnv.InScopeSet -> unit -> unit -> IdSubstEnv -> Subst :=
  fun in_scope tvs cvs ids => Mk_Subst in_scope ids tvs cvs.

Definition setInScope : Subst -> VarEnv.InScopeSet -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst _ ids tvs cvs, in_scope => Mk_Subst in_scope ids tvs cvs
    end.

Definition substIdInfo
   : Subst -> Var.Id -> IdInfo.IdInfo -> option IdInfo.IdInfo :=
  fun subst new_id info =>
    let old_unf := IdInfo.unfoldingInfo info in
    let old_rules := IdInfo.ruleInfo info in
    let nothing_to_do := andb true (negb (false)) in
    if nothing_to_do : bool then None else
    Some (IdInfo.setRuleInfo info old_rules).

Definition substIdBndr
   : GHC.Base.String -> Subst -> Subst -> Var.Id -> (Subst * Var.Id)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _doc, rec_subst, (Mk_Subst in_scope env tvs cvs as subst), old_id =>
        let old_ty := tt in
        let no_type_change := orb (andb true true) true in
        let id1 := VarEnv.uniqAway in_scope old_id in
        let id2 := if no_type_change : bool then id1 else id1 in
        let mb_new_info := substIdInfo rec_subst id2 ((@Var.idInfo tt id2)) in
        let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
        let no_change := id1 GHC.Base.== old_id in
        let new_env :=
          if no_change : bool then VarEnv.delVarEnv env old_id else
          VarEnv.extendVarEnv env old_id (CoreSyn.Var new_id) in
        pair (Mk_Subst (VarEnv.extendInScopeSet in_scope new_id) new_env tvs cvs) new_id
    end.

Definition substBndr : Subst -> Var.Var -> (Subst * Var.Var)%type :=
  fun subst bndr =>
    substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr.

Definition substBndrs : Subst -> list Var.Var -> (Subst * list Var.Var)%type :=
  fun subst bndrs => Data.Traversable.mapAccumL substBndr subst bndrs.

Definition substIdType : Subst -> Var.Id -> Var.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_Subst _ _ tv_env cv_env as subst), id =>
        let old_ty := tt in if orb (andb true true) true : bool then id else id
    end.

Definition clone_id
   : Subst -> Subst -> (Var.Id * Unique.Unique)%type -> (Subst * Var.Id)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | rec_subst, (Mk_Subst in_scope idvs tvs cvs as subst), pair old_id uniq =>
        let id1 := Var.setVarUnique old_id uniq in
        let id2 := substIdType subst id1 in
        let new_id :=
          Id.maybeModifyIdInfo (substIdInfo rec_subst id2 ((@Var.idInfo tt old_id)))
          id2 in
        let 'pair new_idvs new_cvs := pair (VarEnv.extendVarEnv idvs old_id (CoreSyn.Var
                                                                             new_id)) cvs in
        pair (Mk_Subst (VarEnv.extendInScopeSet in_scope new_id) new_idvs tvs new_cvs)
             new_id
    end.

Definition cloneRecIdBndrs
   : Subst ->
     UniqSupply.UniqSupply -> list Var.Id -> (Subst * list Var.Id)%type :=
  fun subst us ids =>
    let 'pair subst' ids' := Data.Traversable.mapAccumL (clone_id subst) subst
                               (GHC.List.zip ids (UniqSupply.uniqsFromSupply us)) in
    pair subst' ids'.

Definition cloneIdBndrs
   : Subst ->
     UniqSupply.UniqSupply -> list Var.Id -> (Subst * list Var.Id)%type :=
  fun subst us ids =>
    Data.Traversable.mapAccumL (clone_id subst) subst (GHC.List.zip ids
                                                                    (UniqSupply.uniqsFromSupply us)).

Definition cloneIdBndr
   : Subst -> UniqSupply.UniqSupply -> Var.Id -> (Subst * Var.Id)%type :=
  fun subst us old_id =>
    clone_id subst subst (pair old_id (UniqSupply.uniqFromSupply us)).

Definition cloneBndr
   : Subst -> Unique.Unique -> Var.Var -> (Subst * Var.Var)%type :=
  fun subst uniq v => clone_id subst subst (pair v uniq).

Definition cloneBndrs
   : Subst ->
     UniqSupply.UniqSupply -> list Var.Var -> (Subst * list Var.Var)%type :=
  fun subst us vs =>
    Data.Traversable.mapAccumL (fun arg_0__ arg_1__ =>
                                  match arg_0__, arg_1__ with
                                  | subst, pair v u => cloneBndr subst u v
                                  end) subst (GHC.List.zip vs (UniqSupply.uniqsFromSupply us)).

Definition substInScope : Subst -> VarEnv.InScopeSet :=
  fun '(Mk_Subst in_scope _ _ _) => in_scope.

Definition substRecBndrs : Subst -> list Var.Id -> (Subst * list Var.Id)%type :=
  fun subst bndrs =>
    let 'pair new_subst new_bndrs := Data.Traversable.mapAccumL (substIdBndr
                                                                 (Datatypes.id (GHC.Base.hs_string__ "rec-bndr")) subst)
                                       subst bndrs in
    pair new_subst new_bndrs.

Definition substBind
   : Subst -> CoreSyn.CoreBind -> (Subst * CoreSyn.CoreBind)%type :=
  fix subst_expr doc subst expr
        := let go_alt :=
             fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | subst, pair (pair con bndrs) rhs =>
                   let 'pair subst' bndrs' := substBndrs subst bndrs in
                   pair (pair con bndrs') (subst_expr doc subst' rhs)
               end in
           let fix go arg_5__
                     := match arg_5__ with
                        | CoreSyn.Var v => lookupIdSubst (Panic.someSDoc) subst v
                        | CoreSyn.Type_ ty => CoreSyn.Type_ (tt)
                        | CoreSyn.Coercion co => CoreSyn.Coercion (tt)
                        | CoreSyn.Lit lit => CoreSyn.Lit lit
                        | CoreSyn.App fun_ arg => CoreSyn.App (go fun_) (go arg)
                        | CoreSyn.Tick tickish e => CoreUtils.mkTick (substTickish subst tickish) (go e)
                        | CoreSyn.Cast e co => CoreSyn.Cast (go e) (tt)
                        | CoreSyn.Lam bndr body =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            CoreSyn.Lam bndr' (subst_expr doc subst' body)
                        | CoreSyn.Let bind body =>
                            let 'pair subst' bind' := substBind subst bind in
                            CoreSyn.Let bind' (subst_expr doc subst' body)
                        | CoreSyn.Case scrut bndr ty alts =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            CoreSyn.Case (go scrut) bndr' (tt) (GHC.Base.map (go_alt subst') alts)
                        end in
           go expr with substBind arg_0__ arg_1__
                          := match arg_0__, arg_1__ with
                             | subst, CoreSyn.NonRec bndr rhs =>
                                 let 'pair subst' bndr' := substBndr subst bndr in
                                 pair subst' (CoreSyn.NonRec bndr' (subst_expr (Datatypes.id
                                                                                (GHC.Base.hs_string__ "substBind"))
                                                                    subst rhs))
                             | subst, CoreSyn.Rec pairs =>
                                 let 'pair bndrs rhss := GHC.List.unzip pairs in
                                 let 'pair subst' bndrs' := substRecBndrs subst bndrs in
                                 let rhss' :=
                                   GHC.Base.map (fun ps =>
                                                   subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBind")) subst'
                                                              (snd ps)) pairs in
                                 pair subst' (CoreSyn.Rec (GHC.List.zip bndrs' rhss'))
                             end for substBind.

Definition deShadowBinds : CoreSyn.CoreProgram -> CoreSyn.CoreProgram :=
  fun binds =>
    Data.Tuple.snd (Data.Traversable.mapAccumL substBind emptySubst binds).

Definition subst_expr
   : GHC.Base.String -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr :=
  fix subst_expr doc subst expr
        := let go_alt :=
             fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | subst, pair (pair con bndrs) rhs =>
                   let 'pair subst' bndrs' := substBndrs subst bndrs in
                   pair (pair con bndrs') (subst_expr doc subst' rhs)
               end in
           let fix go arg_5__
                     := match arg_5__ with
                        | CoreSyn.Var v => lookupIdSubst (Panic.someSDoc) subst v
                        | CoreSyn.Type_ ty => CoreSyn.Type_ (tt)
                        | CoreSyn.Coercion co => CoreSyn.Coercion (tt)
                        | CoreSyn.Lit lit => CoreSyn.Lit lit
                        | CoreSyn.App fun_ arg => CoreSyn.App (go fun_) (go arg)
                        | CoreSyn.Tick tickish e => CoreUtils.mkTick (substTickish subst tickish) (go e)
                        | CoreSyn.Cast e co => CoreSyn.Cast (go e) (tt)
                        | CoreSyn.Lam bndr body =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            CoreSyn.Lam bndr' (subst_expr doc subst' body)
                        | CoreSyn.Let bind body =>
                            let 'pair subst' bind' := substBind subst bind in
                            CoreSyn.Let bind' (subst_expr doc subst' body)
                        | CoreSyn.Case scrut bndr ty alts =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            CoreSyn.Case (go scrut) bndr' (tt) (GHC.Base.map (go_alt subst') alts)
                        end in
           go expr with substBind arg_0__ arg_1__
                          := match arg_0__, arg_1__ with
                             | subst, CoreSyn.NonRec bndr rhs =>
                                 let 'pair subst' bndr' := substBndr subst bndr in
                                 pair subst' (CoreSyn.NonRec bndr' (subst_expr (Datatypes.id
                                                                                (GHC.Base.hs_string__ "substBind"))
                                                                    subst rhs))
                             | subst, CoreSyn.Rec pairs =>
                                 let 'pair bndrs rhss := GHC.List.unzip pairs in
                                 let 'pair subst' bndrs' := substRecBndrs subst bndrs in
                                 let rhss' :=
                                   GHC.Base.map (fun ps =>
                                                   subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBind")) subst'
                                                              (snd ps)) pairs in
                                 pair subst' (CoreSyn.Rec (GHC.List.zip bndrs' rhss'))
                             end for subst_expr.

Definition substExpr
   : GHC.Base.String -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr :=
  fun doc subst orig_expr => subst_expr doc subst orig_expr.

Definition substRule
   : Subst -> (Name.Name -> Name.Name) -> CoreSyn.CoreRule -> CoreSyn.CoreRule :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, _, (CoreSyn.BuiltinRule _ _ _ _ as rule) => rule
    | subst
    , subst_ru_fn
    , (CoreSyn.Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
        let 'pair subst' bndrs' := substBndrs subst bndrs in
        let doc :=
          GHC.Base.mappend (Datatypes.id (GHC.Base.hs_string__ "subst-rule"))
                           (Panic.noString fn_name) in
        match rule with
        | CoreSyn.Rule ru_name_5__ ru_act_6__ ru_fn_7__ ru_rough_8__ ru_bndrs_9__
        ru_args_10__ ru_rhs_11__ ru_auto_12__ ru_origin_13__ ru_orphan_14__
        ru_local_15__ =>
            CoreSyn.Rule ru_name_5__ ru_act_6__ (if is_local : bool
                          then subst_ru_fn fn_name
                          else fn_name) ru_rough_8__ bndrs' (GHC.Base.map (substExpr doc subst') args)
                         (substExpr (Datatypes.id (GHC.Base.hs_string__ "foo")) subst' rhs) ru_auto_12__
                         ru_origin_13__ ru_orphan_14__ ru_local_15__
        | CoreSyn.BuiltinRule _ _ _ _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        end
    end.

Definition substRulesForImportedIds
   : Subst -> list CoreSyn.CoreRule -> list CoreSyn.CoreRule :=
  fun subst rules =>
    let not_needed :=
      fun name =>
        Panic.panicStr (GHC.Base.hs_string__ "substRulesForImportedIds") (Panic.noString
                                                                          name) in
    GHC.Base.map (substRule subst not_needed) rules.

Definition substUnfolding : Subst -> CoreSyn.Unfolding -> CoreSyn.Unfolding :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | subst, (CoreSyn.DFunUnfolding bndrs _ args as df) =>
        let 'pair subst' bndrs' := substBndrs subst bndrs in
        let args' :=
          GHC.Base.map (substExpr (Datatypes.id (GHC.Base.hs_string__ "subst-unf:dfun"))
                        subst') args in
        match df with
        | CoreSyn.NoUnfolding =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | CoreSyn.BootUnfolding =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | CoreSyn.OtherCon _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | CoreSyn.DFunUnfolding df_bndrs_5__ df_con_6__ df_args_7__ =>
            CoreSyn.DFunUnfolding bndrs' df_con_6__ args'
        | CoreSyn.CoreUnfolding _ _ _ _ _ _ _ _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        end
    | subst, (CoreSyn.CoreUnfolding tmpl src _ _ _ _ _ _ as unf) =>
        let new_tmpl :=
          substExpr (Datatypes.id (GHC.Base.hs_string__ "subst-unf")) subst tmpl in
        if negb (CoreSyn.isStableSource src) : bool then CoreSyn.NoUnfolding else
        match unf with
        | CoreSyn.NoUnfolding =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | CoreSyn.BootUnfolding =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | CoreSyn.OtherCon _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | CoreSyn.DFunUnfolding _ _ _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | CoreSyn.CoreUnfolding uf_tmpl_16__ uf_src_17__ uf_is_top_18__ uf_is_value_19__
        uf_is_conlike_20__ uf_is_work_free_21__ uf_expandable_22__ uf_guidance_23__ =>
            CoreSyn.CoreUnfolding new_tmpl uf_src_17__ uf_is_top_18__ uf_is_value_19__
                                  uf_is_conlike_20__ uf_is_work_free_21__ uf_expandable_22__ uf_guidance_23__
        end
    | _, _ => match arg_0__, arg_1__ with | _, unf => unf end
    end.

Definition substUnfoldingSC : Subst -> CoreSyn.Unfolding -> CoreSyn.Unfolding :=
  fun subst unf =>
    if isEmptySubst subst : bool then unf else
    substUnfolding subst unf.

Definition substExprSC
   : GHC.Base.String -> Subst -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr :=
  fun doc subst orig_expr =>
    if isEmptySubst subst : bool then orig_expr else
    subst_expr doc subst orig_expr.

Definition substBindSC
   : Subst -> CoreSyn.CoreBind -> (Subst * CoreSyn.CoreBind)%type :=
  fun subst bind =>
    if negb (isEmptySubst subst) : bool then substBind subst bind else
    match bind with
    | CoreSyn.NonRec bndr rhs =>
        let 'pair subst' bndr' := substBndr subst bndr in
        pair subst' (CoreSyn.NonRec bndr' rhs)
    | CoreSyn.Rec pairs =>
        let 'pair bndrs rhss := GHC.List.unzip pairs in
        let 'pair subst' bndrs' := substRecBndrs subst bndrs in
        let rhss' :=
          if isEmptySubst subst' : bool then rhss else
          GHC.Base.map (subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBindSC"))
                        subst') rhss in
        pair subst' (CoreSyn.Rec (GHC.List.zip bndrs' rhss'))
    end.

Definition substTyVarBndr : Subst -> Var.TyVar -> Subst * Var.TyVar :=
  fun s v => pair s v.

Definition zapSubstEnv : Subst -> Subst :=
  fun '(Mk_Subst in_scope _ _ _) => Mk_Subst in_scope VarEnv.emptyVarEnv tt tt.

(* External variables:
     None Some andb bool cons false id list negb nil op_zt__ option orb pair snd true
     tt unit CoreFVs.expr_fvs CoreSyn.App CoreSyn.BootUnfolding CoreSyn.Breakpoint
     CoreSyn.BuiltinRule CoreSyn.Case CoreSyn.Cast CoreSyn.Coercion CoreSyn.CoreArg
     CoreSyn.CoreBind CoreSyn.CoreExpr CoreSyn.CoreProgram CoreSyn.CoreRule
     CoreSyn.CoreUnfolding CoreSyn.DFunUnfolding CoreSyn.Lam CoreSyn.Let CoreSyn.Lit
     CoreSyn.NoUnfolding CoreSyn.NonRec CoreSyn.OtherCon CoreSyn.Rec CoreSyn.Rule
     CoreSyn.Tick CoreSyn.Tickish CoreSyn.Type_ CoreSyn.Unfolding CoreSyn.Var
     CoreSyn.isStableSource CoreUtils.getIdFromTrivialExpr CoreUtils.mkTick
     Data.Foldable.foldr Data.Traversable.mapAccumL Data.Tuple.fst Data.Tuple.snd
     Datatypes.id GHC.Base.String GHC.Base.map GHC.Base.mappend GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Err.error GHC.List.unzip GHC.List.zip GHC.Num.fromInteger
     Id.maybeModifyIdInfo IdInfo.IdInfo IdInfo.ruleInfo IdInfo.setRuleInfo
     IdInfo.unfoldingInfo Name.Name Panic.noString Panic.panicStr Panic.someSDoc
     Panic.warnPprTrace UniqSupply.UniqSupply UniqSupply.uniqFromSupply
     UniqSupply.uniqsFromSupply Unique.Unique Var.Id Var.TyVar Var.Var Var.idInfo
     Var.isLocalId Var.isLocalVar Var.setVarUnique VarEnv.IdEnv VarEnv.InScopeSet
     VarEnv.delVarEnv VarEnv.delVarEnvList VarEnv.elemInScopeSet
     VarEnv.emptyInScopeSet VarEnv.emptyVarEnv VarEnv.extendInScopeSet
     VarEnv.extendInScopeSetList VarEnv.extendInScopeSetSet VarEnv.extendVarEnv
     VarEnv.extendVarEnvList VarEnv.isEmptyVarEnv VarEnv.lookupInScope
     VarEnv.lookupVarEnv VarEnv.uniqAway VarSet.DVarSet VarSet.VarSet
     VarSet.dVarSetElems VarSet.emptyVarSet VarSet.mkDVarSet
*)
