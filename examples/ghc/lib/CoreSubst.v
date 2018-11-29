(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

(* Require Panic.*)
Require Import Id.
Require Core.
Import Core.ManualNotations.



(* Converted imports: *)

Require Core.
Require CoreFVs.
Require CoreUtils.
Require Data.Foldable.
Require Data.Traversable.
Require Data.Tuple.
Require Datatypes.
Require Import GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Name.
Require Panic.
Require UniqSupply.
Require Unique.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition IdSubstEnv :=
  (Core.IdEnv Core.CoreExpr)%type.

Inductive Subst : Type
  := Mk_Subst : Core.InScopeSet -> IdSubstEnv -> unit -> unit -> Subst.

(* Midamble *)

Instance Default_Subst : GHC.Err.Default Subst :=
  GHC.Err.Build_Default _ (Mk_Subst GHC.Err.default GHC.Err.default tt tt).

Definition mkOpenSubst
   : Core.InScopeSet -> (list (Core.Var * Core.CoreArg) -> Subst) :=
  fun in_scope pairs =>
    Mk_Subst in_scope (Core.mkVarEnv (Coq.Lists.List.flat_map (fun arg_1__ => let 'pair id e := arg_1__ in
                                          if Core.isId id then cons (pair id e) nil else
                                          nil) pairs)) tt tt. 


(* Converted value declarations: *)

Definition zapSubstEnv : Subst -> Subst :=
  fun '(Mk_Subst in_scope _ _ _) => Mk_Subst in_scope Core.emptyVarEnv tt tt.

Definition substTyVarBndr : Subst -> Core.Var -> Subst * Core.Var :=
  fun s v => pair s v.

Definition substInScope : Subst -> Core.InScopeSet :=
  fun '(Mk_Subst in_scope _ _ _) => in_scope.

Definition substIdType : Subst -> Core.Var -> Core.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_Subst _ _ tv_env cv_env as subst), id =>
        let old_ty := tt in if orb (andb true true) true : bool then id else id
    end.

Definition substIdInfo
   : Subst -> Core.Var -> Core.IdInfo -> option Core.IdInfo :=
  fun subst new_id info =>
    let old_unf := Core.unfoldingInfo info in
    let old_rules := Core.ruleInfo info in
    let nothing_to_do := andb true (negb (false)) in
    if nothing_to_do : bool then None else
    Some (Core.setRuleInfo info old_rules).

Definition substIdBndr
   : String -> Subst -> Subst -> Core.Var -> (Subst * Core.Var)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _doc, rec_subst, (Mk_Subst in_scope env tvs cvs as subst), old_id =>
        let old_ty := tt in
        let no_type_change := orb (andb true true) true in
        let id1 := Core.uniqAway in_scope old_id in
        let id2 := if no_type_change : bool then id1 else id1 in
        let mb_new_info := substIdInfo rec_subst id2 ((@Core.idInfo tt id2)) in
        let new_id := maybeModifyIdInfo mb_new_info id2 in
        let no_change := id1 == old_id in
        let new_env :=
          if no_change : bool then Core.delVarEnv env old_id else
          Core.extendVarEnv env old_id (Core.Mk_Var new_id) in
        pair (Mk_Subst (Core.extendInScopeSet in_scope new_id) new_env tvs cvs) new_id
    end.

Definition substRecBndrs
   : Subst -> list Core.Var -> (Subst * list Core.Var)%type :=
  fun subst bndrs =>
    let 'pair new_subst new_bndrs := Data.Traversable.mapAccumL (substIdBndr
                                                                 (Datatypes.id (GHC.Base.hs_string__ "rec-bndr"))
                                                                 (GHC.Err.error Panic.someSDoc)) subst bndrs in
    pair new_subst new_bndrs.

Definition substBndr : Subst -> Core.Var -> (Subst * Core.Var)%type :=
  fun subst bndr =>
    if Core.isTyVar bndr : bool then pair subst bndr else
    if Core.isCoVar bndr : bool then pair subst bndr else
    substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr.

Definition substBndrs
   : Subst -> list Core.Var -> (Subst * list Core.Var)%type :=
  fun subst bndrs => Data.Traversable.mapAccumL substBndr subst bndrs.

Definition setInScope : Subst -> Core.InScopeSet -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst _ ids tvs cvs, in_scope => Mk_Subst in_scope ids tvs cvs
    end.

Definition mkSubst : Core.InScopeSet -> unit -> unit -> IdSubstEnv -> Subst :=
  fun in_scope tvs cvs ids => Mk_Subst in_scope ids tvs cvs.

Definition mkEmptySubst : Core.InScopeSet -> Subst :=
  fun in_scope => Mk_Subst in_scope Core.emptyVarEnv tt tt.

Definition lookupIdSubst : String -> Subst -> Core.Var -> Core.CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | doc, Mk_Subst in_scope ids _ _, v =>
        if negb (Core.isLocalId v) : bool then Core.Mk_Var v else
        match Core.lookupVarEnv ids v with
        | Some e => e
        | _ =>
            match Core.lookupInScope in_scope v with
            | Some v' => Core.Mk_Var v'
            | _ =>
                Panic.warnPprTrace (true) (GHC.Base.hs_string__
                                    "ghc/compiler/coreSyn/CoreSubst.hs") #262 (Panic.someSDoc) (Core.Mk_Var v)
            end
        end
    end.

Definition substDVarSet : Subst -> Core.DVarSet -> Core.DVarSet :=
  fun subst fvs =>
    let subst_fv :=
      fun subst fv acc =>
        if Core.isId fv : bool
        then CoreFVs.expr_fvs (lookupIdSubst (Datatypes.id (GHC.Base.hs_string__
                                                            "substDVarSet")) subst fv) Core.isLocalVar Core.emptyVarSet
             acc else
        id acc in
    Core.mkDVarSet (Data.Tuple.fst (Data.Foldable.foldr (subst_fv subst) (pair nil
                                                                               Core.emptyVarSet) (Core.dVarSetElems
                                                         fvs))).

Definition substIdOcc : Subst -> Core.Var -> Core.Var :=
  fun subst v =>
    match lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "substIdOcc")) subst
            v with
    | Core.Mk_Var v' => v'
    | other => Panic.panicStr (GHC.Base.hs_string__ "substIdOcc") (Panic.someSDoc)
    end.

Definition substTickish
   : Subst -> Core.Tickish Core.Var -> Core.Tickish Core.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | subst, Core.Breakpoint n ids =>
        let do_one :=
          CoreUtils.getIdFromTrivialExpr ∘
          lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "subst_tickish")) subst in
        Core.Breakpoint n (map do_one ids)
    | _subst, other => other
    end.

Definition substBind : Subst -> Core.CoreBind -> (Subst * Core.CoreBind)%type :=
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
                        | Core.Mk_Var v => lookupIdSubst (Panic.someSDoc) subst v
                        | Core.Type_ ty => Core.Type_ (tt)
                        | Core.Coercion co => Core.Coercion (tt)
                        | Core.Lit lit => Core.Lit lit
                        | Core.App fun_ arg => Core.App (go fun_) (go arg)
                        | Core.Tick tickish e => CoreUtils.mkTick (substTickish subst tickish) (go e)
                        | Core.Cast e co => Core.Cast (go e) (tt)
                        | Core.Lam bndr body =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Core.Lam bndr' (subst_expr doc subst' body)
                        | Core.Let bind body =>
                            let 'pair subst' bind' := substBind subst bind in
                            Core.Let bind' (subst_expr doc subst' body)
                        | Core.Case scrut bndr ty alts =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Core.Case (go scrut) bndr' (tt) (map (go_alt subst') alts)
                        end in
           go expr with substBind arg_0__ arg_1__
                          := match arg_0__, arg_1__ with
                             | subst, Core.NonRec bndr rhs =>
                                 let 'pair subst' bndr' := substBndr subst bndr in
                                 pair subst' (Core.NonRec bndr' (subst_expr (Datatypes.id (GHC.Base.hs_string__
                                                                                           "substBind")) subst rhs))
                             | subst, Core.Rec pairs =>
                                 let 'pair bndrs rhss := GHC.List.unzip pairs in
                                 let 'pair subst' bndrs' := substRecBndrs subst bndrs in
                                 let rhss' :=
                                   map (fun ps =>
                                          subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBind")) subst' (snd ps))
                                       pairs in
                                 pair subst' (Core.Rec (GHC.List.zip bndrs' rhss'))
                             end for substBind.

Definition subst_expr : String -> Subst -> Core.CoreExpr -> Core.CoreExpr :=
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
                        | Core.Mk_Var v => lookupIdSubst (Panic.someSDoc) subst v
                        | Core.Type_ ty => Core.Type_ (tt)
                        | Core.Coercion co => Core.Coercion (tt)
                        | Core.Lit lit => Core.Lit lit
                        | Core.App fun_ arg => Core.App (go fun_) (go arg)
                        | Core.Tick tickish e => CoreUtils.mkTick (substTickish subst tickish) (go e)
                        | Core.Cast e co => Core.Cast (go e) (tt)
                        | Core.Lam bndr body =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Core.Lam bndr' (subst_expr doc subst' body)
                        | Core.Let bind body =>
                            let 'pair subst' bind' := substBind subst bind in
                            Core.Let bind' (subst_expr doc subst' body)
                        | Core.Case scrut bndr ty alts =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Core.Case (go scrut) bndr' (tt) (map (go_alt subst') alts)
                        end in
           go expr with substBind arg_0__ arg_1__
                          := match arg_0__, arg_1__ with
                             | subst, Core.NonRec bndr rhs =>
                                 let 'pair subst' bndr' := substBndr subst bndr in
                                 pair subst' (Core.NonRec bndr' (subst_expr (Datatypes.id (GHC.Base.hs_string__
                                                                                           "substBind")) subst rhs))
                             | subst, Core.Rec pairs =>
                                 let 'pair bndrs rhss := GHC.List.unzip pairs in
                                 let 'pair subst' bndrs' := substRecBndrs subst bndrs in
                                 let rhss' :=
                                   map (fun ps =>
                                          subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBind")) subst' (snd ps))
                                       pairs in
                                 pair subst' (Core.Rec (GHC.List.zip bndrs' rhss'))
                             end for subst_expr.

Definition substExpr : String -> Subst -> Core.CoreExpr -> Core.CoreExpr :=
  fun doc subst orig_expr => subst_expr doc subst orig_expr.

Definition substRule
   : Subst -> (Name.Name -> Name.Name) -> Core.CoreRule -> Core.CoreRule :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, _, (Core.BuiltinRule _ _ _ _ as rule) => rule
    | subst
    , subst_ru_fn
    , (Core.Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
        let 'pair subst' bndrs' := substBndrs subst bndrs in
        let doc :=
          mappend (Datatypes.id (GHC.Base.hs_string__ "subst-rule")) Panic.someSDoc in
        match rule with
        | Core.Rule ru_name_5__ ru_act_6__ ru_fn_7__ ru_rough_8__ ru_bndrs_9__
        ru_args_10__ ru_rhs_11__ ru_auto_12__ ru_origin_13__ ru_orphan_14__
        ru_local_15__ =>
            Core.Rule ru_name_5__ ru_act_6__ (if is_local : bool
                       then subst_ru_fn fn_name
                       else fn_name) ru_rough_8__ bndrs' (map (substExpr doc subst') args) (substExpr
                       (Datatypes.id (GHC.Base.hs_string__ "foo")) subst' rhs) ru_auto_12__
                      ru_origin_13__ ru_orphan_14__ ru_local_15__
        | Core.BuiltinRule _ _ _ _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        end
    end.

Definition substRulesForImportedIds
   : Subst -> list Core.CoreRule -> list Core.CoreRule :=
  fun subst rules =>
    let not_needed :=
      fun name =>
        Panic.panicStr (GHC.Base.hs_string__ "substRulesForImportedIds")
        (Panic.someSDoc) in
    map (substRule subst not_needed) rules.

Definition isInScope : Core.Var -> Subst -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, Mk_Subst in_scope _ _ _ => Core.elemInScopeSet v in_scope
    end.

Definition isEmptySubst : Subst -> bool :=
  fun '(Mk_Subst _ id_env tv_env cv_env) =>
    andb (Core.isEmptyVarEnv id_env) (andb true true).

Definition substBindSC
   : Subst -> Core.CoreBind -> (Subst * Core.CoreBind)%type :=
  fun subst bind =>
    if negb (isEmptySubst subst) : bool then substBind subst bind else
    match bind with
    | Core.NonRec bndr rhs =>
        let 'pair subst' bndr' := substBndr subst bndr in
        pair subst' (Core.NonRec bndr' rhs)
    | Core.Rec pairs =>
        let 'pair bndrs rhss := GHC.List.unzip pairs in
        let 'pair subst' bndrs' := substRecBndrs subst bndrs in
        let rhss' :=
          if isEmptySubst subst' : bool then rhss else
          map (subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBindSC")) subst')
          rhss in
        pair subst' (Core.Rec (GHC.List.zip bndrs' rhss'))
    end.

Definition substExprSC : String -> Subst -> Core.CoreExpr -> Core.CoreExpr :=
  fun doc subst orig_expr =>
    if isEmptySubst subst : bool then orig_expr else
    subst_expr doc subst orig_expr.

Definition extendInScopeList : Subst -> list Core.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (Core.extendInScopeSetList in_scope vs) (Core.delVarEnvList ids vs)
        (tt) (tt)
    end.

Definition extendInScopeIds : Subst -> list Core.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (Core.extendInScopeSetList in_scope vs) (Core.delVarEnvList ids vs) tvs
        cvs
    end.

Definition extendInScope : Subst -> Core.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, v =>
        Mk_Subst (Core.extendInScopeSet in_scope v) (Core.delVarEnv ids v) (tt) (tt)
    end.

Definition extendIdSubstList
   : Subst -> list (Core.Var * Core.CoreExpr)%type -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, prs =>
        Mk_Subst in_scope (Core.extendVarEnvList ids prs) tvs cvs
    end.

Definition extendIdSubst : Subst -> Core.Var -> Core.CoreExpr -> Subst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_Subst in_scope ids tvs cvs, v, r =>
        Mk_Subst in_scope (Core.extendVarEnv ids v r) tvs cvs
    end.

Definition extendSubst : Subst -> Core.Var -> Core.CoreArg -> Subst :=
  fun subst var arg =>
    match arg with
    | Core.Type_ ty => subst
    | Core.Coercion co => subst
    | _ => extendIdSubst subst var arg
    end.

Definition extendSubstList
   : Subst -> list (Core.Var * Core.CoreArg)%type -> Subst :=
  fix extendSubstList arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | subst, nil => subst
           | subst, cons (pair var rhs) prs =>
               extendSubstList (extendSubst subst var rhs) prs
           end.

Definition extendSubstWithVar : Subst -> Core.Var -> Core.Var -> Subst :=
  fun subst v1 v2 =>
    if Core.isTyVar v1 : bool then subst else
    if Core.isCoVar v1 : bool then subst else
    extendIdSubst subst v1 (Core.Mk_Var v2).

Definition emptySubst : Subst :=
  Mk_Subst Core.emptyInScopeSet Core.emptyVarEnv tt tt.

Definition delBndrs : Subst -> list Core.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst in_scope (Core.delVarEnvList ids vs) (tt) (tt)
    end.

Definition delBndr : Subst -> Core.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, v =>
        if Core.isCoVar v : bool then Mk_Subst in_scope ids tvs (cvs) else
        if Core.isTyVar v : bool then Mk_Subst in_scope ids (tvs) cvs else
        Mk_Subst in_scope (Core.delVarEnv ids v) tvs cvs
    end.

Definition deShadowBinds : Core.CoreProgram -> Core.CoreProgram :=
  fun binds =>
    Data.Tuple.snd (Data.Traversable.mapAccumL substBind emptySubst binds).

Definition clone_id
   : Subst ->
     Subst -> (Core.Var * Unique.Unique)%type -> (Subst * Core.Var)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | rec_subst, (Mk_Subst in_scope idvs tvs cvs as subst), pair old_id uniq =>
        let id1 := Core.setVarUnique old_id uniq in
        let id2 := substIdType subst id1 in
        let new_id :=
          maybeModifyIdInfo (substIdInfo rec_subst id2 ((@Core.idInfo tt old_id))) id2 in
        let 'pair new_idvs new_cvs := (if Core.isCoVar old_id : bool
                                       then pair idvs cvs else
                                       pair (Core.extendVarEnv idvs old_id (Core.Mk_Var new_id)) cvs) in
        pair (Mk_Subst (Core.extendInScopeSet in_scope new_id) new_idvs tvs new_cvs)
             new_id
    end.

Definition cloneRecIdBndrs
   : Subst ->
     UniqSupply.UniqSupply -> list Core.Var -> (Subst * list Core.Var)%type :=
  fun subst us ids =>
    let 'pair subst' ids' := Data.Traversable.mapAccumL (clone_id (GHC.Err.error
                                                                   Panic.someSDoc)) subst (GHC.List.zip ids
                                                                                                        (UniqSupply.uniqsFromSupply
                                                                                                         us)) in
    pair subst' ids'.

Definition cloneIdBndrs
   : Subst ->
     UniqSupply.UniqSupply -> list Core.Var -> (Subst * list Core.Var)%type :=
  fun subst us ids =>
    Data.Traversable.mapAccumL (clone_id subst) subst (GHC.List.zip ids
                                                                    (UniqSupply.uniqsFromSupply us)).

Definition cloneIdBndr
   : Subst -> UniqSupply.UniqSupply -> Core.Var -> (Subst * Core.Var)%type :=
  fun subst us old_id =>
    clone_id subst subst (pair old_id (UniqSupply.uniqFromSupply us)).

Definition cloneBndr
   : Subst -> Unique.Unique -> Core.Var -> (Subst * Core.Var)%type :=
  fun subst uniq v =>
    if Core.isTyVar v : bool then pair subst v else
    clone_id subst subst (pair v uniq).

Definition cloneBndrs
   : Subst ->
     UniqSupply.UniqSupply -> list Core.Var -> (Subst * list Core.Var)%type :=
  fun subst us vs =>
    Data.Traversable.mapAccumL (fun arg_0__ arg_1__ =>
                                  match arg_0__, arg_1__ with
                                  | subst, pair v u => cloneBndr subst u v
                                  end) subst (GHC.List.zip vs (UniqSupply.uniqsFromSupply us)).

Definition addInScopeSet : Subst -> Core.VarSet -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (Core.extendInScopeSetSet in_scope vs) ids tvs cvs
    end.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreSubst.Outputable__Subst' *)

(* External variables:
     None Some String andb bool cons false id list map mappend maybeModifyIdInfo negb
     nil op_z2218U__ op_zeze__ op_zt__ option orb pair snd true tt unit Core.App
     Core.Breakpoint Core.BuiltinRule Core.Case Core.Cast Core.Coercion Core.CoreArg
     Core.CoreBind Core.CoreExpr Core.CoreProgram Core.CoreRule Core.DVarSet
     Core.IdEnv Core.IdInfo Core.InScopeSet Core.Lam Core.Let Core.Lit Core.Mk_Var
     Core.NonRec Core.Rec Core.Rule Core.Tick Core.Tickish Core.Type_ Core.Var
     Core.VarSet Core.dVarSetElems Core.delVarEnv Core.delVarEnvList
     Core.elemInScopeSet Core.emptyInScopeSet Core.emptyVarEnv Core.emptyVarSet
     Core.extendInScopeSet Core.extendInScopeSetList Core.extendInScopeSetSet
     Core.extendVarEnv Core.extendVarEnvList Core.idInfo Core.isCoVar
     Core.isEmptyVarEnv Core.isId Core.isLocalId Core.isLocalVar Core.isTyVar
     Core.lookupInScope Core.lookupVarEnv Core.mkDVarSet Core.ruleInfo
     Core.setRuleInfo Core.setVarUnique Core.unfoldingInfo Core.uniqAway
     CoreFVs.expr_fvs CoreUtils.getIdFromTrivialExpr CoreUtils.mkTick
     Data.Foldable.foldr Data.Traversable.mapAccumL Data.Tuple.fst Data.Tuple.snd
     Datatypes.id GHC.Err.error GHC.List.unzip GHC.List.zip GHC.Num.fromInteger
     Name.Name Panic.panicStr Panic.someSDoc Panic.warnPprTrace UniqSupply.UniqSupply
     UniqSupply.uniqFromSupply UniqSupply.uniqsFromSupply Unique.Unique
*)
