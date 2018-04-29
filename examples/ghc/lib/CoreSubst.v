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

Require Combined.
Require CoreFVs.
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
Require Name.
Require Panic.
Require UniqSupply.
Require Unique.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition IdSubstEnv :=
  (Combined.IdEnv Combined.CoreExpr)%type.

Inductive Subst : Type
  := Mk_Subst : Combined.InScopeSet -> IdSubstEnv -> unit -> unit -> Subst.
(* Midamble *)

Instance Default_Subst : GHC.Err.Default Subst :=
  GHC.Err.Build_Default _ (Mk_Subst GHC.Err.default GHC.Err.default tt tt).


Parameter substBind1 :  Subst -> Combined.CoreBind -> (Subst * Combined.CoreBind)%type.
Parameter substBndrs1 : Subst -> list Combined.Var -> (Subst * list Combined.Var)%type.
Parameter substBndr1 : Subst -> Combined.Var -> (Subst * Combined.Var)%type.
Parameter substRecBndrs1 : Subst -> list Combined.Var -> (Subst * list Combined.Var)%type.
Parameter substIdBndr1
   : GHC.Base.String -> Subst -> Subst -> Combined.Var -> (Subst * Combined.Var)%type.

Parameter substIdInfo1
   : Subst -> Combined.Var -> Combined.IdInfo -> option Combined.IdInfo.


Definition mkOpenSubst
   : Combined.InScopeSet -> (list (Combined.Var * Combined.CoreArg) -> Subst) :=
  fun in_scope pairs =>
    Mk_Subst in_scope (Combined.mkVarEnv (Coq.Lists.List.flat_map (fun arg_1__ => let 'pair id e := arg_1__ in
                                          if Combined.isId id then cons (pair id e) nil else
                                          nil) pairs)) tt tt. 

(* TODO: Recursive KNOT tying!!! *)
(*
Parameter substRecBndrs : Subst -> list Combined.Var -> (Subst * list Combined.Var)%type.

(*
Definition substRecBndrs : Subst -> list Combined.Var -> (Subst * list Combined.Var)%type :=
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
     UniqSupply.UniqSupply -> list Combined.Var -> (Subst * list Combined.Var)%type.
*)
(* Converted value declarations: *)

(* Skipping instance Outputable__Subst of class Outputable *)

Definition addInScopeSet : Subst -> Combined.VarSet -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (Combined.extendInScopeSetSet in_scope vs) ids tvs cvs
    end.

Definition delBndr : Subst -> Combined.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, v =>
        Mk_Subst in_scope (Combined.delVarEnv ids v) tvs cvs
    end.

Definition delBndrs : Subst -> list Combined.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst in_scope (Combined.delVarEnvList ids vs) (tt) (tt)
    end.

Definition emptySubst : Subst :=
  Mk_Subst Combined.emptyInScopeSet Combined.emptyVarEnv tt tt.

Definition extendIdSubst
   : Subst -> Combined.Var -> Combined.CoreExpr -> Subst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Mk_Subst in_scope ids tvs cvs, v, r =>
        Mk_Subst in_scope (Combined.extendVarEnv ids v r) tvs cvs
    end.

Definition extendSubst : Subst -> Combined.Var -> Combined.CoreArg -> Subst :=
  fun subst var arg =>
    match arg with
    | Combined.Type_ ty => subst
    | Combined.Coercion co => subst
    | _ => extendIdSubst subst var arg
    end.

Definition extendSubstList
   : Subst -> list (Combined.Var * Combined.CoreArg)%type -> Subst :=
  fix extendSubstList arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | subst, nil => subst
           | subst, cons (pair var rhs) prs =>
               extendSubstList (extendSubst subst var rhs) prs
           end.

Definition extendSubstWithVar
   : Subst -> Combined.Var -> Combined.Var -> Subst :=
  fun subst v1 v2 => extendIdSubst subst v1 (Combined.Mk_Var v2).

Definition extendIdSubstList
   : Subst -> list (Combined.Var * Combined.CoreExpr)%type -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, prs =>
        Mk_Subst in_scope (Combined.extendVarEnvList ids prs) tvs cvs
    end.

Definition extendInScope : Subst -> Combined.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, v =>
        Mk_Subst (Combined.extendInScopeSet in_scope v) (Combined.delVarEnv ids v) (tt)
        (tt)
    end.

Definition extendInScopeIds : Subst -> list Combined.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (Combined.extendInScopeSetList in_scope vs) (Combined.delVarEnvList ids
                                                                                     vs) tvs cvs
    end.

Definition extendInScopeList : Subst -> list Combined.Var -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst in_scope ids tvs cvs, vs =>
        Mk_Subst (Combined.extendInScopeSetList in_scope vs) (Combined.delVarEnvList ids
                                                                                     vs) (tt) (tt)
    end.

Definition isEmptySubst : Subst -> bool :=
  fun '(Mk_Subst _ id_env tv_env cv_env) =>
    andb (Combined.isEmptyVarEnv id_env) (andb true true).

Definition isInScope : Combined.Var -> Subst -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, Mk_Subst in_scope _ _ _ => Combined.elemInScopeSet v in_scope
    end.

Definition lookupIdSubst
   : GHC.Base.String -> Subst -> Combined.Var -> Combined.CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | doc, Mk_Subst in_scope ids _ _, v =>
        if negb (Combined.isLocalId v) : bool then Combined.Mk_Var v else
        match Combined.lookupVarEnv ids v with
        | Some e => e
        | _ =>
            match Combined.lookupInScope in_scope v with
            | Some v' => Combined.Mk_Var v'
            | _ =>
                Panic.warnPprTrace (true) (GHC.Base.hs_string__
                                    "ghc/compiler/coreSyn/CoreSubst.hs") #262 (Panic.someSDoc) (Combined.Mk_Var v)
            end
        end
    end.

Definition substDVarSet : Subst -> Combined.DVarSet -> Combined.DVarSet :=
  fun subst fvs =>
    let subst_fv :=
      fun subst fv acc =>
        let j_0__ := id acc in
        CoreFVs.expr_fvs (lookupIdSubst (Datatypes.id (GHC.Base.hs_string__
                                                       "substDVarSet")) subst fv) Combined.isLocalVar
                         Combined.emptyVarSet acc in
    Combined.mkDVarSet (Data.Tuple.fst (Data.Foldable.foldr (subst_fv subst) (pair
                                                             nil Combined.emptyVarSet) (Combined.dVarSetElems fvs))).

Definition substIdOcc : Subst -> Combined.Var -> Combined.Var :=
  fun subst v =>
    match lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "substIdOcc")) subst
            v with
    | Combined.Mk_Var v' => v'
    | other =>
        Panic.panicStr (GHC.Base.hs_string__ "substIdOcc") (Panic.noString (cons
                                                                            (GHC.Base.mappend (Panic.noString v)
                                                                                              (Panic.noString other))
                                                                            (cons (Panic.noString subst) nil)))
    end.

Definition substTickish
   : Subst -> Combined.Tickish Combined.Var -> Combined.Tickish Combined.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | subst, Combined.Breakpoint n ids =>
        let do_one :=
          CoreUtils.getIdFromTrivialExpr GHC.Base.∘
          lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "subst_tickish")) subst in
        Combined.Breakpoint n (GHC.Base.map do_one ids)
    | _subst, other => other
    end.

Definition mkEmptySubst : Combined.InScopeSet -> Subst :=
  fun in_scope => Mk_Subst in_scope Combined.emptyVarEnv tt tt.

Definition mkSubst
   : Combined.InScopeSet -> unit -> unit -> IdSubstEnv -> Subst :=
  fun in_scope tvs cvs ids => Mk_Subst in_scope ids tvs cvs.

Definition setInScope : Subst -> Combined.InScopeSet -> Subst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Subst _ ids tvs cvs, in_scope => Mk_Subst in_scope ids tvs cvs
    end.

Definition substIdInfo
   : Subst -> Combined.Var -> Combined.IdInfo -> option Combined.IdInfo :=
  fun subst new_id info =>
    let old_unf := Combined.unfoldingInfo info in
    let old_rules := Combined.ruleInfo info in
    let nothing_to_do := andb true (negb (false)) in
    if nothing_to_do : bool then None else
    Some (Combined.setRuleInfo info old_rules).

Definition substIdBndr
   : GHC.Base.String ->
     Subst -> Subst -> Combined.Var -> (Subst * Combined.Var)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | _doc, rec_subst, (Mk_Subst in_scope env tvs cvs as subst), old_id =>
        let old_ty := tt in
        let no_type_change := orb (andb true true) true in
        let id1 := Combined.uniqAway in_scope old_id in
        let id2 := if no_type_change : bool then id1 else id1 in
        let mb_new_info := substIdInfo rec_subst id2 ((@Combined.idInfo tt id2)) in
        let new_id := Id.maybeModifyIdInfo mb_new_info id2 in
        let no_change := id1 GHC.Base.== old_id in
        let new_env :=
          if no_change : bool then Combined.delVarEnv env old_id else
          Combined.extendVarEnv env old_id (Combined.Mk_Var new_id) in
        pair (Mk_Subst (Combined.extendInScopeSet in_scope new_id) new_env tvs cvs)
             new_id
    end.

Definition substBndr : Subst -> Combined.Var -> (Subst * Combined.Var)%type :=
  fun subst bndr =>
    substIdBndr (Datatypes.id (GHC.Base.hs_string__ "var-bndr")) subst subst bndr.

Definition substBndrs
   : Subst -> list Combined.Var -> (Subst * list Combined.Var)%type :=
  fun subst bndrs => Data.Traversable.mapAccumL substBndr subst bndrs.

Definition substIdType : Subst -> Combined.Var -> Combined.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_Subst _ _ tv_env cv_env as subst), id =>
        let old_ty := tt in if orb (andb true true) true : bool then id else id
    end.

Definition clone_id
   : Subst ->
     Subst -> (Combined.Var * Unique.Unique)%type -> (Subst * Combined.Var)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | rec_subst, (Mk_Subst in_scope idvs tvs cvs as subst), pair old_id uniq =>
        let id1 := Combined.setVarUnique old_id uniq in
        let id2 := substIdType subst id1 in
        let new_id :=
          Id.maybeModifyIdInfo (substIdInfo rec_subst id2 ((@Combined.idInfo tt old_id)))
          id2 in
        let 'pair new_idvs new_cvs := pair (Combined.extendVarEnv idvs old_id
                                            (Combined.Mk_Var new_id)) cvs in
        pair (Mk_Subst (Combined.extendInScopeSet in_scope new_id) new_idvs tvs new_cvs)
             new_id
    end.

Definition cloneRecIdBndrs
   : Subst ->
     UniqSupply.UniqSupply ->
     list Combined.Var -> (Subst * list Combined.Var)%type :=
  fun subst us ids =>
    let 'pair subst' ids' := Data.Traversable.mapAccumL (clone_id GHC.Err.default)
                               subst (GHC.List.zip ids (UniqSupply.uniqsFromSupply us)) in
    pair subst' ids'.

Definition cloneIdBndrs
   : Subst ->
     UniqSupply.UniqSupply ->
     list Combined.Var -> (Subst * list Combined.Var)%type :=
  fun subst us ids =>
    Data.Traversable.mapAccumL (clone_id subst) subst (GHC.List.zip ids
                                                                    (UniqSupply.uniqsFromSupply us)).

Definition cloneIdBndr
   : Subst ->
     UniqSupply.UniqSupply -> Combined.Var -> (Subst * Combined.Var)%type :=
  fun subst us old_id =>
    clone_id subst subst (pair old_id (UniqSupply.uniqFromSupply us)).

Definition cloneBndr
   : Subst -> Unique.Unique -> Combined.Var -> (Subst * Combined.Var)%type :=
  fun subst uniq v => clone_id subst subst (pair v uniq).

Definition cloneBndrs
   : Subst ->
     UniqSupply.UniqSupply ->
     list Combined.Var -> (Subst * list Combined.Var)%type :=
  fun subst us vs =>
    Data.Traversable.mapAccumL (fun arg_0__ arg_1__ =>
                                  match arg_0__, arg_1__ with
                                  | subst, pair v u => cloneBndr subst u v
                                  end) subst (GHC.List.zip vs (UniqSupply.uniqsFromSupply us)).

Definition substInScope : Subst -> Combined.InScopeSet :=
  fun '(Mk_Subst in_scope _ _ _) => in_scope.

Definition substRecBndrs
   : Subst -> list Combined.Var -> (Subst * list Combined.Var)%type :=
  fun subst bndrs =>
    let 'pair new_subst new_bndrs := Data.Traversable.mapAccumL (substIdBndr
                                                                 (Datatypes.id (GHC.Base.hs_string__ "rec-bndr"))
                                                                 GHC.Err.default) subst bndrs in
    pair new_subst new_bndrs.

Definition substBind
   : Subst -> Combined.CoreBind -> (Subst * Combined.CoreBind)%type :=
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
                        | Combined.Mk_Var v => lookupIdSubst (Panic.someSDoc) subst v
                        | Combined.Type_ ty => Combined.Type_ (tt)
                        | Combined.Coercion co => Combined.Coercion (tt)
                        | Combined.Lit lit => Combined.Lit lit
                        | Combined.App fun_ arg => Combined.App (go fun_) (go arg)
                        | Combined.Tick tickish e =>
                            CoreUtils.mkTick (substTickish subst tickish) (go e)
                        | Combined.Cast e co => Combined.Cast (go e) (tt)
                        | Combined.Lam bndr body =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Combined.Lam bndr' (subst_expr doc subst' body)
                        | Combined.Let bind body =>
                            let 'pair subst' bind' := substBind subst bind in
                            Combined.Let bind' (subst_expr doc subst' body)
                        | Combined.Case scrut bndr ty alts =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Combined.Case (go scrut) bndr' (tt) (GHC.Base.map (go_alt subst') alts)
                        end in
           go expr with substBind arg_0__ arg_1__
                          := match arg_0__, arg_1__ with
                             | subst, Combined.NonRec bndr rhs =>
                                 let 'pair subst' bndr' := substBndr subst bndr in
                                 pair subst' (Combined.NonRec bndr' (subst_expr (Datatypes.id
                                                                                 (GHC.Base.hs_string__ "substBind"))
                                                                     subst rhs))
                             | subst, Combined.Rec pairs =>
                                 let 'pair bndrs rhss := GHC.List.unzip pairs in
                                 let 'pair subst' bndrs' := substRecBndrs subst bndrs in
                                 let rhss' :=
                                   GHC.Base.map (fun ps =>
                                                   subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBind")) subst'
                                                              (snd ps)) pairs in
                                 pair subst' (Combined.Rec (GHC.List.zip bndrs' rhss'))
                             end for substBind.

Definition deShadowBinds : Combined.CoreProgram -> Combined.CoreProgram :=
  fun binds =>
    Data.Tuple.snd (Data.Traversable.mapAccumL substBind emptySubst binds).

Definition subst_expr
   : GHC.Base.String -> Subst -> Combined.CoreExpr -> Combined.CoreExpr :=
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
                        | Combined.Mk_Var v => lookupIdSubst (Panic.someSDoc) subst v
                        | Combined.Type_ ty => Combined.Type_ (tt)
                        | Combined.Coercion co => Combined.Coercion (tt)
                        | Combined.Lit lit => Combined.Lit lit
                        | Combined.App fun_ arg => Combined.App (go fun_) (go arg)
                        | Combined.Tick tickish e =>
                            CoreUtils.mkTick (substTickish subst tickish) (go e)
                        | Combined.Cast e co => Combined.Cast (go e) (tt)
                        | Combined.Lam bndr body =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Combined.Lam bndr' (subst_expr doc subst' body)
                        | Combined.Let bind body =>
                            let 'pair subst' bind' := substBind subst bind in
                            Combined.Let bind' (subst_expr doc subst' body)
                        | Combined.Case scrut bndr ty alts =>
                            let 'pair subst' bndr' := substBndr subst bndr in
                            Combined.Case (go scrut) bndr' (tt) (GHC.Base.map (go_alt subst') alts)
                        end in
           go expr with substBind arg_0__ arg_1__
                          := match arg_0__, arg_1__ with
                             | subst, Combined.NonRec bndr rhs =>
                                 let 'pair subst' bndr' := substBndr subst bndr in
                                 pair subst' (Combined.NonRec bndr' (subst_expr (Datatypes.id
                                                                                 (GHC.Base.hs_string__ "substBind"))
                                                                     subst rhs))
                             | subst, Combined.Rec pairs =>
                                 let 'pair bndrs rhss := GHC.List.unzip pairs in
                                 let 'pair subst' bndrs' := substRecBndrs subst bndrs in
                                 let rhss' :=
                                   GHC.Base.map (fun ps =>
                                                   subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBind")) subst'
                                                              (snd ps)) pairs in
                                 pair subst' (Combined.Rec (GHC.List.zip bndrs' rhss'))
                             end for subst_expr.

Definition substExpr
   : GHC.Base.String -> Subst -> Combined.CoreExpr -> Combined.CoreExpr :=
  fun doc subst orig_expr => subst_expr doc subst orig_expr.

Definition substRule
   : Subst ->
     (Name.Name -> Name.Name) -> Combined.CoreRule -> Combined.CoreRule :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, _, (Combined.BuiltinRule _ _ _ _ as rule) => rule
    | subst
    , subst_ru_fn
    , (Combined.Rule _ _ fn_name _ bndrs args rhs _ _ _ is_local as rule) =>
        let 'pair subst' bndrs' := substBndrs subst bndrs in
        let doc :=
          GHC.Base.mappend (Datatypes.id (GHC.Base.hs_string__ "subst-rule"))
                           (Panic.noString fn_name) in
        match rule with
        | Combined.Rule ru_name_5__ ru_act_6__ ru_fn_7__ ru_rough_8__ ru_bndrs_9__
        ru_args_10__ ru_rhs_11__ ru_auto_12__ ru_origin_13__ ru_orphan_14__
        ru_local_15__ =>
            Combined.Rule ru_name_5__ ru_act_6__ (if is_local : bool
                           then subst_ru_fn fn_name
                           else fn_name) ru_rough_8__ bndrs' (GHC.Base.map (substExpr doc subst') args)
                          (substExpr (Datatypes.id (GHC.Base.hs_string__ "foo")) subst' rhs) ru_auto_12__
                          ru_origin_13__ ru_orphan_14__ ru_local_15__
        | Combined.BuiltinRule _ _ _ _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        end
    end.

Definition substRulesForImportedIds
   : Subst -> list Combined.CoreRule -> list Combined.CoreRule :=
  fun subst rules =>
    let not_needed :=
      fun name =>
        Panic.panicStr (GHC.Base.hs_string__ "substRulesForImportedIds") (Panic.noString
                                                                          name) in
    GHC.Base.map (substRule subst not_needed) rules.

Definition substExprSC
   : GHC.Base.String -> Subst -> Combined.CoreExpr -> Combined.CoreExpr :=
  fun doc subst orig_expr =>
    if isEmptySubst subst : bool then orig_expr else
    subst_expr doc subst orig_expr.

Definition substBindSC
   : Subst -> Combined.CoreBind -> (Subst * Combined.CoreBind)%type :=
  fun subst bind =>
    if negb (isEmptySubst subst) : bool then substBind subst bind else
    match bind with
    | Combined.NonRec bndr rhs =>
        let 'pair subst' bndr' := substBndr subst bndr in
        pair subst' (Combined.NonRec bndr' rhs)
    | Combined.Rec pairs =>
        let 'pair bndrs rhss := GHC.List.unzip pairs in
        let 'pair subst' bndrs' := substRecBndrs subst bndrs in
        let rhss' :=
          if isEmptySubst subst' : bool then rhss else
          GHC.Base.map (subst_expr (Datatypes.id (GHC.Base.hs_string__ "substBindSC"))
                        subst') rhss in
        pair subst' (Combined.Rec (GHC.List.zip bndrs' rhss'))
    end.

Definition substTyVarBndr : Subst -> Combined.Var -> Subst * Combined.Var :=
  fun s v => pair s v.

Axiom substUnfolding : forall {A : Type}, A.

Definition substUnfoldingSC
   : Subst -> Combined.Unfolding -> Combined.Unfolding :=
  fun subst unf =>
    if isEmptySubst subst : bool then unf else
    substUnfolding subst unf.

(* Translating `substUnfolding' failed: using a record pattern for the unknown
   constructor `DFunUnfolding' unsupported *)

Definition zapSubstEnv : Subst -> Subst :=
  fun '(Mk_Subst in_scope _ _ _) => Mk_Subst in_scope Combined.emptyVarEnv tt tt.

(* External variables:
     None Some andb bool cons false id list negb nil op_zt__ option orb pair snd true
     tt unit Combined.App Combined.Breakpoint Combined.BuiltinRule Combined.Case
     Combined.Cast Combined.Coercion Combined.CoreArg Combined.CoreBind
     Combined.CoreExpr Combined.CoreProgram Combined.CoreRule Combined.DVarSet
     Combined.IdEnv Combined.IdInfo Combined.InScopeSet Combined.Lam Combined.Let
     Combined.Lit Combined.Mk_Var Combined.NonRec Combined.Rec Combined.Rule
     Combined.Tick Combined.Tickish Combined.Type_ Combined.Unfolding Combined.Var
     Combined.VarSet Combined.dVarSetElems Combined.delVarEnv Combined.delVarEnvList
     Combined.elemInScopeSet Combined.emptyInScopeSet Combined.emptyVarEnv
     Combined.emptyVarSet Combined.extendInScopeSet Combined.extendInScopeSetList
     Combined.extendInScopeSetSet Combined.extendVarEnv Combined.extendVarEnvList
     Combined.idInfo Combined.isEmptyVarEnv Combined.isLocalId Combined.isLocalVar
     Combined.lookupInScope Combined.lookupVarEnv Combined.mkDVarSet
     Combined.ruleInfo Combined.setRuleInfo Combined.setVarUnique
     Combined.unfoldingInfo Combined.uniqAway CoreFVs.expr_fvs
     CoreUtils.getIdFromTrivialExpr CoreUtils.mkTick Data.Foldable.foldr
     Data.Traversable.mapAccumL Data.Tuple.fst Data.Tuple.snd Datatypes.id
     GHC.Base.String GHC.Base.map GHC.Base.mappend GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Err.default GHC.Err.error GHC.List.unzip GHC.List.zip
     GHC.Num.fromInteger Id.maybeModifyIdInfo Name.Name Panic.noString Panic.panicStr
     Panic.someSDoc Panic.warnPprTrace UniqSupply.UniqSupply
     UniqSupply.uniqFromSupply UniqSupply.uniqsFromSupply Unique.Unique
*)
