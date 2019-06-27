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
Require Data.Foldable.
Require Data.Tuple.
Require FV.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require Id.
Require Maybes.
Require NameSet.
Require NestedRecursionHelpers.
Require Panic.
Require UniqSet.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition FVAnn :=
  Core.DVarSet%type.

Definition CoreExprWithFVs' :=
  (Core.AnnExpr' Core.Id FVAnn)%type.

Definition CoreExprWithFVs :=
  (Core.AnnExpr Core.Id FVAnn)%type.

Definition CoreBindWithFVs :=
  (Core.AnnBind Core.Id FVAnn)%type.

Definition CoreAltWithFVs :=
  (Core.AnnAlt Core.Id FVAnn)%type.

(* Converted value declarations: *)

Definition varTypeTyCoFVs : Core.Var -> FV.FV :=
  fun var => FV.emptyFV.

Definition varTypeTyCoVars : Core.Var -> Core.TyCoVarSet :=
  fun var => FV.fvVarSet (varTypeTyCoFVs var).

Definition unionFVss : list Core.DVarSet -> Core.DVarSet :=
  Core.unionDVarSets.

Definition unionFVs : Core.DVarSet -> Core.DVarSet -> Core.DVarSet :=
  Core.unionDVarSet.

Definition tickish_fvs : Core.Tickish Core.Id -> FV.FV :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.Breakpoint _ ids => FV.mkFVs ids
    | _ => FV.emptyFV
    end.

Definition stableUnfoldingFVs : Core.Unfolding -> option FV.FV :=
  fun '(_other) => None.

Definition orphNamesOfThings {a}
   : (a -> NameSet.NameSet) -> list a -> NameSet.NameSet :=
  fun f =>
    Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ f) NameSet.emptyNameSet.

Definition noFVs : Core.VarSet :=
  Core.emptyVarSet.

Definition idUnfoldingFVs : Core.Id -> FV.FV :=
  fun id => Maybes.orElse (stableUnfoldingFVs (Id.realIdUnfolding id)) FV.emptyFV.

Definition idUnfoldingVars : Core.Id -> Core.VarSet :=
  fun id => FV.fvVarSet (idUnfoldingFVs id).

Definition idRuleFVs : Core.Id -> FV.FV :=
  fun id => FV.emptyFV.

Definition idRuleVars : Core.Id -> Core.VarSet :=
  fun id => FV.fvVarSet (idRuleFVs id).

Definition freeVarsOfAnn : FVAnn -> Core.DIdSet :=
  fun fvs => fvs.

Definition freeVarsOf : CoreExprWithFVs -> Core.DIdSet :=
  fun '(pair fvs _) => fvs.

Axiom expr_fvs : Core.CoreExpr -> FV.FV.

Definition exprsSomeFreeVars
   : FV.InterestingVarFun -> list Core.CoreExpr -> Core.VarSet :=
  fun fv_cand es => FV.fvVarSet (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs es)).

Definition exprsSomeFreeVarsDSet
   : FV.InterestingVarFun -> list Core.CoreExpr -> Core.DVarSet :=
  fun fv_cand e => FV.fvDVarSet (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs e)).

Definition exprsFreeIdsDSet : list Core.CoreExpr -> Core.DIdSet :=
  exprsSomeFreeVarsDSet Core.isLocalId.

Definition exprsSomeFreeVarsList
   : FV.InterestingVarFun -> list Core.CoreExpr -> list Core.Var :=
  fun fv_cand es =>
    FV.fvVarList (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs es)).

Definition exprsFreeIdsList : list Core.CoreExpr -> list Core.Id :=
  exprsSomeFreeVarsList Core.isLocalId.

Definition exprs_fvs : list Core.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV expr_fvs exprs.

Definition vectsFreeVars : list Core.CoreVect -> Core.VarSet :=
  let vectFreeVars :=
    fun arg_0__ =>
      match arg_0__ with
      | Core.Vect _ rhs => FV.fvVarSet (FV.filterFV Core.isLocalId (expr_fvs rhs))
      | Core.NoVect _ => noFVs
      | Core.VectType _ _ _ => noFVs
      | Core.VectClass _ => noFVs
      | Core.VectInst _ => noFVs
      end in
  Core.mapUnionVarSet vectFreeVars.

Definition exprSomeFreeVarsList
   : FV.InterestingVarFun -> Core.CoreExpr -> list Core.Var :=
  fun fv_cand e => FV.fvVarList (FV.filterFV fv_cand (expr_fvs e)).

Definition exprSomeFreeVarsDSet
   : FV.InterestingVarFun -> Core.CoreExpr -> Core.DVarSet :=
  fun fv_cand e => FV.fvDVarSet (FV.filterFV fv_cand (expr_fvs e)).

Definition exprSomeFreeVars
   : FV.InterestingVarFun -> Core.CoreExpr -> Core.VarSet :=
  fun fv_cand e => FV.fvVarSet (FV.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIdsList : Core.CoreExpr -> list Core.Id :=
  exprSomeFreeVarsList Core.isLocalId.

Definition exprFreeIdsDSet : Core.CoreExpr -> Core.DIdSet :=
  exprSomeFreeVarsDSet Core.isLocalId.

Definition exprFreeIds : Core.CoreExpr -> Core.IdSet :=
  exprSomeFreeVars Core.isLocalId.

Definition exprFVs : Core.CoreExpr -> FV.FV :=
  FV.filterFV Core.isLocalVar GHC.Base.∘ expr_fvs.

Definition exprFreeVars : Core.CoreExpr -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsDSet : Core.CoreExpr -> Core.DVarSet :=
  FV.fvDVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsList : Core.CoreExpr -> list Core.Var :=
  FV.fvVarList GHC.Base.∘ exprFVs.

Definition exprsFVs : list Core.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV exprFVs exprs.

Definition exprsFreeVars : list Core.CoreExpr -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprsFVs.

Definition exprsFreeVarsList : list Core.CoreExpr -> list Core.Var :=
  FV.fvVarList GHC.Base.∘ exprsFVs.

Definition dVarTypeTyCoVars : Core.Var -> Core.DTyCoVarSet :=
  fun var => FV.fvDVarSet (varTypeTyCoFVs var).

Definition delBinderFV : Core.Var -> Core.DVarSet -> Core.DVarSet :=
  fun b s => unionFVs (Core.delDVarSet s b) (dVarTypeTyCoVars b).

Definition delBindersFV : list Core.Var -> Core.DVarSet -> Core.DVarSet :=
  fun bs fvs => Data.Foldable.foldr delBinderFV fvs bs.

Definition bndrRuleAndUnfoldingFVs : Core.Id -> FV.FV :=
  fun id =>
    if Core.isId id : bool then FV.unionFV (idRuleFVs id) (idUnfoldingFVs id) else
    FV.emptyFV.

Definition bndrRuleAndUnfoldingVarsDSet : Core.Id -> Core.DVarSet :=
  fun id => FV.fvDVarSet (bndrRuleAndUnfoldingFVs id).

Definition idFVs : Core.Id -> FV.FV :=
  fun id =>
    if andb Util.debugIsOn (negb (Core.isId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreFVs.hs")
          #629)
    else FV.unionFV (varTypeTyCoFVs id) (bndrRuleAndUnfoldingFVs id).

Definition dIdFreeVars : Core.Id -> Core.DVarSet :=
  fun id => FV.fvDVarSet (idFVs id).

Definition idFreeVars : Core.Id -> Core.VarSet :=
  fun id =>
    if andb Util.debugIsOn (negb (Core.isId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreFVs.hs")
          #622)
    else FV.fvVarSet (idFVs id).

Definition rhs_fvs : (Core.Id * Core.CoreExpr)%type -> FV.FV :=
  fun '(pair bndr rhs) =>
    FV.unionFV (expr_fvs rhs) (bndrRuleAndUnfoldingFVs bndr).

Definition addBndr : Core.CoreBndr -> FV.FV -> FV.FV :=
  fun bndr fv fv_cand in_scope acc =>
    (FV.unionFV (varTypeTyCoFVs bndr) (FV.delFV bndr fv)) fv_cand in_scope acc.

Definition addBndrs : list Core.CoreBndr -> FV.FV -> FV.FV :=
  fun bndrs fv => Data.Foldable.foldr addBndr fv bndrs.

Definition bindFreeVars : Core.CoreBind -> Core.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.NonRec b r =>
        FV.fvVarSet (FV.filterFV Core.isLocalVar (rhs_fvs (pair b r)))
    | Core.Rec prs =>
        FV.fvVarSet (FV.filterFV Core.isLocalVar (addBndrs (GHC.Base.map Data.Tuple.fst
                                                            prs) (FV.mapUnionFV rhs_fvs prs)))
    end.

Definition idRuleRhsVars
   : (BasicTypes.Activation -> bool) -> Core.Id -> Core.VarSet :=
  fun is_active id =>
    let get_fvs :=
      fun arg_0__ =>
        match arg_0__ with
        | Core.Rule _ act fn _ bndrs _ rhs _ _ _ _ =>
            let fvs :=
              FV.fvVarSet (FV.filterFV Core.isLocalVar (addBndrs bndrs (expr_fvs rhs))) in
            if is_active act : bool
            then UniqSet.delOneFromUniqSet_Directly fvs (Unique.getUnique fn) else
            noFVs
        | _ => noFVs
        end in
    Core.mapUnionVarSet get_fvs (Id.idCoreRules id).

Definition ruleFVs : Core.CoreRule -> FV.FV :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.BuiltinRule _ _ _ _ => FV.emptyFV
    | Core.Rule _ _ _do_not_include _ bndrs args rhs _ _ _ _ =>
        FV.filterFV Core.isLocalVar (addBndrs bndrs (exprs_fvs (cons rhs args)))
    end.

Definition ruleFreeVars : Core.CoreRule -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ ruleFVs.

Definition rulesFreeVars : list Core.CoreRule -> Core.VarSet :=
  fun rules => Core.mapUnionVarSet ruleFreeVars rules.

Definition rulesFVs : list Core.CoreRule -> FV.FV :=
  FV.mapUnionFV ruleFVs.

Definition rulesFreeVarsDSet : list Core.CoreRule -> Core.DVarSet :=
  fun rules => FV.fvDVarSet (rulesFVs rules).

Definition ruleLhsFVIds : Core.CoreRule -> FV.FV :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.BuiltinRule _ _ _ _ => FV.emptyFV
    | Core.Rule _ _ _ _ bndrs args _ _ _ _ _ =>
        FV.filterFV Core.isLocalId (addBndrs bndrs (exprs_fvs args))
    end.

Definition ruleLhsFreeIds : Core.CoreRule -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ ruleLhsFVIds.

Definition ruleLhsFreeIdsList : Core.CoreRule -> list Core.Var :=
  FV.fvVarList GHC.Base.∘ ruleLhsFVIds.

Definition ruleRhsFreeVars : Core.CoreRule -> Core.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.BuiltinRule _ _ _ _ => noFVs
    | Core.Rule _ _ _ _ bndrs _ rhs _ _ _ _ =>
        FV.fvVarSet (FV.filterFV Core.isLocalVar (addBndrs bndrs (expr_fvs rhs)))
    end.

Definition aFreeVar : Core.Var -> Core.DVarSet :=
  Core.unitDVarSet.

Definition freeVars : Core.CoreExpr -> CoreExprWithFVs :=
  fix freeVars (arg_0__ : Core.CoreExpr) : CoreExprWithFVs
        := match arg_0__ with
           | Core.Mk_Var v =>
               let ty_fvs := dVarTypeTyCoVars v in
               if Core.isLocalVar v : bool
               then pair (unionFVs (aFreeVar v) ty_fvs) (Core.AnnVar v) else
               pair Core.emptyDVarSet (Core.AnnVar v)
           | Core.Lit lit => pair Core.emptyDVarSet (Core.AnnLit lit)
           | Core.Lam b body =>
               let b_ty := Id.idType b in
               let b_fvs := Core.emptyDVarSet in
               let '(pair body_fvs _ as body') := freeVars body in
               pair (unionFVs b_fvs (delBinderFV b body_fvs)) (Core.AnnLam b body')
           | Core.App fun_ arg =>
               let arg' := freeVars arg in
               let fun' := freeVars fun_ in
               pair (unionFVs (freeVarsOf fun') (freeVarsOf arg')) (Core.AnnApp fun' arg')
           | Core.Case scrut bndr ty alts =>
               let fv_alt :=
                 fun '(pair (pair con args) rhs) =>
                   let rhs2 := freeVars rhs in
                   pair (delBindersFV args (freeVarsOf rhs2)) (pair (pair con args) rhs2) in
               let 'pair alts_fvs_s alts2 := NestedRecursionHelpers.mapAndUnzipFix fv_alt
                                               alts in
               let alts_fvs := unionFVss alts_fvs_s in
               let scrut2 := freeVars scrut in
               pair (unionFVs (unionFVs (delBinderFV bndr alts_fvs) (freeVarsOf scrut2))
                              Core.emptyDVarSet) (Core.AnnCase scrut2 bndr ty alts2)
           | Core.Let bind body =>
               let body2 := freeVars body in
               let 'pair bind2 bind_fvs := freeVarsBind bind (freeVarsOf body2) in
               pair bind_fvs (Core.AnnLet bind2 body2)
           end with freeVarsBind (arg_0__ : Core.CoreBind) (arg_1__ : Core.DVarSet)
                      : (CoreBindWithFVs * Core.DVarSet)%type
                      := match arg_0__, arg_1__ with
                         | Core.NonRec binder rhs, body_fvs =>
                             let body_fvs2 := delBinderFV binder body_fvs in
                             let rhs2 := freeVars rhs in
                             pair (Core.AnnNonRec binder rhs2) (unionFVs (unionFVs (freeVarsOf rhs2)
                                                                                   body_fvs2)
                                                                         (bndrRuleAndUnfoldingVarsDSet binder))
                         | Core.Rec binds, body_fvs =>
                             let 'pair binders rhss := GHC.List.unzip binds in
                             let rhss2 := GHC.Base.map (freeVars GHC.Base.∘ snd) binds in
                             let rhs_body_fvs :=
                               Data.Foldable.foldr (unionFVs GHC.Base.∘ freeVarsOf) body_fvs rhss2 in
                             let binders_fvs :=
                               FV.fvDVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs binders) in
                             let all_fvs := unionFVs rhs_body_fvs binders_fvs in
                             pair (Core.AnnRec (GHC.List.zip binders rhss2)) (delBindersFV binders all_fvs)
                         end for freeVars.

Definition freeVarsBind
   : Core.CoreBind -> Core.DVarSet -> (CoreBindWithFVs * Core.DVarSet)%type :=
  fix freeVars (arg_0__ : Core.CoreExpr) : CoreExprWithFVs
        := match arg_0__ with
           | Core.Mk_Var v =>
               let ty_fvs := dVarTypeTyCoVars v in
               if Core.isLocalVar v : bool
               then pair (unionFVs (aFreeVar v) ty_fvs) (Core.AnnVar v) else
               pair Core.emptyDVarSet (Core.AnnVar v)
           | Core.Lit lit => pair Core.emptyDVarSet (Core.AnnLit lit)
           | Core.Lam b body =>
               let b_ty := Id.idType b in
               let b_fvs := Core.emptyDVarSet in
               let '(pair body_fvs _ as body') := freeVars body in
               pair (unionFVs b_fvs (delBinderFV b body_fvs)) (Core.AnnLam b body')
           | Core.App fun_ arg =>
               let arg' := freeVars arg in
               let fun' := freeVars fun_ in
               pair (unionFVs (freeVarsOf fun') (freeVarsOf arg')) (Core.AnnApp fun' arg')
           | Core.Case scrut bndr ty alts =>
               let fv_alt :=
                 fun '(pair (pair con args) rhs) =>
                   let rhs2 := freeVars rhs in
                   pair (delBindersFV args (freeVarsOf rhs2)) (pair (pair con args) rhs2) in
               let 'pair alts_fvs_s alts2 := NestedRecursionHelpers.mapAndUnzipFix fv_alt
                                               alts in
               let alts_fvs := unionFVss alts_fvs_s in
               let scrut2 := freeVars scrut in
               pair (unionFVs (unionFVs (delBinderFV bndr alts_fvs) (freeVarsOf scrut2))
                              Core.emptyDVarSet) (Core.AnnCase scrut2 bndr ty alts2)
           | Core.Let bind body =>
               let body2 := freeVars body in
               let 'pair bind2 bind_fvs := freeVarsBind bind (freeVarsOf body2) in
               pair bind_fvs (Core.AnnLet bind2 body2)
           end with freeVarsBind (arg_0__ : Core.CoreBind) (arg_1__ : Core.DVarSet)
                      : (CoreBindWithFVs * Core.DVarSet)%type
                      := match arg_0__, arg_1__ with
                         | Core.NonRec binder rhs, body_fvs =>
                             let body_fvs2 := delBinderFV binder body_fvs in
                             let rhs2 := freeVars rhs in
                             pair (Core.AnnNonRec binder rhs2) (unionFVs (unionFVs (freeVarsOf rhs2)
                                                                                   body_fvs2)
                                                                         (bndrRuleAndUnfoldingVarsDSet binder))
                         | Core.Rec binds, body_fvs =>
                             let 'pair binders rhss := GHC.List.unzip binds in
                             let rhss2 := GHC.Base.map (freeVars GHC.Base.∘ snd) binds in
                             let rhs_body_fvs :=
                               Data.Foldable.foldr (unionFVs GHC.Base.∘ freeVarsOf) body_fvs rhss2 in
                             let binders_fvs :=
                               FV.fvDVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs binders) in
                             let all_fvs := unionFVs rhs_body_fvs binders_fvs in
                             pair (Core.AnnRec (GHC.List.zip binders rhss2)) (delBindersFV binders all_fvs)
                         end for freeVarsBind.

(* External variables:
     None andb bool cons list negb op_zt__ option pair snd BasicTypes.Activation
     Core.AnnAlt Core.AnnApp Core.AnnBind Core.AnnCase Core.AnnExpr Core.AnnExpr'
     Core.AnnLam Core.AnnLet Core.AnnLit Core.AnnNonRec Core.AnnRec Core.AnnVar
     Core.App Core.Breakpoint Core.BuiltinRule Core.Case Core.CoreBind Core.CoreBndr
     Core.CoreExpr Core.CoreRule Core.CoreVect Core.DIdSet Core.DTyCoVarSet
     Core.DVarSet Core.Id Core.IdSet Core.Lam Core.Let Core.Lit Core.Mk_Var
     Core.NoVect Core.NonRec Core.Rec Core.Rule Core.Tickish Core.TyCoVarSet
     Core.Unfolding Core.Var Core.VarSet Core.Vect Core.VectClass Core.VectInst
     Core.VectType Core.delDVarSet Core.emptyDVarSet Core.emptyVarSet Core.isId
     Core.isLocalId Core.isLocalVar Core.mapUnionVarSet Core.unionDVarSet
     Core.unionDVarSets Core.unitDVarSet Data.Foldable.foldr Data.Tuple.fst FV.FV
     FV.InterestingVarFun FV.delFV FV.emptyFV FV.filterFV FV.fvDVarSet FV.fvVarList
     FV.fvVarSet FV.mapUnionFV FV.mkFVs FV.unionFV GHC.Base.map GHC.Base.op_z2218U__
     GHC.List.unzip GHC.List.zip GHC.Num.fromInteger Id.idCoreRules Id.idType
     Id.realIdUnfolding Maybes.orElse NameSet.NameSet NameSet.emptyNameSet
     NameSet.unionNameSet NestedRecursionHelpers.mapAndUnzipFix Panic.assertPanic
     UniqSet.delOneFromUniqSet_Directly Unique.getUnique Util.debugIsOn
*)
