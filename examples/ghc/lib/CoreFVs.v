(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Combined.



(* Converted imports: *)

Require BasicTypes.
Require Combined.
Require Data.Foldable.
Require Data.Tuple.
Require FV.
Require GHC.Base.
Require GHC.List.
Require Lists.List.
Require NameSet.
Require UniqSet.
Require Unique.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition FVAnn :=
  Combined.DVarSet%type.

Definition CoreExprWithFVs' :=
  (Combined.AnnExpr' Combined.Var FVAnn)%type.

Definition CoreExprWithFVs :=
  (AnnExpr Combined.Var FVAnn)%type.

Definition CoreBindWithFVs :=
  (Combined.AnnBind Combined.Var FVAnn)%type.

Definition CoreAltWithFVs :=
  (AnnAlt Combined.Var FVAnn)%type.
(* Midamble *)



(* Break mutual recursion *)
Parameter freeVarsBind1 : Combined.CoreBind ->
     Combined.DVarSet -> (CoreBindWithFVs * Combined.DVarSet)%type.

(*
NOTE (freeVars): if you try to use a termination edit for freeVars instead of 
the rewrite of unzipAndMap in the edit file, we need to add a type
annotation to fv_alt for the freeVars function to type check. 
The required annotation is 
   fv_alt : Alt CoreBndr -> (VarSet.DVarSet * CoreAltWithFVs)
*)

(* Converted value declarations: *)

Definition aFreeVar : Combined.Var -> Combined.DVarSet :=
  Combined.unitDVarSet.

Definition bndrRuleAndUnfoldingVarsDSet : Combined.Var -> Combined.DVarSet :=
  fun id => FV.fvDVarSet FV.emptyFV.

Definition freeVarsOf : CoreExprWithFVs -> Combined.DIdSet :=
  fun '(pair fvs _) => fvs.

Definition freeVarsOfAnn : FVAnn -> Combined.DIdSet :=
  fun fvs => fvs.

Definition idRuleFVs : Id -> FV.FV :=
  fun id => FV.emptyFV.

Definition idRuleVars : Combined.Var -> Combined.VarSet :=
  fun id => FV.fvVarSet (idRuleFVs id).

Definition idUnfoldingFVs : Id -> FV.FV :=
  fun id => FV.emptyFV.

Definition idUnfoldingVars : Combined.Var -> Combined.VarSet :=
  fun id => FV.fvVarSet (idUnfoldingFVs id).

Definition bndrRuleAndUnfoldingFVs : Combined.Var -> FV.FV :=
  fun id =>
    if Combined.isId id : bool
    then FV.unionFV (idRuleFVs id) (idUnfoldingFVs id) else
    FV.emptyFV.

Definition noFVs : Combined.VarSet :=
  Combined.emptyVarSet.

Definition orphNamesOfThings {a}
   : (a -> NameSet.NameSet) -> list a -> NameSet.NameSet :=
  fun f =>
    Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ f) NameSet.emptyNameSet.

Axiom stableUnfoldingFVs : forall {A : Type}, A.

Definition stableUnfoldingVars : Combined.Unfolding -> option Combined.VarSet :=
  fun unf => GHC.Base.fmap FV.fvVarSet (stableUnfoldingFVs unf).

(* Translating `stableUnfoldingFVs' failed: using a record pattern for the
   unknown constructor `CoreUnfolding' unsupported *)

Definition tickish_fvs : Combined.Tickish Combined.Var -> FV.FV :=
  fun arg_0__ =>
    match arg_0__ with
    | Combined.Breakpoint _ ids => FV.mkFVs ids
    | _ => FV.emptyFV
    end.

Definition unionFVs
   : Combined.DVarSet -> Combined.DVarSet -> Combined.DVarSet :=
  Combined.unionDVarSet.

Definition unionFVss : list Combined.DVarSet -> Combined.DVarSet :=
  Combined.unionDVarSets.

Definition varTypeTyCoFVs : Combined.Var -> FV.FV :=
  fun var => FV.emptyFV.

Definition varTypeTyCoVars : Combined.Var -> Combined.TyCoVarSet :=
  fun var => FV.fvVarSet (varTypeTyCoFVs var).

Definition idFVs : Combined.Var -> FV.FV :=
  fun id => FV.unionFV (varTypeTyCoFVs id) FV.emptyFV.

Definition idFreeVars : Combined.Var -> Combined.VarSet :=
  fun id => FV.fvVarSet (idFVs id).

Definition dIdFreeVars : Combined.Var -> Combined.DVarSet :=
  fun id => FV.fvDVarSet (idFVs id).

Definition dVarTypeTyCoVars : Combined.Var -> Combined.DTyCoVarSet :=
  fun var => FV.fvDVarSet (varTypeTyCoFVs var).

Definition delBinderFV : Combined.Var -> Combined.DVarSet -> Combined.DVarSet :=
  fun b s => unionFVs (Combined.delDVarSet s b) (dVarTypeTyCoVars b).

Definition delBindersFV
   : list Combined.Var -> Combined.DVarSet -> Combined.DVarSet :=
  fun bs fvs => Data.Foldable.foldr delBinderFV fvs bs.

Definition freeVars : Combined.CoreExpr -> CoreExprWithFVs :=
  let go : Combined.CoreExpr -> CoreExprWithFVs :=
    fix go arg_0__
          := match arg_0__ with
             | Combined.Mk_Var v =>
                 let ty_fvs := dVarTypeTyCoVars v in
                 if Combined.isLocalVar v : bool
                 then pair (unionFVs (aFreeVar v) ty_fvs) (Combined.AnnVar v) else
                 pair Combined.emptyDVarSet (Combined.AnnVar v)
             | Combined.Lit lit => pair Combined.emptyDVarSet (Combined.AnnLit lit)
             | Combined.Lam b body =>
                 let b_ty := tt in
                 let b_fvs := Combined.emptyDVarSet in
                 let '(pair body_fvs _ as body') := go body in
                 pair (unionFVs b_fvs (delBinderFV b body_fvs)) (Combined.AnnLam b body')
             | Combined.App fun_ arg =>
                 let arg' := go arg in
                 let fun' := go fun_ in
                 pair (unionFVs (freeVarsOf fun') (freeVarsOf arg')) (Combined.AnnApp fun' arg')
             | Combined.Case scrut bndr ty alts =>
                 let fv_alt :=
                   fun '(pair (pair con args) rhs) =>
                     let rhs2 := go rhs in
                     pair (delBindersFV args (freeVarsOf rhs2)) (pair (pair con args) rhs2) in
                 let 'pair alts_fvs_s alts2 := GHC.List.unzip (Lists.List.map fv_alt alts) in
                 let alts_fvs := unionFVss alts_fvs_s in
                 let scrut2 := go scrut in
                 pair (unionFVs (unionFVs (delBinderFV bndr alts_fvs) (freeVarsOf scrut2))
                                Combined.emptyDVarSet) (Combined.AnnCase scrut2 bndr ty alts2)
             | Combined.Let bind body =>
                 let body2 := go body in
                 let 'pair bind2 bind_fvs := freeVarsBind1 bind (freeVarsOf body2) in
                 pair bind_fvs (Combined.AnnLet bind2 body2)
             | Combined.Cast expr co =>
                 let cfvs := Combined.emptyDVarSet in
                 let expr2 := go expr in
                 pair (unionFVs (freeVarsOf expr2) cfvs) (Combined.AnnCast expr2 (pair cfvs co))
             | Combined.Tick tickish expr =>
                 let tickishFVs :=
                   fun arg_23__ =>
                     match arg_23__ with
                     | Combined.Breakpoint _ ids => Combined.mkDVarSet ids
                     | _ => Combined.emptyDVarSet
                     end in
                 let expr2 := go expr in
                 pair (unionFVs (tickishFVs tickish) (freeVarsOf expr2)) (Combined.AnnTick
                       tickish expr2)
             | Combined.Type_ ty => pair Combined.emptyDVarSet (Combined.AnnType ty)
             | Combined.Coercion co => pair Combined.emptyDVarSet (Combined.AnnCoercion co)
             end in
  go.

Definition freeVarsBind
   : Combined.CoreBind ->
     Combined.DVarSet -> (CoreBindWithFVs * Combined.DVarSet)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Combined.NonRec binder rhs, body_fvs =>
        let body_fvs2 := delBinderFV binder body_fvs in
        let rhs2 := freeVars rhs in
        pair (Combined.AnnNonRec binder rhs2) (unionFVs (unionFVs (freeVarsOf rhs2)
                                                                  body_fvs2) (bndrRuleAndUnfoldingVarsDSet binder))
    | Combined.Rec binds, body_fvs =>
        let 'pair binders rhss := GHC.List.unzip binds in
        let rhss2 := GHC.Base.map freeVars rhss in
        let rhs_body_fvs :=
          Data.Foldable.foldr (unionFVs GHC.Base.∘ freeVarsOf) body_fvs rhss2 in
        let binders_fvs :=
          FV.fvDVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs binders) in
        let all_fvs := unionFVs rhs_body_fvs binders_fvs in
        pair (Combined.AnnRec (GHC.List.zip binders rhss2)) (delBindersFV binders
              all_fvs)
    end.

Definition addBndr : Combined.CoreBndr -> FV.FV -> FV.FV :=
  fun bndr fv fv_cand in_scope acc =>
    (FV.unionFV (varTypeTyCoFVs bndr) (FV.delFV bndr fv)) fv_cand in_scope acc.

Definition addBndrs : list Combined.CoreBndr -> FV.FV -> FV.FV :=
  fun bndrs fv => Data.Foldable.foldr addBndr fv bndrs.

Definition expr_fvs : Combined.CoreExpr -> FV.FV :=
  fix expr_fvs arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | Combined.Type_ ty, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
           | Combined.Coercion co, fv_cand, in_scope, acc =>
               FV.emptyFV fv_cand in_scope acc
           | Combined.Mk_Var var, fv_cand, in_scope, acc =>
               FV.unitFV var fv_cand in_scope acc
           | Combined.Lit _, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
           | Combined.Tick t expr, fv_cand, in_scope, acc =>
               (FV.unionFV (tickish_fvs t) (expr_fvs expr)) fv_cand in_scope acc
           | Combined.App fun_ arg, fv_cand, in_scope, acc =>
               (FV.unionFV (expr_fvs fun_) (expr_fvs arg)) fv_cand in_scope acc
           | Combined.Lam bndr body, fv_cand, in_scope, acc =>
               addBndr bndr (expr_fvs body) fv_cand in_scope acc
           | Combined.Cast expr co, fv_cand, in_scope, acc =>
               (FV.unionFV (expr_fvs expr) FV.emptyFV) fv_cand in_scope acc
           | Combined.Case scrut bndr ty alts, fv_cand, in_scope, acc =>
               let alt_fvs :=
                 fun '(pair (pair _ bndrs) rhs) => addBndrs bndrs (expr_fvs rhs) in
               (FV.unionFV (FV.unionFV (expr_fvs scrut) FV.emptyFV) (addBndr bndr (FV.unionsFV
                                                                                   (Lists.List.map alt_fvs alts))))
               fv_cand in_scope acc
           | Combined.Let (Combined.NonRec bndr rhs) body, fv_cand, in_scope, acc =>
               (FV.unionFV (FV.unionFV (expr_fvs rhs) FV.emptyFV) (addBndr bndr (expr_fvs
                                                                                 body))) fv_cand in_scope acc
           | Combined.Let (Combined.Rec pairs) body, fv_cand, in_scope, acc =>
               addBndrs (GHC.Base.map Data.Tuple.fst pairs) (FV.unionFV (FV.unionsFV
                                                                         (Lists.List.map (fun '(pair bndr rhs) =>
                                                                                            expr_fvs rhs) pairs))
                                                                        (expr_fvs body)) fv_cand in_scope acc
           end.

Definition exprFVs : Combined.CoreExpr -> FV.FV :=
  FV.filterFV Combined.isLocalVar GHC.Base.∘ expr_fvs.

Definition exprFreeVars : Combined.CoreExpr -> Combined.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsDSet : Combined.CoreExpr -> Combined.DVarSet :=
  FV.fvDVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsList : Combined.CoreExpr -> list Combined.Var :=
  FV.fvVarList GHC.Base.∘ exprFVs.

Definition exprsFVs : list Combined.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV exprFVs exprs.

Definition exprsFreeVars : list Combined.CoreExpr -> Combined.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprsFVs.

Definition exprsFreeVarsList : list Combined.CoreExpr -> list Combined.Var :=
  FV.fvVarList GHC.Base.∘ exprsFVs.

Definition exprSomeFreeVars
   : FV.InterestingVarFun -> Combined.CoreExpr -> Combined.VarSet :=
  fun fv_cand e => FV.fvVarSet (FV.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIds : Combined.CoreExpr -> Combined.IdSet :=
  exprSomeFreeVars Combined.isLocalId.

Definition exprSomeFreeVarsDSet
   : FV.InterestingVarFun -> Combined.CoreExpr -> Combined.DVarSet :=
  fun fv_cand e => FV.fvDVarSet (FV.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIdsDSet : Combined.CoreExpr -> Combined.DIdSet :=
  exprSomeFreeVarsDSet Combined.isLocalId.

Definition exprSomeFreeVarsList
   : FV.InterestingVarFun -> Combined.CoreExpr -> list Combined.Var :=
  fun fv_cand e => FV.fvVarList (FV.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIdsList : Combined.CoreExpr -> list Combined.Var :=
  exprSomeFreeVarsList Combined.isLocalId.

Definition exprsSomeFreeVars
   : FV.InterestingVarFun -> list Combined.CoreExpr -> Combined.VarSet :=
  fun fv_cand es => FV.fvVarSet (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs es)).

Definition exprsSomeFreeVarsDSet
   : FV.InterestingVarFun -> list Combined.CoreExpr -> Combined.DVarSet :=
  fun fv_cand e => FV.fvDVarSet (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs e)).

Definition exprsFreeIdsDSet : list Combined.CoreExpr -> Combined.DIdSet :=
  exprsSomeFreeVarsDSet Combined.isLocalId.

Definition exprsSomeFreeVarsList
   : FV.InterestingVarFun -> list Combined.CoreExpr -> list Combined.Var :=
  fun fv_cand es =>
    FV.fvVarList (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs es)).

Definition exprsFreeIdsList : list Combined.CoreExpr -> list Combined.Var :=
  exprsSomeFreeVarsList Combined.isLocalId.

Definition exprs_fvs : list Combined.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV expr_fvs exprs.

Definition ruleFVs : Combined.CoreRule -> FV.FV :=
  fun arg_0__ =>
    match arg_0__ with
    | Combined.BuiltinRule _ _ _ _ => FV.emptyFV
    | Combined.Rule _ _ _do_not_include _ bndrs args rhs _ _ _ _ =>
        FV.filterFV Combined.isLocalVar (addBndrs bndrs (exprs_fvs (cons rhs args)))
    end.

Definition ruleFreeVars : Combined.CoreRule -> Combined.VarSet :=
  FV.fvVarSet GHC.Base.∘ ruleFVs.

Definition rulesFreeVars : list Combined.CoreRule -> Combined.VarSet :=
  fun rules => Combined.mapUnionVarSet ruleFreeVars rules.

Definition rulesFVs : list Combined.CoreRule -> FV.FV :=
  FV.mapUnionFV ruleFVs.

Definition rulesFreeVarsDSet : list Combined.CoreRule -> Combined.DVarSet :=
  fun rules => FV.fvDVarSet (rulesFVs rules).

Definition ruleLhsFVIds : Combined.CoreRule -> FV.FV :=
  fun arg_0__ =>
    match arg_0__ with
    | Combined.BuiltinRule _ _ _ _ => FV.emptyFV
    | Combined.Rule _ _ _ _ bndrs args _ _ _ _ _ =>
        FV.filterFV Combined.isLocalId (addBndrs bndrs (exprs_fvs args))
    end.

Definition ruleLhsFreeIds : Combined.CoreRule -> Combined.VarSet :=
  FV.fvVarSet GHC.Base.∘ ruleLhsFVIds.

Definition ruleLhsFreeIdsList : Combined.CoreRule -> list Combined.Var :=
  FV.fvVarList GHC.Base.∘ ruleLhsFVIds.

Definition idRuleRhsVars
   : (BasicTypes.Activation -> bool) -> Combined.Var -> Combined.VarSet :=
  fun is_active id =>
    let get_fvs :=
      fun arg_0__ =>
        match arg_0__ with
        | Combined.Rule _ act fn _ bndrs _ rhs _ _ _ _ =>
            let fvs :=
              FV.fvVarSet (FV.filterFV Combined.isLocalVar (addBndrs bndrs (expr_fvs rhs))) in
            if is_active act : bool
            then UniqSet.delOneFromUniqSet_Directly fvs (Unique.getUnique fn) else
            noFVs
        | _ => noFVs
        end in
    Combined.emptyVarSet.

Definition rhs_fvs : (Combined.Var * Combined.CoreExpr)%type -> FV.FV :=
  fun '(pair bndr rhs) => FV.unionFV (expr_fvs rhs) FV.emptyFV.

Definition bindFreeVars : Combined.CoreBind -> Combined.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | Combined.NonRec b r =>
        FV.fvVarSet (FV.filterFV Combined.isLocalVar (rhs_fvs (pair b r)))
    | Combined.Rec prs =>
        FV.fvVarSet (FV.filterFV Combined.isLocalVar (addBndrs (GHC.Base.map
                                                                Data.Tuple.fst prs) (FV.mapUnionFV rhs_fvs prs)))
    end.

Definition ruleRhsFreeVars : Combined.CoreRule -> Combined.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | Combined.BuiltinRule _ _ _ _ => noFVs
    | Combined.Rule _ _ _ _ bndrs _ rhs _ _ _ _ =>
        FV.fvVarSet (FV.filterFV Combined.isLocalVar (addBndrs bndrs (expr_fvs rhs)))
    end.

Definition vectsFreeVars : list Combined.CoreVect -> Combined.VarSet :=
  let vectFreeVars :=
    fun arg_0__ =>
      match arg_0__ with
      | Combined.Vect _ rhs =>
          FV.fvVarSet (FV.filterFV Combined.isLocalId (expr_fvs rhs))
      | Combined.NoVect _ => noFVs
      | Combined.VectType _ _ _ => noFVs
      | Combined.VectClass _ => noFVs
      | Combined.VectInst _ => noFVs
      end in
  Combined.mapUnionVarSet vectFreeVars.

(* External variables:
     AnnAlt AnnExpr Id bool cons freeVarsBind1 list op_zt__ option pair tt
     BasicTypes.Activation Combined.AnnApp Combined.AnnBind Combined.AnnCase
     Combined.AnnCast Combined.AnnCoercion Combined.AnnExpr' Combined.AnnLam
     Combined.AnnLet Combined.AnnLit Combined.AnnNonRec Combined.AnnRec
     Combined.AnnTick Combined.AnnType Combined.AnnVar Combined.App
     Combined.Breakpoint Combined.BuiltinRule Combined.Case Combined.Cast
     Combined.Coercion Combined.CoreBind Combined.CoreBndr Combined.CoreExpr
     Combined.CoreRule Combined.CoreVect Combined.DIdSet Combined.DTyCoVarSet
     Combined.DVarSet Combined.IdSet Combined.Lam Combined.Let Combined.Lit
     Combined.Mk_Var Combined.NoVect Combined.NonRec Combined.Rec Combined.Rule
     Combined.Tick Combined.Tickish Combined.TyCoVarSet Combined.Type_
     Combined.Unfolding Combined.Var Combined.VarSet Combined.Vect Combined.VectClass
     Combined.VectInst Combined.VectType Combined.delDVarSet Combined.emptyDVarSet
     Combined.emptyVarSet Combined.isId Combined.isLocalId Combined.isLocalVar
     Combined.mapUnionVarSet Combined.mkDVarSet Combined.unionDVarSet
     Combined.unionDVarSets Combined.unitDVarSet Data.Foldable.foldr Data.Tuple.fst
     FV.FV FV.InterestingVarFun FV.delFV FV.emptyFV FV.filterFV FV.fvDVarSet
     FV.fvVarList FV.fvVarSet FV.mapUnionFV FV.mkFVs FV.unionFV FV.unionsFV FV.unitFV
     GHC.Base.fmap GHC.Base.map GHC.Base.op_z2218U__ GHC.List.unzip GHC.List.zip
     Lists.List.map NameSet.NameSet NameSet.emptyNameSet NameSet.unionNameSet
     UniqSet.delOneFromUniqSet_Directly Unique.getUnique
*)
