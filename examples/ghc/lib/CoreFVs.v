(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Core.



(* Converted imports: *)

Require BasicTypes.
Require Core.
Require Data.Foldable.
Require Data.Tuple.
Require FV.
Require GHC.Base.
Require GHC.List.
Require Lists.List.
Require NameSet.
Require UniqSet.
Require Unique.
Require Util.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition FVAnn :=
  DVarSet%type.

Definition CoreExprWithFVs' :=
  (Core.AnnExpr' Core.Var FVAnn)%type.

Definition CoreExprWithFVs :=
  (AnnExpr Core.Var FVAnn)%type.

Definition CoreBindWithFVs :=
  (Core.AnnBind Core.Var FVAnn)%type.

Definition CoreAltWithFVs :=
  (AnnAlt Core.Var FVAnn)%type.

(* Midamble *)



(* Break mutual recursion *)
Parameter freeVarsBind1 : Core.CoreBind ->
     DVarSet -> (CoreBindWithFVs * DVarSet)%type.

(*
NOTE (freeVars): if you try to use a termination edit for freeVars 
you may need to add a type
annotation to fv_alt for the freeVars function to type check. 
The required annotation is 
   fv_alt : Alt CoreBndr -> (VarSet.DVarSet * CoreAltWithFVs)
*)

(* Converted value declarations: *)

Definition varTypeTyCoFVs : Core.Var -> FV.FV :=
  fun var => FV.emptyFV.

Definition varTypeTyCoVars : Core.Var -> Core.TyCoVarSet :=
  fun var => FV.fvVarSet (varTypeTyCoFVs var).

Definition unionFVss : list DVarSet -> DVarSet :=
  Core.unionDVarSets.

Definition unionFVs : DVarSet -> DVarSet -> DVarSet :=
  Core.unionDVarSet.

Definition tickish_fvs : Core.Tickish Core.Var -> FV.FV :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.Breakpoint _ ids => FV.mkFVs ids
    | _ => FV.emptyFV
    end.

Definition orphNamesOfThings {a}
   : (a -> NameSet.NameSet) -> list a -> NameSet.NameSet :=
  fun f =>
    Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ f) NameSet.emptyNameSet.

Definition noFVs : Core.VarSet :=
  Core.emptyVarSet.

Definition idUnfoldingFVs : Id -> FV.FV :=
  fun id => FV.emptyFV.

Definition idUnfoldingVars : Core.Var -> Core.VarSet :=
  fun id => FV.fvVarSet (idUnfoldingFVs id).

Definition idRuleFVs : Id -> FV.FV :=
  fun id => FV.emptyFV.

Definition idRuleVars : Core.Var -> Core.VarSet :=
  fun id => FV.fvVarSet (idRuleFVs id).

Definition idFVs : Core.Var -> FV.FV :=
  fun id => FV.unionFV (varTypeTyCoFVs id) FV.emptyFV.

Definition idFreeVars : Core.Var -> Core.VarSet :=
  fun id => FV.fvVarSet (idFVs id).

Definition freeVarsOfAnn : FVAnn -> Core.DIdSet :=
  fun fvs => fvs.

Definition freeVarsOf : CoreExprWithFVs -> Core.DIdSet :=
  fun '(pair fvs _) => fvs.

Definition dVarTypeTyCoVars : Core.Var -> Core.DTyCoVarSet :=
  fun var => FV.fvDVarSet (varTypeTyCoFVs var).

Definition delBinderFV : Core.Var -> DVarSet -> DVarSet :=
  fun b s => unionFVs (Core.delDVarSet s b) (dVarTypeTyCoVars b).

Definition delBindersFV : list Core.Var -> DVarSet -> DVarSet :=
  fun bs fvs => Data.Foldable.foldr delBinderFV fvs bs.

Definition dIdFreeVars : Core.Var -> DVarSet :=
  fun id => FV.fvDVarSet (idFVs id).

Definition bndrRuleAndUnfoldingVarsDSet : Core.Var -> DVarSet :=
  fun id => FV.fvDVarSet FV.emptyFV.

Definition bndrRuleAndUnfoldingFVs : Core.Var -> FV.FV :=
  fun id =>
    if Core.isId id : bool then FV.unionFV (idRuleFVs id) (idUnfoldingFVs id) else
    FV.emptyFV.

Definition addBndr : Core.CoreBndr -> FV.FV -> FV.FV :=
  fun bndr fv fv_cand in_scope acc =>
    (FV.unionFV (varTypeTyCoFVs bndr) (FV.delFV bndr fv)) fv_cand in_scope acc.

Definition addBndrs : list Core.CoreBndr -> FV.FV -> FV.FV :=
  fun bndrs fv => Data.Foldable.foldr addBndr fv bndrs.

Definition expr_fvs : Core.CoreExpr -> FV.FV :=
  fix expr_fvs arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | Core.Type_ ty, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
           | Core.Coercion co, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
           | Core.Mk_Var var, fv_cand, in_scope, acc => FV.unitFV var fv_cand in_scope acc
           | Core.Lit _, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
           | Core.Tick t expr, fv_cand, in_scope, acc =>
               (FV.unionFV (tickish_fvs t) (expr_fvs expr)) fv_cand in_scope acc
           | Core.App fun_ arg, fv_cand, in_scope, acc =>
               (FV.unionFV (expr_fvs fun_) (expr_fvs arg)) fv_cand in_scope acc
           | Core.Lam bndr body, fv_cand, in_scope, acc =>
               addBndr bndr (expr_fvs body) fv_cand in_scope acc
           | Core.Cast expr co, fv_cand, in_scope, acc =>
               (FV.unionFV (expr_fvs expr) FV.emptyFV) fv_cand in_scope acc
           | Core.Case scrut bndr ty alts, fv_cand, in_scope, acc =>
               let alt_fvs :=
                 fun '(pair (pair _ bndrs) rhs) => addBndrs bndrs (expr_fvs rhs) in
               (FV.unionFV (FV.unionFV (expr_fvs scrut) FV.emptyFV) (addBndr bndr (FV.unionsFV
                                                                                   (Lists.List.map alt_fvs alts))))
               fv_cand in_scope acc
           | Core.Let (Core.NonRec bndr rhs) body, fv_cand, in_scope, acc =>
               (FV.unionFV (FV.unionFV (expr_fvs rhs) FV.emptyFV) (addBndr bndr (expr_fvs
                                                                                 body))) fv_cand in_scope acc
           | Core.Let (Core.Rec pairs) body, fv_cand, in_scope, acc =>
               addBndrs (GHC.Base.map Data.Tuple.fst pairs) (FV.unionFV (FV.unionsFV
                                                                         (Lists.List.map (fun '(pair bndr rhs) =>
                                                                                            expr_fvs rhs) pairs))
                                                                        (expr_fvs body)) fv_cand in_scope acc
           end.

Definition exprFVs : Core.CoreExpr -> FV.FV :=
  FV.filterFV Core.isLocalVar GHC.Base.∘ expr_fvs.

Definition exprFreeVars : Core.CoreExpr -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsDSet : Core.CoreExpr -> DVarSet :=
  FV.fvDVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsList : Core.CoreExpr -> list Core.Var :=
  FV.fvVarList GHC.Base.∘ exprFVs.

Definition exprsFVs : list Core.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV exprFVs exprs.

Definition exprsFreeVars : list Core.CoreExpr -> Core.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprsFVs.

Definition exprsFreeVarsList : list Core.CoreExpr -> list Core.Var :=
  FV.fvVarList GHC.Base.∘ exprsFVs.

Definition exprSomeFreeVars
   : FV.InterestingVarFun -> Core.CoreExpr -> Core.VarSet :=
  fun fv_cand e => FV.fvVarSet (FV.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIds : Core.CoreExpr -> Core.IdSet :=
  exprSomeFreeVars Core.isLocalId.

Definition exprSomeFreeVarsDSet
   : FV.InterestingVarFun -> Core.CoreExpr -> DVarSet :=
  fun fv_cand e => FV.fvDVarSet (FV.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIdsDSet : Core.CoreExpr -> Core.DIdSet :=
  exprSomeFreeVarsDSet Core.isLocalId.

Definition exprSomeFreeVarsList
   : FV.InterestingVarFun -> Core.CoreExpr -> list Core.Var :=
  fun fv_cand e => FV.fvVarList (FV.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIdsList : Core.CoreExpr -> list Core.Var :=
  exprSomeFreeVarsList Core.isLocalId.

Definition exprsSomeFreeVars
   : FV.InterestingVarFun -> list Core.CoreExpr -> Core.VarSet :=
  fun fv_cand es => FV.fvVarSet (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs es)).

Definition exprsSomeFreeVarsDSet
   : FV.InterestingVarFun -> list Core.CoreExpr -> DVarSet :=
  fun fv_cand e => FV.fvDVarSet (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs e)).

Definition exprsFreeIdsDSet : list Core.CoreExpr -> Core.DIdSet :=
  exprsSomeFreeVarsDSet Core.isLocalId.

Definition exprsSomeFreeVarsList
   : FV.InterestingVarFun -> list Core.CoreExpr -> list Core.Var :=
  fun fv_cand es =>
    FV.fvVarList (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs es)).

Definition exprsFreeIdsList : list Core.CoreExpr -> list Core.Var :=
  exprsSomeFreeVarsList Core.isLocalId.

Definition exprs_fvs : list Core.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV expr_fvs exprs.

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

Definition rulesFreeVarsDSet : list Core.CoreRule -> DVarSet :=
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

Definition idRuleRhsVars
   : (BasicTypes.Activation -> bool) -> Core.Var -> Core.VarSet :=
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
    Core.emptyVarSet.

Definition rhs_fvs : (Core.Var * Core.CoreExpr)%type -> FV.FV :=
  fun '(pair bndr rhs) => FV.unionFV (expr_fvs rhs) FV.emptyFV.

Definition bindFreeVars : Core.CoreBind -> Core.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.NonRec b r =>
        FV.fvVarSet (FV.filterFV Core.isLocalVar (rhs_fvs (pair b r)))
    | Core.Rec prs =>
        FV.fvVarSet (FV.filterFV Core.isLocalVar (addBndrs (GHC.Base.map Data.Tuple.fst
                                                            prs) (FV.mapUnionFV rhs_fvs prs)))
    end.

Definition ruleRhsFreeVars : Core.CoreRule -> Core.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.BuiltinRule _ _ _ _ => noFVs
    | Core.Rule _ _ _ _ bndrs _ rhs _ _ _ _ =>
        FV.fvVarSet (FV.filterFV Core.isLocalVar (addBndrs bndrs (expr_fvs rhs)))
    end.

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

Definition aFreeVar : Core.Var -> DVarSet :=
  Core.unitDVarSet.

Definition freeVars : Core.CoreExpr -> CoreExprWithFVs :=
  let go : Core.CoreExpr -> CoreExprWithFVs :=
    fix go arg_0__
          := match arg_0__ with
             | Core.Mk_Var v =>
                 let ty_fvs := dVarTypeTyCoVars v in
                 if Core.isLocalVar v : bool
                 then pair (unionFVs (aFreeVar v) ty_fvs) (Core.AnnVar v) else
                 pair Core.emptyDVarSet (Core.AnnVar v)
             | Core.Lit lit => pair Core.emptyDVarSet (Core.AnnLit lit)
             | Core.Lam b body =>
                 let b_ty := tt in
                 let b_fvs := Core.emptyDVarSet in
                 let '(pair body_fvs _ as body') := go body in
                 pair (unionFVs b_fvs (delBinderFV b body_fvs)) (Core.AnnLam b body')
             | Core.App fun_ arg =>
                 let arg' := go arg in
                 let fun' := go fun_ in
                 pair (unionFVs (freeVarsOf fun') (freeVarsOf arg')) (Core.AnnApp fun' arg')
             | Core.Case scrut bndr ty alts =>
                 let fv_alt :=
                   fun '(pair (pair con args) rhs) =>
                     let rhs2 := go rhs in
                     pair (delBindersFV args (freeVarsOf rhs2)) (pair (pair con args) rhs2) in
                 let 'pair alts_fvs_s alts2 := Util.mapAndUnzip fv_alt alts in
                 let alts_fvs := unionFVss alts_fvs_s in
                 let scrut2 := go scrut in
                 pair (unionFVs (unionFVs (delBinderFV bndr alts_fvs) (freeVarsOf scrut2))
                                Core.emptyDVarSet) (Core.AnnCase scrut2 bndr ty alts2)
             | Core.Let bind body =>
                 let body2 := go body in
                 let 'pair bind2 bind_fvs := freeVarsBind1 bind (freeVarsOf body2) in
                 pair bind_fvs (Core.AnnLet bind2 body2)
             | Core.Cast expr co =>
                 let cfvs := Core.emptyDVarSet in
                 let expr2 := go expr in
                 pair (unionFVs (freeVarsOf expr2) cfvs) (Core.AnnCast expr2 (pair cfvs co))
             | Core.Tick tickish expr =>
                 let tickishFVs :=
                   fun arg_23__ =>
                     match arg_23__ with
                     | Core.Breakpoint _ ids => Core.mkDVarSet ids
                     | _ => Core.emptyDVarSet
                     end in
                 let expr2 := go expr in
                 pair (unionFVs (tickishFVs tickish) (freeVarsOf expr2)) (Core.AnnTick tickish
                       expr2)
             | Core.Type_ ty => pair Core.emptyDVarSet (Core.AnnType ty)
             | Core.Coercion co => pair Core.emptyDVarSet (Core.AnnCoercion co)
             end in
  go.

Definition freeVarsBind
   : Core.CoreBind -> DVarSet -> (CoreBindWithFVs * DVarSet)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Core.NonRec binder rhs, body_fvs =>
        let body_fvs2 := delBinderFV binder body_fvs in
        let rhs2 := freeVars rhs in
        pair (Core.AnnNonRec binder rhs2) (unionFVs (unionFVs (freeVarsOf rhs2)
                                                              body_fvs2) (bndrRuleAndUnfoldingVarsDSet binder))
    | Core.Rec binds, body_fvs =>
        let 'pair binders rhss := GHC.List.unzip binds in
        let rhss2 := GHC.Base.map freeVars rhss in
        let rhs_body_fvs :=
          Data.Foldable.foldr (unionFVs GHC.Base.∘ freeVarsOf) body_fvs rhss2 in
        let binders_fvs :=
          FV.fvDVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs binders) in
        let all_fvs := unionFVs rhs_body_fvs binders_fvs in
        pair (Core.AnnRec (GHC.List.zip binders rhss2)) (delBindersFV binders all_fvs)
    end.

(* External variables:
     AnnAlt AnnExpr DVarSet Id bool cons freeVarsBind1 list op_zt__ pair tt
     BasicTypes.Activation Core.AnnApp Core.AnnBind Core.AnnCase Core.AnnCast
     Core.AnnCoercion Core.AnnExpr' Core.AnnLam Core.AnnLet Core.AnnLit
     Core.AnnNonRec Core.AnnRec Core.AnnTick Core.AnnType Core.AnnVar Core.App
     Core.Breakpoint Core.BuiltinRule Core.Case Core.Cast Core.Coercion Core.CoreBind
     Core.CoreBndr Core.CoreExpr Core.CoreRule Core.CoreVect Core.DIdSet
     Core.DTyCoVarSet Core.IdSet Core.Lam Core.Let Core.Lit Core.Mk_Var Core.NoVect
     Core.NonRec Core.Rec Core.Rule Core.Tick Core.Tickish Core.TyCoVarSet Core.Type_
     Core.Var Core.VarSet Core.Vect Core.VectClass Core.VectInst Core.VectType
     Core.delDVarSet Core.emptyDVarSet Core.emptyVarSet Core.isId Core.isLocalId
     Core.isLocalVar Core.mapUnionVarSet Core.mkDVarSet Core.unionDVarSet
     Core.unionDVarSets Core.unitDVarSet Data.Foldable.foldr Data.Tuple.fst FV.FV
     FV.InterestingVarFun FV.delFV FV.emptyFV FV.filterFV FV.fvDVarSet FV.fvVarList
     FV.fvVarSet FV.mapUnionFV FV.mkFVs FV.unionFV FV.unionsFV FV.unitFV GHC.Base.map
     GHC.Base.op_z2218U__ GHC.List.unzip GHC.List.zip Lists.List.map NameSet.NameSet
     NameSet.emptyNameSet NameSet.unionNameSet UniqSet.delOneFromUniqSet_Directly
     Unique.getUnique Util.mapAndUnzip
*)
