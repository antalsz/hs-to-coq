(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import CoreSyn.

(* Converted imports: *)

Require BasicTypes.
Require CoreSyn.
Require Data.Foldable.
Require Data.Tuple.
Require FV.
Require GHC.Base.
Require GHC.List.
Require Lists.List.
Require NameSet.
Require UniqSet.
Require Unique.
Require Var.
Require VarSet.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition FVAnn :=
  VarSet.DVarSet%type.

Definition CoreExprWithFVs' :=
  (CoreSyn.AnnExpr' Var.Id FVAnn)%type.

Definition CoreExprWithFVs :=
  (AnnExpr Var.Id FVAnn)%type.

Definition CoreBindWithFVs :=
  (CoreSyn.AnnBind Var.Id FVAnn)%type.

Definition CoreAltWithFVs :=
  (AnnAlt Var.Id FVAnn)%type.
(* Midamble *)


(* Break mutual recursion *)
Parameter freeVarsBind1 : CoreSyn.CoreBind ->
     VarSet.DVarSet -> (CoreBindWithFVs * VarSet.DVarSet)%type.

(*
NOTE (freeVars): if you try to use a termination edit for freeVars instead of 
the rewrite of unzipAndMap in the edit file, we need to add a type
annotation to fv_alt for the freeVars function to type check. 
The required annotation is 
   fv_alt : Alt CoreBndr -> (VarSet.DVarSet * CoreAltWithFVs)
*)

(* Converted value declarations: *)

Definition aFreeVar : Var.Var -> VarSet.DVarSet :=
  VarSet.unitDVarSet.

Definition bndrRuleAndUnfoldingVarsDSet : Var.Id -> VarSet.DVarSet :=
  fun id => FV.fvDVarSet FV.emptyFV.

Definition freeVarsOf : CoreExprWithFVs -> VarSet.DIdSet :=
  fun '(pair fvs _) => fvs.

Definition freeVarsOfAnn : FVAnn -> VarSet.DIdSet :=
  fun fvs => fvs.

Definition idRuleFVs : Var.Id -> FV.FV :=
  fun id => FV.emptyFV.

Definition idRuleVars : Var.Id -> VarSet.VarSet :=
  fun id => FV.fvVarSet (idRuleFVs id).

Definition idUnfoldingFVs : Var.Id -> FV.FV :=
  fun id => FV.emptyFV.

Definition idUnfoldingVars : Var.Id -> VarSet.VarSet :=
  fun id => FV.fvVarSet (idUnfoldingFVs id).

Definition bndrRuleAndUnfoldingFVs : Var.Id -> FV.FV :=
  fun id =>
    if Var.isId id : bool then FV.unionFV (idRuleFVs id) (idUnfoldingFVs id) else
    FV.emptyFV.

Definition noFVs : VarSet.VarSet :=
  VarSet.emptyVarSet.

Definition orphNamesOfThings {a}
   : (a -> NameSet.NameSet) -> list a -> NameSet.NameSet :=
  fun f =>
    Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ f) NameSet.emptyNameSet.

Definition tickish_fvs : CoreSyn.Tickish Var.Id -> FV.FV :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreSyn.Breakpoint _ ids => FV.mkFVs ids
    | _ => FV.emptyFV
    end.

Definition unionFVs : VarSet.DVarSet -> VarSet.DVarSet -> VarSet.DVarSet :=
  VarSet.unionDVarSet.

Definition unionFVss : list VarSet.DVarSet -> VarSet.DVarSet :=
  VarSet.unionDVarSets.

Definition varTypeTyCoFVs : Var.Var -> FV.FV :=
  fun var => FV.emptyFV.

Definition varTypeTyCoVars : Var.Var -> VarSet.TyCoVarSet :=
  fun var => FV.fvVarSet (varTypeTyCoFVs var).

Definition idFVs : Var.Id -> FV.FV :=
  fun id => FV.unionFV (varTypeTyCoFVs id) FV.emptyFV.

Definition idFreeVars : Var.Id -> VarSet.VarSet :=
  fun id => FV.fvVarSet (idFVs id).

Definition dIdFreeVars : Var.Id -> VarSet.DVarSet :=
  fun id => FV.fvDVarSet (idFVs id).

Definition dVarTypeTyCoVars : Var.Var -> VarSet.DTyCoVarSet :=
  fun var => FV.fvDVarSet (varTypeTyCoFVs var).

Definition delBinderFV : Var.Var -> VarSet.DVarSet -> VarSet.DVarSet :=
  fun b s => unionFVs (VarSet.delDVarSet s b) (dVarTypeTyCoVars b).

Definition delBindersFV : list Var.Var -> VarSet.DVarSet -> VarSet.DVarSet :=
  fun bs fvs => Data.Foldable.foldr delBinderFV fvs bs.

Definition freeVars : CoreSyn.CoreExpr -> CoreExprWithFVs :=
  let go : CoreSyn.CoreExpr -> CoreExprWithFVs :=
    fix go arg_0__
          := match arg_0__ with
             | CoreSyn.Var v =>
                 let ty_fvs := dVarTypeTyCoVars v in
                 if Var.isLocalVar v : bool
                 then pair (unionFVs (aFreeVar v) ty_fvs) (CoreSyn.AnnVar v) else
                 pair VarSet.emptyDVarSet (CoreSyn.AnnVar v)
             | CoreSyn.Lit lit => pair VarSet.emptyDVarSet (CoreSyn.AnnLit lit)
             | CoreSyn.Lam b body =>
                 let b_ty := tt in
                 let b_fvs := VarSet.emptyDVarSet in
                 let '(pair body_fvs _ as body') := go body in
                 pair (unionFVs b_fvs (delBinderFV b body_fvs)) (CoreSyn.AnnLam b body')
             | CoreSyn.App fun_ arg =>
                 let arg' := go arg in
                 let fun' := go fun_ in
                 pair (unionFVs (freeVarsOf fun') (freeVarsOf arg')) (CoreSyn.AnnApp fun' arg')
             | CoreSyn.Case scrut bndr ty alts =>
                 let fv_alt :=
                   fun '(pair (pair con args) rhs) =>
                     let rhs2 := go rhs in
                     pair (delBindersFV args (freeVarsOf rhs2)) (pair (pair con args) rhs2) in
                 let 'pair alts_fvs_s alts2 := GHC.List.unzip (Lists.List.map fv_alt alts) in
                 let alts_fvs := unionFVss alts_fvs_s in
                 let scrut2 := go scrut in
                 pair (unionFVs (unionFVs (delBinderFV bndr alts_fvs) (freeVarsOf scrut2))
                                VarSet.emptyDVarSet) (CoreSyn.AnnCase scrut2 bndr ty alts2)
             | CoreSyn.Let bind body =>
                 let body2 := go body in
                 let 'pair bind2 bind_fvs := freeVarsBind1 bind (freeVarsOf body2) in
                 pair bind_fvs (CoreSyn.AnnLet bind2 body2)
             | CoreSyn.Cast expr co =>
                 let cfvs := VarSet.emptyDVarSet in
                 let expr2 := go expr in
                 pair (unionFVs (freeVarsOf expr2) cfvs) (CoreSyn.AnnCast expr2 (pair cfvs co))
             | CoreSyn.Tick tickish expr =>
                 let tickishFVs :=
                   fun arg_23__ =>
                     match arg_23__ with
                     | CoreSyn.Breakpoint _ ids => VarSet.mkDVarSet ids
                     | _ => VarSet.emptyDVarSet
                     end in
                 let expr2 := go expr in
                 pair (unionFVs (tickishFVs tickish) (freeVarsOf expr2)) (CoreSyn.AnnTick tickish
                       expr2)
             | CoreSyn.Type_ ty => pair VarSet.emptyDVarSet (CoreSyn.AnnType ty)
             | CoreSyn.Coercion co => pair VarSet.emptyDVarSet (CoreSyn.AnnCoercion co)
             end in
  go.

Definition freeVarsBind
   : CoreSyn.CoreBind ->
     VarSet.DVarSet -> (CoreBindWithFVs * VarSet.DVarSet)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CoreSyn.NonRec binder rhs, body_fvs =>
        let body_fvs2 := delBinderFV binder body_fvs in
        let rhs2 := freeVars rhs in
        pair (CoreSyn.AnnNonRec binder rhs2) (unionFVs (unionFVs (freeVarsOf rhs2)
                                                                 body_fvs2) (bndrRuleAndUnfoldingVarsDSet binder))
    | CoreSyn.Rec binds, body_fvs =>
        let 'pair binders rhss := GHC.List.unzip binds in
        let rhss2 := GHC.Base.map freeVars rhss in
        let rhs_body_fvs :=
          Data.Foldable.foldr (unionFVs GHC.Base.∘ freeVarsOf) body_fvs rhss2 in
        let binders_fvs :=
          FV.fvDVarSet (FV.mapUnionFV bndrRuleAndUnfoldingFVs binders) in
        let all_fvs := unionFVs rhs_body_fvs binders_fvs in
        pair (CoreSyn.AnnRec (GHC.List.zip binders rhss2)) (delBindersFV binders
              all_fvs)
    end.

Definition addBndr : CoreSyn.CoreBndr -> FV.FV -> FV.FV :=
  fun bndr fv fv_cand in_scope acc =>
    (FV.unionFV (varTypeTyCoFVs bndr) (FV.delFV bndr fv)) fv_cand in_scope acc.

Definition addBndrs : list CoreSyn.CoreBndr -> FV.FV -> FV.FV :=
  fun bndrs fv => Data.Foldable.foldr addBndr fv bndrs.

Definition expr_fvs : CoreSyn.CoreExpr -> FV.FV :=
  fix expr_fvs arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | CoreSyn.Type_ ty, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
           | CoreSyn.Coercion co, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
           | CoreSyn.Var var, fv_cand, in_scope, acc => FV.unitFV var fv_cand in_scope acc
           | CoreSyn.Lit _, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
           | CoreSyn.Tick t expr, fv_cand, in_scope, acc =>
               (FV.unionFV (tickish_fvs t) (expr_fvs expr)) fv_cand in_scope acc
           | CoreSyn.App fun_ arg, fv_cand, in_scope, acc =>
               (FV.unionFV (expr_fvs fun_) (expr_fvs arg)) fv_cand in_scope acc
           | CoreSyn.Lam bndr body, fv_cand, in_scope, acc =>
               addBndr bndr (expr_fvs body) fv_cand in_scope acc
           | CoreSyn.Cast expr co, fv_cand, in_scope, acc =>
               (FV.unionFV (expr_fvs expr) FV.emptyFV) fv_cand in_scope acc
           | CoreSyn.Case scrut bndr ty alts, fv_cand, in_scope, acc =>
               let alt_fvs :=
                 fun '(pair (pair _ bndrs) rhs) => addBndrs bndrs (expr_fvs rhs) in
               (FV.unionFV (FV.unionFV (expr_fvs scrut) FV.emptyFV) (addBndr bndr (FV.unionsFV
                                                                                   (Lists.List.map alt_fvs alts))))
               fv_cand in_scope acc
           | CoreSyn.Let (CoreSyn.NonRec bndr rhs) body, fv_cand, in_scope, acc =>
               (FV.unionFV (FV.unionFV (expr_fvs rhs) FV.emptyFV) (addBndr bndr (expr_fvs
                                                                                 body))) fv_cand in_scope acc
           | CoreSyn.Let (CoreSyn.Rec pairs) body, fv_cand, in_scope, acc =>
               addBndrs (GHC.Base.map Data.Tuple.fst pairs) (FV.unionFV (FV.unionsFV
                                                                         (Lists.List.map (fun '(pair bndr rhs) =>
                                                                                            expr_fvs rhs) pairs))
                                                                        (expr_fvs body)) fv_cand in_scope acc
           end.

Definition exprFVs : CoreSyn.CoreExpr -> FV.FV :=
  FV.filterFV Var.isLocalVar GHC.Base.∘ expr_fvs.

Definition exprFreeVars : CoreSyn.CoreExpr -> VarSet.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsDSet : CoreSyn.CoreExpr -> VarSet.DVarSet :=
  FV.fvDVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsList : CoreSyn.CoreExpr -> list Var.Var :=
  FV.fvVarList GHC.Base.∘ exprFVs.

Definition exprsFVs : list CoreSyn.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV exprFVs exprs.

Definition exprsFreeVars : list CoreSyn.CoreExpr -> VarSet.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprsFVs.

Definition exprsFreeVarsList : list CoreSyn.CoreExpr -> list Var.Var :=
  FV.fvVarList GHC.Base.∘ exprsFVs.

Definition exprSomeFreeVars
   : FV.InterestingVarFun -> CoreSyn.CoreExpr -> VarSet.VarSet :=
  fun fv_cand e => FV.fvVarSet (FV.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIds : CoreSyn.CoreExpr -> VarSet.IdSet :=
  exprSomeFreeVars Var.isLocalId.

Definition exprSomeFreeVarsDSet
   : FV.InterestingVarFun -> CoreSyn.CoreExpr -> VarSet.DVarSet :=
  fun fv_cand e => FV.fvDVarSet (FV.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIdsDSet : CoreSyn.CoreExpr -> VarSet.DIdSet :=
  exprSomeFreeVarsDSet Var.isLocalId.

Definition exprSomeFreeVarsList
   : FV.InterestingVarFun -> CoreSyn.CoreExpr -> list Var.Var :=
  fun fv_cand e => FV.fvVarList (FV.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIdsList : CoreSyn.CoreExpr -> list Var.Id :=
  exprSomeFreeVarsList Var.isLocalId.

Definition exprsSomeFreeVars
   : FV.InterestingVarFun -> list CoreSyn.CoreExpr -> VarSet.VarSet :=
  fun fv_cand es => FV.fvVarSet (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs es)).

Definition exprsSomeFreeVarsDSet
   : FV.InterestingVarFun -> list CoreSyn.CoreExpr -> VarSet.DVarSet :=
  fun fv_cand e => FV.fvDVarSet (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs e)).

Definition exprsFreeIdsDSet : list CoreSyn.CoreExpr -> VarSet.DIdSet :=
  exprsSomeFreeVarsDSet Var.isLocalId.

Definition exprsSomeFreeVarsList
   : FV.InterestingVarFun -> list CoreSyn.CoreExpr -> list Var.Var :=
  fun fv_cand es =>
    FV.fvVarList (FV.filterFV fv_cand (FV.mapUnionFV expr_fvs es)).

Definition exprsFreeIdsList : list CoreSyn.CoreExpr -> list Var.Id :=
  exprsSomeFreeVarsList Var.isLocalId.

Definition exprs_fvs : list CoreSyn.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV expr_fvs exprs.

Definition ruleFVs : CoreSyn.CoreRule -> FV.FV :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreSyn.BuiltinRule _ _ _ _ => FV.emptyFV
    | CoreSyn.Rule _ _ _do_not_include _ bndrs args rhs _ _ _ _ =>
        FV.filterFV Var.isLocalVar (addBndrs bndrs (exprs_fvs (cons rhs args)))
    end.

Definition ruleFreeVars : CoreSyn.CoreRule -> VarSet.VarSet :=
  FV.fvVarSet GHC.Base.∘ ruleFVs.

Definition rulesFreeVars : list CoreSyn.CoreRule -> VarSet.VarSet :=
  fun rules => VarSet.mapUnionVarSet ruleFreeVars rules.

Definition rulesFVs : list CoreSyn.CoreRule -> FV.FV :=
  FV.mapUnionFV ruleFVs.

Definition rulesFreeVarsDSet : list CoreSyn.CoreRule -> VarSet.DVarSet :=
  fun rules => FV.fvDVarSet (rulesFVs rules).

Definition ruleLhsFVIds : CoreSyn.CoreRule -> FV.FV :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreSyn.BuiltinRule _ _ _ _ => FV.emptyFV
    | CoreSyn.Rule _ _ _ _ bndrs args _ _ _ _ _ =>
        FV.filterFV Var.isLocalId (addBndrs bndrs (exprs_fvs args))
    end.

Definition ruleLhsFreeIds : CoreSyn.CoreRule -> VarSet.VarSet :=
  FV.fvVarSet GHC.Base.∘ ruleLhsFVIds.

Definition ruleLhsFreeIdsList : CoreSyn.CoreRule -> list Var.Var :=
  FV.fvVarList GHC.Base.∘ ruleLhsFVIds.

Definition idRuleRhsVars
   : (BasicTypes.Activation -> bool) -> Var.Id -> VarSet.VarSet :=
  fun is_active id =>
    let get_fvs :=
      fun arg_0__ =>
        match arg_0__ with
        | CoreSyn.Rule _ act fn _ bndrs _ rhs _ _ _ _ =>
            let fvs :=
              FV.fvVarSet (FV.filterFV Var.isLocalVar (addBndrs bndrs (expr_fvs rhs))) in
            if is_active act : bool
            then UniqSet.delOneFromUniqSet_Directly fvs (Unique.getUnique fn) else
            noFVs
        | _ => noFVs
        end in
    VarSet.emptyVarSet.

Definition rhs_fvs : (Var.Id * CoreSyn.CoreExpr)%type -> FV.FV :=
  fun '(pair bndr rhs) => FV.unionFV (expr_fvs rhs) FV.emptyFV.

Definition bindFreeVars : CoreSyn.CoreBind -> VarSet.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreSyn.NonRec b r =>
        FV.fvVarSet (FV.filterFV Var.isLocalVar (rhs_fvs (pair b r)))
    | CoreSyn.Rec prs =>
        FV.fvVarSet (FV.filterFV Var.isLocalVar (addBndrs (GHC.Base.map Data.Tuple.fst
                                                           prs) (FV.mapUnionFV rhs_fvs prs)))
    end.

Definition ruleRhsFreeVars : CoreSyn.CoreRule -> VarSet.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreSyn.BuiltinRule _ _ _ _ => noFVs
    | CoreSyn.Rule _ _ _ _ bndrs _ rhs _ _ _ _ =>
        FV.fvVarSet (FV.filterFV Var.isLocalVar (addBndrs bndrs (expr_fvs rhs)))
    end.

Definition stableUnfoldingFVs : CoreSyn.Unfolding -> option FV.FV :=
  fun unf =>
    let j_1__ :=
      match unf with
      | CoreSyn.DFunUnfolding bndrs _ args =>
          Some (FV.filterFV Var.isLocalVar (FV.delFVs (VarSet.mkVarSet bndrs) (exprs_fvs
                                                       args)))
      | _other => None
      end in
    match unf with
    | CoreSyn.CoreUnfolding rhs src _ _ _ _ _ _ =>
        if CoreSyn.isStableSource src : bool
        then Some (FV.filterFV Var.isLocalVar (expr_fvs rhs)) else
        j_1__
    | _ => j_1__
    end.

Definition stableUnfoldingVars : CoreSyn.Unfolding -> option VarSet.VarSet :=
  fun unf => GHC.Base.fmap FV.fvVarSet (stableUnfoldingFVs unf).

Definition vectsFreeVars : list CoreSyn.CoreVect -> VarSet.VarSet :=
  let vectFreeVars :=
    fun arg_0__ =>
      match arg_0__ with
      | CoreSyn.Vect _ rhs => FV.fvVarSet (FV.filterFV Var.isLocalId (expr_fvs rhs))
      | CoreSyn.NoVect _ => noFVs
      | CoreSyn.VectType _ _ _ => noFVs
      | CoreSyn.VectClass _ => noFVs
      | CoreSyn.VectInst _ => noFVs
      end in
  VarSet.mapUnionVarSet vectFreeVars.

(* External variables:
     AnnAlt AnnExpr None Some bool cons freeVarsBind1 list op_zt__ option pair tt
     BasicTypes.Activation CoreSyn.AnnApp CoreSyn.AnnBind CoreSyn.AnnCase
     CoreSyn.AnnCast CoreSyn.AnnCoercion CoreSyn.AnnExpr' CoreSyn.AnnLam
     CoreSyn.AnnLet CoreSyn.AnnLit CoreSyn.AnnNonRec CoreSyn.AnnRec CoreSyn.AnnTick
     CoreSyn.AnnType CoreSyn.AnnVar CoreSyn.App CoreSyn.Breakpoint
     CoreSyn.BuiltinRule CoreSyn.Case CoreSyn.Cast CoreSyn.Coercion CoreSyn.CoreBind
     CoreSyn.CoreBndr CoreSyn.CoreExpr CoreSyn.CoreRule CoreSyn.CoreUnfolding
     CoreSyn.CoreVect CoreSyn.DFunUnfolding CoreSyn.Lam CoreSyn.Let CoreSyn.Lit
     CoreSyn.NoVect CoreSyn.NonRec CoreSyn.Rec CoreSyn.Rule CoreSyn.Tick
     CoreSyn.Tickish CoreSyn.Type_ CoreSyn.Unfolding CoreSyn.Var CoreSyn.Vect
     CoreSyn.VectClass CoreSyn.VectInst CoreSyn.VectType CoreSyn.isStableSource
     Data.Foldable.foldr Data.Tuple.fst FV.FV FV.InterestingVarFun FV.delFV FV.delFVs
     FV.emptyFV FV.filterFV FV.fvDVarSet FV.fvVarList FV.fvVarSet FV.mapUnionFV
     FV.mkFVs FV.unionFV FV.unionsFV FV.unitFV GHC.Base.fmap GHC.Base.map
     GHC.Base.op_z2218U__ GHC.List.unzip GHC.List.zip Lists.List.map NameSet.NameSet
     NameSet.emptyNameSet NameSet.unionNameSet UniqSet.delOneFromUniqSet_Directly
     Unique.getUnique Var.Id Var.Var Var.isId Var.isLocalId Var.isLocalVar
     VarSet.DIdSet VarSet.DTyCoVarSet VarSet.DVarSet VarSet.IdSet VarSet.TyCoVarSet
     VarSet.VarSet VarSet.delDVarSet VarSet.emptyDVarSet VarSet.emptyVarSet
     VarSet.mapUnionVarSet VarSet.mkDVarSet VarSet.mkVarSet VarSet.unionDVarSet
     VarSet.unionDVarSets VarSet.unitDVarSet
*)
