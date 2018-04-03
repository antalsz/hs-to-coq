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

Require CoreSyn.
Require CoreType.
Require Data.Foldable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require Id.
Require IdInfo2.
Require Maybes.
Require Name.
Require NameSet.
Require Panic.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition FVAnn :=
  CoreType.DVarSet%type.

Definition CoreExprWithFVs' :=
  (CoreSyn.AnnExpr' CoreType.Id FVAnn)%type.

Definition CoreExprWithFVs :=
  (AnnExpr CoreType.Id FVAnn)%type.

Definition CoreBindWithFVs :=
  (CoreSyn.AnnBind CoreType.Id FVAnn)%type.

Definition CoreAltWithFVs :=
  (AnnAlt CoreType.Id FVAnn)%type.
(* Midamble *)

Require Import Var.

Parameter tickish_fvs : CoreSyn.Tickish Var.Id -> FV.FV.

(* Very bad treatment of guards. Plus needs a lot from Coercion/Type/TyCoRep *)
Parameter freeVars : CoreSyn.CoreExpr -> CoreExprWithFVs.
Parameter expr_fvs : CoreSyn.CoreExpr -> FV.FV.

Parameter exprOrphNames : CoreSyn.CoreExpr -> NameSet.NameSet.
(*
Fixpoint exprOrphNames (e : CoreSyn.CoreExpr) : NameSet.NameSet :=
    let go_alt :=
      fun arg_13__ => match arg_13__ with | pair (pair _ _) r => exprOrphNames r end in
    let exprsOrphNames : list CoreSyn.CoreExpr -> NameSet.NameSet :=
        fun es =>
          Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ exprOrphNames)
                              NameSet.emptyNameSet es in
    match e with
    | CoreSyn.Var v => let n := Id.idName v in
                      if Name.isExternalName n : bool
                      then NameSet.unitNameSet n
                      else NameSet.emptyNameSet
    | CoreSyn.Lit _ => NameSet.emptyNameSet
    | CoreSyn.Type_ ty => orphNamesOfType ty
    | CoreSyn.Coercion co => orphNamesOfCo co
    | CoreSyn.App e1 e2 => NameSet.unionNameSet (exprOrphNames e1) (exprOrphNames e2)
    | CoreSyn.Lam v e => NameSet.delFromNameSet (exprOrphNames e) (Id.idName v)
    | CoreSyn.Tick _ e => exprOrphNames e
    | CoreSyn.Cast e co => NameSet.unionNameSet (exprOrphNames e) (orphNamesOfCo co)
    | CoreSyn.Let (CoreSyn.NonRec _ r) e => NameSet.unionNameSet (exprOrphNames e) (exprOrphNames r)
    | CoreSyn.Let (CoreSyn.Rec prs) e => (exprOrphNames e)
(*      NameSet.unionNameSet (exprsOrphNames
                              (GHC.Base.map Data.Tuple.snd prs))  *)
    | CoreSyn.Case e _ ty as_ => NameSet.unionNameSet
                                  (NameSet.unionNameSet (exprOrphNames e)
                                                        (orphNamesOfType ty))
                                  (NameSet.unionNameSets (GHC.Base.map go_alt as_))
    end. *)

Parameter orphNamesOfCo : Core.Coercion -> NameSet.NameSet.
(*
Fixpoint orphNamesOfCo (arg_0__ : Core.Coercion): NameSet.NameSet :=
  let  orphNamesOfCos : list Core.Coercion -> NameSet.NameSet :=
       orphNamesOfThings orphNamesOfCo in
  let orphNamesOfProv : Core.UnivCoProvenance -> NameSet.NameSet :=
  fun arg_0__ =>
    match arg_0__ with
      | Core.UnsafeCoerceProv => NameSet.emptyNameSet
      | Core.PhantomProv co => orphNamesOfCo co
      | Core.ProofIrrelProv co => orphNamesOfCo co
      | Core.PluginProv _ => NameSet.emptyNameSet
      | Core.HoleProv _ => NameSet.emptyNameSet
    end in

  match arg_0__ with
             | Core.Refl _ ty => orphNamesOfType ty
             | Core.TyConAppCo _ tc cos => NameSet.unionNameSet (NameSet.unitNameSet
                                                                (Name.getName tc)) (orphNamesOfCos cos)
             | Core.AppCo co1 co2 => NameSet.unionNameSet (orphNamesOfCo co1) (orphNamesOfCo
                                                          co2)
             | Core.ForAllCo _ kind_co co => NameSet.unionNameSet (orphNamesOfCo kind_co)
                                                                  (orphNamesOfCo co)
             | Core.CoVarCo _ => NameSet.emptyNameSet
             | Core.AxiomInstCo con _ cos => NameSet.unionNameSet (orphNamesOfCoCon con)
                                                                  (orphNamesOfCos cos)
             | Core.UnivCo p _ t1 t2 => NameSet.unionNameSet (NameSet.unionNameSet
                                                             (orphNamesOfProv p) (orphNamesOfType t1)) (orphNamesOfType
                                                             t2)
             | Core.SymCo co => orphNamesOfCo co
             | Core.TransCo co1 co2 => NameSet.unionNameSet (orphNamesOfCo co1)
                                                            (orphNamesOfCo co2)
             | Core.NthCo _ co => orphNamesOfCo co
             | Core.LRCo _ co => orphNamesOfCo co
             | Core.InstCo co arg => NameSet.unionNameSet (orphNamesOfCo co) (orphNamesOfCo
                                                          arg)
             | Core.CoherenceCo co1 co2 => NameSet.unionNameSet (orphNamesOfCo co1)
                                                                (orphNamesOfCo co2)
             | Core.KindCo co => orphNamesOfCo co
             | Core.SubCo co => orphNamesOfCo co
             | Core.AxiomRuleCo _ cs => orphNamesOfCos cs
           end.
*)
(* Converted value declarations: *)

Definition aFreeVar : CoreType.Var -> CoreType.DVarSet :=
  CoreType.unitDVarSet.

Definition exprFVs : CoreSyn.CoreExpr -> CoreType.FV :=
  CoreType.filterFV CoreType.isLocalVar GHC.Base.∘ expr_fvs.

Definition exprFreeVars : CoreSyn.CoreExpr -> CoreType.VarSet :=
  CoreType.fvVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsDSet : CoreSyn.CoreExpr -> CoreType.DVarSet :=
  CoreType.fvDVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsList : CoreSyn.CoreExpr -> list CoreType.Var :=
  CoreType.fvVarList GHC.Base.∘ exprFVs.

Definition exprsFVs : list CoreSyn.CoreExpr -> CoreType.FV :=
  fun exprs => CoreType.mapUnionFV exprFVs exprs.

Definition exprsFreeVars : list CoreSyn.CoreExpr -> CoreType.VarSet :=
  CoreType.fvVarSet GHC.Base.∘ exprsFVs.

Definition exprsFreeVarsList : list CoreSyn.CoreExpr -> list CoreType.Var :=
  CoreType.fvVarList GHC.Base.∘ exprsFVs.

Definition exprSomeFreeVars
   : CoreType.InterestingVarFun -> CoreSyn.CoreExpr -> CoreType.VarSet :=
  fun fv_cand e => CoreType.fvVarSet (CoreType.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIds : CoreSyn.CoreExpr -> CoreType.IdSet :=
  exprSomeFreeVars CoreType.isLocalId.

Definition exprSomeFreeVarsDSet
   : CoreType.InterestingVarFun -> CoreSyn.CoreExpr -> CoreType.DVarSet :=
  fun fv_cand e => CoreType.fvDVarSet (CoreType.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIdsDSet : CoreSyn.CoreExpr -> CoreType.DIdSet :=
  exprSomeFreeVarsDSet CoreType.isLocalId.

Definition exprSomeFreeVarsList
   : CoreType.InterestingVarFun -> CoreSyn.CoreExpr -> list CoreType.Var :=
  fun fv_cand e => CoreType.fvVarList (CoreType.filterFV fv_cand (expr_fvs e)).

Definition exprFreeIdsList : CoreSyn.CoreExpr -> list CoreType.Id :=
  exprSomeFreeVarsList CoreType.isLocalId.

Definition exprsOrphNames : list CoreSyn.CoreExpr -> NameSet.NameSet :=
  fun es =>
    Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ exprOrphNames)
    NameSet.emptyNameSet es.

Definition exprsSomeFreeVars
   : CoreType.InterestingVarFun -> list CoreSyn.CoreExpr -> CoreType.VarSet :=
  fun fv_cand es =>
    CoreType.fvVarSet (CoreType.filterFV fv_cand (CoreType.mapUnionFV expr_fvs es)).

Definition exprsSomeFreeVarsDSet
   : CoreType.InterestingVarFun -> list CoreSyn.CoreExpr -> CoreType.DVarSet :=
  fun fv_cand e =>
    CoreType.fvDVarSet (CoreType.filterFV fv_cand (CoreType.mapUnionFV expr_fvs e)).

Definition exprsFreeIdsDSet : list CoreSyn.CoreExpr -> CoreType.DIdSet :=
  exprsSomeFreeVarsDSet CoreType.isLocalId.

Definition exprsSomeFreeVarsList
   : CoreType.InterestingVarFun -> list CoreSyn.CoreExpr -> list CoreType.Var :=
  fun fv_cand es =>
    CoreType.fvVarList (CoreType.filterFV fv_cand (CoreType.mapUnionFV expr_fvs
                                                                       es)).

Definition exprsFreeIdsList : list CoreSyn.CoreExpr -> list CoreType.Id :=
  exprsSomeFreeVarsList CoreType.isLocalId.

Definition exprs_fvs : list CoreSyn.CoreExpr -> CoreType.FV :=
  fun exprs => CoreType.mapUnionFV expr_fvs exprs.

Definition freeVarsOf : CoreExprWithFVs -> CoreType.DIdSet :=
  fun arg_0__ => let 'pair fvs _ := arg_0__ in fvs.

Definition freeVarsOfAnn : FVAnn -> CoreType.DIdSet :=
  fun fvs => fvs.

Definition idRuleFVs : CoreType.Id -> CoreType.FV :=
  fun id =>
    if andb Util.debugIsOn (negb (CoreType.isId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreFVs.hs")
          #645)
    else CoreType.mkFVs (CoreType.dVarSetElems (IdInfo2.ruleInfoFreeVars
                                                (Id.idSpecialisation id))).

Definition idRuleVars : CoreType.Id -> CoreType.VarSet :=
  fun id => CoreType.fvVarSet (idRuleFVs id).

Axiom idRuleRhsVars : forall {A : Type}, A.

(* Translating `idRuleRhsVars' failed: using a record pattern for the unknown
   constructor `Rule' unsupported *)

Definition noFVs : CoreType.VarSet :=
  CoreType.emptyVarSet.

Definition vectsFreeVars : list CoreSyn.CoreVect -> CoreType.VarSet :=
  let vectFreeVars :=
    fun arg_0__ =>
      match arg_0__ with
      | CoreSyn.Vect _ rhs =>
          CoreType.fvVarSet (CoreType.filterFV CoreType.isLocalId (expr_fvs rhs))
      | CoreSyn.NoVect _ => noFVs
      | CoreSyn.VectType _ _ _ => noFVs
      | CoreSyn.VectClass _ => noFVs
      | CoreSyn.VectInst _ => noFVs
      end in
  CoreType.mapUnionVarSet vectFreeVars.

Axiom orphNamesOfCoAxBranch : forall {A : Type}, A.

Definition orphNamesOfCoAxBranches {br}
   : CoreType.Branches br -> NameSet.NameSet :=
  Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ orphNamesOfCoAxBranch)
  NameSet.emptyNameSet GHC.Base.∘
  CoreType.fromBranches.

(* Translating `orphNamesOfCoAxBranch' failed: using a record pattern for the
   unknown constructor `CoAxBranch' unsupported *)

Axiom orphNamesOfCoCon : forall {A : Type}, A.

(* Translating `orphNamesOfCoCon' failed: using a record pattern for the unknown
   constructor `CoAxiom' unsupported *)

Definition orphNamesOfProv : CoreType.UnivCoProvenance -> NameSet.NameSet :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreType.UnsafeCoerceProv => NameSet.emptyNameSet
    | CoreType.PhantomProv co => orphNamesOfCo co
    | CoreType.ProofIrrelProv co => orphNamesOfCo co
    | CoreType.PluginProv _ => NameSet.emptyNameSet
    end.

Definition orphNamesOfThings {a}
   : (a -> NameSet.NameSet) -> list a -> NameSet.NameSet :=
  fun f =>
    Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ f) NameSet.emptyNameSet.

Definition orphNamesOfCos : list CoreType.Coercion -> NameSet.NameSet :=
  orphNamesOfThings orphNamesOfCo.

Definition orphNamesOfTyCon : CoreType.TyCon -> NameSet.NameSet :=
  fun tycon =>
    NameSet.unionNameSet (NameSet.unitNameSet (Name.getName tycon))
                         (match CoreType.tyConClass_maybe tycon with
                          | None => NameSet.emptyNameSet
                          | Some cls => NameSet.unitNameSet (Name.getName cls)
                          end).

Axiom orphNamesOfType : forall {A : Type}, A.

Definition orphNamesOfTypes : list CoreType.Type_ -> NameSet.NameSet :=
  orphNamesOfThings orphNamesOfType.

Definition orphNamesOfAxiom {br} : CoreType.CoAxiom br -> NameSet.NameSet :=
  fun axiom =>
    NameSet.extendNameSet (orphNamesOfTypes (Data.Foldable.concatMap
                                             CoreType.coAxBranchLHS (CoreType.fromBranches (CoreType.coAxiomBranches
                                                                                            axiom)))) (Name.getName
                           (CoreType.coAxiomTyCon axiom)).

(* Translating `orphNamesOfType' failed: using a record pattern for the unknown
   constructor `LitTy' unsupported *)

Axiom ruleFVs : forall {A : Type}, A.

Definition ruleFreeVars : CoreSyn.CoreRule -> CoreType.VarSet :=
  CoreType.fvVarSet GHC.Base.∘ ruleFVs.

Definition rulesFreeVars : list CoreSyn.CoreRule -> CoreType.VarSet :=
  fun rules => CoreType.mapUnionVarSet ruleFreeVars rules.

Definition rulesFVs : list CoreSyn.CoreRule -> CoreType.FV :=
  CoreType.mapUnionFV ruleFVs.

Definition rulesFreeVarsDSet : list CoreSyn.CoreRule -> CoreType.DVarSet :=
  fun rules => CoreType.fvDVarSet (rulesFVs rules).

(* Translating `ruleFVs' failed: using a record pattern for the unknown
   constructor `BuiltinRule' unsupported *)

Axiom ruleLhsFVIds : forall {A : Type}, A.

Definition ruleLhsFreeIds : CoreSyn.CoreRule -> CoreType.VarSet :=
  CoreType.fvVarSet GHC.Base.∘ ruleLhsFVIds.

Definition ruleLhsFreeIdsList : CoreSyn.CoreRule -> list CoreType.Var :=
  CoreType.fvVarList GHC.Base.∘ ruleLhsFVIds.

(* Translating `ruleLhsFVIds' failed: using a record pattern for the unknown
   constructor `BuiltinRule' unsupported *)

Axiom ruleRhsFreeVars : forall {A : Type}, A.

(* Translating `ruleRhsFreeVars' failed: using a record pattern for the unknown
   constructor `BuiltinRule' unsupported *)

Axiom stableUnfoldingFVs : forall {A : Type}, A.

Definition stableUnfoldingVars : CoreSyn.Unfolding -> option CoreType.VarSet :=
  fun unf => GHC.Base.fmap CoreType.fvVarSet (stableUnfoldingFVs unf).

Definition idUnfoldingFVs : CoreType.Id -> CoreType.FV :=
  fun id =>
    Maybes.orElse (stableUnfoldingFVs (Id.realIdUnfolding id)) CoreType.emptyFV.

Definition idUnfoldingVars : CoreType.Id -> CoreType.VarSet :=
  fun id => CoreType.fvVarSet (idUnfoldingFVs id).

Definition bndrRuleAndUnfoldingFVs : CoreType.Id -> CoreType.FV :=
  fun id =>
    if CoreType.isId id : bool
    then CoreType.unionFV (idRuleFVs id) (idUnfoldingFVs id) else
    CoreType.emptyFV.

Definition bndrRuleAndUnfoldingVarsDSet : CoreType.Id -> CoreType.DVarSet :=
  fun id => CoreType.fvDVarSet (bndrRuleAndUnfoldingFVs id).

Definition rhs_fvs : (CoreType.Id * CoreSyn.CoreExpr)%type -> CoreType.FV :=
  fun arg_0__ =>
    let 'pair bndr rhs := arg_0__ in
    CoreType.unionFV (expr_fvs rhs) (bndrRuleAndUnfoldingFVs bndr).

(* Translating `stableUnfoldingFVs' failed: using a record pattern for the
   unknown constructor `CoreUnfolding' unsupported *)

Definition unionFVs
   : CoreType.DVarSet -> CoreType.DVarSet -> CoreType.DVarSet :=
  CoreType.unionDVarSet.

Definition unionFVss : list CoreType.DVarSet -> CoreType.DVarSet :=
  CoreType.unionDVarSets.

Definition varTypeTyCoFVs : CoreType.Var -> CoreType.FV :=
  fun var => CoreType.tyCoFVsOfType (CoreType.varType var).

Definition varTypeTyCoVars : CoreType.Var -> CoreType.TyCoVarSet :=
  fun var => CoreType.fvVarSet (varTypeTyCoFVs var).

Definition dVarTypeTyCoVars : CoreType.Var -> CoreType.DTyCoVarSet :=
  fun var => CoreType.fvDVarSet (varTypeTyCoFVs var).

Definition delBinderFV : CoreType.Var -> CoreType.DVarSet -> CoreType.DVarSet :=
  fun b s => unionFVs (CoreType.delDVarSet s b) (dVarTypeTyCoVars b).

Definition delBindersFV
   : list CoreType.Var -> CoreType.DVarSet -> CoreType.DVarSet :=
  fun bs fvs => Data.Foldable.foldr delBinderFV fvs bs.

Definition freeVarsBind
   : CoreSyn.CoreBind ->
     CoreType.DVarSet -> (CoreBindWithFVs * CoreType.DVarSet)%type :=
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
          CoreType.fvDVarSet (CoreType.mapUnionFV bndrRuleAndUnfoldingFVs binders) in
        let all_fvs := unionFVs rhs_body_fvs binders_fvs in
        pair (CoreSyn.AnnRec (GHC.List.zip binders rhss2)) (delBindersFV binders
              all_fvs)
    end.

Definition idFVs : CoreType.Id -> CoreType.FV :=
  fun id =>
    if andb Util.debugIsOn (negb (CoreType.isId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreFVs.hs")
          #629)
    else CoreType.unionFV (varTypeTyCoFVs id) (bndrRuleAndUnfoldingFVs id).

Definition dIdFreeVars : CoreType.Id -> CoreType.DVarSet :=
  fun id => CoreType.fvDVarSet (idFVs id).

Definition idFreeVars : CoreType.Id -> CoreType.VarSet :=
  fun id =>
    if andb Util.debugIsOn (negb (CoreType.isId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreFVs.hs")
          #622)
    else CoreType.fvVarSet (idFVs id).

Definition addBndr : CoreSyn.CoreBndr -> CoreType.FV -> CoreType.FV :=
  fun bndr fv fv_cand in_scope acc =>
    (CoreType.unionFV (varTypeTyCoFVs bndr) (CoreType.delFV bndr fv)) fv_cand
    in_scope acc.

Definition addBndrs : list CoreSyn.CoreBndr -> CoreType.FV -> CoreType.FV :=
  fun bndrs fv => Data.Foldable.foldr addBndr fv bndrs.

Definition bindFreeVars : CoreSyn.CoreBind -> CoreType.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreSyn.NonRec b r =>
        CoreType.fvVarSet (CoreType.filterFV CoreType.isLocalVar (rhs_fvs (pair b r)))
    | CoreSyn.Rec prs =>
        CoreType.fvVarSet (CoreType.filterFV CoreType.isLocalVar (addBndrs (GHC.Base.map
                                                                            Data.Tuple.fst prs) (CoreType.mapUnionFV
                                                                            rhs_fvs prs)))
    end.

(* External variables:
     AnnAlt AnnExpr None Some andb bool exprOrphNames expr_fvs freeVars list negb
     op_zt__ option orphNamesOfCo pair CoreSyn.AnnBind CoreSyn.AnnExpr'
     CoreSyn.AnnNonRec CoreSyn.AnnRec CoreSyn.CoreBind CoreSyn.CoreBndr
     CoreSyn.CoreExpr CoreSyn.CoreRule CoreSyn.CoreVect CoreSyn.NoVect CoreSyn.NonRec
     CoreSyn.Rec CoreSyn.Unfolding CoreSyn.Vect CoreSyn.VectClass CoreSyn.VectInst
     CoreSyn.VectType CoreType.Branches CoreType.CoAxiom CoreType.Coercion
     CoreType.DIdSet CoreType.DTyCoVarSet CoreType.DVarSet CoreType.FV CoreType.Id
     CoreType.IdSet CoreType.InterestingVarFun CoreType.PhantomProv
     CoreType.PluginProv CoreType.ProofIrrelProv CoreType.TyCoVarSet CoreType.TyCon
     CoreType.Type_ CoreType.UnivCoProvenance CoreType.UnsafeCoerceProv CoreType.Var
     CoreType.VarSet CoreType.coAxBranchLHS CoreType.coAxiomBranches
     CoreType.coAxiomTyCon CoreType.dVarSetElems CoreType.delDVarSet CoreType.delFV
     CoreType.emptyFV CoreType.emptyVarSet CoreType.filterFV CoreType.fromBranches
     CoreType.fvDVarSet CoreType.fvVarList CoreType.fvVarSet CoreType.isId
     CoreType.isLocalId CoreType.isLocalVar CoreType.mapUnionFV
     CoreType.mapUnionVarSet CoreType.mkFVs CoreType.tyCoFVsOfType
     CoreType.tyConClass_maybe CoreType.unionDVarSet CoreType.unionDVarSets
     CoreType.unionFV CoreType.unitDVarSet CoreType.varType Data.Foldable.concatMap
     Data.Foldable.foldr Data.Tuple.fst GHC.Base.fmap GHC.Base.map
     GHC.Base.op_z2218U__ GHC.List.unzip GHC.List.zip GHC.Num.fromInteger
     Id.idSpecialisation Id.realIdUnfolding IdInfo2.ruleInfoFreeVars Maybes.orElse
     Name.getName NameSet.NameSet NameSet.emptyNameSet NameSet.extendNameSet
     NameSet.unionNameSet NameSet.unitNameSet Panic.assertPanic Util.debugIsOn
*)
