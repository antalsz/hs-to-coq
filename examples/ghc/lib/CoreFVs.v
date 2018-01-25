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

Require CoAxiom.
Require Core.
Require CoreSyn.
Require Data.Foldable.
Require Data.Tuple.
Require FV.
Require GHC.Base.
Require Id.
Require IdInfo2.
Require Maybes.
Require Name.
Require NameSet.
Require Panic.
Require TyCoRep.
Require TyCon.
Require Util.
Require Var.
Require VarSet.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive FVAnn : Type := Mk_FVAnn
                         : VarSet.DVarSet -> VarSet.DVarSet -> Core.Type_ -> FVAnn.

Definition CoreExprWithFVs' :=
  (CoreSyn.AnnExpr' Var.Id FVAnn)%type.

Definition CoreExprWithFVs :=
  (AnnExpr Var.Id FVAnn)%type.

Definition CoreBindWithFVs :=
  (CoreSyn.AnnBind Var.Id FVAnn)%type.

Definition CoreAltWithFVs :=
  (AnnAlt Var.Id FVAnn)%type.

Definition fva_fvs (arg_0__ : FVAnn) :=
  match arg_0__ with
    | Mk_FVAnn fva_fvs _ _ => fva_fvs
  end.

Definition fva_ty (arg_1__ : FVAnn) :=
  match arg_1__ with
    | Mk_FVAnn _ _ fva_ty => fva_ty
  end.

Definition fva_ty_fvs (arg_2__ : FVAnn) :=
  match arg_2__ with
    | Mk_FVAnn _ fva_ty_fvs _ => fva_ty_fvs
  end.
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

Definition aFreeVar : Core.Var -> VarSet.DVarSet :=
  VarSet.unitDVarSet.

Definition exprFVs : CoreSyn.CoreExpr -> FV.FV :=
  FV.filterFV Var.isLocalVar GHC.Base.∘ expr_fvs.

Definition exprFreeVars : CoreSyn.CoreExpr -> VarSet.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsDSet : CoreSyn.CoreExpr -> VarSet.DVarSet :=
  FV.fvDVarSet GHC.Base.∘ exprFVs.

Definition exprFreeVarsList : CoreSyn.CoreExpr -> list Core.Var :=
  FV.fvVarList GHC.Base.∘ exprFVs.

Definition exprsFVs : list CoreSyn.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV exprFVs exprs.

Definition exprsFreeVars : list CoreSyn.CoreExpr -> VarSet.VarSet :=
  FV.fvVarSet GHC.Base.∘ exprsFVs.

Definition exprsFreeVarsList : list CoreSyn.CoreExpr -> list Core.Var :=
  FV.fvVarList GHC.Base.∘ exprsFVs.

Definition exprSomeFreeVars
    : FV.InterestingVarFun -> CoreSyn.CoreExpr -> VarSet.VarSet :=
  fun fv_cand e =>
    FV.fvVarSet GHC.Base.$ (FV.filterFV fv_cand GHC.Base.$ expr_fvs e).

Definition exprFreeIds : CoreSyn.CoreExpr -> VarSet.IdSet :=
  exprSomeFreeVars Var.isLocalId.

Definition exprSomeFreeVarsDSet
    : FV.InterestingVarFun -> CoreSyn.CoreExpr -> VarSet.DVarSet :=
  fun fv_cand e =>
    FV.fvDVarSet GHC.Base.$ (FV.filterFV fv_cand GHC.Base.$ expr_fvs e).

Definition exprFreeIdsDSet : CoreSyn.CoreExpr -> VarSet.DIdSet :=
  exprSomeFreeVarsDSet Var.isLocalId.

Definition exprSomeFreeVarsList
    : FV.InterestingVarFun -> CoreSyn.CoreExpr -> list Core.Var :=
  fun fv_cand e =>
    FV.fvVarList GHC.Base.$ (FV.filterFV fv_cand GHC.Base.$ expr_fvs e).

Definition exprFreeIdsList : CoreSyn.CoreExpr -> list Var.Id :=
  exprSomeFreeVarsList Var.isLocalId.

Definition exprTypeFV : CoreExprWithFVs -> Core.Type_ :=
  fun arg_0__ => match arg_0__ with | pair (Mk_FVAnn _ _ ty) _ => ty end.

Definition exprsOrphNames : list CoreSyn.CoreExpr -> NameSet.NameSet :=
  fun es =>
    Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ exprOrphNames)
    NameSet.emptyNameSet es.

Definition exprsSomeFreeVars : FV.InterestingVarFun -> list
                               CoreSyn.CoreExpr -> VarSet.VarSet :=
  fun fv_cand es =>
    FV.fvVarSet GHC.Base.$ (FV.filterFV fv_cand GHC.Base.$ FV.mapUnionFV expr_fvs
    es).

Definition exprsSomeFreeVarsDSet : FV.InterestingVarFun -> list
                                   CoreSyn.CoreExpr -> VarSet.DVarSet :=
  fun fv_cand e =>
    FV.fvDVarSet GHC.Base.$ (FV.filterFV fv_cand GHC.Base.$ FV.mapUnionFV expr_fvs
    e).

Definition exprsFreeIdsDSet : list CoreSyn.CoreExpr -> VarSet.DIdSet :=
  exprsSomeFreeVarsDSet Var.isLocalId.

Definition exprsSomeFreeVarsList : FV.InterestingVarFun -> list
                                   CoreSyn.CoreExpr -> list Core.Var :=
  fun fv_cand es =>
    FV.fvVarList GHC.Base.$ (FV.filterFV fv_cand GHC.Base.$ FV.mapUnionFV expr_fvs
    es).

Definition exprsFreeIdsList : list CoreSyn.CoreExpr -> list Var.Id :=
  exprsSomeFreeVarsList Var.isLocalId.

Definition exprs_fvs : list CoreSyn.CoreExpr -> FV.FV :=
  fun exprs => FV.mapUnionFV expr_fvs exprs.

Definition freeVarsOf : CoreExprWithFVs -> VarSet.DIdSet :=
  fun arg_0__ => match arg_0__ with | pair (Mk_FVAnn fvs _ _) _ => fvs end.

Definition freeVarsOfAnn : FVAnn -> VarSet.DIdSet :=
  fva_fvs.

Definition freeVarsOfType : CoreExprWithFVs -> VarSet.DTyCoVarSet :=
  fun arg_0__ => match arg_0__ with | pair (Mk_FVAnn _ ty_fvs _) _ => ty_fvs end.

Definition freeVarsOfTypeAnn : FVAnn -> VarSet.DTyCoVarSet :=
  fva_ty_fvs.

Definition idRuleFVs : Var.Id -> FV.FV :=
  fun id =>
    if andb Util.debugIsOn (negb (Var.isId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreFVs.hs")
         (GHC.Num.fromInteger 664))
    else FV.mkFVs (VarSet.dVarSetElems GHC.Base.$ IdInfo2.ruleInfoFreeVars
                  (Id.idSpecialisation id)).

Definition idRuleVars : Var.Id -> VarSet.VarSet :=
  fun id => FV.fvVarSet GHC.Base.$ idRuleFVs id.

Axiom idRuleRhsVars : forall {A : Type}, A.

(* Translating `idRuleRhsVars' failed: using a record pattern for the unknown
   constructor `Rule' unsupported *)

Definition noFVs : VarSet.VarSet :=
  VarSet.emptyVarSet.

Definition vectsFreeVars : list CoreSyn.CoreVect -> VarSet.VarSet :=
  let vectFreeVars :=
    fun arg_0__ =>
      match arg_0__ with
        | CoreSyn.Vect _ rhs => FV.fvVarSet GHC.Base.$ (FV.filterFV Var.isLocalId
                                GHC.Base.$ expr_fvs rhs)
        | CoreSyn.NoVect _ => noFVs
        | CoreSyn.VectType _ _ _ => noFVs
        | CoreSyn.VectClass _ => noFVs
        | CoreSyn.VectInst _ => noFVs
      end in
  VarSet.mapUnionVarSet vectFreeVars.

Axiom orphNamesOfCoAxBranch : forall {A : Type}, A.

Definition orphNamesOfCoAxBranches {br} : Core.Branches br -> NameSet.NameSet :=
  Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ orphNamesOfCoAxBranch)
  NameSet.emptyNameSet GHC.Base.∘ CoAxiom.fromBranches.

(* Translating `orphNamesOfCoAxBranch' failed: using a record pattern for the
   unknown constructor `CoAxBranch' unsupported *)

Axiom orphNamesOfCoCon : forall {A : Type}, A.

(* Translating `orphNamesOfCoCon' failed: using a record pattern for the unknown
   constructor `CoAxiom' unsupported *)

Definition orphNamesOfProv : Core.UnivCoProvenance -> NameSet.NameSet :=
  fun arg_0__ =>
    match arg_0__ with
      | Core.UnsafeCoerceProv => NameSet.emptyNameSet
      | Core.PhantomProv co => orphNamesOfCo co
      | Core.ProofIrrelProv co => orphNamesOfCo co
      | Core.PluginProv _ => NameSet.emptyNameSet
      | Core.HoleProv _ => NameSet.emptyNameSet
    end.

Definition orphNamesOfThings {a} : (a -> NameSet.NameSet) -> list
                                   a -> NameSet.NameSet :=
  fun f =>
    Data.Foldable.foldr (NameSet.unionNameSet GHC.Base.∘ f) NameSet.emptyNameSet.

Definition orphNamesOfCos : list Core.Coercion -> NameSet.NameSet :=
  orphNamesOfThings orphNamesOfCo.

Definition orphNamesOfTyCon : Core.TyCon -> NameSet.NameSet :=
  fun tycon =>
    NameSet.unionNameSet (NameSet.unitNameSet (Name.getName tycon))
                         (match TyCon.tyConClass_maybe tycon with
                           | None => NameSet.emptyNameSet
                           | Some cls => NameSet.unitNameSet (Name.getName cls)
                         end).

Axiom orphNamesOfType : forall {A : Type}, A.

Definition orphNamesOfTypes : list Core.Type_ -> NameSet.NameSet :=
  orphNamesOfThings orphNamesOfType.

Definition orphNamesOfAxiom {br} : Core.CoAxiom br -> NameSet.NameSet :=
  fun axiom =>
    NameSet.extendNameSet (orphNamesOfTypes (Data.Foldable.concatMap
                                            CoAxiom.coAxBranchLHS GHC.Base.$ (CoAxiom.fromBranches GHC.Base.$
                                            CoAxiom.coAxiomBranches axiom))) (Name.getName (CoAxiom.coAxiomTyCon
                                                                                           axiom)).

(* Translating `orphNamesOfType' failed: using a record pattern for the unknown
   constructor `LitTy' unsupported *)

Axiom ruleFVs : forall {A : Type}, A.

Definition ruleFreeVars : CoreSyn.CoreRule -> VarSet.VarSet :=
  FV.fvVarSet GHC.Base.∘ ruleFVs.

Definition rulesFreeVars : list CoreSyn.CoreRule -> VarSet.VarSet :=
  fun rules => VarSet.mapUnionVarSet ruleFreeVars rules.

Definition rulesFVs : list CoreSyn.CoreRule -> FV.FV :=
  FV.mapUnionFV ruleFVs.

Definition rulesFreeVarsDSet : list CoreSyn.CoreRule -> VarSet.DVarSet :=
  fun rules => FV.fvDVarSet GHC.Base.$ rulesFVs rules.

(* Translating `ruleFVs' failed: using a record pattern for the unknown
   constructor `BuiltinRule' unsupported *)

Axiom ruleLhsFVIds : forall {A : Type}, A.

Definition ruleLhsFreeIds : CoreSyn.CoreRule -> VarSet.VarSet :=
  FV.fvVarSet GHC.Base.∘ ruleLhsFVIds.

Definition ruleLhsFreeIdsList : CoreSyn.CoreRule -> list Core.Var :=
  FV.fvVarList GHC.Base.∘ ruleLhsFVIds.

(* Translating `ruleLhsFVIds' failed: using a record pattern for the unknown
   constructor `BuiltinRule' unsupported *)

Axiom ruleRhsFreeVars : forall {A : Type}, A.

(* Translating `ruleRhsFreeVars' failed: using a record pattern for the unknown
   constructor `BuiltinRule' unsupported *)

Axiom stableUnfoldingFVs : forall {A : Type}, A.

Definition stableUnfoldingVars : CoreSyn.Unfolding -> option VarSet.VarSet :=
  fun unf => GHC.Base.fmap FV.fvVarSet (stableUnfoldingFVs unf).

Definition idUnfoldingFVs : Var.Id -> FV.FV :=
  fun id => Maybes.orElse (stableUnfoldingFVs (Id.realIdUnfolding id)) FV.emptyFV.

Definition idUnfoldingVars : Var.Id -> VarSet.VarSet :=
  fun id => FV.fvVarSet GHC.Base.$ idUnfoldingFVs id.

Definition idRuleAndUnfoldingFVs : Var.Id -> FV.FV :=
  fun id =>
    if andb Util.debugIsOn (negb (Var.isId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreFVs.hs")
         (GHC.Num.fromInteger 656))
    else FV.unionFV (idRuleFVs id) (idUnfoldingFVs id).

Definition idRuleAndUnfoldingVars : Var.Id -> VarSet.VarSet :=
  fun id => FV.fvVarSet GHC.Base.$ idRuleAndUnfoldingFVs id.

Definition idRuleAndUnfoldingVarsDSet : Var.Id -> VarSet.DVarSet :=
  fun id => FV.fvDVarSet GHC.Base.$ idRuleAndUnfoldingFVs id.

Definition bndrRuleAndUnfoldingFVs : Core.Var -> FV.FV :=
  fun v => if Var.isTyVar v : bool then FV.emptyFV else idRuleAndUnfoldingFVs v.

Definition rhs_fvs : (Var.Id * CoreSyn.CoreExpr)%type -> FV.FV :=
  fun arg_0__ =>
    match arg_0__ with
      | pair bndr rhs => FV.unionFV (expr_fvs rhs) (bndrRuleAndUnfoldingFVs bndr)
    end.

(* Translating `stableUnfoldingFVs' failed: using a record pattern for the
   unknown constructor `CoreUnfolding' unsupported *)

Definition unionFVs : VarSet.DVarSet -> VarSet.DVarSet -> VarSet.DVarSet :=
  VarSet.unionDVarSet.

Definition unionFVss : list VarSet.DVarSet -> VarSet.DVarSet :=
  VarSet.unionDVarSets.

Definition varTypeTyCoFVs : Core.Var -> FV.FV :=
  fun var => TyCoRep.tyCoFVsOfType (varType var).

Definition varTypeTyCoVars : Core.Var -> VarSet.TyCoVarSet :=
  fun var => FV.fvVarSet GHC.Base.$ varTypeTyCoFVs var.

Definition idFVs : Var.Id -> FV.FV :=
  fun id =>
    if andb Util.debugIsOn (negb (Var.isId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreFVs.hs")
         (GHC.Num.fromInteger 641))
    else FV.unionFV (varTypeTyCoFVs id) (idRuleAndUnfoldingFVs id).

Definition idFreeVars : Var.Id -> VarSet.VarSet :=
  fun id =>
    if andb Util.debugIsOn (negb (Var.isId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreFVs.hs")
         (GHC.Num.fromInteger 634))
    else FV.fvVarSet GHC.Base.$ idFVs id.

Definition dIdFreeVars : Var.Id -> VarSet.DVarSet :=
  fun id => FV.fvDVarSet GHC.Base.$ idFVs id.

Definition dVarTypeTyCoVars : Core.Var -> VarSet.DTyCoVarSet :=
  fun var => FV.fvDVarSet GHC.Base.$ varTypeTyCoFVs var.

Definition delBinderFV : Core.Var -> VarSet.DVarSet -> VarSet.DVarSet :=
  fun b s => unionFVs (VarSet.delDVarSet s b) (dVarTypeTyCoVars b).

Definition delBindersFV : list Core.Var -> VarSet.DVarSet -> VarSet.DVarSet :=
  fun bs fvs => Data.Foldable.foldr delBinderFV fvs bs.

Definition addBndr : CoreSyn.CoreBndr -> FV.FV -> FV.FV :=
  fun bndr fv fv_cand in_scope acc =>
    (FV.unionFV (varTypeTyCoFVs bndr) (FV.delFV bndr fv)) fv_cand in_scope acc.

Definition addBndrs : list CoreSyn.CoreBndr -> FV.FV -> FV.FV :=
  fun bndrs fv => Data.Foldable.foldr addBndr fv bndrs.

Definition bindFreeVars : CoreSyn.CoreBind -> VarSet.VarSet :=
  fun arg_0__ =>
    match arg_0__ with
      | CoreSyn.NonRec b r => FV.fvVarSet GHC.Base.$ (FV.filterFV Var.isLocalVar
                              GHC.Base.$ rhs_fvs (pair b r))
      | CoreSyn.Rec prs => FV.fvVarSet GHC.Base.$ (FV.filterFV Var.isLocalVar
                           GHC.Base.$ addBndrs (GHC.Base.map Data.Tuple.fst prs) (FV.mapUnionFV rhs_fvs
                                                                                 prs))
    end.

(* Unbound variables:
     AnnAlt AnnExpr None Some andb bool exprOrphNames expr_fvs list negb op_zt__
     option orphNamesOfCo pair varType CoAxiom.coAxBranchLHS CoAxiom.coAxiomBranches
     CoAxiom.coAxiomTyCon CoAxiom.fromBranches Core.Branches Core.CoAxiom
     Core.Coercion Core.HoleProv Core.PhantomProv Core.PluginProv Core.ProofIrrelProv
     Core.TyCon Core.Type_ Core.UnivCoProvenance Core.UnsafeCoerceProv Core.Var
     CoreSyn.AnnBind CoreSyn.AnnExpr' CoreSyn.CoreBind CoreSyn.CoreBndr
     CoreSyn.CoreExpr CoreSyn.CoreRule CoreSyn.CoreVect CoreSyn.NoVect CoreSyn.NonRec
     CoreSyn.Rec CoreSyn.Unfolding CoreSyn.Vect CoreSyn.VectClass CoreSyn.VectInst
     CoreSyn.VectType Data.Foldable.concatMap Data.Foldable.foldr Data.Tuple.fst
     FV.FV FV.InterestingVarFun FV.delFV FV.emptyFV FV.filterFV FV.fvDVarSet
     FV.fvVarList FV.fvVarSet FV.mapUnionFV FV.mkFVs FV.unionFV GHC.Base.fmap
     GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zd__ Id.idSpecialisation
     Id.realIdUnfolding IdInfo2.ruleInfoFreeVars Maybes.orElse Name.getName
     NameSet.NameSet NameSet.emptyNameSet NameSet.extendNameSet NameSet.unionNameSet
     NameSet.unitNameSet Panic.assertPanic TyCoRep.tyCoFVsOfType
     TyCon.tyConClass_maybe Util.debugIsOn Var.Id Var.isId Var.isLocalId
     Var.isLocalVar Var.isTyVar VarSet.DIdSet VarSet.DTyCoVarSet VarSet.DVarSet
     VarSet.IdSet VarSet.TyCoVarSet VarSet.VarSet VarSet.dVarSetElems
     VarSet.delDVarSet VarSet.emptyVarSet VarSet.mapUnionVarSet VarSet.unionDVarSet
     VarSet.unionDVarSets VarSet.unitDVarSet
*)
