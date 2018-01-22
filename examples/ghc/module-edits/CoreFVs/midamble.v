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