(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require CoreFVs.
Require CoreUtils.
Require Data.Bifunctor.
Require Data.Foldable.
Require Data.Traversable.
Require Data.Tuple.
Require FastString.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.Err.
Require Id.
Require State.
Require Unique.
Require Util.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition ExitifyM :=
  (State.State (list (Core.JoinId * Core.CoreExpr)%type))%type.

(* Converted value declarations: *)

Definition mkExitJoinId
   : Core.InScopeSet ->
     AxiomatizedTypes.Type_ -> BasicTypes.JoinArity -> ExitifyM Core.JoinId :=
  fun in_scope ty join_arity =>
    let exit_id_tmpl :=
      Id.asJoinId (Id.mkSysLocal (FastString.fsLit (GHC.Base.hs_string__ "exit"))
                   Unique.initExitJoinUnique ty) join_arity in
    State.get GHC.Base.>>=
    (fun fs =>
       let avoid :=
         Core.extendInScopeSet (Core.extendInScopeSetList in_scope (GHC.Base.map
                                                           Data.Tuple.fst fs)) exit_id_tmpl in
       GHC.Base.return_ (Core.uniqAway avoid exit_id_tmpl)).

Definition addExit
   : Core.InScopeSet ->
     BasicTypes.JoinArity -> Core.CoreExpr -> ExitifyM Core.JoinId :=
  fun in_scope join_arity rhs =>
    let ty := CoreUtils.exprType rhs in
    mkExitJoinId in_scope ty join_arity GHC.Base.>>=
    (fun v =>
       State.get GHC.Base.>>=
       (fun fs => State.put (cons (pair v rhs) fs) GHC.Base.>> GHC.Base.return_ v)).

Definition exitifyRec
   : Core.InScopeSet ->
     list (Core.Var * Core.CoreExpr)%type -> list Core.CoreBind :=
  fun in_scope pairs =>
    let go_exit
     : list Core.Var -> Core.CoreExpr -> Core.VarSet -> ExitifyM Core.CoreExpr :=
      fun captured e fvs =>
        let zap :=
          fun v => if Core.isId v : bool then Id.setIdInfo v Core.vanillaIdInfo else v in
        let abs_vars :=
          let pick :=
            fun arg_1__ arg_2__ =>
              match arg_1__, arg_2__ with
              | v, pair fvs' acc =>
                  if Core.elemVarSet v fvs' : bool
                  then pair (Core.delVarSet fvs' v) (cons (zap v) acc) else
                  pair fvs' acc
              end in
          Data.Tuple.snd (Data.Foldable.foldr pick (pair fvs nil) captured) in
        let captures_join_points := Data.Foldable.any Id.isJoinId abs_vars in
        let is_interesting :=
          Core.anyVarSet Core.isLocalId (Core.minusVarSet fvs (Core.mkVarSet captured)) in
        let isCapturedVarArg :=
          fun arg_9__ =>
            match arg_9__ with
            | Core.Mk_Var v => Data.Foldable.elem v captured
            | _ => false
            end in
        let j_14__ :=
          let avoid := Core.extendInScopeSetList in_scope captured in
          let rhs := Core.mkLams abs_vars e in
          addExit avoid (Coq.Lists.List.length abs_vars) rhs GHC.Base.>>=
          (fun v => GHC.Base.return_ (Core.mkVarApps (Core.Mk_Var v) abs_vars)) in
        let j_15__ :=
          if captures_join_points : bool then GHC.Base.return_ e else
          j_14__ in
        let j_16__ :=
          if negb is_interesting : bool then GHC.Base.return_ e else
          j_15__ in
        match Core.collectArgs e with
        | pair (Core.Mk_Var f) args =>
            if andb (Id.isJoinId f) (Data.Foldable.all isCapturedVarArg args) : bool
            then GHC.Base.return_ e else
            j_16__
        | _ => j_16__
        end in
    let recursive_calls := Core.mkVarSet (GHC.Base.map Data.Tuple.fst pairs) in
    let go : list Core.Var -> CoreFVs.CoreExprWithFVs -> ExitifyM Core.CoreExpr :=
      GHC.DeferredFix.deferredFix2 (fun go
                                    (arg_19__ : list Core.Var)
                                    (arg_20__ : CoreFVs.CoreExprWithFVs) =>
                                      match arg_19__, arg_20__ with
                                      | captured, ann_e =>
                                          let j_22__ :=
                                            match arg_19__, arg_20__ with
                                            | _, ann_e => GHC.Base.return_ (Core.deAnnotate ann_e)
                                            end in
                                          let j_40__ :=
                                            match arg_19__, arg_20__ with
                                            | captured, pair _ (Core.AnnCase scrut bndr ty alts) =>
                                                Data.Traversable.forM alts (fun '(pair (pair dc pats) rhs) =>
                                                                              go (Coq.Init.Datatypes.app captured
                                                                                                         (Coq.Init.Datatypes.app
                                                                                                          (cons bndr
                                                                                                                nil)
                                                                                                          pats)) rhs
                                                                              GHC.Base.>>=
                                                                              (fun rhs' =>
                                                                                 GHC.Base.return_ (pair (pair dc pats)
                                                                                                        rhs')))
                                                GHC.Base.>>=
                                                (fun alts' =>
                                                   GHC.Base.return_ (Core.Case (Core.deAnnotate scrut) bndr ty alts'))
                                            | captured, pair _ (Core.AnnLet ann_bind body) =>
                                                let bind := Core.deAnnBind ann_bind in
                                                let j_37__ :=
                                                  go (Coq.Init.Datatypes.app captured (Core.bindersOf bind)) body
                                                  GHC.Base.>>=
                                                  (fun body' => GHC.Base.return_ (Core.Let bind body')) in
                                                let j_38__ :=
                                                  match ann_bind with
                                                  | Core.AnnRec pairs =>
                                                      if Id.isJoinId (Data.Tuple.fst (GHC.Err.head pairs)) : bool
                                                      then let js := GHC.Base.map Data.Tuple.fst pairs in
                                                           Data.Traversable.forM pairs (fun '(pair j rhs) =>
                                                                                          let join_arity :=
                                                                                            Id.idJoinArity j in
                                                                                          let 'pair params join_body :=
                                                                                            Core.collectNAnnBndrs
                                                                                              join_arity rhs in
                                                                                          go (Coq.Init.Datatypes.app
                                                                                              captured
                                                                                              (Coq.Init.Datatypes.app js
                                                                                                                      params))
                                                                                          join_body GHC.Base.>>=
                                                                                          (fun join_body' =>
                                                                                             let rhs' :=
                                                                                               Core.mkLams params
                                                                                               join_body' in
                                                                                             GHC.Base.return_ (pair j
                                                                                                                    rhs')))
                                                           GHC.Base.>>=
                                                           (fun pairs' =>
                                                              go (Coq.Init.Datatypes.app captured js) body GHC.Base.>>=
                                                              (fun body' =>
                                                                 GHC.Base.return_ (Core.Let (Core.Rec pairs')
                                                                                            body'))) else
                                                      j_37__
                                                  | _ => j_37__
                                                  end in
                                                match ann_bind with
                                                | Core.AnnNonRec j rhs =>
                                                    match Id.isJoinId_maybe j with
                                                    | Some join_arity =>
                                                        let 'pair params join_body := Core.collectNAnnBndrs join_arity
                                                                                        rhs in
                                                        go (Coq.Init.Datatypes.app captured params) join_body
                                                        GHC.Base.>>=
                                                        (fun join_body' =>
                                                           let rhs' := Core.mkLams params join_body' in
                                                           go (Coq.Init.Datatypes.app captured (cons j nil)) body
                                                           GHC.Base.>>=
                                                           (fun body' =>
                                                              GHC.Base.return_ (Core.Let (Core.NonRec j rhs') body')))
                                                    | _ => j_38__
                                                    end
                                                | _ => j_38__
                                                end
                                            | _, _ => j_22__
                                            end in
                                          let fvs :=
                                            Core.dVarSetToVarSet (CoreFVs.exprFreeVars (Core.deAnnotate ann_e)) in
                                          if Core.disjointVarSet fvs recursive_calls : bool
                                          then go_exit captured (Core.deAnnotate ann_e) fvs else
                                          j_40__
                                      end) in
    let ann_pairs := GHC.Base.map (Data.Bifunctor.second CoreFVs.freeVars) pairs in
    let 'pair pairs' exits := (fun arg_45__ => State.runState arg_45__ nil)
                                (Data.Traversable.forM ann_pairs (fun '(pair x rhs) =>
                                                          let 'pair args body := Core.collectNAnnBndrs (Id.idJoinArity
                                                                                                        x) rhs in
                                                          go args body GHC.Base.>>=
                                                          (fun body' =>
                                                             let rhs' := Core.mkLams args body' in
                                                             GHC.Base.return_ (pair x rhs')))) in
    Coq.Init.Datatypes.app (let cont_52__ arg_53__ :=
                              let 'pair xid rhs := arg_53__ in
                              cons (Core.NonRec xid rhs) nil in
                            Coq.Lists.List.flat_map cont_52__ exits) (cons (Core.Rec pairs') nil).

Definition exitifyProgram : Core.CoreProgram -> Core.CoreProgram :=
  fun binds =>
    let go : Core.InScopeSet -> Core.CoreExpr -> Core.CoreExpr :=
      fix go (arg_0__ : Core.InScopeSet) (arg_1__ : Core.CoreExpr) : Core.CoreExpr
            := match arg_0__, arg_1__ with
               | _, (Core.Mk_Var _ as e) => e
               | _, (Core.Lit _ as e) => e
               | _, (Core.Mk_Type _ as e) => e
               | _, (Core.Mk_Coercion _ as e) => e
               | in_scope, Core.Cast e' c => Core.Cast (go in_scope e') c
               | in_scope, Core.App e1 e2 => Core.App (go in_scope e1) (go in_scope e2)
               | in_scope, Core.Lam v e' =>
                   let in_scope' := Core.extendInScopeSet in_scope v in
                   Core.Lam v (go in_scope' e')
               | in_scope, Core.Case scrut bndr ty alts =>
                   let in_scope1 := Core.extendInScopeSet in_scope bndr in
                   let go_alt :=
                     fun '(pair (pair dc pats) rhs) =>
                       let in_scope' := Core.extendInScopeSetList in_scope1 pats in
                       pair (pair dc pats) (go in_scope' rhs) in
                   Core.Case (go in_scope scrut) bndr ty (GHC.Base.map go_alt alts)
               | in_scope, Core.Let (Core.NonRec bndr rhs) body =>
                   let in_scope' := Core.extendInScopeSet in_scope bndr in
                   Core.Let (Core.NonRec bndr (go in_scope rhs)) (go in_scope' body)
               | in_scope, Core.Let (Core.Rec pairs) body =>
                   let in_scope' :=
                     Core.extendInScopeSetList in_scope (Core.bindersOf (Core.Rec pairs)) in
                   let pairs' := Util.mapSnd (go in_scope') pairs in
                   let body' := go in_scope' body in
                   let is_join_rec :=
                     Data.Foldable.any (Id.isJoinId GHC.Base.∘ Data.Tuple.fst) pairs in
                   if is_join_rec : bool then Core.mkLets (exitifyRec in_scope' pairs') body' else
                   Core.Let (Core.Rec pairs') body'
               end in
    let in_scope_toplvl :=
      Core.extendInScopeSetList Core.emptyInScopeSet (Core.bindersOfBinds binds) in
    let goTopLvl :=
      fun arg_22__ =>
        match arg_22__ with
        | Core.NonRec v e => Core.NonRec v (go in_scope_toplvl e)
        | Core.Rec pairs =>
            Core.Rec (GHC.Base.map (Data.Bifunctor.second (go in_scope_toplvl)) pairs)
        end in
    GHC.Base.map goTopLvl binds.

(* External variables:
     Some andb bool cons false list negb nil op_zt__ pair AxiomatizedTypes.Type_
     BasicTypes.JoinArity Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     Coq.Lists.List.length Core.AnnCase Core.AnnLet Core.AnnNonRec Core.AnnRec
     Core.App Core.Case Core.Cast Core.CoreBind Core.CoreExpr Core.CoreProgram
     Core.InScopeSet Core.JoinId Core.Lam Core.Let Core.Lit Core.Mk_Coercion
     Core.Mk_Type Core.Mk_Var Core.NonRec Core.Rec Core.Var Core.VarSet
     Core.anyVarSet Core.bindersOf Core.bindersOfBinds Core.collectArgs
     Core.collectNAnnBndrs Core.dVarSetToVarSet Core.deAnnBind Core.deAnnotate
     Core.delVarSet Core.disjointVarSet Core.elemVarSet Core.emptyInScopeSet
     Core.extendInScopeSet Core.extendInScopeSetList Core.isId Core.isLocalId
     Core.minusVarSet Core.mkLams Core.mkLets Core.mkVarApps Core.mkVarSet
     Core.uniqAway Core.vanillaIdInfo CoreFVs.CoreExprWithFVs CoreFVs.exprFreeVars
     CoreFVs.freeVars CoreUtils.exprType Data.Bifunctor.second Data.Foldable.all
     Data.Foldable.any Data.Foldable.elem Data.Foldable.foldr Data.Traversable.forM
     Data.Tuple.fst Data.Tuple.snd FastString.fsLit GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.return_
     GHC.DeferredFix.deferredFix2 GHC.Err.head Id.asJoinId Id.idJoinArity Id.isJoinId
     Id.isJoinId_maybe Id.mkSysLocal Id.setIdInfo State.State State.get State.put
     State.runState Unique.initExitJoinUnique Util.mapSnd
*)
