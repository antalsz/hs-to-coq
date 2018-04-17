(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require CoreArity.
Require CoreSyn.
Require Data.Traversable.
Require GHC.Base.
Require GHC.List.
Require GHC.Prim.
Require Id.
Require IdInfo.
Require Maybes.
Require Name.
Require OccName.
Require SrcLoc.
Require UniqFM.
Require Var.
Require VarEnv.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition op_zeZC__ {a} {b} : a -> (a -> b) -> b :=
  fun m k => GHC.Prim.seq m (k m).

Notation "'_=:_'" := (op_zeZC__).

Infix "=:" := (_=:_) (at level 99).

Definition tidyIdBndr
   : VarEnv.TidyEnv -> Var.Id -> (VarEnv.TidyEnv * Var.Id)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (pair tidy_env var_env as env), id =>
        let 'pair tidy_env' occ' := OccName.tidyOccName tidy_env (Name.getOccName id) in
        let old_info := (@Var.idInfo tt id) in
        let old_unf := IdInfo.unfoldingInfo old_info in
        let new_unf := CoreSyn.noUnfolding in
        let new_info :=
          IdInfo.setOneShotInfo (IdInfo.setOccInfo IdInfo.vanillaIdInfo (IdInfo.occInfo
                                                    old_info)) (IdInfo.oneShotInfo old_info) in
        let name' := Name.mkInternalName (Id.idUnique id) occ' SrcLoc.noSrcSpan in
        let ty' := tt in
        let id' := Id.mkLocalIdWithInfo name' ty' new_info in
        let var_env' := VarEnv.extendVarEnv var_env id id' in
        pair (pair tidy_env' var_env') id'
    end.

Definition tidyBndr
   : VarEnv.TidyEnv -> Var.Var -> (VarEnv.TidyEnv * Var.Var)%type :=
  fun env var => tidyIdBndr env var.

Definition tidyBndrs
   : VarEnv.TidyEnv -> list Var.Var -> (VarEnv.TidyEnv * list Var.Var)%type :=
  fun env vars => Data.Traversable.mapAccumL tidyBndr env vars.

Definition tidyLetBndr
   : VarEnv.TidyEnv ->
     VarEnv.TidyEnv ->
     (Var.Id * CoreSyn.CoreExpr)%type -> (VarEnv.TidyEnv * Var.Var)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | rec_tidy_env, (pair tidy_env var_env as env), pair id rhs =>
        let 'pair tidy_env' occ' := OccName.tidyOccName tidy_env (Name.getOccName id) in
        let old_info := (@Var.idInfo tt id) in
        let old_unf := IdInfo.unfoldingInfo old_info in
        let new_unf := CoreSyn.noUnfolding in
        let new_info :=
          IdInfo.setInlinePragInfo (IdInfo.setArityInfo (IdInfo.setOccInfo
                                                         IdInfo.vanillaIdInfo (IdInfo.occInfo old_info))
                                                        (CoreArity.exprArity rhs)) (IdInfo.inlinePragInfo old_info) in
        let details := Var.idDetails id in
        let name' := Name.mkInternalName (Id.idUnique id) occ' SrcLoc.noSrcSpan in
        let ty' := tt in
        let id' := Var.mkLocalVar details name' ty' new_info in
        let var_env' := VarEnv.extendVarEnv var_env id id' in
        pair (pair tidy_env' var_env') id'
    end.

Definition tidyNameOcc : VarEnv.TidyEnv -> Name.Name -> Name.Name :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair _ var_env, n =>
        match UniqFM.lookupUFM var_env n with
        | None => n
        | Some v => Id.idName v
        end
    end.

Definition tidyVarOcc : VarEnv.TidyEnv -> Var.Var -> Var.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair _ var_env, v => Maybes.orElse (VarEnv.lookupVarEnv var_env v) v
    end.

Definition tidyTickish
   : VarEnv.TidyEnv -> CoreSyn.Tickish Var.Id -> CoreSyn.Tickish Var.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | env, CoreSyn.Breakpoint ix ids =>
        CoreSyn.Breakpoint ix (GHC.Base.map (tidyVarOcc env) ids)
    | _, other_tickish => other_tickish
    end.

Definition tidyBind
   : VarEnv.TidyEnv ->
     CoreSyn.CoreBind -> (VarEnv.TidyEnv * CoreSyn.CoreBind)%type :=
  fix tidyExpr arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | env, CoreSyn.Var v => CoreSyn.Var (tidyVarOcc env v)
           | env, CoreSyn.Type_ ty => CoreSyn.Type_ (tt)
           | env, CoreSyn.Coercion co => CoreSyn.Coercion (tt)
           | _, CoreSyn.Lit lit => CoreSyn.Lit lit
           | env, CoreSyn.App f a => CoreSyn.App (tidyExpr env f) (tidyExpr env a)
           | env, CoreSyn.Tick t e => CoreSyn.Tick (tidyTickish env t) (tidyExpr env e)
           | env, CoreSyn.Cast e co => CoreSyn.Cast (tidyExpr env e) (tt)
           | env, CoreSyn.Let b e =>
               tidyBind env b =: (fun '(pair env' b') => CoreSyn.Let b' (tidyExpr env' e))
           | env, CoreSyn.Case e b ty alts =>
               tidyBndr env b =:
               (fun '(pair env' b) =>
                  CoreSyn.Case (tidyExpr env e) b (tt) (GHC.Base.map ((fun env x =>
                                                                         let 'pair (pair con vs) rhs := x in
                                                                         let 'pair env' vs := tidyBndrs env vs in
                                                                         pair (pair con vs) (tidyExpr env' rhs)) env')
                                                        alts))
           | env, CoreSyn.Lam b e =>
               tidyBndr env b =: (fun '(pair env' b) => CoreSyn.Lam b (tidyExpr env' e))
           end with tidyBind arg_0__ arg_1__
                      := match arg_0__, arg_1__ with
                         | env, CoreSyn.NonRec bndr rhs =>
                             tidyLetBndr env env (pair bndr rhs) =:
                             (fun '(pair env' bndr') => pair env' (CoreSyn.NonRec bndr' (tidyExpr env' rhs)))
                         | env, CoreSyn.Rec prs =>
                             let 'pair env' bndrs' := Data.Traversable.mapAccumL (tidyLetBndr env) env prs in
                             GHC.Base.map (fun x => tidyExpr env' (snd x)) prs =:
                             (fun rhss' => pair env' (CoreSyn.Rec (GHC.List.zip bndrs' rhss')))
                         end for tidyBind.

Definition tidyExpr : VarEnv.TidyEnv -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr :=
  fix tidyExpr arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | env, CoreSyn.Var v => CoreSyn.Var (tidyVarOcc env v)
           | env, CoreSyn.Type_ ty => CoreSyn.Type_ (tt)
           | env, CoreSyn.Coercion co => CoreSyn.Coercion (tt)
           | _, CoreSyn.Lit lit => CoreSyn.Lit lit
           | env, CoreSyn.App f a => CoreSyn.App (tidyExpr env f) (tidyExpr env a)
           | env, CoreSyn.Tick t e => CoreSyn.Tick (tidyTickish env t) (tidyExpr env e)
           | env, CoreSyn.Cast e co => CoreSyn.Cast (tidyExpr env e) (tt)
           | env, CoreSyn.Let b e =>
               tidyBind env b =: (fun '(pair env' b') => CoreSyn.Let b' (tidyExpr env' e))
           | env, CoreSyn.Case e b ty alts =>
               tidyBndr env b =:
               (fun '(pair env' b) =>
                  CoreSyn.Case (tidyExpr env e) b (tt) (GHC.Base.map ((fun env x =>
                                                                         let 'pair (pair con vs) rhs := x in
                                                                         let 'pair env' vs := tidyBndrs env vs in
                                                                         pair (pair con vs) (tidyExpr env' rhs)) env')
                                                        alts))
           | env, CoreSyn.Lam b e =>
               tidyBndr env b =: (fun '(pair env' b) => CoreSyn.Lam b (tidyExpr env' e))
           end with tidyBind arg_0__ arg_1__
                      := match arg_0__, arg_1__ with
                         | env, CoreSyn.NonRec bndr rhs =>
                             tidyLetBndr env env (pair bndr rhs) =:
                             (fun '(pair env' bndr') => pair env' (CoreSyn.NonRec bndr' (tidyExpr env' rhs)))
                         | env, CoreSyn.Rec prs =>
                             let 'pair env' bndrs' := Data.Traversable.mapAccumL (tidyLetBndr env) env prs in
                             GHC.Base.map (fun x => tidyExpr env' (snd x)) prs =:
                             (fun rhss' => pair env' (CoreSyn.Rec (GHC.List.zip bndrs' rhss')))
                         end for tidyExpr.

Definition tidyAlt : VarEnv.TidyEnv -> CoreSyn.CoreAlt -> CoreSyn.CoreAlt :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | env, pair (pair con vs) rhs =>
        tidyBndrs env vs =:
        (fun '(pair env' vs) => pair (pair con vs) (tidyExpr env' rhs))
    end.

Module Notations.
Notation "'_CoreTidy.=:_'" := (op_zeZC__).
Infix "CoreTidy.=:" := (_=:_) (at level 99).
End Notations.

(* External variables:
     None Some list op_zt__ pair snd tt CoreArity.exprArity CoreSyn.App
     CoreSyn.Breakpoint CoreSyn.Case CoreSyn.Cast CoreSyn.Coercion CoreSyn.CoreAlt
     CoreSyn.CoreBind CoreSyn.CoreExpr CoreSyn.Lam CoreSyn.Let CoreSyn.Lit
     CoreSyn.NonRec CoreSyn.Rec CoreSyn.Tick CoreSyn.Tickish CoreSyn.Type_
     CoreSyn.Var CoreSyn.noUnfolding Data.Traversable.mapAccumL GHC.Base.map
     GHC.List.zip GHC.Prim.seq Id.idName Id.idUnique Id.mkLocalIdWithInfo
     IdInfo.inlinePragInfo IdInfo.occInfo IdInfo.oneShotInfo IdInfo.setArityInfo
     IdInfo.setInlinePragInfo IdInfo.setOccInfo IdInfo.setOneShotInfo
     IdInfo.unfoldingInfo IdInfo.vanillaIdInfo Maybes.orElse Name.Name
     Name.getOccName Name.mkInternalName OccName.tidyOccName SrcLoc.noSrcSpan
     UniqFM.lookupUFM Var.Id Var.Var Var.idDetails Var.idInfo Var.mkLocalVar
     VarEnv.TidyEnv VarEnv.extendVarEnv VarEnv.lookupVarEnv
*)
