(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Combined.
Require CoreArity.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Prim.
Require Id.
Require Maybes.
Require Name.
Require OccName.
Require SrcLoc.
Require UniqFM.

(* No type declarations to convert. *)
(* Converted value declarations: *)

Definition op_zeZC__ {a} {b} : a -> (a -> b) -> b :=
  fun m k => GHC.Prim.seq m (k m).

Notation "'_=:_'" := (op_zeZC__).

Infix "=:" := (_=:_) (at level 99).

Definition tidyIdBndr
   : Combined.TidyEnv -> Combined.Var -> (Combined.TidyEnv * Combined.Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (pair tidy_env var_env as env), id =>
        let 'pair tidy_env' occ' := OccName.tidyOccName tidy_env (Name.getOccName id) in
        let old_info := (@Combined.idInfo tt id) in
        let old_unf := Combined.unfoldingInfo old_info in
        let new_unf :=
          if Combined.isEvaldUnfolding old_unf : bool then Combined.evaldUnfolding else
          Combined.noUnfolding in
        let new_info :=
          Combined.setOneShotInfo (Combined.setOccInfo Combined.vanillaIdInfo
                                                       (Combined.occInfo old_info)) (Combined.oneShotInfo old_info) in
        let name' := Name.mkInternalName (Id.idUnique id) occ' SrcLoc.noSrcSpan in
        let ty' := tt in
        let id' := Id.mkLocalIdWithInfo name' ty' new_info in
        let var_env' := Combined.extendVarEnv var_env id id' in
        pair (pair tidy_env' var_env') id'
    end.

Definition tidyBndr
   : Combined.TidyEnv -> Combined.Var -> (Combined.TidyEnv * Combined.Var)%type :=
  fun env var => tidyIdBndr env var.

Definition tidyBndrs
   : Combined.TidyEnv ->
     list Combined.Var -> (Combined.TidyEnv * list Combined.Var)%type :=
  fun env vars => Data.Traversable.mapAccumL tidyBndr env vars.

Definition tidyLetBndr
   : Combined.TidyEnv ->
     Combined.TidyEnv ->
     (Combined.Var * Combined.CoreExpr)%type ->
     (Combined.TidyEnv * Combined.Var)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | rec_tidy_env, (pair tidy_env var_env as env), pair id rhs =>
        let 'pair tidy_env' occ' := OccName.tidyOccName tidy_env (Name.getOccName id) in
        let old_info := (@Combined.idInfo tt id) in
        let old_unf := Combined.unfoldingInfo old_info in
        let new_unf :=
          if Combined.isEvaldUnfolding old_unf : bool then Combined.evaldUnfolding else
          Combined.noUnfolding in
        let new_info :=
          Combined.setInlinePragInfo (Combined.setArityInfo (Combined.setOccInfo
                                                             Combined.vanillaIdInfo (Combined.occInfo old_info))
                                                            (CoreArity.exprArity rhs)) (Combined.inlinePragInfo
                                      old_info) in
        let details := Combined.idDetails id in
        let name' := Name.mkInternalName (Id.idUnique id) occ' SrcLoc.noSrcSpan in
        let ty' := tt in
        let id' := Combined.mkLocalVar details name' ty' new_info in
        let var_env' := Combined.extendVarEnv var_env id id' in
        pair (pair tidy_env' var_env') id'
    end.

Definition tidyNameOcc : Combined.TidyEnv -> Name.Name -> Name.Name :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair _ var_env, n =>
        match UniqFM.lookupUFM var_env n with
        | None => n
        | Some v => Id.idName v
        end
    end.

Definition tidyVarOcc : Combined.TidyEnv -> Combined.Var -> Combined.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair _ var_env, v => Maybes.orElse (Combined.lookupVarEnv var_env v) v
    end.

Definition tidyTickish
   : Combined.TidyEnv ->
     Combined.Tickish Combined.Var -> Combined.Tickish Combined.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | env, Combined.Breakpoint ix ids =>
        Combined.Breakpoint ix (GHC.Base.map (tidyVarOcc env) ids)
    | _, other_tickish => other_tickish
    end.

Definition tidyBind
   : Combined.TidyEnv ->
     Combined.CoreBind -> (Combined.TidyEnv * Combined.CoreBind)%type :=
  fix tidyExpr arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | env, Combined.Mk_Var v => Combined.Mk_Var (tidyVarOcc env v)
           | env, Combined.Type_ ty => Combined.Type_ (tt)
           | env, Combined.Coercion co => Combined.Coercion (tt)
           | _, Combined.Lit lit => Combined.Lit lit
           | env, Combined.App f a => Combined.App (tidyExpr env f) (tidyExpr env a)
           | env, Combined.Tick t e => Combined.Tick (tidyTickish env t) (tidyExpr env e)
           | env, Combined.Cast e co => Combined.Cast (tidyExpr env e) (tt)
           | env, Combined.Let b e =>
               tidyBind env b =: (fun '(pair env' b') => Combined.Let b' (tidyExpr env' e))
           | env, Combined.Case e b ty alts =>
               tidyBndr env b =:
               (fun '(pair env' b) =>
                  Combined.Case (tidyExpr env e) b (tt) (GHC.Base.map ((fun env x =>
                                                                          let 'pair (pair con vs) rhs := x in
                                                                          let 'pair env' vs := tidyBndrs env vs in
                                                                          pair (pair con vs) (tidyExpr env' rhs)) env')
                                                         alts))
           | env, Combined.Lam b e =>
               tidyBndr env b =: (fun '(pair env' b) => Combined.Lam b (tidyExpr env' e))
           end with tidyBind arg_0__ arg_1__
                      := match arg_0__, arg_1__ with
                         | env, Combined.NonRec bndr rhs =>
                             tidyLetBndr env env (pair bndr rhs) =:
                             (fun '(pair env' bndr') =>
                                pair env' (Combined.NonRec bndr' (tidyExpr env' rhs)))
                         | env, Combined.Rec prs =>
                             let 'pair env' bndrs' := Data.Traversable.mapAccumL (tidyLetBndr
                                                                                  GHC.Err.default) env prs in
                             GHC.Base.map (fun x => tidyExpr env' (snd x)) prs =:
                             (fun rhss' => pair env' (Combined.Rec (GHC.List.zip bndrs' rhss')))
                         end for tidyBind.

Definition tidyExpr
   : Combined.TidyEnv -> Combined.CoreExpr -> Combined.CoreExpr :=
  fix tidyExpr arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | env, Combined.Mk_Var v => Combined.Mk_Var (tidyVarOcc env v)
           | env, Combined.Type_ ty => Combined.Type_ (tt)
           | env, Combined.Coercion co => Combined.Coercion (tt)
           | _, Combined.Lit lit => Combined.Lit lit
           | env, Combined.App f a => Combined.App (tidyExpr env f) (tidyExpr env a)
           | env, Combined.Tick t e => Combined.Tick (tidyTickish env t) (tidyExpr env e)
           | env, Combined.Cast e co => Combined.Cast (tidyExpr env e) (tt)
           | env, Combined.Let b e =>
               tidyBind env b =: (fun '(pair env' b') => Combined.Let b' (tidyExpr env' e))
           | env, Combined.Case e b ty alts =>
               tidyBndr env b =:
               (fun '(pair env' b) =>
                  Combined.Case (tidyExpr env e) b (tt) (GHC.Base.map ((fun env x =>
                                                                          let 'pair (pair con vs) rhs := x in
                                                                          let 'pair env' vs := tidyBndrs env vs in
                                                                          pair (pair con vs) (tidyExpr env' rhs)) env')
                                                         alts))
           | env, Combined.Lam b e =>
               tidyBndr env b =: (fun '(pair env' b) => Combined.Lam b (tidyExpr env' e))
           end with tidyBind arg_0__ arg_1__
                      := match arg_0__, arg_1__ with
                         | env, Combined.NonRec bndr rhs =>
                             tidyLetBndr env env (pair bndr rhs) =:
                             (fun '(pair env' bndr') =>
                                pair env' (Combined.NonRec bndr' (tidyExpr env' rhs)))
                         | env, Combined.Rec prs =>
                             let 'pair env' bndrs' := Data.Traversable.mapAccumL (tidyLetBndr
                                                                                  GHC.Err.default) env prs in
                             GHC.Base.map (fun x => tidyExpr env' (snd x)) prs =:
                             (fun rhss' => pair env' (Combined.Rec (GHC.List.zip bndrs' rhss')))
                         end for tidyExpr.

Definition tidyAlt : Combined.TidyEnv -> Combined.CoreAlt -> Combined.CoreAlt :=
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
     None Some bool list op_zt__ pair snd tt Combined.App Combined.Breakpoint
     Combined.Case Combined.Cast Combined.Coercion Combined.CoreAlt Combined.CoreBind
     Combined.CoreExpr Combined.Lam Combined.Let Combined.Lit Combined.Mk_Var
     Combined.NonRec Combined.Rec Combined.Tick Combined.Tickish Combined.TidyEnv
     Combined.Type_ Combined.Var Combined.evaldUnfolding Combined.extendVarEnv
     Combined.idDetails Combined.idInfo Combined.inlinePragInfo
     Combined.isEvaldUnfolding Combined.lookupVarEnv Combined.mkLocalVar
     Combined.noUnfolding Combined.occInfo Combined.oneShotInfo Combined.setArityInfo
     Combined.setInlinePragInfo Combined.setOccInfo Combined.setOneShotInfo
     Combined.unfoldingInfo Combined.vanillaIdInfo CoreArity.exprArity
     Data.Traversable.mapAccumL GHC.Base.map GHC.Err.default GHC.List.zip
     GHC.Prim.seq Id.idName Id.idUnique Id.mkLocalIdWithInfo Maybes.orElse Name.Name
     Name.getOccName Name.mkInternalName OccName.tidyOccName SrcLoc.noSrcSpan
     UniqFM.lookupUFM
*)
