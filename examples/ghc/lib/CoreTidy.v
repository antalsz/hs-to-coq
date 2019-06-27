(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Core.
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
Require TyCoRep.
Require UniqFM.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition tidyVarOcc : Core.TidyEnv -> Core.Var -> Core.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair _ var_env, v => Maybes.orElse (Core.lookupVarEnv var_env v) v
    end.

Definition tidyUnfolding
   : Core.TidyEnv -> Core.Unfolding -> Core.Unfolding -> Core.Unfolding :=
  fun e u v => u.

Definition tidyTickish
   : Core.TidyEnv -> Core.Tickish Core.Id -> Core.Tickish Core.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | env, Core.Breakpoint ix ids =>
        Core.Breakpoint ix (GHC.Base.map (tidyVarOcc env) ids)
    | _, other_tickish => other_tickish
    end.

Definition tidyNameOcc : Core.TidyEnv -> Name.Name -> Name.Name :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair _ var_env, n =>
        match UniqFM.lookupUFM var_env n with
        | None => n
        | Some v => Id.idName v
        end
    end.

Definition tidyLetBndr
   : Core.TidyEnv ->
     Core.TidyEnv ->
     (Core.Id * Core.CoreExpr)%type -> (Core.TidyEnv * Core.Var)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | rec_tidy_env, (pair tidy_env var_env as env), pair id rhs =>
        let 'pair tidy_env' occ' := OccName.tidyOccName tidy_env (Name.getOccName id) in
        let old_info := (@Core.idInfo tt id) in
        let old_unf := Core.unfoldingInfo old_info in
        let new_unf :=
          if Core.isStableUnfolding old_unf : bool
          then tidyUnfolding rec_tidy_env old_unf old_unf else
          Core.noUnfolding in
        let new_info :=
          Core.setUnfoldingInfo (Core.setInlinePragInfo (Core.setDemandInfo
                                                         (Core.setStrictnessInfo (Core.setArityInfo (Core.setOccInfo
                                                                                                     Core.vanillaIdInfo
                                                                                                     (Core.occInfo
                                                                                                      old_info))
                                                                                                    (CoreArity.exprArity
                                                                                                     rhs))
                                                                                 (Core.zapUsageEnvSig
                                                                                  (Core.strictnessInfo old_info)))
                                                         (Core.demandInfo old_info)) (Core.inlinePragInfo old_info))
                                new_unf in
        let details := Core.idDetails id in
        let name' := Name.mkInternalName (Id.idUnique id) occ' SrcLoc.noSrcSpan in
        let ty' := TyCoRep.tidyType env (Id.idType id) in
        let id' := Core.mkLocalVar details name' ty' new_info in
        let var_env' := Core.extendVarEnv var_env id id' in
        pair (pair tidy_env' var_env') id'
    end.

Definition tidyIdBndr
   : Core.TidyEnv -> Core.Id -> (Core.TidyEnv * Core.Id)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (pair tidy_env var_env as env), id =>
        let 'pair tidy_env' occ' := OccName.tidyOccName tidy_env (Name.getOccName id) in
        let old_info := (@Core.idInfo tt id) in
        let old_unf := Core.unfoldingInfo old_info in
        let new_unf := Core.noUnfolding in
        let new_info :=
          Core.setOneShotInfo (Core.setUnfoldingInfo (Core.setOccInfo Core.vanillaIdInfo
                                                                      (Core.occInfo old_info)) new_unf)
                              (Core.oneShotInfo old_info) in
        let name' := Name.mkInternalName (Id.idUnique id) occ' SrcLoc.noSrcSpan in
        let ty' := TyCoRep.tidyType env (Id.idType id) in
        let id' := Id.mkLocalIdWithInfo name' ty' new_info in
        let var_env' := Core.extendVarEnv var_env id id' in
        pair (pair tidy_env' var_env') id'
    end.

Definition tidyBndr
   : Core.TidyEnv -> Core.Var -> (Core.TidyEnv * Core.Var)%type :=
  fun env var =>
    if Core.isTyCoVar var : bool then TyCoRep.tidyTyCoVarBndr env var else
    tidyIdBndr env var.

Definition tidyBndrs
   : Core.TidyEnv -> list Core.Var -> (Core.TidyEnv * list Core.Var)%type :=
  fun env vars => Data.Traversable.mapAccumL tidyBndr env vars.

Definition op_zeZC__ {a} {b} : a -> (a -> b) -> b :=
  fun m k => GHC.Prim.seq m (k m).

Notation "'_=:_'" := (op_zeZC__).

Infix "=:" := (_=:_) (at level 99).

Definition tidyBind
   : Core.TidyEnv -> Core.CoreBind -> (Core.TidyEnv * Core.CoreBind)%type :=
  fix tidyExpr (arg_0__ : Core.TidyEnv) (arg_1__ : Core.CoreExpr) : Core.CoreExpr
        := let tidyAlt (arg_0__ : Core.TidyEnv) (arg_1__ : Core.CoreAlt)
            : Core.CoreAlt :=
             match arg_0__, arg_1__ with
             | env, pair (pair con vs) rhs =>
                 tidyBndrs env vs =:
                 (fun '(pair env' vs) => pair (pair con vs) (tidyExpr env' rhs))
             end in
           match arg_0__, arg_1__ with
           | env, Core.Mk_Var v => Core.Mk_Var (tidyVarOcc env v)
           | env => Core.Type_ (TyCoRep.tidyType env ty)
           | env => Core.Coercion (TyCoRep.tidyCo env co)
           | _, Core.Lit lit => Core.Lit lit
           | env, Core.App f a => Core.App (tidyExpr env f) (tidyExpr env a)
           | env => Core.Tick (tidyTickish env t) (tidyExpr env e)
           | env => Core.Cast (tidyExpr env e) (TyCoRep.tidyCo env co)
           | env, Core.Let b e =>
               tidyBind env b =: (fun '(pair env' b') => Core.Let b' (tidyExpr env' e))
           | env, Core.Case e b ty alts =>
               tidyBndr env b =:
               (fun '(pair env' b) =>
                  Core.Case (tidyExpr env e) b (TyCoRep.tidyType env ty) (GHC.Base.map (tidyAlt
                                                                                        env') alts))
           | env, Core.Lam b e =>
               tidyBndr env b =: (fun '(pair env' b) => Core.Lam b (tidyExpr env' e))
           end with tidyBind (arg_0__ : Core.TidyEnv) (arg_1__ : Core.CoreBind)
                      : (Core.TidyEnv * Core.CoreBind)%type
                      := match arg_0__, arg_1__ with
                         | env, Core.NonRec bndr rhs =>
                             tidyLetBndr env env (pair bndr rhs) =:
                             (fun '(pair env' bndr') => pair env' (Core.NonRec bndr' (tidyExpr env' rhs)))
                         | env, Core.Rec prs =>
                             let 'pair env' bndrs' := Data.Traversable.mapAccumL (tidyLetBndr
                                                                                  GHC.Err.default) env prs in
                             GHC.Base.map (fun x => tidyExpr env' (snd x)) prs =:
                             (fun rhss' => pair env' (Core.Rec (GHC.List.zip bndrs' rhss')))
                         end for tidyBind.

Definition tidyExpr : Core.TidyEnv -> Core.CoreExpr -> Core.CoreExpr :=
  fix tidyExpr (arg_0__ : Core.TidyEnv) (arg_1__ : Core.CoreExpr) : Core.CoreExpr
        := let tidyAlt (arg_0__ : Core.TidyEnv) (arg_1__ : Core.CoreAlt)
            : Core.CoreAlt :=
             match arg_0__, arg_1__ with
             | env, pair (pair con vs) rhs =>
                 tidyBndrs env vs =:
                 (fun '(pair env' vs) => pair (pair con vs) (tidyExpr env' rhs))
             end in
           match arg_0__, arg_1__ with
           | env, Core.Mk_Var v => Core.Mk_Var (tidyVarOcc env v)
           | env => Core.Type_ (TyCoRep.tidyType env ty)
           | env => Core.Coercion (TyCoRep.tidyCo env co)
           | _, Core.Lit lit => Core.Lit lit
           | env, Core.App f a => Core.App (tidyExpr env f) (tidyExpr env a)
           | env => Core.Tick (tidyTickish env t) (tidyExpr env e)
           | env => Core.Cast (tidyExpr env e) (TyCoRep.tidyCo env co)
           | env, Core.Let b e =>
               tidyBind env b =: (fun '(pair env' b') => Core.Let b' (tidyExpr env' e))
           | env, Core.Case e b ty alts =>
               tidyBndr env b =:
               (fun '(pair env' b) =>
                  Core.Case (tidyExpr env e) b (TyCoRep.tidyType env ty) (GHC.Base.map (tidyAlt
                                                                                        env') alts))
           | env, Core.Lam b e =>
               tidyBndr env b =: (fun '(pair env' b) => Core.Lam b (tidyExpr env' e))
           end with tidyBind (arg_0__ : Core.TidyEnv) (arg_1__ : Core.CoreBind)
                      : (Core.TidyEnv * Core.CoreBind)%type
                      := match arg_0__, arg_1__ with
                         | env, Core.NonRec bndr rhs =>
                             tidyLetBndr env env (pair bndr rhs) =:
                             (fun '(pair env' bndr') => pair env' (Core.NonRec bndr' (tidyExpr env' rhs)))
                         | env, Core.Rec prs =>
                             let 'pair env' bndrs' := Data.Traversable.mapAccumL (tidyLetBndr
                                                                                  GHC.Err.default) env prs in
                             GHC.Base.map (fun x => tidyExpr env' (snd x)) prs =:
                             (fun rhss' => pair env' (Core.Rec (GHC.List.zip bndrs' rhss')))
                         end for tidyExpr.

Definition tidyAlt : Core.TidyEnv -> Core.CoreAlt -> Core.CoreAlt :=
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
     None Some bool co e list op_zt__ pair snd t tt ty Core.App Core.Breakpoint
     Core.Case Core.Cast Core.Coercion Core.CoreAlt Core.CoreBind Core.CoreExpr
     Core.Id Core.Lam Core.Let Core.Lit Core.Mk_Var Core.NonRec Core.Rec Core.Tick
     Core.Tickish Core.TidyEnv Core.Type_ Core.Unfolding Core.Var Core.demandInfo
     Core.extendVarEnv Core.idDetails Core.idInfo Core.inlinePragInfo
     Core.isStableUnfolding Core.isTyCoVar Core.lookupVarEnv Core.mkLocalVar
     Core.noUnfolding Core.occInfo Core.oneShotInfo Core.setArityInfo
     Core.setDemandInfo Core.setInlinePragInfo Core.setOccInfo Core.setOneShotInfo
     Core.setStrictnessInfo Core.setUnfoldingInfo Core.strictnessInfo
     Core.unfoldingInfo Core.vanillaIdInfo Core.zapUsageEnvSig CoreArity.exprArity
     Data.Traversable.mapAccumL GHC.Base.map GHC.Err.default GHC.List.zip
     GHC.Prim.seq Id.idName Id.idType Id.idUnique Id.mkLocalIdWithInfo Maybes.orElse
     Name.Name Name.getOccName Name.mkInternalName OccName.tidyOccName
     SrcLoc.noSrcSpan TyCoRep.tidyCo TyCoRep.tidyTyCoVarBndr TyCoRep.tidyType
     UniqFM.lookupUFM
*)
