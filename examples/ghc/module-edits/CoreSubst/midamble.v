Instance Default_Subst : GHC.Err.Default Subst :=
  GHC.Err.Build_Default _ (Mk_Subst GHC.Err.default GHC.Err.default tt tt).

(*
Definition mkOpenSubst
   : Core.InScopeSet -> (list (Core.Var * Core.CoreArg) -> Subst) :=
  fun in_scope pairs =>
    Mk_Subst in_scope (Core.mkVarEnv (Coq.Lists.List.flat_map (fun arg_1__ => let 'pair id e := arg_1__ in
                                          if Core.isId id then cons (pair id e) nil else
                                          nil) pairs)) tt tt. 

*)