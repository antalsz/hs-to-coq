Instance Default_Subst : GHC.Err.Default Subst :=
  GHC.Err.Build_Default _ (Mk_Subst GHC.Err.default GHC.Err.default tt tt).


Parameter substBind1 :  Subst -> CoreSyn.CoreBind -> (Subst * CoreSyn.CoreBind)%type.
Parameter substBndrs1 : Subst -> list Var.Var -> (Subst * list Var.Var)%type.
Parameter substBndr1 : Subst -> Var.Var -> (Subst * Var.Var)%type.
Parameter substRecBndrs1 : Subst -> list Var.Id -> (Subst * list Var.Id)%type.
Parameter substIdBndr1
   : GHC.Base.String -> Subst -> Subst -> Var.Id -> (Subst * Var.Id)%type.

Parameter substIdInfo1
   : Subst -> Var.Id -> IdInfo.IdInfo -> option IdInfo.IdInfo.


Definition mkOpenSubst
   : VarEnv.InScopeSet -> (list (Var.Var * CoreSyn.CoreArg) -> Subst) :=
  fun in_scope pairs =>
    Mk_Subst in_scope (VarEnv.mkVarEnv (Coq.Lists.List.flat_map (fun arg_1__ => let 'pair id e := arg_1__ in
                                          if Var.isId id then cons (pair id e) nil else
                                          nil) pairs)) tt tt. 

(* TODO: Recursive KNOT tying!!! *)
(*
Parameter substRecBndrs : Subst -> list Var.Id -> (Subst * list Var.Id)%type.

(*
Definition substRecBndrs : Subst -> list Var.Id -> (Subst * list Var.Id)%type :=
  fun subst bndrs =>
    let 'pair new_subst new_bndrs := 
        Data.Traversable.mapAccumL (substIdBndr
                                      (Datatypes.id (GHC.Base.hs_string__ "rec-bndr"))
                                      new_subst) subst bndrs in
    pair new_subst new_bndrs.
*)

(* TODO: recursive knot *)
Parameter cloneRecIdBndrs
   : Subst ->
     UniqSupply.UniqSupply -> list Var.Id -> (Subst * list Var.Id)%type.
*)