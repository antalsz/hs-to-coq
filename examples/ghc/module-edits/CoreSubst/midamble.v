Instance Default_Subst : GHC.Err.Default Subst :=
  GHC.Err.Build_Default _ (Mk_Subst GHC.Err.default GHC.Err.default tt tt).


Parameter substBind1 :  Subst -> Core.CoreBind -> (Subst * Core.CoreBind)%type.
Parameter substBndrs1 : Subst -> list Core.Var -> (Subst * list Core.Var)%type.
Parameter substBndr1 : Subst -> Core.Var -> (Subst * Core.Var)%type.
Parameter substRecBndrs1 : Subst -> list Core.Var -> (Subst * list Core.Var)%type.
Parameter substIdBndr1
   : GHC.Base.String -> Subst -> Subst -> Core.Var -> (Subst * Core.Var)%type.

Parameter substIdInfo1
   : Subst -> Core.Var -> Core.IdInfo -> option Core.IdInfo.


Definition mkOpenSubst
   : Core.InScopeSet -> (list (Core.Var * Core.CoreArg) -> Subst) :=
  fun in_scope pairs =>
    Mk_Subst in_scope (Core.mkVarEnv (Coq.Lists.List.flat_map (fun arg_1__ => let 'pair id e := arg_1__ in
                                          if Core.isId id then cons (pair id e) nil else
                                          nil) pairs)) tt tt. 

(* TODO: Recursive KNOT tying!!! *)
(*
Parameter substRecBndrs : Subst -> list Core.Var -> (Subst * list Core.Var)%type.

(*
Definition substRecBndrs : Subst -> list Core.Var -> (Subst * list Core.Var)%type :=
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
     UniqSupply.UniqSupply -> list Core.Var -> (Subst * list Core.Var)%type.
*)
