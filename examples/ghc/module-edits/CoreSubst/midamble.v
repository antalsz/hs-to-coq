Instance Default_Subst : GHC.Err.Default Subst :=
  GHC.Err.Build_Default _ (Mk_Subst GHC.Err.default GHC.Err.default tt tt).


Parameter substBind1 :  Subst -> Combined.CoreBind -> (Subst * Combined.CoreBind)%type.
Parameter substBndrs1 : Subst -> list Combined.Var -> (Subst * list Combined.Var)%type.
Parameter substBndr1 : Subst -> Combined.Var -> (Subst * Combined.Var)%type.
Parameter substRecBndrs1 : Subst -> list Combined.Var -> (Subst * list Combined.Var)%type.
Parameter substIdBndr1
   : GHC.Base.String -> Subst -> Subst -> Combined.Var -> (Subst * Combined.Var)%type.

Parameter substIdInfo1
   : Subst -> Combined.Var -> Combined.IdInfo -> option Combined.IdInfo.


Definition mkOpenSubst
   : Combined.InScopeSet -> (list (Combined.Var * Combined.CoreArg) -> Subst) :=
  fun in_scope pairs =>
    Mk_Subst in_scope (Combined.mkVarEnv (Coq.Lists.List.flat_map (fun arg_1__ => let 'pair id e := arg_1__ in
                                          if Combined.isId id then cons (pair id e) nil else
                                          nil) pairs)) tt tt. 

(* TODO: Recursive KNOT tying!!! *)
(*
Parameter substRecBndrs : Subst -> list Combined.Var -> (Subst * list Combined.Var)%type.

(*
Definition substRecBndrs : Subst -> list Combined.Var -> (Subst * list Combined.Var)%type :=
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
     UniqSupply.UniqSupply -> list Combined.Var -> (Subst * list Combined.Var)%type.
*)