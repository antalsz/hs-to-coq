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
Require Data.Foldable.
Require Data.Tuple.
Require DynFlags.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require MkCore.
Require Panic.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition FreeVarSet :=
  Core.DIdSet%type.

Definition BoundVarSet :=
  Core.DIdSet%type.

Inductive FloatInBind : Type
  := | FB : BoundVarSet -> FreeVarSet -> MkCore.FloatBind -> FloatInBind.

Definition FloatInBinds :=
  (list FloatInBind)%type.

Definition DropBox :=
  (FreeVarSet * FloatInBinds)%type%type.

(* Midamble *)

Instance Default_FloatBind : GHC.Err.Default MkCore.FloatBind :=  {}.
Admitted.

Instance Default_FloatInBind : GHC.Err.Default FloatInBind := 
  GHC.Err.Build_Default _ (FB GHC.Err.default GHC.Err.default GHC.Err.default).

(* Converted value declarations: *)

Definition wrapFloats : FloatInBinds -> Core.CoreExpr -> Core.CoreExpr :=
  fix wrapFloats (arg_0__ : FloatInBinds) (arg_1__ : Core.CoreExpr)
        : Core.CoreExpr
        := match arg_0__, arg_1__ with
           | nil, e => e
           | cons (FB _ _ fl) bs, e => wrapFloats bs (MkCore.wrapFloat fl e)
           end.

Definition noFloatIntoLam : list Core.Var -> bool :=
  fun bndrs =>
    let bad := fun b => andb (Core.isId b) (negb (Id.isOneShotBndr b)) in
    Data.Foldable.any bad bndrs.

Definition noFloatIntoArg
   : CoreFVs.CoreExprWithFVs' -> AxiomatizedTypes.Type_ -> bool :=
  fun expr expr_ty =>
    let deann_expr := Core.deAnnotate' expr in
    if (@Core.isUnliftedType tt expr_ty) : bool then true else
    match expr with
    | Core.AnnLam bndr e =>
        let 'pair bndrs _ := Core.collectAnnBndrs e in
        orb (noFloatIntoLam (cons bndr bndrs)) (Data.Foldable.all Core.isTyVar (cons
                                                                                bndr bndrs))
    | _ => orb (CoreUtils.exprIsTrivial deann_expr) (CoreUtils.exprIsHNF deann_expr)
    end.

Definition noFloatIntoRhs
   : BasicTypes.RecFlag -> Core.Id -> CoreFVs.CoreExprWithFVs' -> bool :=
  fun is_rec bndr rhs =>
    if Id.isJoinId bndr : bool then BasicTypes.isRec is_rec else
    noFloatIntoArg rhs (Id.idType bndr).

Definition floatIsDupable : DynFlags.DynFlags -> MkCore.FloatBind -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | dflags, MkCore.FloatCase scrut _ _ _ => CoreUtils.exprIsDupable dflags scrut
    | dflags, MkCore.FloatLet (Core.Rec prs) =>
        Data.Foldable.all (CoreUtils.exprIsDupable dflags GHC.Base.∘ Data.Tuple.snd) prs
    | dflags, MkCore.FloatLet (Core.NonRec _ r) => CoreUtils.exprIsDupable dflags r
    end.

Definition floatIsCase : MkCore.FloatBind -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | MkCore.FloatCase _ _ _ _ => true
    | MkCore.FloatLet _ => false
    end.

Definition sepBindsByDropPoint
   : DynFlags.DynFlags ->
     bool -> list FreeVarSet -> FloatInBinds -> list FloatInBinds :=
  fun dflags is_case drop_pts floaters =>
    let n_alts := Coq.Lists.List.length drop_pts in
    let go : FloatInBinds -> list DropBox -> list FloatInBinds :=
      fix go (arg_1__ : FloatInBinds) (arg_2__ : list DropBox) : list FloatInBinds
            := match arg_1__, arg_2__ with
               | nil, drop_boxes =>
                   GHC.Base.map (GHC.List.reverse GHC.Base.∘ Data.Tuple.snd) drop_boxes
               | cons (FB bndrs bind_fvs bind as bind_w_fvs) binds
               , (cons here_box fork_boxes as drop_boxes) =>
                   let insert : DropBox -> DropBox :=
                     fun '(pair fvs drops) =>
                       pair (Core.unionDVarSet fvs bind_fvs) (cons bind_w_fvs drops) in
                   let insert_maybe :=
                     fun arg_7__ arg_8__ =>
                       match arg_7__, arg_8__ with
                       | box, true => insert box
                       | box, false => box
                       end in
                   match (let cont_11__ arg_12__ :=
                              let 'pair fvs _ := arg_12__ in
                              cons (Core.intersectsDVarSet fvs bndrs) nil in
                            Coq.Lists.List.flat_map cont_11__ drop_boxes) with
                   | cons used_here used_in_flags =>
                       let n_used_alts := Util.count GHC.Base.id used_in_flags in
                       let cant_push :=
                         if is_case : bool
                         then orb (n_used_alts GHC.Base.== n_alts) (andb (n_used_alts GHC.Base.> #1)
                                                                         (negb (floatIsDupable dflags bind))) else
                         orb (floatIsCase bind) (n_used_alts GHC.Base.> #1) in
                       let drop_here := orb used_here cant_push in
                       let new_fork_boxes :=
                         Util.zipWithEqual (GHC.Base.hs_string__ "FloatIn.sepBinds") insert_maybe
                         fork_boxes used_in_flags in
                       let new_boxes :=
                         if drop_here : bool then (cons (insert here_box) fork_boxes) else
                         (cons here_box new_fork_boxes) in
                       go binds new_boxes
                   | _ => GHC.Err.patternFailure
                   end
               | _, _ => Panic.panic (GHC.Base.hs_string__ "sepBindsByDropPoint/go")
               end in
    if Data.Foldable.null floaters : bool
    then cons nil (Coq.Lists.List.flat_map (fun _ => cons nil nil) drop_pts) else
    if andb Util.debugIsOn (negb (Util.lengthAtLeast drop_pts #2)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__
                             "ghc/compiler/simplCore/FloatIn.hs") #680)
    else go floaters (GHC.Base.map (fun fvs => pair fvs nil) (cons Core.emptyDVarSet
                                                                   drop_pts)).

Axiom fiExpr : DynFlags.DynFlags ->
               FloatInBinds -> CoreFVs.CoreExprWithFVs -> Core.CoreExpr.

Definition fiRhs
   : DynFlags.DynFlags ->
     FloatInBinds -> Core.CoreBndr -> CoreFVs.CoreExprWithFVs -> Core.CoreExpr :=
  fun dflags to_drop bndr rhs =>
    match Id.isJoinId_maybe bndr with
    | Some join_arity =>
        let 'pair bndrs body := Core.collectNAnnBndrs join_arity rhs in
        Core.mkLams bndrs (fiExpr dflags to_drop body)
    | _ => fiExpr dflags to_drop rhs
    end.

Definition fbFVs : FloatInBind -> Core.DVarSet :=
  fun '(FB _ fvs _) => fvs.

Definition floatedBindsFVs : FloatInBinds -> FreeVarSet :=
  fun binds => Core.mapUnionDVarSet fbFVs binds.

Definition fiBind
   : DynFlags.DynFlags ->
     FloatInBinds ->
     CoreFVs.CoreBindWithFVs ->
     Core.DVarSet -> (FloatInBinds * FloatInBind * FloatInBinds)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | dflags, to_drop, Core.AnnNonRec id (pair rhs_fvs rhs as ann_rhs), body_fvs =>
        let rule_fvs := CoreFVs.bndrRuleAndUnfoldingVarsDSet id in
        let extra_fvs :=
          if noFloatIntoRhs BasicTypes.NonRecursive id rhs : bool
          then Core.unionDVarSet rule_fvs rhs_fvs else
          rule_fvs in
        let body_fvs2 := Core.delDVarSet body_fvs id in
        match sepBindsByDropPoint dflags false (cons extra_fvs (cons rhs_fvs (cons
                                                                      body_fvs2 nil))) to_drop with
        | cons shared_binds (cons extra_binds (cons rhs_binds (cons body_binds nil))) =>
            let rhs' := fiRhs dflags rhs_binds id ann_rhs in
            let rhs_fvs' :=
              Core.unionDVarSet (Core.unionDVarSet rhs_fvs (floatedBindsFVs rhs_binds))
                                rule_fvs in
            pair (pair (Coq.Init.Datatypes.app extra_binds shared_binds) (FB
                        (Core.unitDVarSet id) rhs_fvs' (MkCore.FloatLet (Core.NonRec id rhs'))))
                 body_binds
        | _ => GHC.Err.patternFailure
        end
    | dflags, to_drop, Core.AnnRec bindings, body_fvs =>
        let fi_bind
         : list FloatInBinds ->
           list (Core.Id * CoreFVs.CoreExprWithFVs)%type ->
           list (Core.Id * Core.CoreExpr)%type :=
          fun to_drops pairs =>
            let cont_11__ arg_12__ :=
              let 'pair (pair binder rhs) to_drop := arg_12__ in
              cons (pair binder (fiRhs dflags to_drop binder rhs)) nil in
            Coq.Lists.List.flat_map cont_11__ (Util.zipEqual (GHC.Base.hs_string__
                                                              "fi_bind") pairs to_drops) in
        let 'pair ids rhss := GHC.List.unzip bindings in
        let rhss_fvs := GHC.Base.map CoreFVs.freeVarsOf rhss in
        let rule_fvs := Core.mapUnionDVarSet CoreFVs.bndrRuleAndUnfoldingVarsDSet ids in
        let extra_fvs :=
          Core.unionDVarSet rule_fvs (Core.unionDVarSets (let cont_17__ arg_18__ :=
                                                            let 'pair bndr (pair rhs_fvs rhs) := arg_18__ in
                                                            if noFloatIntoRhs BasicTypes.Recursive bndr rhs : bool
                                                            then cons rhs_fvs nil else
                                                            nil in
                                                          Coq.Lists.List.flat_map cont_17__ bindings)) in
        match sepBindsByDropPoint dflags false (cons extra_fvs (cons body_fvs rhss_fvs))
                to_drop with
        | cons shared_binds (cons extra_binds (cons body_binds rhss_binds)) =>
            let rhs_fvs' :=
              Core.unionDVarSet (Core.unionDVarSet (Core.unionDVarSets rhss_fvs)
                                                   (Core.unionDVarSets (GHC.Base.map floatedBindsFVs rhss_binds)))
                                rule_fvs in
            pair (pair (Coq.Init.Datatypes.app extra_binds shared_binds) (FB (Core.mkDVarSet
                                                                              ids) rhs_fvs' (MkCore.FloatLet (Core.Rec
                                                                                                              (fi_bind
                                                                                                               rhss_binds
                                                                                                               bindings)))))
                 body_binds
        | _ => GHC.Err.patternFailure
        end
    end.

(* External variables:
     Some andb bool cons false list negb nil op_zt__ orb pair true tt
     AxiomatizedTypes.Type_ BasicTypes.NonRecursive BasicTypes.RecFlag
     BasicTypes.Recursive BasicTypes.isRec Coq.Init.Datatypes.app
     Coq.Lists.List.flat_map Coq.Lists.List.length Core.AnnLam Core.AnnNonRec
     Core.AnnRec Core.CoreBndr Core.CoreExpr Core.DIdSet Core.DVarSet Core.Id
     Core.NonRec Core.Rec Core.Var Core.collectAnnBndrs Core.collectNAnnBndrs
     Core.deAnnotate' Core.delDVarSet Core.emptyDVarSet Core.intersectsDVarSet
     Core.isId Core.isTyVar Core.isUnliftedType Core.mapUnionDVarSet Core.mkDVarSet
     Core.mkLams Core.unionDVarSet Core.unionDVarSets Core.unitDVarSet
     CoreFVs.CoreBindWithFVs CoreFVs.CoreExprWithFVs CoreFVs.CoreExprWithFVs'
     CoreFVs.bndrRuleAndUnfoldingVarsDSet CoreFVs.freeVarsOf CoreUtils.exprIsDupable
     CoreUtils.exprIsHNF CoreUtils.exprIsTrivial Data.Foldable.all Data.Foldable.any
     Data.Foldable.null Data.Tuple.snd DynFlags.DynFlags GHC.Base.id GHC.Base.map
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Err.patternFailure
     GHC.List.reverse GHC.List.unzip GHC.Num.fromInteger Id.idType Id.isJoinId
     Id.isJoinId_maybe Id.isOneShotBndr MkCore.FloatBind MkCore.FloatCase
     MkCore.FloatLet MkCore.wrapFloat Panic.assertPanic Panic.panic Util.count
     Util.debugIsOn Util.lengthAtLeast Util.zipEqual Util.zipWithEqual
*)
