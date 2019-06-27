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
Require Core.
Require Data.Foldable.
Require Data.Maybe.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.Num.
Require Id.
Require Literal.
Require OrdList.
Require Panic.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition CheapAppFun :=
  (Core.Id -> BasicTypes.Arity -> bool)%type.

(* Converted value declarations: *)

Axiom tryEtaReduce : list Core.Var -> Core.CoreExpr -> option Core.CoreExpr.

Definition trimConArgs
   : Core.AltCon -> list Core.CoreArg -> list Core.CoreArg :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Core.DEFAULT, args =>
        if andb Util.debugIsOn (negb (Data.Foldable.null args)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/coreSyn/CoreUtils.hs") #600)
        else nil
    | Core.LitAlt _, args =>
        if andb Util.debugIsOn (negb (Data.Foldable.null args)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/coreSyn/CoreUtils.hs") #601)
        else nil
    | Core.DataAlt dc, args => Util.dropList (Core.dataConUnivTyVars dc) args
    end.

Definition tickHNFArgs
   : Core.Tickish Core.Var -> Core.CoreExpr -> Core.CoreExpr :=
  fun t orig => orig.

Definition stripTicksTopE {b}
   : (Core.Tickish Core.Id -> bool) -> Core.Expr b -> Core.Expr b :=
  fun p => let go := fun '(other) => other in go.

Definition stripTicksT {b}
   : (Core.Tickish Core.Id -> bool) ->
     Core.Expr b -> list (Core.Tickish Core.Id) :=
  fun p expr =>
    let go :=
      fix go arg_0__
            := let go_a (arg_13__ : Core.Alt b) : OrdList.OrdList (Core.Tickish Core.Id) :=
                 let 'pair (pair _ _) e := arg_13__ in
                 go e in
               match arg_0__ with
               | Core.App e a => OrdList.appOL (go e) (go a)
               | Core.Lam _ e => go e
               | Core.Let b e => OrdList.appOL (go_bs b) (go e)
               | Core.Case e _ _ as_ =>
                   OrdList.appOL (go e) (OrdList.concatOL (GHC.Base.map go_a as_))
               | _ => OrdList.nilOL
               end with go_bs arg_6__
                          := let go_b (arg_10__ : b * Core.Expr b)
                              : OrdList.OrdList (Core.Tickish Core.Id) :=
                               let 'pair _ e := arg_10__ in
                               go e in
                             match arg_6__ with
                             | Core.NonRec _ e => go e
                             | Core.Rec bs => OrdList.concatOL (GHC.Base.map go_b bs)
                             end for go in
    let go_bs :=
      fix go arg_0__
            := let go_a (arg_13__ : Core.Alt b) : OrdList.OrdList (Core.Tickish Core.Id) :=
                 let 'pair (pair _ _) e := arg_13__ in
                 go e in
               match arg_0__ with
               | Core.App e a => OrdList.appOL (go e) (go a)
               | Core.Lam _ e => go e
               | Core.Let b e => OrdList.appOL (go_bs b) (go e)
               | Core.Case e _ _ as_ =>
                   OrdList.appOL (go e) (OrdList.concatOL (GHC.Base.map go_a as_))
               | _ => OrdList.nilOL
               end with go_bs arg_6__
                          := let go_b (arg_10__ : b * Core.Expr b)
                              : OrdList.OrdList (Core.Tickish Core.Id) :=
                               let 'pair _ e := arg_10__ in
                               go e in
                             match arg_6__ with
                             | Core.NonRec _ e => go e
                             | Core.Rec bs => OrdList.concatOL (GHC.Base.map go_b bs)
                             end for go_bs in
    let go_b : b * Core.Expr b -> OrdList.OrdList (Core.Tickish Core.Id) :=
      fun '(pair _ e) => go e in
    let go_a : Core.Alt b -> OrdList.OrdList (Core.Tickish Core.Id) :=
      fun '(pair (pair _ _) e) => go e in
    OrdList.fromOL (go expr).

Definition stripTicksE {b}
   : (Core.Tickish Core.Id -> bool) -> Core.Expr b -> Core.Expr b :=
  fun p expr =>
    let go :=
      fix go arg_0__
            := let go_a (arg_13__ : Core.Alt b) : Core.Alt b :=
                 let 'pair (pair c bs) e := arg_13__ in
                 pair (pair c bs) (go e) in
               match arg_0__ with
               | Core.App e a => Core.App (go e) (go a)
               | Core.Lam b e => Core.Lam b (go e)
               | Core.Let b e => Core.Let (go_bs b) (go e)
               | Core.Case e b t as_ => Core.Case (go e) b t (GHC.Base.map go_a as_)
               | other => other
               end with go_bs arg_6__
                          := let go_b (arg_10__ : b * Core.Expr b) : b * Core.Expr b :=
                               let 'pair b e := arg_10__ in
                               pair b (go e) in
                             match arg_6__ with
                             | Core.NonRec b e => Core.NonRec b (go e)
                             | Core.Rec bs => Core.Rec (GHC.Base.map go_b bs)
                             end for go in
    let go_bs :=
      fix go arg_0__
            := let go_a (arg_13__ : Core.Alt b) : Core.Alt b :=
                 let 'pair (pair c bs) e := arg_13__ in
                 pair (pair c bs) (go e) in
               match arg_0__ with
               | Core.App e a => Core.App (go e) (go a)
               | Core.Lam b e => Core.Lam b (go e)
               | Core.Let b e => Core.Let (go_bs b) (go e)
               | Core.Case e b t as_ => Core.Case (go e) b t (GHC.Base.map go_a as_)
               | other => other
               end with go_bs arg_6__
                          := let go_b (arg_10__ : b * Core.Expr b) : b * Core.Expr b :=
                               let 'pair b e := arg_10__ in
                               pair b (go e) in
                             match arg_6__ with
                             | Core.NonRec b e => Core.NonRec b (go e)
                             | Core.Rec bs => Core.Rec (GHC.Base.map go_b bs)
                             end for go_bs in
    let go_b : b * Core.Expr b -> b * Core.Expr b :=
      fun '(pair b e) => pair b (go e) in
    let go_a : Core.Alt b -> Core.Alt b :=
      fun '(pair (pair c bs) e) => pair (pair c bs) (go e) in
    go expr.

Axiom refineDefaultAlt : list Unique.Unique ->
                         Core.TyCon ->
                         list AxiomatizedTypes.Type_ ->
                         list Core.AltCon -> list Core.CoreAlt -> (bool * list Core.CoreAlt)%type.

Axiom needsCaseBinding : AxiomatizedTypes.Type_ -> Core.CoreExpr -> bool.

Definition mkTickNoHNF
   : Core.Tickish Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun t e => if exprIsHNF e : bool then tickHNFArgs t e else mkTick t e.

Definition mkAltExpr
   : Core.AltCon ->
     list Core.CoreBndr -> list AxiomatizedTypes.Type_ -> Core.CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Core.DataAlt con, args, inst_tys =>
        Core.mkConApp con (Coq.Init.Datatypes.app (GHC.Base.map Core.Type_ inst_tys)
                                                  (Core.varsToCoreExprs args))
    | Core.LitAlt lit, nil, nil => Core.Lit lit
    | Core.LitAlt _, _, _ => Panic.panic (GHC.Base.hs_string__ "mkAltExpr LitAlt")
    | Core.DEFAULT, _, _ => Panic.panic (GHC.Base.hs_string__ "mkAltExpr DEFAULT")
    end.

Definition mergeAlts {a} {b}
   : list (Core.AltCon * a * b)%type ->
     list (Core.AltCon * a * b)%type -> list (Core.AltCon * a * b)%type :=
  GHC.DeferredFix.deferredFix1 (fun mergeAlts
                                (arg_0__ arg_1__ : list (Core.AltCon * a * b)%type) =>
                                  match arg_0__, arg_1__ with
                                  | nil, as2 => as2
                                  | as1, nil => as1
                                  | cons a1 as1, cons a2 as2 =>
                                      match Core.cmpAlt a1 a2 with
                                      | Lt => cons a1 (mergeAlts as1 (cons a2 as2))
                                      | Eq => cons a1 (mergeAlts as1 as2)
                                      | Gt => cons a2 (mergeAlts (cons a1 as1) as2)
                                      end
                                  end).

Definition locBind
   : GHC.Base.String ->
     Core.Var -> Core.Var -> list GHC.Base.String -> list GHC.Base.String :=
  fun loc b1 b2 diffs =>
    let bindLoc :=
      if b1 GHC.Base.== b2 : bool then Panic.someSDoc else
      GHC.Base.mappend (GHC.Base.mappend Panic.someSDoc Panic.someSDoc)
                       Panic.someSDoc in
    let addLoc := fun d => d in GHC.Base.map addLoc diffs.

Definition isWorkFreeApp : CheapAppFun :=
  fun fn n_val_args =>
    if n_val_args GHC.Base.== #0 : bool then true else
    if n_val_args GHC.Base.< Id.idArity fn : bool then true else
    match Core.idDetails fn with
    | Core.DataConWorkId _ => true
    | _ => false
    end.

Definition isJoinBind : Core.CoreBind -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.NonRec b _ => Id.isJoinId b
    | Core.Rec (cons (pair b _) _) => Id.isJoinId b
    | _ => false
    end.

Axiom isExprLevPoly : Core.CoreExpr -> bool.

Axiom isExpandableApp : CheapAppFun.

Axiom isEmptyTy : AxiomatizedTypes.Type_ -> bool.

Axiom isDivOp : unit -> bool.

Definition isDefaultAlt {a} {b} : (Core.AltCon * a * b)%type -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | pair (pair Core.DEFAULT _) _ => true
    | _ => false
    end.

Axiom isCheapApp : CheapAppFun.

Definition getIdFromTrivialExpr_maybe : Core.CoreExpr -> option Core.Id :=
  fun e =>
    let fix go arg_0__
              := match arg_0__ with
                 | Core.Mk_Var v => Some v
                 | Core.App f t => if negb (Core.isRuntimeArg t) : bool then go f else None
                 | Core.Lam b e => if negb (Core.isRuntimeVar b) : bool then go e else None
                 | _ => None
                 end in
    go e.

Definition getIdFromTrivialExpr : Core.CoreExpr -> Core.Id :=
  fun e =>
    Data.Maybe.fromMaybe (Panic.panicStr (GHC.Base.hs_string__
                                          "getIdFromTrivialExpr") (Panic.someSDoc)) (getIdFromTrivialExpr_maybe e).

Definition findDefault {a} {b}
   : list (Core.AltCon * list a * b)%type ->
     (list (Core.AltCon * list a * b)%type * option b)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | cons (pair (pair Core.DEFAULT args) rhs) alts =>
        if andb Util.debugIsOn (negb (Data.Foldable.null args)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/coreSyn/CoreUtils.hs") #519)
        else pair alts (Some rhs)
    | alts => pair alts None
    end.

Definition findAlt {a} {b}
   : Core.AltCon ->
     list (Core.AltCon * a * b)%type -> option (Core.AltCon * a * b)%type :=
  fun con alts =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | nil, deflt => deflt
                 | cons (pair (pair con1 _) _ as alt) alts, deflt =>
                     match Core.cmpAltCon con con1 with
                     | Lt => deflt
                     | Eq => Some alt
                     | Gt =>
                         if andb Util.debugIsOn (negb (negb (con1 GHC.Base.== Core.DEFAULT))) : bool
                         then (Panic.assertPanic (GHC.Base.hs_string__
                                                  "ghc/compiler/coreSyn/CoreUtils.hs") #545)
                         else go alts deflt
                     end
                 end in
    match alts with
    | cons (pair (pair Core.DEFAULT _) _ as deflt) alts => go alts (Some deflt)
    | _ => go alts None
    end.

Axiom filterAlts : forall {a},
                   Core.TyCon ->
                   list AxiomatizedTypes.Type_ ->
                   list Core.AltCon ->
                   list (Core.AltCon * list Core.Var * a)%type ->
                   (list Core.AltCon * list (Core.AltCon * list Core.Var * a)%type)%type.

Axiom expr_ok : (unit -> bool) -> Core.CoreExpr -> bool.

Axiom exprType : Core.CoreExpr -> AxiomatizedTypes.Type_.

Axiom exprOkForSpeculation : Core.CoreExpr -> bool.

Axiom exprOkForSideEffects : Core.CoreExpr -> bool.

Definition exprIsTrivial : Core.CoreExpr -> bool :=
  fix exprIsTrivial (arg_0__ : Core.CoreExpr) : bool
        := match arg_0__ with
           | Core.Mk_Var _ => true
           | Core.Lit lit => Literal.litIsTrivial lit
           | Core.App e arg => andb (negb (Core.isRuntimeArg arg)) (exprIsTrivial e)
           | Core.Lam b e => andb (negb (Core.isRuntimeVar b)) (exprIsTrivial e)
           | Core.Case e _ _ nil => exprIsTrivial e
           | _ => false
           end.

Definition exprIsTickedString_maybe : Core.CoreExpr -> option GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.Lit (Literal.MachStr bs) => Some bs
    | _ => None
    end.

Definition exprIsTickedString : Core.CoreExpr -> bool :=
  Data.Maybe.isJust GHC.Base.∘ exprIsTickedString_maybe.

Definition exprIsTopLevelBindable
   : Core.CoreExpr -> AxiomatizedTypes.Type_ -> bool :=
  fun expr ty => orb (negb (Core.isUnliftedType ty)) (exprIsTickedString expr).

Axiom exprIsDupable : DynFlags.DynFlags -> Core.CoreExpr -> bool.

Axiom exprIsConLike : Core.CoreExpr -> bool.

Axiom exprIsCheapX : CheapAppFun -> Core.CoreExpr -> bool.

Definition exprIsExpandable : Core.CoreExpr -> bool :=
  exprIsCheapX isExpandableApp.

Definition exprIsWorkFree : Core.CoreExpr -> bool :=
  exprIsCheapX isWorkFreeApp.

Definition exprIsCheap : Core.CoreExpr -> bool :=
  exprIsCheapX isCheapApp.

Axiom exprIsBottom : Core.CoreExpr -> bool.

Definition exprIsBig {b} : Core.Expr b -> bool :=
  fix exprIsBig (arg_0__ : Core.Expr b) : bool
        := match arg_0__ with
           | Core.Lit _ => false
           | Core.Mk_Var _ => false
           | Core.Lam _ e => exprIsBig e
           | Core.App f a => orb (exprIsBig f) (exprIsBig a)
           | _ => true
           end.

Definition eqTickish
   : Core.RnEnv2 -> Core.Tickish Core.Id -> Core.Tickish Core.Id -> bool :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | env, Core.Breakpoint lid lids, Core.Breakpoint rid rids =>
        andb (lid GHC.Base.== rid) (GHC.Base.map (Core.rnOccL env) lids GHC.Base.==
              GHC.Base.map (Core.rnOccR env) rids)
    | _, l, r => l GHC.Base.== r
    end.

Axiom eqExpr : Core.InScopeSet -> Core.CoreExpr -> Core.CoreExpr -> bool.

Definition dupAppSize : nat :=
  #8.

Axiom diffUnfold : Core.RnEnv2 ->
                   Core.Unfolding -> Core.Unfolding -> list GHC.Base.String.

Axiom diffIdInfo : Core.RnEnv2 -> Core.Var -> Core.Var -> list GHC.Base.String.

Axiom diffExpr : bool ->
                 Core.RnEnv2 -> Core.CoreExpr -> Core.CoreExpr -> list GHC.Base.String.

Axiom diffBinds : bool ->
                  Core.RnEnv2 ->
                  list (Core.Var * Core.CoreExpr)%type ->
                  list (Core.Var * Core.CoreExpr)%type ->
                  (list GHC.Base.String * Core.RnEnv2)%type.

Axiom dataConRepInstPat : list Unique.Unique ->
                          Core.DataCon ->
                          list AxiomatizedTypes.Type_ -> (list Core.TyVar * list Core.Id)%type.

Axiom dataConRepFSInstPat : list FastString.FastString ->
                            list Unique.Unique ->
                            Core.DataCon ->
                            list AxiomatizedTypes.Type_ -> (list Core.TyVar * list Core.Id)%type.

Axiom dataConInstPat : list FastString.FastString ->
                       list Unique.Unique ->
                       Core.DataCon ->
                       list AxiomatizedTypes.Type_ -> (list Core.TyVar * list Core.Id)%type.

Axiom coreAltsType : list Core.CoreAlt -> AxiomatizedTypes.Type_.

Axiom coreAltType : Core.CoreAlt -> AxiomatizedTypes.Type_.

Axiom combineIdenticalAlts : list Core.AltCon ->
                             list Core.CoreAlt -> (bool * list Core.AltCon * list Core.CoreAlt)%type.

Axiom cheapEqExpr' : forall {b},
                     (Core.Tickish Core.Id -> bool) -> Core.Expr b -> Core.Expr b -> bool.

Definition cheapEqExpr {b} : Core.Expr b -> Core.Expr b -> bool :=
  cheapEqExpr' (GHC.Base.const false).

Axiom bindNonRec : Core.Id -> Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr.

Axiom applyTypeToArgs : Core.CoreExpr ->
                        AxiomatizedTypes.Type_ -> list Core.CoreExpr -> AxiomatizedTypes.Type_.

Axiom app_ok : (unit -> bool) -> Core.Id -> list Core.CoreExpr -> bool.

Definition altsAreExhaustive {b} : list (Core.Alt b) -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => false
    | cons (pair (pair con1 _) _) alts =>
        match con1 with
        | Core.DEFAULT => true
        | Core.LitAlt _ => false
        | Core.DataAlt c =>
            Util.lengthIs alts (Core.tyConFamilySize (Core.dataConTyCon c) GHC.Num.- #1)
        end
    end.

Definition addDefault {a} {b}
   : list (Core.AltCon * list a * b)%type ->
     option b -> list (Core.AltCon * list a * b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | alts, None => alts
    | alts, Some rhs => cons (pair (pair Core.DEFAULT nil) rhs) alts
    end.

(* External variables:
     Eq Gt Lt None Some andb bool cons exprIsHNF false list mkTick nat negb nil
     op_zt__ option orb pair true unit AxiomatizedTypes.Type_ BasicTypes.Arity
     Coq.Init.Datatypes.app Core.Alt Core.AltCon Core.App Core.Breakpoint Core.Case
     Core.CoreAlt Core.CoreArg Core.CoreBind Core.CoreBndr Core.CoreExpr Core.DEFAULT
     Core.DataAlt Core.DataCon Core.DataConWorkId Core.Expr Core.Id Core.InScopeSet
     Core.Lam Core.Let Core.Lit Core.LitAlt Core.Mk_Var Core.NonRec Core.Rec
     Core.RnEnv2 Core.Tickish Core.TyCon Core.TyVar Core.Type_ Core.Unfolding
     Core.Var Core.cmpAlt Core.cmpAltCon Core.dataConTyCon Core.dataConUnivTyVars
     Core.idDetails Core.isRuntimeArg Core.isRuntimeVar Core.isUnliftedType
     Core.mkConApp Core.rnOccL Core.rnOccR Core.tyConFamilySize Core.varsToCoreExprs
     Data.Foldable.null Data.Maybe.fromMaybe Data.Maybe.isJust DynFlags.DynFlags
     FastString.FastString GHC.Base.String GHC.Base.const GHC.Base.map
     GHC.Base.mappend GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zl__
     GHC.DeferredFix.deferredFix1 GHC.Num.fromInteger GHC.Num.op_zm__ Id.idArity
     Id.isJoinId Literal.MachStr Literal.litIsTrivial OrdList.OrdList OrdList.appOL
     OrdList.concatOL OrdList.fromOL OrdList.nilOL Panic.assertPanic Panic.panic
     Panic.panicStr Panic.someSDoc Unique.Unique Util.debugIsOn Util.dropList
     Util.lengthIs
*)
