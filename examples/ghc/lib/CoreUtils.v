(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require Data.Foldable.
Require Data.Maybe.
Require Data.Tuple.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.List.
Require GHC.Num.
Require Id.
Require Literal.
Require NestedRecursionHelpers.
Require OrdList.
Require Panic.
Require PrelNames.
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

Definition stripTicksTopT {b}
   : (Core.Tickish Core.Id -> bool) ->
     Core.Expr b -> list (Core.Tickish Core.Id) :=
  fun p =>
    let fix go arg_0__ arg_1__
              := let j_2__ := match arg_0__, arg_1__ with | ts, _ => ts end in
                 match arg_0__, arg_1__ with
                 | ts, Core.Tick t e => if p t : bool then go (cons t ts) e else j_2__
                 | _, _ => j_2__
                 end in
    go nil.

Definition stripTicksTopE {b}
   : (Core.Tickish Core.Id -> bool) -> Core.Expr b -> Core.Expr b :=
  fun p =>
    let fix go arg_0__
              := let j_1__ := let 'other := arg_0__ in other in
                 match arg_0__ with
                 | Core.Tick t e => if p t : bool then go e else j_1__
                 | _ => j_1__
                 end in
    go.

Definition stripTicksTop {b}
   : (Core.Tickish Core.Id -> bool) ->
     Core.Expr b -> (list (Core.Tickish Core.Id) * Core.Expr b)%type :=
  fun p =>
    let fix go arg_0__ arg_1__
              := let j_3__ :=
                   match arg_0__, arg_1__ with
                   | ts, other => pair (GHC.List.reverse ts) other
                   end in
                 match arg_0__, arg_1__ with
                 | ts, Core.Tick t e => if p t : bool then go (cons t ts) e else j_3__
                 | _, _ => j_3__
                 end in
    go nil.

Definition stripTicksT {b}
   : (Core.Tickish Core.Id -> bool) ->
     Core.Expr b -> list (Core.Tickish Core.Id) :=
  fun p expr =>
    let go :=
      fix go arg_0__
            := let go_a (arg_16__ : Core.Alt b) : OrdList.OrdList (Core.Tickish Core.Id) :=
                 let 'pair (pair _ _) e := arg_16__ in
                 go e in
               match arg_0__ with
               | Core.App e a => OrdList.appOL (go e) (go a)
               | Core.Lam _ e => go e
               | Core.Let b e => OrdList.appOL (go_bs b) (go e)
               | Core.Case e _ _ as_ =>
                   OrdList.appOL (go e) (OrdList.concatOL (GHC.Base.map go_a as_))
               | Core.Cast e _ => go e
               | Core.Tick t e => if p t : bool then OrdList.consOL t (go e) else go e
               | _ => OrdList.nilOL
               end with go_bs arg_9__
                          := let go_b (arg_13__ : b * Core.Expr b)
                              : OrdList.OrdList (Core.Tickish Core.Id) :=
                               let 'pair _ e := arg_13__ in
                               go e in
                             match arg_9__ with
                             | Core.NonRec _ e => go e
                             | Core.Rec bs => OrdList.concatOL (GHC.Base.map go_b bs)
                             end for go in
    let go_bs :=
      fix go arg_0__
            := let go_a (arg_16__ : Core.Alt b) : OrdList.OrdList (Core.Tickish Core.Id) :=
                 let 'pair (pair _ _) e := arg_16__ in
                 go e in
               match arg_0__ with
               | Core.App e a => OrdList.appOL (go e) (go a)
               | Core.Lam _ e => go e
               | Core.Let b e => OrdList.appOL (go_bs b) (go e)
               | Core.Case e _ _ as_ =>
                   OrdList.appOL (go e) (OrdList.concatOL (GHC.Base.map go_a as_))
               | Core.Cast e _ => go e
               | Core.Tick t e => if p t : bool then OrdList.consOL t (go e) else go e
               | _ => OrdList.nilOL
               end with go_bs arg_9__
                          := let go_b (arg_13__ : b * Core.Expr b)
                              : OrdList.OrdList (Core.Tickish Core.Id) :=
                               let 'pair _ e := arg_13__ in
                               go e in
                             match arg_9__ with
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
            := let go_a (arg_17__ : Core.Alt b) : Core.Alt b :=
                 let 'pair (pair c bs) e := arg_17__ in
                 pair (pair c bs) (go e) in
               match arg_0__ with
               | Core.App e a => Core.App (go e) (go a)
               | Core.Lam b e => Core.Lam b (go e)
               | Core.Let b e => Core.Let (go_bs b) (go e)
               | Core.Case e b t as_ => Core.Case (go e) b t (GHC.Base.map go_a as_)
               | Core.Cast e c => Core.Cast (go e) c
               | Core.Tick t e => if p t : bool then go e else Core.Tick t (go e)
               | _ => let 'other := arg_0__ in other
               end with go_bs arg_10__
                          := let go_b (arg_14__ : b * Core.Expr b) : b * Core.Expr b :=
                               let 'pair b e := arg_14__ in
                               pair b (go e) in
                             match arg_10__ with
                             | Core.NonRec b e => Core.NonRec b (go e)
                             | Core.Rec bs => Core.Rec (GHC.Base.map go_b bs)
                             end for go in
    let go_bs :=
      fix go arg_0__
            := let go_a (arg_17__ : Core.Alt b) : Core.Alt b :=
                 let 'pair (pair c bs) e := arg_17__ in
                 pair (pair c bs) (go e) in
               match arg_0__ with
               | Core.App e a => Core.App (go e) (go a)
               | Core.Lam b e => Core.Lam b (go e)
               | Core.Let b e => Core.Let (go_bs b) (go e)
               | Core.Case e b t as_ => Core.Case (go e) b t (GHC.Base.map go_a as_)
               | Core.Cast e c => Core.Cast (go e) c
               | Core.Tick t e => if p t : bool then go e else Core.Tick t (go e)
               | _ => let 'other := arg_0__ in other
               end with go_bs arg_10__
                          := let go_b (arg_14__ : b * Core.Expr b) : b * Core.Expr b :=
                               let 'pair b e := arg_14__ in
                               pair b (go e) in
                             match arg_10__ with
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
                         list unit ->
                         list Core.AltCon -> list Core.CoreAlt -> (bool * list Core.CoreAlt)%type.

Axiom needsCaseBinding : unit -> Core.CoreExpr -> bool.

Definition mkTick : Core.Tickish Core.Var -> Core.CoreExpr -> Core.CoreExpr :=
  fun t orig => orig.

Definition mkTicks
   : list (Core.Tickish Core.Id) -> Core.CoreExpr -> Core.CoreExpr :=
  fun ticks expr => Data.Foldable.foldr mkTick expr ticks.

Definition mkCast : Core.CoreExpr -> unit -> Core.CoreExpr :=
  fun c t => c.

Definition mkAltExpr
   : Core.AltCon -> list Core.CoreBndr -> list unit -> Core.CoreExpr :=
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

Definition isSaturatedConApp : Core.CoreExpr -> bool :=
  fun e =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | Core.App f a, as_ => go f (cons a as_)
                 | Core.Mk_Var fun_, args =>
                     andb (Id.isConLikeId fun_) (Id.idArity fun_ GHC.Base.== Core.valArgCount args)
                 | Core.Cast f _, as_ => go f as_
                 | _, _ => false
                 end in
    go e nil.

Definition isJoinBind : Core.CoreBind -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.NonRec b _ => Id.isJoinId b
    | Core.Rec (cons (pair b _) _) => Id.isJoinId b
    | _ => false
    end.

Axiom isExprLevPoly : Core.CoreExpr -> bool.

Axiom isExpandableApp : CheapAppFun.

Axiom isEmptyTy : unit -> bool.

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
                 | Core.Tick t e => if negb (Core.tickishIsCode t) : bool then go e else None
                 | Core.Cast e _ => go e
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
                   list unit ->
                   list Core.AltCon ->
                   list (Core.AltCon * list Core.Var * a)%type ->
                   (list Core.AltCon * list (Core.AltCon * list Core.Var * a)%type)%type.

Axiom expr_ok : (unit -> bool) -> Core.CoreExpr -> bool.

Axiom exprType : Core.CoreExpr -> unit.

Axiom exprOkForSpeculation : Core.CoreExpr -> bool.

Axiom exprOkForSideEffects : Core.CoreExpr -> bool.

Definition exprIsTrivial : Core.CoreExpr -> bool :=
  fix exprIsTrivial (arg_0__ : Core.CoreExpr) : bool
        := match arg_0__ with
           | Core.Mk_Var _ => true
           | Core.Type_ _ => true
           | Core.Coercion _ => true
           | Core.Lit lit => Literal.litIsTrivial lit
           | Core.App e arg => andb (negb (Core.isRuntimeArg arg)) (exprIsTrivial e)
           | Core.Lam b e => andb (negb (Core.isRuntimeVar b)) (exprIsTrivial e)
           | Core.Tick t e => andb (negb (Core.tickishIsCode t)) (exprIsTrivial e)
           | Core.Cast e _ => exprIsTrivial e
           | Core.Case e _ _ nil => exprIsTrivial e
           | _ => false
           end.

Definition exprIsTickedString_maybe : Core.CoreExpr -> option GHC.Base.String :=
  fix exprIsTickedString_maybe (arg_0__ : Core.CoreExpr) : option GHC.Base.String
        := match arg_0__ with
           | Core.Lit (Literal.MachStr bs) => Some bs
           | Core.Tick t e =>
               if Core.tickishPlace t GHC.Base.== Core.PlaceCostCentre : bool then None else
               exprIsTickedString_maybe e
           | _ => None
           end.

Definition exprIsTickedString : Core.CoreExpr -> bool :=
  Data.Maybe.isJust GHC.Base.∘ exprIsTickedString_maybe.

Definition exprIsTopLevelBindable : Core.CoreExpr -> unit -> bool :=
  fun expr ty => orb (negb (Core.isUnliftedType ty)) (exprIsTickedString expr).

Definition exprIsHNFlike
   : (Core.Var -> bool) -> (Core.Unfolding -> bool) -> Core.CoreExpr -> bool :=
  fun is_con is_con_unf =>
    let id_app_is_value :=
      fun id n_val_args =>
        orb (is_con id) (orb (Id.idArity id GHC.Base.> n_val_args) false) in
    let app_is_value : Core.CoreExpr -> nat -> bool :=
      fix app_is_value (arg_1__ : Core.CoreExpr) (arg_2__ : nat) : bool
            := match arg_1__, arg_2__ with
               | Core.Mk_Var f, nva => id_app_is_value f nva
               | Core.Tick _ f, nva => app_is_value f nva
               | Core.Cast f _, nva => app_is_value f nva
               | Core.App f a, nva =>
                   if Core.isValArg a : bool then app_is_value f (nva GHC.Num.+ #1) else
                   app_is_value f nva
               | _, _ => false
               end in
    let fix is_hnf_like arg_9__
              := match arg_9__ with
                 | Core.Mk_Var v => orb (id_app_is_value v #0) (is_con_unf (Id.idUnfolding v))
                 | Core.Lit _ => true
                 | Core.Type_ _ => true
                 | Core.Coercion _ => true
                 | Core.Lam b e => orb (Core.isRuntimeVar b) (is_hnf_like e)
                 | Core.Tick tickish e =>
                     andb (negb (Core.tickishCounts tickish)) (is_hnf_like e)
                 | Core.Cast e _ => is_hnf_like e
                 | Core.App e a =>
                     if Core.isValArg a : bool then app_is_value e #1 else
                     is_hnf_like e
                 | _ => match arg_9__ with | Core.Let _ e => is_hnf_like e | _ => false end
                 end in
    is_hnf_like.

Definition exprIsHNF : Core.CoreExpr -> bool :=
  exprIsHNFlike Id.isDataConWorkId Core.isEvaldUnfolding.

Definition mkTickNoHNF
   : Core.Tickish Core.Id -> Core.CoreExpr -> Core.CoreExpr :=
  fun t e => if exprIsHNF e : bool then tickHNFArgs t e else mkTick t e.

Definition exprIsConLike : Core.CoreExpr -> bool :=
  exprIsHNFlike Id.isConLikeId Core.isConLikeUnfolding.

Definition exprIsCheapX : CheapAppFun -> Core.CoreExpr -> bool :=
  fun ok_app e =>
    let fix go arg_1__ arg_2__
              := let ok e := go #0 e in
                 match arg_1__, arg_2__ with
                 | n, Core.Mk_Var v => ok_app v n
                 | _, Core.Lit _ => true
                 | _, Core.Type_ _ => true
                 | _, Core.Coercion _ => true
                 | n, Core.Cast e _ => go n e
                 | n, Core.Case scrut _ _ alts =>
                     andb (ok scrut) (Data.Foldable.and (let cont_5__ arg_6__ :=
                                                           let 'pair (pair _ _) rhs := arg_6__ in
                                                           cons (go n rhs) nil in
                                                         Coq.Lists.List.flat_map cont_5__ alts))
                 | n, Core.Tick t e => if Core.tickishCounts t : bool then false else go n e
                 | n, Core.Lam x e =>
                     if Core.isRuntimeVar x : bool
                     then orb (n GHC.Base.== #0) (go (n GHC.Num.- #1) e) else
                     go n e
                 | n, Core.App f e =>
                     if Core.isRuntimeArg e : bool then andb (go (n GHC.Num.+ #1) f) (ok e) else
                     go n f
                 | n, Core.Let (Core.NonRec _ r) e => andb (go n e) (ok r)
                 | n, Core.Let (Core.Rec prs) e =>
                     andb (go n e) (Data.Foldable.all (ok GHC.Base.∘ Data.Tuple.snd) prs)
                 end in
    let ok := fun e => go #0 e in ok e.

Definition exprIsExpandable : Core.CoreExpr -> bool :=
  exprIsCheapX isExpandableApp.

Definition exprIsWorkFree : Core.CoreExpr -> bool :=
  exprIsCheapX isWorkFreeApp.

Definition exprIsCheap : Core.CoreExpr -> bool :=
  exprIsCheapX isCheapApp.

Definition exprIsBottom : Core.CoreExpr -> bool :=
  fun e =>
    let fix go arg_0__ arg_1__
              := let j_3__ :=
                   match arg_0__, arg_1__ with
                   | _, Core.Case _ _ _ alts => Data.Foldable.null alts
                   | _, _ => false
                   end in
                 match arg_0__, arg_1__ with
                 | n, Core.Mk_Var v => andb (Id.isBottomingId v) (n GHC.Base.>= Id.idArity v)
                 | n, Core.App e a =>
                     if Core.isTypeArg a : bool then go n e else
                     go (n GHC.Num.+ #1) e
                 | n, Core.Tick _ e => go n e
                 | n, Core.Cast e _ => go n e
                 | n, Core.Let _ e => go n e
                 | n, Core.Lam v e => if Core.isTyVar v : bool then go n e else j_3__
                 | _, _ => j_3__
                 end in
    if isEmptyTy (tt) : bool then true else
    go #0 e.

Definition exprIsBig {b} : Core.Expr b -> bool :=
  fix exprIsBig (arg_0__ : Core.Expr b) : bool
        := match arg_0__ with
           | Core.Lit _ => false
           | Core.Mk_Var _ => false
           | Core.Type_ _ => false
           | Core.Coercion _ => false
           | Core.Lam _ e => exprIsBig e
           | Core.App f a => orb (exprIsBig f) (exprIsBig a)
           | Core.Cast e _ => exprIsBig e
           | Core.Tick _ e => exprIsBig e
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

Definition eqExpr : Core.InScopeSet -> Core.CoreExpr -> Core.CoreExpr -> bool :=
  fun in_scope e1 e2 =>
    let fix go arg_0__ arg_1__ arg_2__
              := let go_alt (arg_18__ : Core.RnEnv2) (arg_19__ arg_20__ : Core.CoreAlt)
                  : bool :=
                   match arg_18__, arg_19__, arg_20__ with
                   | env, pair (pair c1 bs1) e1, pair (pair c2 bs2) e2 =>
                       andb (c1 GHC.Base.== c2) (go (env) e1 e2)
                   end in
                 match arg_0__, arg_1__, arg_2__ with
                 | env, Core.Mk_Var v1, Core.Mk_Var v2 =>
                     if Core.rnOccL env v1 GHC.Base.== Core.rnOccR env v2 : bool then true else
                     false
                 | _, Core.Lit lit1, Core.Lit lit2 => lit1 GHC.Base.== lit2
                 | env, Core.Type_ t1, Core.Type_ t2 => Core.eqTypeX env t1 t2
                 | env, Core.Coercion co1, Core.Coercion co2 => Core.eqCoercionX env co1 co2
                 | env, Core.Cast e1 co1, Core.Cast e2 co2 =>
                     andb (Core.eqCoercionX env co1 co2) (go env e1 e2)
                 | env, Core.App f1 a1, Core.App f2 a2 => andb (go env f1 f2) (go env a1 a2)
                 | env, Core.Tick n1 e1, Core.Tick n2 e2 =>
                     andb (eqTickish env n1 n2) (go env e1 e2)
                 | env, Core.Lam b1 e1, Core.Lam b2 e2 =>
                     andb (Core.eqTypeX env (Core.varType b1) (Core.varType b2)) (go (Core.rnBndr2
                                                                                      env b1 b2) e1 e2)
                 | env, Core.Let (Core.NonRec v1 r1) e1, Core.Let (Core.NonRec v2 r2) e2 =>
                     andb (go env r1 r2) (go (Core.rnBndr2 env v1 v2) e1 e2)
                 | env, Core.Let (Core.Rec ps1) e1, Core.Let (Core.Rec ps2) e2 =>
                     let 'pair bs2 rs2 := GHC.List.unzip ps2 in
                     let 'pair bs1 rs1 := GHC.List.unzip ps1 in
                     let env' := env in
                     andb (Util.equalLength ps1 ps2) (andb (NestedRecursionHelpers.all2Map (go env')
                                                                                           snd snd ps1 ps2) (go env' e1
                                                            e2))
                 | env, Core.Case e1 b1 t1 a1, Core.Case e2 b2 t2 a2 =>
                     if Data.Foldable.null a1 : bool
                     then andb (Data.Foldable.null a2) (andb (go env e1 e2) (Core.eqTypeX env t1
                                                              t2)) else
                     andb (go env e1 e2) (NestedRecursionHelpers.all2Map (go_alt (Core.rnBndr2 env b1
                                                                                  b2)) id id a1 a2)
                 | _, _, _ => false
                 end in
    let go_alt : Core.RnEnv2 -> Core.CoreAlt -> Core.CoreAlt -> bool :=
      fun arg_18__ arg_19__ arg_20__ =>
        match arg_18__, arg_19__, arg_20__ with
        | env, pair (pair c1 bs1) e1, pair (pair c2 bs2) e2 =>
            andb (c1 GHC.Base.== c2) (go (env) e1 e2)
        end in
    go (Core.mkRnEnv2 in_scope) e1 e2.

Definition dupAppSize : nat :=
  #8.

Definition exprIsDupable : DynFlags.DynFlags -> Core.CoreExpr -> bool :=
  fun dflags e =>
    let decrement : nat -> option nat :=
      fun arg_0__ =>
        let 'num_1__ := arg_0__ in
        if num_1__ GHC.Base.== #0 : bool then None else
        let 'n := arg_0__ in
        Some (n GHC.Num.- #1) in
    let go : nat -> Core.CoreExpr -> option nat :=
      fix go (arg_6__ : nat) (arg_7__ : Core.CoreExpr) : option nat
            := match arg_6__, arg_7__ with
               | n, Core.Type_ _ => Some n
               | n, Core.Coercion _ => Some n
               | n, Core.Mk_Var _ => decrement n
               | n, Core.Tick _ e => go n e
               | n, Core.Cast e _ => go n e
               | n, Core.App f a => match go n a with | Some n' => go n' f | _ => None end
               | n, Core.Lit lit =>
                   if Literal.litIsDupable dflags lit : bool then decrement n else
                   None
               | _, _ => None
               end in
    Data.Maybe.isJust (go dupAppSize e).

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
                          Core.DataCon -> list unit -> (list Core.TyVar * list Core.Id)%type.

Axiom dataConRepFSInstPat : list FastString.FastString ->
                            list Unique.Unique ->
                            Core.DataCon -> list unit -> (list Core.TyVar * list Core.Id)%type.

Axiom dataConInstPat : list FastString.FastString ->
                       list Unique.Unique ->
                       Core.DataCon -> list unit -> (list Core.TyVar * list Core.Id)%type.

Axiom coreAltsType : list Core.CoreAlt -> unit.

Axiom coreAltType : Core.CoreAlt -> unit.

Axiom combineIdenticalAlts : list Core.AltCon ->
                             list Core.CoreAlt -> (bool * list Core.AltCon * list Core.CoreAlt)%type.

Definition collectMakeStaticArgs
   : Core.CoreExpr ->
     option (Core.CoreExpr * unit * Core.CoreExpr * Core.CoreExpr)%type :=
  fun '(e) =>
    match Core.collectArgsTicks (GHC.Base.const true) e with
    | pair (pair (Core.Mk_Var b as fun_) (cons (Core.Type_ t) (cons loc (cons arg
        nil)))) _ =>
        if Id.idName b GHC.Base.== PrelNames.makeStaticName : bool
        then Some (pair (pair (pair fun_ t) loc) arg) else
        None
    | _ => None
    end.

Axiom cheapEqExpr' : forall {b},
                     (Core.Tickish Core.Id -> bool) -> Core.Expr b -> Core.Expr b -> bool.

Definition cheapEqExpr {b} : Core.Expr b -> Core.Expr b -> bool :=
  cheapEqExpr' (GHC.Base.const false).

Axiom bindNonRec : Core.Id -> Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr.

Axiom applyTypeToArgs : Core.CoreExpr -> unit -> list Core.CoreExpr -> unit.

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
     Eq Gt Lt None Some andb bool cons false id list nat negb nil op_zt__ option orb
     pair snd true tt unit BasicTypes.Arity Coq.Init.Datatypes.app
     Coq.Lists.List.flat_map Core.Alt Core.AltCon Core.App Core.Breakpoint Core.Case
     Core.Cast Core.Coercion Core.CoreAlt Core.CoreArg Core.CoreBind Core.CoreBndr
     Core.CoreExpr Core.DEFAULT Core.DataAlt Core.DataCon Core.DataConWorkId
     Core.Expr Core.Id Core.InScopeSet Core.Lam Core.Let Core.Lit Core.LitAlt
     Core.Mk_Var Core.NonRec Core.PlaceCostCentre Core.Rec Core.RnEnv2 Core.Tick
     Core.Tickish Core.TyCon Core.TyVar Core.Type_ Core.Unfolding Core.Var
     Core.cmpAlt Core.cmpAltCon Core.collectArgsTicks Core.dataConTyCon
     Core.dataConUnivTyVars Core.eqCoercionX Core.eqTypeX Core.idDetails
     Core.isConLikeUnfolding Core.isEvaldUnfolding Core.isRuntimeArg
     Core.isRuntimeVar Core.isTyVar Core.isTypeArg Core.isUnliftedType Core.isValArg
     Core.mkConApp Core.mkRnEnv2 Core.rnBndr2 Core.rnOccL Core.rnOccR
     Core.tickishCounts Core.tickishIsCode Core.tickishPlace Core.tyConFamilySize
     Core.valArgCount Core.varType Core.varsToCoreExprs Data.Foldable.all
     Data.Foldable.and Data.Foldable.foldr Data.Foldable.null Data.Maybe.fromMaybe
     Data.Maybe.isJust Data.Tuple.snd DynFlags.DynFlags FastString.FastString
     GHC.Base.String GHC.Base.const GHC.Base.map GHC.Base.mappend
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__
     GHC.Base.op_zl__ GHC.DeferredFix.deferredFix1 GHC.List.reverse GHC.List.unzip
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ Id.idArity Id.idName
     Id.idUnfolding Id.isBottomingId Id.isConLikeId Id.isDataConWorkId Id.isJoinId
     Literal.MachStr Literal.litIsDupable Literal.litIsTrivial
     NestedRecursionHelpers.all2Map OrdList.OrdList OrdList.appOL OrdList.concatOL
     OrdList.consOL OrdList.fromOL OrdList.nilOL Panic.assertPanic Panic.panic
     Panic.panicStr Panic.someSDoc PrelNames.makeStaticName Unique.Unique
     Util.debugIsOn Util.dropList Util.equalLength Util.lengthIs
*)
