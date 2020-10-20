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
Require Data.Foldable.
Require Data.Maybe.
Require Data.OldList.
Require Data.Tuple.
Require Datatypes.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require Literal.
Require NestedRecursionHelpers.
Require OrdList.
Require Pair.
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

Axiom exprType : Core.CoreExpr -> AxiomatizedTypes.Type_.

Axiom coreAltType : Core.CoreAlt -> AxiomatizedTypes.Type_.

Axiom coreAltsType : list Core.CoreAlt -> AxiomatizedTypes.Type_.

Axiom isExprLevPoly : Core.CoreExpr -> bool.

Axiom applyTypeToArgs : Core.CoreExpr ->
                        AxiomatizedTypes.Type_ -> list Core.CoreExpr -> AxiomatizedTypes.Type_.

Fixpoint mkCast (arg_0__ : Core.CoreExpr) (arg_1__ : AxiomatizedTypes.Coercion)
           : Core.CoreExpr
           := match arg_0__, arg_1__ with
              | e, co =>
                  if (if andb Util.debugIsOn (negb (Core.coercionRole co GHC.Base.==
                                                    AxiomatizedTypes.Representational)) : bool
                      then (GHC.Err.error (GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend
                                                                               (GHC.Base.mappend (GHC.Base.mappend
                                                                                                  (Datatypes.id
                                                                                                   (GHC.Base.hs_string__
                                                                                                    "coercion"))
                                                                                                  Panic.someSDoc)
                                                                                                 Panic.someSDoc)
                                                                               Panic.someSDoc) (Datatypes.id
                                                                               (GHC.Base.hs_string__ "has wrong role")))
                                                            Panic.someSDoc))
                      else Core.isReflCo co) : bool
                  then e else
                  let j_7__ :=
                    match arg_0__, arg_1__ with
                    | Core.Cast expr co2, co =>
                        Panic.warnPprTrace (let 'Pair.Mk_Pair _from_ty2 to_ty2 := Core.coercionKind
                                                                                    co2 in
                                            let 'Pair.Mk_Pair from_ty _to_ty := Core.coercionKind co in
                                            negb (Core.eqType from_ty to_ty2)) (GHC.Base.hs_string__
                                            "ghc/compiler/coreSyn/CoreUtils.hs") #279 (Panic.someSDoc) (mkCast expr
                                                                                                               (Core.mkTransCo
                                                                                                                co2 co))
                    | expr, co =>
                        let 'Pair.Mk_Pair from_ty _to_ty := Core.coercionKind co in
                        Panic.warnPprTrace (negb (Core.eqType from_ty (exprType expr)))
                                           (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreUtils.hs") #290
                                           (GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend
                                                                                                  (Datatypes.id
                                                                                                   (GHC.Base.hs_string__
                                                                                                    "Trying to coerce"))
                                                                                                  (Datatypes.id
                                                                                                   (GHC.Base.hs_string__
                                                                                                    "(")))
                                                                                                 Panic.someSDoc)
                                                                               Panic.someSDoc) (Datatypes.id
                                                              (GHC.Base.hs_string__ ")"))) (Core.Cast expr co)
                    end in
                  match arg_0__, arg_1__ with
                  | Core.Mk_Coercion e_co, co =>
                      if Core.isCoercionType (Pair.pSnd (Core.coercionKind co)) : bool
                      then Core.Mk_Coercion (Core.mkCoCast e_co co) else
                      j_7__
                  | _, _ => j_7__
                  end
              end.

(* Skipping definition `CoreUtils.mkTick' *)

(* Skipping definition `CoreUtils.mkTicks' *)

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

(* Skipping definition `CoreUtils.mkTickNoHNF' *)

(* Skipping definition `CoreUtils.tickHNFArgs' *)

(* Skipping definition `CoreUtils.stripTicksTop' *)

Definition stripTicksTopE {b}
   : (Core.Tickish Core.Id -> bool) -> Core.Expr b -> Core.Expr b :=
  fun p => let go := fun '(other) => other in go.

(* Skipping definition `CoreUtils.stripTicksTopT' *)

Definition stripTicksE {b}
   : (Core.Tickish Core.Id -> bool) -> Core.Expr b -> Core.Expr b :=
  fun p expr =>
    let go :=
      fix go arg_0__
            := let go_a (arg_14__ : Core.Alt b) : Core.Alt b :=
                 let 'pair (pair c bs) e := arg_14__ in
                 pair (pair c bs) (go e) in
               match arg_0__ with
               | Core.App e a => Core.App (go e) (go a)
               | Core.Lam b e => Core.Lam b (go e)
               | Core.Let b e => Core.Let (go_bs b) (go e)
               | Core.Case e b t as_ => Core.Case (go e) b t (GHC.Base.map go_a as_)
               | Core.Cast e c => Core.Cast (go e) c
               | other => other
               end with go_bs arg_7__
                          := let go_b (arg_11__ : b * Core.Expr b) : b * Core.Expr b :=
                               let 'pair b e := arg_11__ in
                               pair b (go e) in
                             match arg_7__ with
                             | Core.NonRec b e => Core.NonRec b (go e)
                             | Core.Rec bs => Core.Rec (GHC.Base.map go_b bs)
                             end for go in
    let go_bs :=
      fix go arg_0__
            := let go_a (arg_14__ : Core.Alt b) : Core.Alt b :=
                 let 'pair (pair c bs) e := arg_14__ in
                 pair (pair c bs) (go e) in
               match arg_0__ with
               | Core.App e a => Core.App (go e) (go a)
               | Core.Lam b e => Core.Lam b (go e)
               | Core.Let b e => Core.Let (go_bs b) (go e)
               | Core.Case e b t as_ => Core.Case (go e) b t (GHC.Base.map go_a as_)
               | Core.Cast e c => Core.Cast (go e) c
               | other => other
               end with go_bs arg_7__
                          := let go_b (arg_11__ : b * Core.Expr b) : b * Core.Expr b :=
                               let 'pair b e := arg_11__ in
                               pair b (go e) in
                             match arg_7__ with
                             | Core.NonRec b e => Core.NonRec b (go e)
                             | Core.Rec bs => Core.Rec (GHC.Base.map go_b bs)
                             end for go_bs in
    let go_b : b * Core.Expr b -> b * Core.Expr b :=
      fun '(pair b e) => pair b (go e) in
    let go_a : Core.Alt b -> Core.Alt b :=
      fun '(pair (pair c bs) e) => pair (pair c bs) (go e) in
    go expr.

Definition stripTicksT {b}
   : (Core.Tickish Core.Id -> bool) ->
     Core.Expr b -> list (Core.Tickish Core.Id) :=
  fun p expr =>
    let go :=
      fix go arg_0__
            := let go_a (arg_14__ : Core.Alt b) : OrdList.OrdList (Core.Tickish Core.Id) :=
                 let 'pair (pair _ _) e := arg_14__ in
                 go e in
               match arg_0__ with
               | Core.App e a => OrdList.appOL (go e) (go a)
               | Core.Lam _ e => go e
               | Core.Let b e => OrdList.appOL (go_bs b) (go e)
               | Core.Case e _ _ as_ =>
                   OrdList.appOL (go e) (OrdList.concatOL (GHC.Base.map go_a as_))
               | Core.Cast e _ => go e
               | _ => OrdList.nilOL
               end with go_bs arg_7__
                          := let go_b (arg_11__ : b * Core.Expr b)
                              : OrdList.OrdList (Core.Tickish Core.Id) :=
                               let 'pair _ e := arg_11__ in
                               go e in
                             match arg_7__ with
                             | Core.NonRec _ e => go e
                             | Core.Rec bs => OrdList.concatOL (GHC.Base.map go_b bs)
                             end for go in
    let go_bs :=
      fix go arg_0__
            := let go_a (arg_14__ : Core.Alt b) : OrdList.OrdList (Core.Tickish Core.Id) :=
                 let 'pair (pair _ _) e := arg_14__ in
                 go e in
               match arg_0__ with
               | Core.App e a => OrdList.appOL (go e) (go a)
               | Core.Lam _ e => go e
               | Core.Let b e => OrdList.appOL (go_bs b) (go e)
               | Core.Case e _ _ as_ =>
                   OrdList.appOL (go e) (OrdList.concatOL (GHC.Base.map go_a as_))
               | Core.Cast e _ => go e
               | _ => OrdList.nilOL
               end with go_bs arg_7__
                          := let go_b (arg_11__ : b * Core.Expr b)
                              : OrdList.OrdList (Core.Tickish Core.Id) :=
                               let 'pair _ e := arg_11__ in
                               go e in
                             match arg_7__ with
                             | Core.NonRec _ e => go e
                             | Core.Rec bs => OrdList.concatOL (GHC.Base.map go_b bs)
                             end for go_bs in
    let go_b : b * Core.Expr b -> OrdList.OrdList (Core.Tickish Core.Id) :=
      fun '(pair _ e) => go e in
    let go_a : Core.Alt b -> OrdList.OrdList (Core.Tickish Core.Id) :=
      fun '(pair (pair _ _) e) => go e in
    OrdList.fromOL (go expr).

Axiom bindNonRec : Core.Id -> Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr.

Axiom exprOkForSpeculation : Core.CoreExpr -> bool.

Definition needsCaseBinding : AxiomatizedTypes.Type_ -> Core.CoreExpr -> bool :=
  fun ty rhs => andb (Core.isUnliftedType ty) (negb (exprOkForSpeculation rhs)).

Definition mkAltExpr
   : Core.AltCon ->
     list Core.CoreBndr -> list AxiomatizedTypes.Type_ -> Core.CoreExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Core.DataAlt con, args, inst_tys =>
        Core.mkConApp con (Coq.Init.Datatypes.app (GHC.Base.map Core.Mk_Type inst_tys)
                                                  (Core.varsToCoreExprs args))
    | Core.LitAlt lit, nil, nil => Core.Lit lit
    | Core.LitAlt _, _, _ => Panic.panic (GHC.Base.hs_string__ "mkAltExpr LitAlt")
    | Core.DEFAULT, _, _ => Panic.panic (GHC.Base.hs_string__ "mkAltExpr DEFAULT")
    end.

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

Definition addDefault {a} {b}
   : list (Core.AltCon * list a * b)%type ->
     option b -> list (Core.AltCon * list a * b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | alts, None => alts
    | alts, Some rhs => cons (pair (pair Core.DEFAULT nil) rhs) alts
    end.

Definition isDefaultAlt {a} {b} : (Core.AltCon * a * b)%type -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | pair (pair Core.DEFAULT _) _ => true
    | _ => false
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

Definition filterAlts {a}
   : Core.TyCon ->
     list AxiomatizedTypes.Type_ ->
     list Core.AltCon ->
     list (Core.AltCon * list Core.Var * a)%type ->
     (list Core.AltCon * list (Core.AltCon * list Core.Var * a)%type)%type :=
  fun _tycon inst_tys imposs_cons alts =>
    let impossible_alt {a} {b}
     : list AxiomatizedTypes.Type_ -> (Core.AltCon * a * b)%type -> bool :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | _, pair (pair con _) _ =>
            if Data.Foldable.elem con imposs_cons : bool then true else
            match arg_0__, arg_1__ with
            | inst_tys, pair (pair (Core.DataAlt con) _) _ =>
                Core.dataConCannotMatch inst_tys con
            | _, _ => false
            end
        end in
    let 'pair alts_wo_default maybe_deflt := findDefault alts in
    let alt_cons :=
      let cont_7__ arg_8__ := let 'pair (pair con _) _ := arg_8__ in cons con nil in
      Coq.Lists.List.flat_map cont_7__ alts_wo_default in
    let imposs_deflt_cons :=
      Data.OldList.nub (Coq.Init.Datatypes.app imposs_cons alt_cons) in
    let trimmed_alts := Util.filterOut (impossible_alt inst_tys) alts_wo_default in
    pair imposs_deflt_cons (addDefault trimmed_alts maybe_deflt).

Axiom refineDefaultAlt : list Unique.Unique ->
                         Core.TyCon ->
                         list AxiomatizedTypes.Type_ ->
                         list Core.AltCon -> list Core.CoreAlt -> (bool * list Core.CoreAlt)%type.

Axiom combineIdenticalAlts : list Core.AltCon ->
                             list Core.CoreAlt -> (bool * list Core.AltCon * list Core.CoreAlt)%type.

Fixpoint exprIsTrivial (arg_0__ : Core.CoreExpr) : bool
           := match arg_0__ with
              | Core.Mk_Var _ => true
              | Core.Mk_Type _ => true
              | Core.Mk_Coercion _ => true
              | Core.Lit lit => Literal.litIsTrivial lit
              | Core.App e arg => andb (negb (Core.isRuntimeArg arg)) (exprIsTrivial e)
              | Core.Lam b e => andb (negb (Core.isRuntimeVar b)) (exprIsTrivial e)
              | Core.Cast e _ => exprIsTrivial e
              | Core.Case e _ _ nil => exprIsTrivial e
              | _ => false
              end.

Definition getIdFromTrivialExpr_maybe : Core.CoreExpr -> option Core.Id :=
  fun e =>
    let fix go arg_0__
              := match arg_0__ with
                 | Core.Mk_Var v => Some v
                 | Core.App f t => if negb (Core.isRuntimeArg t) : bool then go f else None
                 | Core.Cast e _ => go e
                 | Core.Lam b e => if negb (Core.isRuntimeVar b) : bool then go e else None
                 | _ => None
                 end in
    go e.

Definition getIdFromTrivialExpr : Core.CoreExpr -> Core.Id :=
  fun e =>
    Data.Maybe.fromMaybe (Panic.panicStr (GHC.Base.hs_string__
                                          "getIdFromTrivialExpr") (Panic.someSDoc)) (getIdFromTrivialExpr_maybe e).

Definition isEmptyTy : AxiomatizedTypes.Type_ -> bool :=
  fun ty =>
    match Core.splitTyConApp_maybe ty with
    | Some (pair tc inst_tys) =>
        match Core.tyConDataCons_maybe tc with
        | Some dcs =>
            if Data.Foldable.all (Core.dataConCannotMatch inst_tys) dcs : bool
            then true else
            false
        | _ => false
        end
    | _ => false
    end.

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
                 | n, Core.Cast e _ => go n e
                 | n, Core.Let _ e => go n e
                 | n, Core.Lam v e => if Core.isTyVar v : bool then go n e else j_3__
                 | _, _ => j_3__
                 end in
    if isEmptyTy (exprType e) : bool then true else
    go #0 e.

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
               | n, Core.Mk_Type _ => Some n
               | n, Core.Mk_Coercion _ => Some n
               | n, Core.Mk_Var _ => decrement n
               | n, Core.Cast e _ => go n e
               | n, Core.App f a => match go n a with | Some n' => go n' f | _ => None end
               | n, Core.Lit lit =>
                   if Literal.litIsDupable dflags lit : bool then decrement n else
                   None
               | _, _ => None
               end in
    Data.Maybe.isJust (go dupAppSize e).

Definition exprIsCheapX : CheapAppFun -> Core.CoreExpr -> bool :=
  fun ok_app e =>
    let fix go arg_1__ arg_2__
              := let ok e := go #0 e in
                 match arg_1__, arg_2__ with
                 | n, Core.Mk_Var v => ok_app v n
                 | _, Core.Lit _ => true
                 | _, Core.Mk_Type _ => true
                 | _, Core.Mk_Coercion _ => true
                 | n, Core.Cast e _ => go n e
                 | n, Core.Case scrut _ _ alts =>
                     andb (ok scrut) (Data.Foldable.and (let cont_5__ arg_6__ :=
                                                           let 'pair (pair _ _) rhs := arg_6__ in
                                                           cons (go n rhs) nil in
                                                         Coq.Lists.List.flat_map cont_5__ alts))
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

Axiom isCheapApp : CheapAppFun.

Definition exprIsCheap : Core.CoreExpr -> bool :=
  exprIsCheapX isCheapApp.

Axiom isExpandableApp : CheapAppFun.

Definition exprIsExpandable : Core.CoreExpr -> bool :=
  exprIsCheapX isExpandableApp.

Definition isWorkFreeApp : CheapAppFun :=
  fun fn n_val_args =>
    if n_val_args GHC.Base.== #0 : bool then true else
    if n_val_args GHC.Base.< Id.idArity fn : bool then true else
    match Core.idDetails fn with
    | Core.DataConWorkId _ => true
    | _ => false
    end.

Definition exprIsWorkFree : Core.CoreExpr -> bool :=
  exprIsCheapX isWorkFreeApp.

Axiom exprOkForSideEffects : Core.CoreExpr -> bool.

Axiom expr_ok : (AxiomatizedTypes.PrimOp -> bool) -> Core.CoreExpr -> bool.

Axiom app_ok : (AxiomatizedTypes.PrimOp -> bool) ->
               Core.Id -> list Core.CoreExpr -> bool.

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

Axiom isDivOp : AxiomatizedTypes.PrimOp -> bool.

Definition exprIsHNFlike
   : (Core.Var -> bool) -> (Core.Unfolding -> bool) -> Core.CoreExpr -> bool :=
  fun is_con is_con_unf =>
    let id_app_is_value :=
      fun id n_val_args =>
        orb (is_con id) (orb (Id.idArity id GHC.Base.> n_val_args) (Unique.hasKey id
                                                                                  PrelNames.absentErrorIdKey)) in
    let app_is_value : Core.CoreExpr -> nat -> bool :=
      fix app_is_value (arg_1__ : Core.CoreExpr) (arg_2__ : nat) : bool
            := match arg_1__, arg_2__ with
               | Core.Mk_Var f, nva => id_app_is_value f nva
               | Core.Cast f _, nva => app_is_value f nva
               | Core.App f a, nva =>
                   if Core.isValArg a : bool then app_is_value f (nva GHC.Num.+ #1) else
                   app_is_value f nva
               | _, _ => false
               end in
    let fix is_hnf_like arg_8__
              := match arg_8__ with
                 | Core.Mk_Var v => orb (id_app_is_value v #0) (is_con_unf (Id.idUnfolding v))
                 | Core.Lit _ => true
                 | Core.Mk_Type _ => true
                 | Core.Mk_Coercion _ => true
                 | Core.Lam b e => orb (Core.isRuntimeVar b) (is_hnf_like e)
                 | Core.Cast e _ => is_hnf_like e
                 | Core.App e a =>
                     if Core.isValArg a : bool then app_is_value e #1 else
                     is_hnf_like e
                 | _ => match arg_8__ with | Core.Let _ e => is_hnf_like e | _ => false end
                 end in
    is_hnf_like.

Definition exprIsHNF : Core.CoreExpr -> bool :=
  exprIsHNFlike Id.isDataConWorkId Core.isEvaldUnfolding.

Definition exprIsConLike : Core.CoreExpr -> bool :=
  exprIsHNFlike Id.isConLikeId Core.isConLikeUnfolding.

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

Axiom cheapEqExpr' : forall {b},
                     (Core.Tickish Core.Id -> bool) -> Core.Expr b -> Core.Expr b -> bool.

Definition cheapEqExpr {b} : Core.Expr b -> Core.Expr b -> bool :=
  cheapEqExpr' (GHC.Base.const false).

Fixpoint exprIsBig {b} (arg_0__ : Core.Expr b) : bool
           := match arg_0__ with
              | Core.Lit _ => false
              | Core.Mk_Var _ => false
              | Core.Mk_Type _ => false
              | Core.Mk_Coercion _ => false
              | Core.Lam _ e => exprIsBig e
              | Core.App f a => orb (exprIsBig f) (exprIsBig a)
              | Core.Cast e _ => exprIsBig e
              | _ => true
              end.

Definition eqExpr : Core.InScopeSet -> Core.CoreExpr -> Core.CoreExpr -> bool :=
  fun in_scope e1 e2 =>
    let fix go arg_0__ arg_1__ arg_2__
              := let go_alt (arg_18__ : Core.RnEnv2) (arg_19__ arg_20__ : Core.CoreAlt)
                  : bool :=
                   match arg_18__, arg_19__, arg_20__ with
                   | env, pair (pair c1 bs1) e1, pair (pair c2 bs2) e2 =>
                       andb (c1 GHC.Base.== c2) (go (Core.rnBndrs2 env bs1 bs2) e1 e2)
                   end in
                 match arg_0__, arg_1__, arg_2__ with
                 | env, Core.Mk_Var v1, Core.Mk_Var v2 =>
                     if Core.rnOccL env v1 GHC.Base.== Core.rnOccR env v2 : bool then true else
                     false
                 | _, Core.Lit lit1, Core.Lit lit2 => lit1 GHC.Base.== lit2
                 | env, Core.Mk_Type t1, Core.Mk_Type t2 => Core.eqTypeX env t1 t2
                 | env, Core.Mk_Coercion co1, Core.Mk_Coercion co2 =>
                     Core.eqCoercionX env co1 co2
                 | env, Core.Cast e1 co1, Core.Cast e2 co2 =>
                     andb (Core.eqCoercionX env co1 co2) (go env e1 e2)
                 | env, Core.App f1 a1, Core.App f2 a2 => andb (go env f1 f2) (go env a1 a2)
                 | env, Core.Lam b1 e1, Core.Lam b2 e2 =>
                     andb (Core.eqTypeX env (Core.varType b1) (Core.varType b2)) (go (Core.rnBndr2
                                                                                      env b1 b2) e1 e2)
                 | env, Core.Let (Core.NonRec v1 r1) e1, Core.Let (Core.NonRec v2 r2) e2 =>
                     andb (go env r1 r2) (go (Core.rnBndr2 env v1 v2) e1 e2)
                 | env, Core.Let (Core.Rec ps1) e1, Core.Let (Core.Rec ps2) e2 =>
                     let 'pair bs2 rs2 := GHC.List.unzip ps2 in
                     let 'pair bs1 rs1 := GHC.List.unzip ps1 in
                     let env' := Core.rnBndrs2 env bs1 bs2 in
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
            andb (c1 GHC.Base.== c2) (go (Core.rnBndrs2 env bs1 bs2) e1 e2)
        end in
    go (Core.mkRnEnv2 in_scope) e1 e2.

Definition eqTickish
   : Core.RnEnv2 -> Core.Tickish Core.Id -> Core.Tickish Core.Id -> bool :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | env, Core.Breakpoint lid lids, Core.Breakpoint rid rids =>
        andb (lid GHC.Base.== rid) (GHC.Base.map (Core.rnOccL env) lids GHC.Base.==
              GHC.Base.map (Core.rnOccR env) rids)
    | _, l, r => l GHC.Base.== r
    end.

Axiom diffExpr : bool ->
                 Core.RnEnv2 -> Core.CoreExpr -> Core.CoreExpr -> list GHC.Base.String.

Axiom diffBinds : bool ->
                  Core.RnEnv2 ->
                  list (Core.Var * Core.CoreExpr)%type ->
                  list (Core.Var * Core.CoreExpr)%type ->
                  (list GHC.Base.String * Core.RnEnv2)%type.

Axiom diffIdInfo : Core.RnEnv2 -> Core.Var -> Core.Var -> list GHC.Base.String.

Axiom diffUnfold : Core.RnEnv2 ->
                   Core.Unfolding -> Core.Unfolding -> list GHC.Base.String.

Definition locBind
   : GHC.Base.String ->
     Core.Var -> Core.Var -> list GHC.Base.String -> list GHC.Base.String :=
  fun loc b1 b2 diffs =>
    let bindLoc :=
      if b1 GHC.Base.== b2 : bool then Panic.someSDoc else
      GHC.Base.mappend (GHC.Base.mappend Panic.someSDoc Panic.someSDoc)
                       Panic.someSDoc in
    let addLoc := fun d => d in GHC.Base.map addLoc diffs.

Axiom tryEtaReduce : list Core.Var -> Core.CoreExpr -> option Core.CoreExpr.

(* Skipping definition `CoreUtils.rhsIsStatic' *)

Definition collectMakeStaticArgs
   : Core.CoreExpr ->
     option (Core.CoreExpr * AxiomatizedTypes.Type_ * Core.CoreExpr *
             Core.CoreExpr)%type :=
  fun '(e) =>
    match Core.collectArgsTicks (GHC.Base.const true) e with
    | pair (pair (Core.Mk_Var b as fun_) (cons (Core.Mk_Type t) (cons loc (cons arg
        nil)))) _ =>
        if Id.idName b GHC.Base.== PrelNames.makeStaticName : bool
        then Some (pair (pair (pair fun_ t) loc) arg) else
        None
    | _ => None
    end.

Definition isJoinBind : Core.CoreBind -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.NonRec b _ => Id.isJoinId b
    | Core.Rec (cons (pair b _) _) => Id.isJoinId b
    | _ => false
    end.

(* External variables:
     Eq Gt Lt None Some andb bool cons false id list nat negb nil op_zt__ option orb
     pair snd true AxiomatizedTypes.Coercion AxiomatizedTypes.PrimOp
     AxiomatizedTypes.Representational AxiomatizedTypes.Type_ BasicTypes.Arity
     Coq.Init.Datatypes.app Coq.Lists.List.flat_map Core.Alt Core.AltCon Core.App
     Core.Breakpoint Core.Case Core.Cast Core.CoreAlt Core.CoreArg Core.CoreBind
     Core.CoreBndr Core.CoreExpr Core.DEFAULT Core.DataAlt Core.DataCon
     Core.DataConWorkId Core.Expr Core.Id Core.InScopeSet Core.Lam Core.Let Core.Lit
     Core.LitAlt Core.Mk_Coercion Core.Mk_Type Core.Mk_Var Core.NonRec Core.Rec
     Core.RnEnv2 Core.Tickish Core.TyCon Core.TyVar Core.Unfolding Core.Var
     Core.cmpAlt Core.cmpAltCon Core.coercionKind Core.coercionRole
     Core.collectArgsTicks Core.dataConCannotMatch Core.dataConTyCon
     Core.dataConUnivTyVars Core.eqCoercionX Core.eqType Core.eqTypeX Core.idDetails
     Core.isCoercionType Core.isConLikeUnfolding Core.isEvaldUnfolding Core.isReflCo
     Core.isRuntimeArg Core.isRuntimeVar Core.isTyVar Core.isTypeArg
     Core.isUnliftedType Core.isValArg Core.mkCoCast Core.mkConApp Core.mkRnEnv2
     Core.mkTransCo Core.rnBndr2 Core.rnBndrs2 Core.rnOccL Core.rnOccR
     Core.splitTyConApp_maybe Core.tyConDataCons_maybe Core.tyConFamilySize
     Core.valArgCount Core.varType Core.varsToCoreExprs Data.Foldable.all
     Data.Foldable.and Data.Foldable.elem Data.Foldable.null Data.Maybe.fromMaybe
     Data.Maybe.isJust Data.OldList.nub Data.Tuple.snd Datatypes.id DynFlags.DynFlags
     FastString.FastString GHC.Base.String GHC.Base.const GHC.Base.map
     GHC.Base.mappend GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.DeferredFix.deferredFix1 GHC.Err.error
     GHC.List.unzip GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ Id.idArity
     Id.idName Id.idUnfolding Id.isBottomingId Id.isConLikeId Id.isDataConWorkId
     Id.isJoinId Literal.MachStr Literal.litIsDupable Literal.litIsTrivial
     NestedRecursionHelpers.all2Map OrdList.OrdList OrdList.appOL OrdList.concatOL
     OrdList.fromOL OrdList.nilOL Pair.Mk_Pair Pair.pSnd Panic.assertPanic
     Panic.panic Panic.panicStr Panic.someSDoc Panic.warnPprTrace
     PrelNames.absentErrorIdKey PrelNames.makeStaticName Unique.Unique Unique.hasKey
     Util.debugIsOn Util.dropList Util.equalLength Util.filterOut Util.lengthIs
*)
