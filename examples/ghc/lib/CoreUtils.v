(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)




(* Converted imports: *)

Require BasicTypes.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require Data.Foldable.
Require Data.Maybe.
Require Data.OldList.
Require DynFlags.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require Literal.
Require Panic.
Require PrelNames.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition CheapAppFun :=
  (Core.Var -> BasicTypes.Arity -> bool)%type.
(* Midamble *)

(* Record selector *)
Require Import Pair.

(* Notation for Alt *)

Definition Alt b := prod (prod Core.AltCon (list b)) (Core.Expr b).

(* Redefinition with correct recursion structure *)
Require OrdList.

Definition stripTicksE {b} (p : Core.Tickish Core.Var -> bool) (expr : Core.Expr b) : Core.Expr b :=
  let go := fix  go arg__ := match arg__ with
              | Core.App e a        => Core.App (go e) (go a)
              | Core.Lam b e        => Core.Lam b (go e)
              | Core.Let b e        => Core.Let (go_bs b) (go e)
              | Core.Case e b t as_ => let fix map_go_a arg__ := match arg__ with
                                             | nil              => nil
                                             | cons (c,bs,e) xs => cons (c, bs, go e) (map_go_a xs)
                                           end
                                       in Core.Case (go e) b t (map_go_a as_)
              | Core.Cast e c       => Core.Cast (go e) c
              | Core.Tick t e       => if p t
                                       then go e
                                       else Core.Tick t (go e)
              | other               => other
            end
            with go_bs arg__ := match arg__ with
              | Core.NonRec b e => Core.NonRec b (go e)
              | Core.Rec bs     => let fix map_go_b arg__ := match arg__ with
                                         | nil           => nil
                                         | cons (b,e) xs => cons (b, go e) xs
                                       end
                                   in Core.Rec (map_go_b bs)
            end
            for go
  in go expr.

Definition stripTicksT {b} (p : Core.Tickish Core.Var -> bool) (expr : Core.Expr b) : list (Core.Tickish Core.Var) :=
  let go := fix  go arg__ := match arg__ with
              | Core.App e a        => OrdList.appOL (go e) (go a)
              | Core.Lam _ e        => go e
              | Core.Let b e        => OrdList.appOL (go_bs b) (go e)
              | Core.Case e _ _ as_ => let fix map_go_a arg__ := match arg__ with
                                             | nil              => nil
                                             | cons (_,_,e) xs => cons (go e) (map_go_a xs)
                                           end
                                       in OrdList.appOL (go e) (OrdList.concatOL (map_go_a as_))
              | Core.Cast e _       => go e
              | Core.Tick t e       => if p t
                                       then OrdList.consOL t (go e)
                                       else go e
              | _                   => OrdList.nilOL
            end
            with go_bs arg__ := match arg__ with
              | Core.NonRec _ e => go e
              | Core.Rec bs     => let fix map_go_b arg__ := match arg__ with
                                         | nil           => nil
                                         | cons (_,e) xs => cons (go e) (map_go_b xs)
                                       end
                                   in OrdList.concatOL (map_go_b bs)
            end
            for go
  in OrdList.fromOL (go expr).

(* Converted value declarations: *)

Definition addDefault {a} {b}
   : list (Core.AltCon * list a * b)%type ->
     option b -> list (Core.AltCon * list a * b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | alts, None => alts
    | alts, Some rhs => cons (pair (pair Core.DEFAULT nil) rhs) alts
    end.

Definition altsAreExhaustive {b} : list (Alt b) -> bool :=
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

Definition cheapEqExpr' {b}
   : (Core.Expr b -> bool) -> Core.Expr b -> Core.Expr b -> bool :=
  GHC.Err.default.

Definition cheapEqExpr {b} : Core.Expr b -> Core.Expr b -> bool :=
  cheapEqExpr' (GHC.Base.const false).

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
      fix go arg_6__ arg_7__
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

Axiom eqExpr : forall {A : Type}, A.

(* Translating `eqExpr' failed: non-structural mutual recursion unsupported [in
   module CoreUtils] *)

Definition eqTickish
   : Core.RnEnv2 -> Core.Tickish Core.Var -> Core.Tickish Core.Var -> bool :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | env, Core.Breakpoint lid lids, Core.Breakpoint rid rids =>
        andb (lid GHC.Base.== rid) (GHC.Base.map (Core.rnOccL env) lids GHC.Base.==
              GHC.Base.map (Core.rnOccR env) rids)
    | _, l, r => l GHC.Base.== r
    end.

Definition exprIsBig {b} : Core.Expr b -> bool :=
  fix exprIsBig arg_0__
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
    go #0 e.

Axiom exprIsCheapX : forall {A : Type}, A.

(* Translating `exprIsCheapX' failed: non-structural mutual recursion
   unsupported [in module CoreUtils] *)

Definition exprIsHNFlike
   : (Core.Var -> bool) -> (Core.Unfolding -> bool) -> Core.CoreExpr -> bool :=
  fun is_con is_con_unf =>
    let id_app_is_value :=
      fun id n_val_args =>
        orb (is_con id) (orb (Id.idArity id GHC.Base.> n_val_args) false) in
    let app_is_value : Core.CoreExpr -> nat -> bool :=
      fix app_is_value arg_1__ arg_2__
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

Definition exprIsConLike : Core.CoreExpr -> bool :=
  exprIsHNFlike Id.isConLikeId Core.isConLikeUnfolding.

Definition exprIsTickedString_maybe : Core.CoreExpr -> option GHC.Base.String :=
  fix exprIsTickedString_maybe arg_0__
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
  fun expr ty => orb (negb (false)) (exprIsTickedString expr).

Definition exprIsTrivial : Core.CoreExpr -> bool :=
  fix exprIsTrivial arg_0__
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
                     | Gt => go alts deflt
                     end
                 end in
    match alts with
    | cons (pair (pair Core.DEFAULT _) _ as deflt) alts => go alts (Some deflt)
    | _ => go alts None
    end.

Definition findDefault {a} {b}
   : list (Core.AltCon * list a * b)%type ->
     (list (Core.AltCon * list a * b)%type * option b)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | cons (pair (pair Core.DEFAULT args) rhs) alts => pair alts (Some rhs)
    | alts => pair alts None
    end.

Definition filterAlts {a}
   : Core.TyCon ->
     list unit ->
     list Core.AltCon ->
     list (Core.AltCon * list Core.Var * a)%type ->
     (list Core.AltCon * list (Core.AltCon * list Core.Var * a)%type)%type :=
  fun _tycon inst_tys imposs_cons alts =>
    let impossible_alt {a} {b} : list unit -> (Core.AltCon * a * b)%type -> bool :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | _, pair (pair con _) _ =>
            if Data.Foldable.elem con imposs_cons : bool then true else
            match arg_0__, arg_1__ with
            | inst_tys, pair (pair (Core.DataAlt con) _) _ => false
            | _, _ => false
            end
        end in
    let 'pair alts_wo_default maybe_deflt := findDefault alts in
    let alt_cons :=
      let cont_6__ arg_7__ := let 'pair (pair con _) _ := arg_7__ in cons con nil in
      Coq.Lists.List.flat_map cont_6__ alts_wo_default in
    let imposs_deflt_cons :=
      Data.OldList.nub (Coq.Init.Datatypes.app imposs_cons alt_cons) in
    let trimmed_alts := Util.filterOut (impossible_alt inst_tys) alts_wo_default in
    pair imposs_deflt_cons (addDefault trimmed_alts maybe_deflt).

Definition getIdFromTrivialExpr_maybe : Core.CoreExpr -> option Core.Var :=
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

Definition getIdFromTrivialExpr : Core.CoreExpr -> Core.Var :=
  fun e =>
    Data.Maybe.fromMaybe (Panic.panicStr (GHC.Base.hs_string__
                                          "getIdFromTrivialExpr") (Panic.someSDoc)) (getIdFromTrivialExpr_maybe e).

Definition isCheapApp : CheapAppFun :=
  GHC.Err.default.

Definition exprIsCheap : Core.CoreExpr -> bool :=
  exprIsCheapX isCheapApp.

Definition isDefaultAlt {a} {b} : (Core.AltCon * a * b)%type -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | pair (pair Core.DEFAULT _) _ => true
    | _ => false
    end.

Definition isDivOp : unit -> bool :=
  GHC.Err.default.

Definition isExpandableApp : CheapAppFun :=
  GHC.Err.default.

Definition exprIsExpandable : Core.CoreExpr -> bool :=
  exprIsCheapX isExpandableApp.

Definition isExprLevPoly : Core.CoreExpr -> bool :=
  GHC.Err.default.

Definition isJoinBind : Core.CoreBind -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.NonRec b _ => Id.isJoinId b
    | Core.Rec (cons (pair b _) _) => Id.isJoinId b
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

Definition locBind
   : GHC.Base.String ->
     Core.Var -> Core.Var -> list GHC.Base.String -> list GHC.Base.String :=
  fun loc b1 b2 diffs =>
    let bindLoc :=
      if b1 GHC.Base.== b2 : bool then Panic.someSDoc else
      GHC.Base.mappend (GHC.Base.mappend Panic.someSDoc Panic.someSDoc)
                       Panic.someSDoc in
    let addLoc := fun d => Panic.someSDoc in GHC.Base.map addLoc diffs.

Definition mergeAlts {a} {b}
   : list (Core.AltCon * a * b)%type ->
     list (Core.AltCon * a * b)%type -> list (Core.AltCon * a * b)%type :=
  GHC.DeferredFix.deferredFix2 (fun mergeAlts arg_0__ arg_1__ =>
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

Definition mkCast : Core.CoreExpr -> unit -> Core.CoreExpr :=
  fun c t => c.

Definition mkTick : Core.Tickish Core.Var -> Core.CoreExpr -> Core.CoreExpr :=
  fun t orig => orig.

Definition mkTicks
   : list (Core.Tickish Core.Var) -> Core.CoreExpr -> Core.CoreExpr :=
  fun ticks expr => Data.Foldable.foldr mkTick expr ticks.

Definition stripTicksTop {b}
   : (Core.Tickish Core.Var -> bool) ->
     Core.Expr b -> (list (Core.Tickish Core.Var) * Core.Expr b)%type :=
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

Definition stripTicksTopE {b}
   : (Core.Tickish Core.Var -> bool) -> Core.Expr b -> Core.Expr b :=
  fun p =>
    let fix go arg_0__
              := let j_1__ := let 'other := arg_0__ in other in
                 match arg_0__ with
                 | Core.Tick t e => if p t : bool then go e else j_1__
                 | _ => j_1__
                 end in
    go.

Definition stripTicksTopT {b}
   : (Core.Tickish Core.Var -> bool) ->
     Core.Expr b -> list (Core.Tickish Core.Var) :=
  fun p =>
    let fix go arg_0__ arg_1__
              := let j_2__ := match arg_0__, arg_1__ with | ts, _ => ts end in
                 match arg_0__, arg_1__ with
                 | ts, Core.Tick t e => if p t : bool then go (cons t ts) e else j_2__
                 | _, _ => j_2__
                 end in
    go nil.

Definition tickHNFArgs
   : Core.Tickish Core.Var -> Core.CoreExpr -> Core.CoreExpr :=
  fun t orig => orig.

Definition mkTickNoHNF
   : Core.Tickish Core.Var -> Core.CoreExpr -> Core.CoreExpr :=
  fun t e => if exprIsHNF e : bool then tickHNFArgs t e else mkTick t e.

Definition trimConArgs
   : Core.AltCon -> list Core.CoreArg -> list Core.CoreArg :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Core.DEFAULT, args => nil
    | Core.LitAlt _, args => nil
    | Core.DataAlt dc, args => Util.dropList (Core.dataConUnivTyVars dc) args
    end.

(* External variables:
     Alt Eq Gt Lt None Some andb bool cons false list nat negb nil op_zt__ option orb
     pair true unit BasicTypes.Arity Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     Core.AltCon Core.App Core.Breakpoint Core.Case Core.Cast Core.Coercion
     Core.CoreArg Core.CoreBind Core.CoreBndr Core.CoreExpr Core.DEFAULT Core.DataAlt
     Core.DataConWorkId Core.Expr Core.Lam Core.Let Core.Lit Core.LitAlt Core.Mk_Var
     Core.NonRec Core.PlaceCostCentre Core.Rec Core.RnEnv2 Core.Tick Core.Tickish
     Core.TyCon Core.Type_ Core.Unfolding Core.Var Core.cmpAlt Core.cmpAltCon
     Core.collectArgsTicks Core.dataConTyCon Core.dataConUnivTyVars Core.idDetails
     Core.isConLikeUnfolding Core.isEvaldUnfolding Core.isRuntimeArg
     Core.isRuntimeVar Core.isTyVar Core.isTypeArg Core.isValArg Core.mkConApp
     Core.rnOccL Core.rnOccR Core.tickishCounts Core.tickishIsCode Core.tickishPlace
     Core.tyConFamilySize Core.valArgCount Core.varsToCoreExprs Data.Foldable.elem
     Data.Foldable.foldr Data.Foldable.null Data.Maybe.fromMaybe Data.Maybe.isJust
     Data.OldList.nub DynFlags.DynFlags GHC.Base.String GHC.Base.const GHC.Base.map
     GHC.Base.mappend GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.DeferredFix.deferredFix2 GHC.Err.default
     GHC.List.reverse GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ Id.idArity
     Id.idName Id.idUnfolding Id.isBottomingId Id.isConLikeId Id.isDataConWorkId
     Id.isJoinId Literal.MachStr Literal.litIsDupable Literal.litIsTrivial
     Panic.panic Panic.panicStr Panic.someSDoc PrelNames.makeStaticName Util.dropList
     Util.filterOut Util.lengthIs
*)
