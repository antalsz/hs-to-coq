(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Combined.


(* Converted imports: *)

Require BasicTypes.
Require Combined.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require Unique.

(* Converted type declarations: *)

Definition CheapAppFun :=
  (Combined.Var -> BasicTypes.Arity -> bool)%type.
(* Midamble *)

(* Record selector *)
Require Import Pair.

(* Notation for Alt *)
Require Import Combined.


(* Converted value declarations: *)

Axiom tryEtaReduce : list Combined.Var ->
                     Combined.CoreExpr -> option Combined.CoreExpr.

Axiom exprIsBottom : Combined.CoreExpr -> bool.

Axiom bindNonRec : Combined.Var ->
                   Combined.CoreExpr -> Combined.CoreExpr -> Combined.CoreExpr.

Axiom mkCast : Combined.CoreExpr -> unit -> Combined.CoreExpr.

Axiom isExprLevPoly : Combined.CoreExpr -> bool.

(* coreAltsType skipped *)

(* coreAltType skipped *)

(* exprType skipped *)

(* applyTypeToArgs skipped *)

Axiom mkTickNoHNF : Combined.Tickish Combined.Var ->
                    Combined.CoreExpr -> Combined.CoreExpr.

Axiom combineIdenticalAlts : list Combined.AltCon ->
                             list Combined.CoreAlt ->
                             (bool * list Combined.AltCon * list Combined.CoreAlt)%type.

Axiom mkTicks : list (Combined.Tickish Combined.Var) ->
                Combined.CoreExpr -> Combined.CoreExpr.

Axiom tickHNFArgs : Combined.Tickish Combined.Var ->
                    Combined.CoreExpr -> Combined.CoreExpr.

Axiom mkTick : Combined.Tickish Combined.Var ->
               Combined.CoreExpr -> Combined.CoreExpr.

Axiom isSaturatedConApp : Combined.CoreExpr -> bool.

Axiom stripTicksTop : forall {b},
                      (Combined.Tickish Combined.Var -> bool) ->
                      Combined.Expr b ->
                      (list (Combined.Tickish Combined.Var) * Combined.Expr b)%type.

Axiom cheapEqExpr : forall {b}, Combined.Expr b -> Combined.Expr b -> bool.

Axiom cheapEqExpr' : forall {b},
                     (Combined.Tickish Combined.Var -> bool) ->
                     Combined.Expr b -> Combined.Expr b -> bool.

Axiom exprOkForSideEffects : Combined.CoreExpr -> bool.

Axiom needsCaseBinding : unit -> Combined.CoreExpr -> bool.

Axiom exprOkForSpeculation : Combined.CoreExpr -> bool.

Axiom app_ok : (unit -> bool) -> Combined.Var -> list Combined.CoreExpr -> bool.

Axiom expr_ok : (unit -> bool) -> Combined.CoreExpr -> bool.

Axiom stripTicksTopE : forall {b},
                       (Combined.Tickish Combined.Var -> bool) -> Combined.Expr b -> Combined.Expr b.

Axiom stripTicksTopT : forall {b},
                       (Combined.Tickish Combined.Var -> bool) ->
                       Combined.Expr b -> list (Combined.Tickish Combined.Var).

Axiom stripTicksE : forall {b},
                    (Combined.Tickish Combined.Var -> bool) -> Combined.Expr b -> Combined.Expr b.

Axiom stripTicksT : forall {b},
                    (Combined.Tickish Combined.Var -> bool) ->
                    Combined.Expr b -> list (Combined.Tickish Combined.Var).

Axiom mkAltExpr : Combined.AltCon ->
                  list Combined.CoreBndr -> list unit -> Combined.CoreExpr.

Axiom filterAlts : forall {a},
                   Combined.TyCon ->
                   list unit ->
                   list Combined.AltCon ->
                   list (Combined.AltCon * list Combined.Var * a)%type ->
                   (list Combined.AltCon *
                    list (Combined.AltCon * list Combined.Var * a)%type)%type.

Axiom findDefault : forall {a} {b},
                    list (Combined.AltCon * list a * b)%type ->
                    (list (Combined.AltCon * list a * b)%type * option b)%type.

Axiom addDefault : forall {a} {b},
                   list (Combined.AltCon * list a * b)%type ->
                   option b -> list (Combined.AltCon * list a * b)%type.

Axiom isDefaultAlt : forall {a} {b}, (Combined.AltCon * a * b)%type -> bool.

Axiom findAlt : forall {a} {b},
                Combined.AltCon ->
                list (Combined.AltCon * a * b)%type -> option (Combined.AltCon * a * b)%type.

Axiom refineDefaultAlt : list Unique.Unique ->
                         Combined.TyCon ->
                         list unit ->
                         list Combined.AltCon ->
                         list Combined.CoreAlt -> (bool * list Combined.CoreAlt)%type.

Axiom mergeAlts : forall {a} {b},
                  list (Combined.AltCon * a * b)%type ->
                  list (Combined.AltCon * a * b)%type -> list (Combined.AltCon * a * b)%type.

Axiom trimConArgs : Combined.AltCon ->
                    list Combined.CoreArg -> list Combined.CoreArg.

Axiom exprIsTrivial : Combined.CoreExpr -> bool.

Axiom getIdFromTrivialExpr : Combined.CoreExpr -> Combined.Var.

Axiom getIdFromTrivialExpr_maybe : Combined.CoreExpr -> option Combined.Var.

Axiom exprIsDupable : DynFlags.DynFlags -> Combined.CoreExpr -> bool.

Axiom dupAppSize : GHC.Num.Int.

Axiom exprIsCheap : Combined.CoreExpr -> bool.

Axiom exprIsExpandable : Combined.CoreExpr -> bool.

Axiom exprIsWorkFree : Combined.CoreExpr -> bool.

Axiom exprIsCheapX : CheapAppFun -> Combined.CoreExpr -> bool.

Axiom isExpandableApp : CheapAppFun.

Axiom isCheapApp : CheapAppFun.

Axiom isWorkFreeApp : CheapAppFun.

Axiom altsAreExhaustive : forall {b}, list (Alt b) -> bool.

Axiom isDivOp : unit -> bool.

Axiom exprIsHNF : Combined.CoreExpr -> bool.

Axiom exprIsConLike : Combined.CoreExpr -> bool.

Axiom exprIsHNFlike : (Combined.Var -> bool) ->
                      (Combined.Unfolding -> bool) -> Combined.CoreExpr -> bool.

Axiom exprIsTopLevelBindable : Combined.CoreExpr -> unit -> bool.

Axiom exprIsTickedString : Combined.CoreExpr -> bool.

Axiom exprIsTickedString_maybe : Combined.CoreExpr -> option GHC.Base.String.

Axiom dataConRepInstPat : list Unique.Unique ->
                          Combined.DataCon -> list unit -> (list Combined.Var * list Combined.Var)%type.

Axiom dataConRepFSInstPat : list FastString.FastString ->
                            list Unique.Unique ->
                            Combined.DataCon -> list unit -> (list Combined.Var * list Combined.Var)%type.

Axiom dataConInstPat : list FastString.FastString ->
                       list Unique.Unique ->
                       Combined.DataCon -> list unit -> (list Combined.Var * list Combined.Var)%type.

Axiom exprIsBig : forall {b}, Combined.Expr b -> bool.

Axiom eqExpr : Combined.InScopeSet ->
               Combined.CoreExpr -> Combined.CoreExpr -> bool.

Axiom diffUnfold : Combined.RnEnv2 ->
                   Combined.Unfolding -> Combined.Unfolding -> list GHC.Base.String.

Axiom diffIdInfo : Combined.RnEnv2 ->
                   Combined.Var -> Combined.Var -> list GHC.Base.String.

Axiom diffBinds : bool ->
                  Combined.RnEnv2 ->
                  list (Combined.Var * Combined.CoreExpr)%type ->
                  list (Combined.Var * Combined.CoreExpr)%type ->
                  (list GHC.Base.String * Combined.RnEnv2)%type.

Axiom diffExpr : bool ->
                 Combined.RnEnv2 ->
                 Combined.CoreExpr -> Combined.CoreExpr -> list GHC.Base.String.

Axiom eqTickish : Combined.RnEnv2 ->
                  Combined.Tickish Combined.Var -> Combined.Tickish Combined.Var -> bool.

Axiom locBind : GHC.Base.String ->
                Combined.Var -> Combined.Var -> list GHC.Base.String -> list GHC.Base.String.

(* rhsIsStatic skipped *)

Axiom isEmptyTy : unit -> bool.

(* collectMakeStaticArgs skipped *)

Axiom isJoinBind : Combined.CoreBind -> bool.

(* External variables:
     Alt bool list op_zt__ option unit BasicTypes.Arity Combined.AltCon
     Combined.CoreAlt Combined.CoreArg Combined.CoreBind Combined.CoreBndr
     Combined.CoreExpr Combined.DataCon Combined.Expr Combined.InScopeSet
     Combined.RnEnv2 Combined.Tickish Combined.TyCon Combined.Unfolding Combined.Var
     DynFlags.DynFlags FastString.FastString GHC.Base.String GHC.Num.Int
     Unique.Unique
*)
