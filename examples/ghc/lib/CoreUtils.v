(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Core.


(* Converted imports: *)

Require Core.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require Unique.

(* Converted type declarations: *)

Definition CheapAppFun :=
  (Core.Var -> nat -> bool)%type.
(* Midamble *)

(* Record selector *)
Require Import Pair.

(* Notation for Alt *)
Require Import Core.


(* Converted value declarations: *)

Axiom tryEtaReduce : list Core.Var -> Core.CoreExpr -> option Core.CoreExpr.

Axiom exprIsBottom : Core.CoreExpr -> bool.

Axiom bindNonRec : Core.Var -> Core.CoreExpr -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkCast : Core.CoreExpr -> unit -> Core.CoreExpr.

Axiom isExprLevPoly : Core.CoreExpr -> bool.

(* coreAltsType skipped *)

(* coreAltType skipped *)

(* exprType skipped *)

(* applyTypeToArgs skipped *)

Axiom mkTickNoHNF : Core.Tickish Core.Var -> Core.CoreExpr -> Core.CoreExpr.

Axiom combineIdenticalAlts : list Core.AltCon ->
                             list Core.CoreAlt -> (bool * list Core.AltCon * list Core.CoreAlt)%type.

Axiom mkTicks : list (Core.Tickish Core.Var) -> Core.CoreExpr -> Core.CoreExpr.

Axiom tickHNFArgs : Core.Tickish Core.Var -> Core.CoreExpr -> Core.CoreExpr.

Axiom mkTick : Core.Tickish Core.Var -> Core.CoreExpr -> Core.CoreExpr.

Axiom isSaturatedConApp : Core.CoreExpr -> bool.

Axiom stripTicksTop : forall {b},
                      (Core.Tickish Core.Var -> bool) ->
                      Core.Expr b -> (list (Core.Tickish Core.Var) * Core.Expr b)%type.

Axiom cheapEqExpr : forall {b}, Core.Expr b -> Core.Expr b -> bool.

Axiom cheapEqExpr' : forall {b},
                     (Core.Tickish Core.Var -> bool) -> Core.Expr b -> Core.Expr b -> bool.

Axiom exprOkForSideEffects : Core.CoreExpr -> bool.

Axiom needsCaseBinding : unit -> Core.CoreExpr -> bool.

Axiom exprOkForSpeculation : Core.CoreExpr -> bool.

Axiom app_ok : (unit -> bool) -> Core.Var -> list Core.CoreExpr -> bool.

Axiom expr_ok : (unit -> bool) -> Core.CoreExpr -> bool.

Axiom stripTicksTopE : forall {b},
                       (Core.Tickish Core.Var -> bool) -> Core.Expr b -> Core.Expr b.

Axiom stripTicksTopT : forall {b},
                       (Core.Tickish Core.Var -> bool) -> Core.Expr b -> list (Core.Tickish Core.Var).

Axiom stripTicksE : forall {b},
                    (Core.Tickish Core.Var -> bool) -> Core.Expr b -> Core.Expr b.

Axiom stripTicksT : forall {b},
                    (Core.Tickish Core.Var -> bool) -> Core.Expr b -> list (Core.Tickish Core.Var).

Axiom mkAltExpr : Core.AltCon ->
                  list Core.CoreBndr -> list unit -> Core.CoreExpr.

Axiom filterAlts : forall {a},
                   Core.TyCon ->
                   list unit ->
                   list Core.AltCon ->
                   list (Core.AltCon * list Core.Var * a)%type ->
                   (list Core.AltCon * list (Core.AltCon * list Core.Var * a)%type)%type.

Axiom findDefault : forall {a} {b},
                    list (Core.AltCon * list a * b)%type ->
                    (list (Core.AltCon * list a * b)%type * option b)%type.

Axiom addDefault : forall {a} {b},
                   list (Core.AltCon * list a * b)%type ->
                   option b -> list (Core.AltCon * list a * b)%type.

Axiom isDefaultAlt : forall {a} {b}, (Core.AltCon * a * b)%type -> bool.

Axiom findAlt : forall {a} {b},
                Core.AltCon ->
                list (Core.AltCon * a * b)%type -> option (Core.AltCon * a * b)%type.

Axiom refineDefaultAlt : list Unique.Unique ->
                         Core.TyCon ->
                         list unit ->
                         list Core.AltCon -> list Core.CoreAlt -> (bool * list Core.CoreAlt)%type.

Axiom mergeAlts : forall {a} {b},
                  list (Core.AltCon * a * b)%type ->
                  list (Core.AltCon * a * b)%type -> list (Core.AltCon * a * b)%type.

Axiom trimConArgs : Core.AltCon -> list Core.CoreArg -> list Core.CoreArg.

Axiom exprIsTrivial : Core.CoreExpr -> bool.

Axiom getIdFromTrivialExpr : Core.CoreExpr -> Core.Var.

Axiom getIdFromTrivialExpr_maybe : Core.CoreExpr -> option Core.Var.

Axiom exprIsDupable : DynFlags.DynFlags -> Core.CoreExpr -> bool.

Axiom dupAppSize : nat.

Axiom exprIsCheap : Core.CoreExpr -> bool.

Axiom exprIsExpandable : Core.CoreExpr -> bool.

Axiom exprIsWorkFree : Core.CoreExpr -> bool.

Axiom exprIsCheapX : CheapAppFun -> Core.CoreExpr -> bool.

Axiom isExpandableApp : CheapAppFun.

Axiom isCheapApp : CheapAppFun.

Axiom isWorkFreeApp : CheapAppFun.

Axiom altsAreExhaustive : forall {b}, list (Alt b) -> bool.

Axiom isDivOp : unit -> bool.

Axiom exprIsHNF : Core.CoreExpr -> bool.

Axiom exprIsConLike : Core.CoreExpr -> bool.

Axiom exprIsHNFlike : (Core.Var -> bool) ->
                      (Core.Unfolding -> bool) -> Core.CoreExpr -> bool.

Axiom exprIsTopLevelBindable : Core.CoreExpr -> unit -> bool.

Axiom exprIsTickedString : Core.CoreExpr -> bool.

Axiom exprIsTickedString_maybe : Core.CoreExpr -> option GHC.Base.String.

Axiom dataConRepInstPat : list Unique.Unique ->
                          Core.DataCon -> list unit -> (list Core.Var * list Core.Var)%type.

Axiom dataConRepFSInstPat : list FastString.FastString ->
                            list Unique.Unique ->
                            Core.DataCon -> list unit -> (list Core.Var * list Core.Var)%type.

Axiom dataConInstPat : list FastString.FastString ->
                       list Unique.Unique ->
                       Core.DataCon -> list unit -> (list Core.Var * list Core.Var)%type.

Axiom exprIsBig : forall {b}, Core.Expr b -> bool.

Axiom eqExpr : Core.InScopeSet -> Core.CoreExpr -> Core.CoreExpr -> bool.

Axiom diffUnfold : Core.RnEnv2 ->
                   Core.Unfolding -> Core.Unfolding -> list GHC.Base.String.

Axiom diffIdInfo : Core.RnEnv2 -> Core.Var -> Core.Var -> list GHC.Base.String.

Axiom diffBinds : bool ->
                  Core.RnEnv2 ->
                  list (Core.Var * Core.CoreExpr)%type ->
                  list (Core.Var * Core.CoreExpr)%type ->
                  (list GHC.Base.String * Core.RnEnv2)%type.

Axiom diffExpr : bool ->
                 Core.RnEnv2 -> Core.CoreExpr -> Core.CoreExpr -> list GHC.Base.String.

Axiom eqTickish : Core.RnEnv2 ->
                  Core.Tickish Core.Var -> Core.Tickish Core.Var -> bool.

Axiom locBind : GHC.Base.String ->
                Core.Var -> Core.Var -> list GHC.Base.String -> list GHC.Base.String.

(* rhsIsStatic skipped *)

Axiom isEmptyTy : unit -> bool.

(* collectMakeStaticArgs skipped *)

Axiom isJoinBind : Core.CoreBind -> bool.

(* External variables:
     Alt bool list nat op_zt__ option unit Core.AltCon Core.CoreAlt Core.CoreArg
     Core.CoreBind Core.CoreBndr Core.CoreExpr Core.DataCon Core.Expr Core.InScopeSet
     Core.RnEnv2 Core.Tickish Core.TyCon Core.Unfolding Core.Var DynFlags.DynFlags
     FastString.FastString GHC.Base.String Unique.Unique
*)
