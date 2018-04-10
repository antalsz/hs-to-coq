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
Require CoreSyn.
Require DataCon.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require TyCon.
Require Unique.
Require Var.
Require VarEnv.

(* Converted type declarations: *)

Definition CheapAppFun :=
  (Var.Id -> BasicTypes.Arity -> bool)%type.
(* Midamble *)

(* Record selector *)
Require Import Pair.

Require Import CoreSyn.

(* Uses functions from Type. Also recursion is tricky *)
(*
Parameter applyTypeToArgs : CoreSyn.CoreExpr -> Core.Type_ -> list
                            CoreSyn.CoreExpr -> Core.Type_.
Parameter exprType : CoreSyn.CoreExpr -> Core.Type_.

Parameter coreAltType : CoreSyn.CoreAlt -> Core.Type_.

Parameter mkCast : CoreSyn.CoreExpr -> Core.Coercion -> CoreSyn.CoreExpr.

Parameter dataConInstPat : list FastString.FastString -> list
                            Unique.Unique -> DataCon.DataCon -> list Core.Type_ -> (list TyVar * list
                            Var.Id)%type.
*)
(* Converted value declarations: *)

Axiom tryEtaReduce : list Var.Var ->
                     CoreSyn.CoreExpr -> option CoreSyn.CoreExpr.

Axiom exprIsBottom : CoreSyn.CoreExpr -> bool.

Axiom bindNonRec : Var.Id ->
                   CoreSyn.CoreExpr -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

(* mkCast skipped *)

Axiom isExprLevPoly : CoreSyn.CoreExpr -> bool.

Axiom coreAltsType : list CoreSyn.CoreAlt -> unit.

(* coreAltType skipped *)

(* exprType skipped *)

(* applyTypeToArgs skipped *)

Axiom mkTickNoHNF : CoreSyn.Tickish Var.Id ->
                    CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom combineIdenticalAlts : list CoreSyn.AltCon ->
                             list CoreSyn.CoreAlt ->
                             (bool * list CoreSyn.AltCon * list CoreSyn.CoreAlt)%type.

Axiom mkTicks : list (CoreSyn.Tickish Var.Id) ->
                CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom tickHNFArgs : CoreSyn.Tickish Var.Id ->
                    CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom mkTick : CoreSyn.Tickish Var.Id -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom isSaturatedConApp : CoreSyn.CoreExpr -> bool.

Axiom stripTicksTop : forall {b},
                      (CoreSyn.Tickish Var.Id -> bool) ->
                      CoreSyn.Expr b -> (list (CoreSyn.Tickish Var.Id) * CoreSyn.Expr b)%type.

Axiom cheapEqExpr : forall {b}, CoreSyn.Expr b -> CoreSyn.Expr b -> bool.

Axiom cheapEqExpr' : forall {b},
                     (CoreSyn.Tickish Var.Id -> bool) -> CoreSyn.Expr b -> CoreSyn.Expr b -> bool.

Axiom exprOkForSideEffects : CoreSyn.CoreExpr -> bool.

Axiom needsCaseBinding : unit -> CoreSyn.CoreExpr -> bool.

Axiom exprOkForSpeculation : CoreSyn.CoreExpr -> bool.

Axiom app_ok : (unit -> bool) -> Var.Id -> list CoreSyn.CoreExpr -> bool.

Axiom expr_ok : (unit -> bool) -> CoreSyn.CoreExpr -> bool.

Axiom stripTicksTopE : forall {b},
                       (CoreSyn.Tickish Var.Id -> bool) -> CoreSyn.Expr b -> CoreSyn.Expr b.

Axiom stripTicksTopT : forall {b},
                       (CoreSyn.Tickish Var.Id -> bool) ->
                       CoreSyn.Expr b -> list (CoreSyn.Tickish Var.Id).

Axiom stripTicksE : forall {b},
                    (CoreSyn.Tickish Var.Id -> bool) -> CoreSyn.Expr b -> CoreSyn.Expr b.

Axiom stripTicksT : forall {b},
                    (CoreSyn.Tickish Var.Id -> bool) ->
                    CoreSyn.Expr b -> list (CoreSyn.Tickish Var.Id).

Axiom mkAltExpr : CoreSyn.AltCon ->
                  list CoreSyn.CoreBndr -> list unit -> CoreSyn.CoreExpr.

Axiom filterAlts : forall {a},
                   TyCon.TyCon ->
                   list unit ->
                   list CoreSyn.AltCon ->
                   list (CoreSyn.AltCon * list Var.Var * a)%type ->
                   (list CoreSyn.AltCon * list (CoreSyn.AltCon * list Var.Var * a)%type)%type.

Axiom findDefault : forall {a} {b},
                    list (CoreSyn.AltCon * list a * b)%type ->
                    (list (CoreSyn.AltCon * list a * b)%type * option b)%type.

Axiom addDefault : forall {a} {b},
                   list (CoreSyn.AltCon * list a * b)%type ->
                   option b -> list (CoreSyn.AltCon * list a * b)%type.

Axiom isDefaultAlt : forall {a} {b}, (CoreSyn.AltCon * a * b)%type -> bool.

Axiom findAlt : forall {a} {b},
                CoreSyn.AltCon ->
                list (CoreSyn.AltCon * a * b)%type -> option (CoreSyn.AltCon * a * b)%type.

Axiom refineDefaultAlt : list Unique.Unique ->
                         TyCon.TyCon ->
                         list unit ->
                         list CoreSyn.AltCon ->
                         list CoreSyn.CoreAlt -> (bool * list CoreSyn.CoreAlt)%type.

Axiom mergeAlts : forall {a} {b},
                  list (CoreSyn.AltCon * a * b)%type ->
                  list (CoreSyn.AltCon * a * b)%type -> list (CoreSyn.AltCon * a * b)%type.

Axiom trimConArgs : CoreSyn.AltCon ->
                    list CoreSyn.CoreArg -> list CoreSyn.CoreArg.

Axiom exprIsTrivial : CoreSyn.CoreExpr -> bool.

Axiom getIdFromTrivialExpr : CoreSyn.CoreExpr -> Var.Id.

Axiom getIdFromTrivialExpr_maybe : CoreSyn.CoreExpr -> option Var.Id.

Axiom exprIsDupable : DynFlags.DynFlags -> CoreSyn.CoreExpr -> bool.

Axiom dupAppSize : GHC.Num.Int.

Axiom exprIsCheap : CoreSyn.CoreExpr -> bool.

Axiom exprIsExpandable : CoreSyn.CoreExpr -> bool.

Axiom exprIsWorkFree : CoreSyn.CoreExpr -> bool.

Axiom exprIsCheapX : CheapAppFun -> CoreSyn.CoreExpr -> bool.

Axiom isExpandableApp : CheapAppFun.

Axiom isCheapApp : CheapAppFun.

Axiom isWorkFreeApp : CheapAppFun.

Axiom altsAreExhaustive : forall {b}, list (Alt b) -> bool.

Axiom isDivOp : unit -> bool.

Axiom exprIsHNF : CoreSyn.CoreExpr -> bool.

Axiom exprIsConLike : CoreSyn.CoreExpr -> bool.

(* exprIsHNFlike skipped *)

Axiom exprIsTopLevelBindable : CoreSyn.CoreExpr -> unit -> bool.

Axiom exprIsTickedString : CoreSyn.CoreExpr -> bool.

Axiom exprIsTickedString_maybe : CoreSyn.CoreExpr -> option GHC.Base.String.

(* dataConRepInstPat skipped *)

Axiom dataConRepFSInstPat : list FastString.FastString ->
                            list Unique.Unique ->
                            DataCon.DataCon -> list unit -> (list Var.TyVar * list Var.Id)%type.

(* dataConInstPat skipped *)

Axiom exprIsBig : forall {b}, CoreSyn.Expr b -> bool.

Axiom eqExpr : VarEnv.InScopeSet ->
               CoreSyn.CoreExpr -> CoreSyn.CoreExpr -> bool.

(* diffUnfold skipped *)

(* diffIdInfo skipped *)

(* diffBinds skipped *)

(* diffExpr skipped *)

Axiom eqTickish : VarEnv.RnEnv2 ->
                  CoreSyn.Tickish Var.Id -> CoreSyn.Tickish Var.Id -> bool.

(* locBind skipped *)

(* rhsIsStatic skipped *)

Axiom isEmptyTy : unit -> bool.

Axiom collectMakeStaticArgs : CoreSyn.CoreExpr ->
                              option (CoreSyn.CoreExpr * unit * CoreSyn.CoreExpr * CoreSyn.CoreExpr)%type.

Axiom isJoinBind : CoreSyn.CoreBind -> bool.

(* External variables:
     Alt bool list op_zt__ option unit BasicTypes.Arity CoreSyn.AltCon
     CoreSyn.CoreAlt CoreSyn.CoreArg CoreSyn.CoreBind CoreSyn.CoreBndr
     CoreSyn.CoreExpr CoreSyn.Expr CoreSyn.Tickish DataCon.DataCon DynFlags.DynFlags
     FastString.FastString GHC.Base.String GHC.Num.Int TyCon.TyCon Unique.Unique
     Var.Id Var.TyVar Var.Var VarEnv.InScopeSet VarEnv.RnEnv2
*)
