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
Require CoreSyn.
Require DataCon.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require Unique.
Require Var.
Require VarEnv.

(* Converted type declarations: *)

Definition CheapAppFun :=
  (Var.Id -> GHC.Num.Int -> bool)%type.
(* Midamble *)

(* Record selector *)
Require Import Pair.

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

Axiom tryEtaReduce : list Core.Var -> CoreSyn.CoreExpr -> option
                     CoreSyn.CoreExpr.

Axiom exprIsBottom : CoreSyn.CoreExpr -> bool.

Axiom bindNonRec
        : Var.Id -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

(* mkCast skipped *)

Axiom coreAltsType : list CoreSyn.CoreAlt -> Core.Type_.

(* coreAltType skipped *)

(* exprType skipped *)

(* applyTypeToArgs skipped *)

Axiom mkTickNoHNF : CoreSyn.Tickish
                    Var.Id -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom combineIdenticalAlts : list CoreSyn.AltCon -> list
                             CoreSyn.CoreAlt -> (bool * list CoreSyn.AltCon * list CoreSyn.CoreAlt)%type.

Axiom mkTicks : list (CoreSyn.Tickish
                     Var.Id) -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom tickHNFArgs : CoreSyn.Tickish
                    Var.Id -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom mkTick : CoreSyn.Tickish Var.Id -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr.

Axiom isSaturatedConApp : CoreSyn.CoreExpr -> bool.

Axiom stripTicksTop : forall {b},
                        (CoreSyn.Tickish Var.Id -> bool) -> CoreSyn.Expr b -> (list (CoreSyn.Tickish
                                                                                    Var.Id) * CoreSyn.Expr b)%type.

Axiom cheapEqExpr : forall {b}, CoreSyn.Expr b -> CoreSyn.Expr b -> bool.

Axiom cheapEqExpr' : forall {b},
                       (CoreSyn.Tickish Var.Id -> bool) -> CoreSyn.Expr b -> CoreSyn.Expr b -> bool.

Axiom exprOkForSideEffects : forall {b}, CoreSyn.Expr b -> bool.

Axiom needsCaseBinding : Core.Type_ -> CoreSyn.CoreExpr -> bool.

Axiom exprOkForSpeculation : forall {b}, CoreSyn.Expr b -> bool.

Axiom app_ok : forall {b},
                 (unit -> bool) -> Var.Id -> list (CoreSyn.Expr b) -> bool.

Axiom expr_ok : forall {b}, (unit -> bool) -> CoreSyn.Expr b -> bool.

Axiom stripTicksTopE : forall {b},
                         (CoreSyn.Tickish Var.Id -> bool) -> CoreSyn.Expr b -> CoreSyn.Expr b.

Axiom stripTicksTopT : forall {b},
                         (CoreSyn.Tickish Var.Id -> bool) -> CoreSyn.Expr b -> list (CoreSyn.Tickish
                                                                                    Var.Id).

Axiom stripTicksE : forall {b},
                      (CoreSyn.Tickish Var.Id -> bool) -> CoreSyn.Expr b -> CoreSyn.Expr b.

Axiom stripTicksT : forall {b},
                      (CoreSyn.Tickish Var.Id -> bool) -> CoreSyn.Expr b -> list (CoreSyn.Tickish
                                                                                 Var.Id).

Axiom mkAltExpr : CoreSyn.AltCon -> list CoreSyn.CoreBndr -> list
                  Core.Type_ -> CoreSyn.CoreExpr.

Axiom filterAlts : forall {a},
                     Core.TyCon -> list Core.Type_ -> list CoreSyn.AltCon -> list (CoreSyn.AltCon *
                                                                                  list Core.Var * a)%type -> (list
                     CoreSyn.AltCon * list (CoreSyn.AltCon * list Core.Var * a)%type)%type.

Axiom findDefault : forall {a} {b},
                      list (CoreSyn.AltCon * list a * b)%type -> (list (CoreSyn.AltCon * list a *
                                                                       b)%type * option b)%type.

Axiom addDefault : forall {a} {b},
                     list (CoreSyn.AltCon * list a * b)%type -> option b -> list (CoreSyn.AltCon *
                                                                                 list a * b)%type.

Axiom isDefaultAlt : forall {a} {b}, (CoreSyn.AltCon * a * b)%type -> bool.

Axiom findAlt : forall {a} {b},
                  CoreSyn.AltCon -> list (CoreSyn.AltCon * a * b)%type -> option (CoreSyn.AltCon *
                                                                                 a * b)%type.

Axiom refineDefaultAlt : list Unique.Unique -> Core.TyCon -> list
                         Core.Type_ -> list CoreSyn.AltCon -> list CoreSyn.CoreAlt -> (bool * list
                         CoreSyn.CoreAlt)%type.

Axiom mergeAlts : forall {a} {b},
                    list (CoreSyn.AltCon * a * b)%type -> list (CoreSyn.AltCon * a * b)%type -> list
                    (CoreSyn.AltCon * a * b)%type.

Axiom trimConArgs : CoreSyn.AltCon -> list CoreSyn.CoreArg -> list
                    CoreSyn.CoreArg.

Axiom exprIsTrivial : CoreSyn.CoreExpr -> bool.

Axiom getIdFromTrivialExpr : CoreSyn.CoreExpr -> Var.Id.

Axiom getIdFromTrivialExpr_maybe : CoreSyn.CoreExpr -> option Var.Id.

Axiom exprIsDupable : DynFlags.DynFlags -> CoreSyn.CoreExpr -> bool.

Axiom dupAppSize : GHC.Num.Int.

Axiom exprIsWorkFree : CoreSyn.CoreExpr -> bool.

Axiom exprIsCheap : CoreSyn.CoreExpr -> bool.

Axiom exprIsExpandable : CoreSyn.CoreExpr -> bool.

Axiom exprIsCheap' : CheapAppFun -> CoreSyn.CoreExpr -> bool.

Axiom isCheapApp : CheapAppFun.

Axiom isExpandableApp : CheapAppFun.

Axiom altsAreExhaustive : forall {b}, list (CoreSyn.Alt b) -> bool.

Axiom isDivOp : unit -> bool.

Axiom exprIsHNF : CoreSyn.CoreExpr -> bool.

Axiom exprIsConLike : CoreSyn.CoreExpr -> bool.

(* exprIsHNFlike skipped *)

(* dataConRepInstPat skipped *)

Axiom dataConRepFSInstPat : list FastString.FastString -> list
                            Unique.Unique -> DataCon.DataCon -> list Core.Type_ -> (list TyVar * list
                            Var.Id)%type.

(* dataConInstPat skipped *)

Axiom exprIsBig : forall {b}, CoreSyn.Expr b -> bool.

Axiom eqExpr
        : VarEnv.InScopeSet -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr -> bool.

Axiom diffUnfold
        : VarEnv.RnEnv2 -> CoreSyn.Unfolding -> CoreSyn.Unfolding -> list
          Outputable.SDoc.

Axiom diffIdInfo : VarEnv.RnEnv2 -> Core.Var -> Core.Var -> list
                   Outputable.SDoc.

Axiom diffBinds : bool -> VarEnv.RnEnv2 -> list (Core.Var *
                                                CoreSyn.CoreExpr)%type -> list (Core.Var *
                                                                               CoreSyn.CoreExpr)%type -> (list
                  Outputable.SDoc * VarEnv.RnEnv2)%type.

Axiom diffExpr
        : bool -> VarEnv.RnEnv2 -> CoreSyn.CoreExpr -> CoreSyn.CoreExpr -> list
          Outputable.SDoc.

Axiom eqTickish : VarEnv.RnEnv2 -> CoreSyn.Tickish Var.Id -> CoreSyn.Tickish
                  Var.Id -> bool.

Axiom locBind : GHC.Base.String -> Core.Var -> Core.Var -> list
                Outputable.SDoc -> list Outputable.SDoc.

(* rhsIsStatic skipped *)

Axiom isEmptyTy : Core.Type_ -> bool.

(* Unbound variables:
     TyVar bool list op_zt__ option unit Core.TyCon Core.Type_ Core.Var CoreSyn.Alt
     CoreSyn.AltCon CoreSyn.CoreAlt CoreSyn.CoreArg CoreSyn.CoreBndr CoreSyn.CoreExpr
     CoreSyn.Expr CoreSyn.Tickish CoreSyn.Unfolding DataCon.DataCon DynFlags.DynFlags
     FastString.FastString GHC.Base.String GHC.Num.Int Outputable.SDoc Unique.Unique
     Var.Id VarEnv.InScopeSet VarEnv.RnEnv2
*)
