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

Require GHC.Num.
Require Var.

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

Axiom tryEtaReduce : forall {A : Type}, A.

Axiom exprIsBottom : forall {A : Type}, A.

Axiom bindNonRec : forall {A : Type}, A.

Axiom mkCast : forall {A : Type}, A.

Axiom coreAltsType : forall {A : Type}, A.

Axiom coreAltType : forall {A : Type}, A.

Axiom exprType : forall {A : Type}, A.

Axiom applyTypeToArgs : forall {A : Type}, A.

Axiom mkTickNoHNF : forall {A : Type}, A.

Axiom combineIdenticalAlts : forall {A : Type}, A.

Axiom mkTicks : forall {A : Type}, A.

Axiom tickHNFArgs : forall {A : Type}, A.

Axiom mkTick : forall {A : Type}, A.

Axiom isSaturatedConApp : forall {A : Type}, A.

Axiom stripTicksTop : forall {A : Type}, A.

Axiom cheapEqExpr : forall {A : Type}, A.

Axiom cheapEqExpr' : forall {A : Type}, A.

Axiom exprOkForSideEffects : forall {A : Type}, A.

Axiom needsCaseBinding : forall {A : Type}, A.

Axiom exprOkForSpeculation : forall {A : Type}, A.

Axiom app_ok : forall {A : Type}, A.

Axiom expr_ok : forall {A : Type}, A.

Axiom stripTicksTopE : forall {A : Type}, A.

Axiom stripTicksTopT : forall {A : Type}, A.

Axiom stripTicksE : forall {A : Type}, A.

Axiom stripTicksT : forall {A : Type}, A.

Axiom mkAltExpr : forall {A : Type}, A.

Axiom filterAlts : forall {A : Type}, A.

Axiom findDefault : forall {A : Type}, A.

Axiom addDefault : forall {A : Type}, A.

Axiom isDefaultAlt : forall {A : Type}, A.

Axiom findAlt : forall {A : Type}, A.

Axiom refineDefaultAlt : forall {A : Type}, A.

Axiom mergeAlts : forall {A : Type}, A.

Axiom trimConArgs : forall {A : Type}, A.

Axiom exprIsTrivial : forall {A : Type}, A.

Axiom getIdFromTrivialExpr : forall {A : Type}, A.

Axiom getIdFromTrivialExpr_maybe : forall {A : Type}, A.

Axiom exprIsDupable : forall {A : Type}, A.

Axiom dupAppSize : forall {A : Type}, A.

Axiom exprIsWorkFree : forall {A : Type}, A.

Axiom exprIsCheap : forall {A : Type}, A.

Axiom exprIsExpandable : forall {A : Type}, A.

Axiom exprIsCheap' : forall {A : Type}, A.

Axiom isCheapApp : forall {A : Type}, A.

Axiom isExpandableApp : forall {A : Type}, A.

Axiom altsAreExhaustive : forall {A : Type}, A.

Axiom isDivOp : forall {A : Type}, A.

Axiom exprIsHNF : forall {A : Type}, A.

Axiom exprIsConLike : forall {A : Type}, A.

Axiom exprIsHNFlike : forall {A : Type}, A.

Axiom dataConRepInstPat : forall {A : Type}, A.

Axiom dataConRepFSInstPat : forall {A : Type}, A.

Axiom dataConInstPat : forall {A : Type}, A.

Axiom exprIsBig : forall {A : Type}, A.

Axiom eqExpr : forall {A : Type}, A.

Axiom diffUnfold : forall {A : Type}, A.

Axiom diffIdInfo : forall {A : Type}, A.

Axiom diffBinds : forall {A : Type}, A.

Axiom diffExpr : forall {A : Type}, A.

Axiom eqTickish : forall {A : Type}, A.

Axiom locBind : forall {A : Type}, A.

Axiom rhsIsStatic : forall {A : Type}, A.

Axiom isEmptyTy : forall {A : Type}, A.

(* Unbound variables:
     bool GHC.Num.Int Var.Id
*)
