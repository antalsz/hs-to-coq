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