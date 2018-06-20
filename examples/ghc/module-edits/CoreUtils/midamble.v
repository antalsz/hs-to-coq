(* Record selector *)
Require Import Pair.

(* Notation for Alt *)

Definition Alt b := prod (prod Core.AltCon (list b)) (Core.Expr b).
