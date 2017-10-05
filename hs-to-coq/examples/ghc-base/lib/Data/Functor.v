(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Set Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)


(* Converted imports: *)

Require GHC.Base.
Require GHC.BaseGen.

(* Converted declarations: *)

Definition op_zdzg__ {f} {a} {b} `{GHC.BaseGen.Functor f} : f a -> b -> f b :=
  GHC.BaseGen.flip GHC.BaseGen.op_zlzd__.

Infix "$>" := (op_zdzg__) (at level 99).

Notation "'_$>_'" := (op_zdzg__).

Definition op_zlzdzg__ {f} {a} {b} `{GHC.BaseGen.Functor f} : (a -> b) -> f
                                                              a -> f b :=
  GHC.BaseGen.fmap.

Infix "<$>" := (op_zlzdzg__) (at level 99).

Notation "'_<$>_'" := (op_zlzdzg__).

Definition void {f} {a} `{GHC.BaseGen.Functor f} : f a -> f unit :=
  fun arg_0__ => match arg_0__ with | x => GHC.BaseGen.op_zlzd__ tt x end.

(* Unbound variables:
     GHC.BaseGen.Functor GHC.BaseGen.flip GHC.BaseGen.fmap GHC.BaseGen.op_zlzd__ tt
     unit
*)
