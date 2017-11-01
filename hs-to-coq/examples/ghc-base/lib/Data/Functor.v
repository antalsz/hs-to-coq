(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require GHC.Base.

(* Converted declarations: *)

Definition op_zdzg__ {f} {a} {b} `{GHC.Base.Functor f} : f a -> b -> f b :=
  GHC.Base.flip GHC.Base.op_zlzd__.

Infix "$>" := (op_zdzg__) (at level 99).

Notation "'_$>_'" := (op_zdzg__).

Definition op_zlzdzg__ {f} {a} {b} `{GHC.Base.Functor f} : (a -> b) -> f a -> f
                                                           b :=
  GHC.Base.fmap.

Infix "<$>" := (op_zlzdzg__) (at level 99).

Notation "'_<$>_'" := (op_zlzdzg__).

Definition void {f} {a} `{GHC.Base.Functor f} : f a -> f unit :=
  fun arg_0__ => match arg_0__ with | x => GHC.Base.op_zlzd__ tt x end.

(* Unbound variables:
     GHC.Base.Functor GHC.Base.flip GHC.Base.fmap GHC.Base.op_zlzd__ tt unit
*)
