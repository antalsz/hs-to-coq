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

Require GHC.Base.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition op_zlzdzg__ {f} {a} {b} `{GHC.Base.Functor f}
   : (a -> b) -> f a -> f b :=
  GHC.Base.fmap.

Notation "'_<$>_'" := (op_zlzdzg__).

Infix "<$>" := (_<$>_) (at level 99).

Definition op_zlzazg__ {f} {a} {b} `{GHC.Base.Functor f}
   : f a -> (a -> b) -> f b :=
  fun as_ f => f <$> as_.

Notation "'_<&>_'" := (op_zlzazg__).

Infix "<&>" := (_<&>_) (at level 99).

Definition op_zdzg__ {f} {a} {b} `{GHC.Base.Functor f} : f a -> b -> f b :=
  GHC.Base.flip _GHC.Base.<$_.

Notation "'_$>_'" := (op_zdzg__).

Infix "$>" := (_$>_) (at level 99).

Definition void {f} {a} `{GHC.Base.Functor f} : f a -> f unit :=
  fun x => tt GHC.Base.<$ x.

Module Notations.
Notation "'_Data.Functor.<$>_'" := (op_zlzdzg__).
Infix "Data.Functor.<$>" := (_<$>_) (at level 99).
Notation "'_Data.Functor.<&>_'" := (op_zlzazg__).
Infix "Data.Functor.<&>" := (_<&>_) (at level 99).
Notation "'_Data.Functor.$>_'" := (op_zdzg__).
Infix "Data.Functor.$>" := (_$>_) (at level 99).
End Notations.

(* External variables:
     tt unit GHC.Base.Functor GHC.Base.flip GHC.Base.fmap GHC.Base.op_zlzd__
*)
