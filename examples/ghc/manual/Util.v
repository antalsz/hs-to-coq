Require Import GHC.Base.

Parameter debugIsOn : bool.

(*
thenCmp EQ       ordering = ordering
thenCmp ordering _        = ordering
*)

Definition thenCmp o1 o2 : comparison :=
  match o1 with
  | Eq => o2
  | _  => o1
  end.
