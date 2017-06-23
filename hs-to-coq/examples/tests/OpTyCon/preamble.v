Require Export Coq.Lists.List.

Parameter Int : Type.
Notation "[->]"  := (fun x y => x -> y).
Notation "[,]"  := (fun x y => (x,y)).

Set Implicit Arguments.
Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
