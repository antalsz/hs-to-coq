From mathcomp Require Import ssrnat seq.
Require Import Coq.Strings.String.

Definition list_pure {a : Type} (x : a) : seq a :=
  [::x].
Definition list_bind {a b : Type} (xs : seq a) (f : a -> seq b) : seq b :=
  List.flat_map f xs.
Definition list_then {a b : Type} (xs : seq a) (ys : seq b) : seq b :=
  list_bind xs (fun _ => ys).
Definition list_guard (b : bool) : seq unit :=
  if b then list_pure tt else [::].
Definition list_fail {a : Type} (s : string) : seq a :=
  [::].

Notation pure  := list_pure.
Infix ">>="    := list_bind (left associativity, at level 90).
Infix ">>"     := list_then (left associativity, at level 90).
Notation guard := list_guard.
Notation fail  := list_fail.

Notation even := Nat.even.
