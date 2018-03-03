From mathcomp Require Import ssrbool ssreflect.

Ltac expand_pairs :=
  match goal with
    |- context[let (_,_) := ?e in _] =>
    rewrite (surjective_pairing e)
  end.

Ltac destruct_match :=
  match goal with
  | [ H :context[match ?a with _ => _ end] |- _] =>
    let Heq := fresh "Heq" in
    destruct a eqn:Heq=>//
  | [ |- context[match ?a with _ => _ end]] =>
    let Heq := fresh "Heq" in
    destruct a eqn:Heq=>//
  end.
