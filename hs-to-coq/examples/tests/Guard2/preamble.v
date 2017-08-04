Axiom patternFailure : forall {a}, a.

Require Export Coq.Lists.List.
Axiom Char     : Type.
Definition String := list Char.

Require Coq.Strings.String.
Require Coq.Strings.Ascii.

Bind Scope string_scope with String.string.
Bind Scope char_scope   with Ascii.ascii.

Axiom hs_char__ : Ascii.ascii -> Char.
Notation "'&#' c" := (hs_char__ c) (at level 1, format "'&#' c").

Fixpoint hs_string__ (s : String.string) : String :=
  match s with
  | String.EmptyString => nil
  | String.String c s  => &#c :: hs_string__ s
  end.
Notation "'&' s" := (hs_string__ s) (at level 1, format "'&' s").
Axiom error : forall {A : Type}, String -> A.

Set Implicit Arguments.
Generalizable All Variables.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
