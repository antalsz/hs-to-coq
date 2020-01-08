Require Export Coq.Lists.List.
Axiom Char     : Type.
Definition String := list Char.

Require Coq.Strings.String.
Require Coq.Strings.Ascii.
Import String.StringSyntax Ascii.AsciiSyntax.

Bind Scope string_scope with String.string.
Bind Scope char_scope   with Ascii.ascii.

Axiom hs_char__ : Ascii.ascii -> Char.

Module GHC.
Module Base.
Fixpoint hs_string__ (s : String.string) : String :=
  match s with
  | String.EmptyString => nil
  | String.String c s  => hs_char__ c :: hs_string__ s
  end.
End Base.
Module Err.
Axiom error : forall {A : Type}, String -> A.
End Err.
End GHC.
