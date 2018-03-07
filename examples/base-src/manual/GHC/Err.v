Require Import GHC.Base.
Require Import GHC.Num.

Class Default (a :Type) := {
  default : a
}.

Instance default_num {a} `{ Num a} : Default a := { default := #0 }.
Instance default_bool : Default bool := { default := false }.
Instance default_monoid {a} `{ Monoid a } : Default a :=
  { default := mempty }.
Instance default_applicative {a}{f} `{Default a} `{Applicative f}
  : Default (f a ) := { default := pure default }.


Instance default_arr {a}{b} `{Default b} : Default (a -> b) := { default := fun x => default }.
Instance default_option {a} : Default (option a) := { default := None }.
Instance default_list {a} : Default (list a) := { default := nil } .

Definition error {a} `{Default a} : String -> a :=
  fun s => default.
Opaque error.
Definition errorWithoutStackTrace {a} `{Default a} :
  String -> a := error.
