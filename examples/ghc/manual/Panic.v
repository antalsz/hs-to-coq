Require Import  GHC.Base.
Require Import GHC.Num.
Require Import GHC.Err.

Definition head {a} `{Default a} (xs : list a) : a :=
  match xs with
  | (x::_) => x
  | _      => default
  end.

Parameter noString : forall {a}, a -> String.
Parameter someSDoc : String.


Parameter panicStr : forall {a} `{Default a}, String -> String -> a.
Parameter panic : forall {a} `{Default a}, String -> a.
Parameter sorry : forall {a} `{Default a}, String -> a.
Parameter pgmError : forall {a} `{Default a}, String -> a.
Parameter warnPprTrace :  forall {a}, bool -> String -> Integer -> String -> a -> a.
Parameter assertPanic :  forall {a} `{Default a}, String -> Integer -> a.
Parameter assertPprPanic : forall {a} `{Default a}, String -> Integer -> String -> String -> a.
