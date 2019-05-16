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

Definition warnPprTrace {a} (b:bool) (msg : String) (i : Integer) (msg2: String) (x: a) : a
  := if b then @pgmError a (Build_Default a x) msg else x.

Parameter assertPanic :  forall {a} `{Default a}, String -> Integer -> a.
Parameter assertPprPanic : forall {a} `{Default a}, String -> Integer -> String -> String -> a.

(* TODO: Where should this live?  I currently need it pre-theories. —ASZ *)
Inductive panicked {a} : a -> Prop :=
| PlainPanic `{Default a} {s}     : panicked (panic s)
| StrPanic   `{Default a} {s} {d} : panicked (panicStr s d).
