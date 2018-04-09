Require Import  GHC.Base.
Require Import GHC.Num.
Require Import GHC.Err.

Parameter head : forall {a} `{Default a}, list a -> a.

Parameter noString : forall {a}, a -> String.
Parameter someSDoc : String.


Parameter panicStr : forall {a} `{Default a}, String -> String -> a.
Parameter panic : forall {a} `{Default a}, String -> a.
Parameter sorry : forall {a} `{Default a}, String -> a.
Parameter pgmError : forall {a} `{Default a}, String -> a.
Parameter warnPprTrace :  forall {a}, bool -> String -> Integer -> String -> a -> a.
Parameter assertPanic :  forall {a} `{Default a}, String -> Integer -> a.
Parameter assertPprPanic : forall {a} `{Default a}, String -> Integer -> String -> String -> a.
