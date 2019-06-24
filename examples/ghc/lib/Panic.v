(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require GHC.Err.
Require GHC.Num.

(* Converted type declarations: *)

Inductive GhcException : Type
  := | Signal : GHC.Num.Int -> GhcException
  |  UsageError : GHC.Base.String -> GhcException
  |  CmdLineError : GHC.Base.String -> GhcException
  |  Panic : GHC.Base.String -> GhcException
  |  PprPanic : GHC.Base.String -> GHC.Base.String -> GhcException
  |  Sorry : GHC.Base.String -> GhcException
  |  PprSorry : GHC.Base.String -> GHC.Base.String -> GhcException
  |  InstallationError : GHC.Base.String -> GhcException
  |  ProgramError : GHC.Base.String -> GhcException
  |  PprProgramError : GHC.Base.String -> GHC.Base.String -> GhcException.

(* Converted value declarations: *)

Axiom throwGhcException : forall {a} `{GHC.Err.Default a}, GhcException -> a.

Axiom sorryDoc : forall {a} `{GHC.Err.Default a},
                 GHC.Base.String -> GHC.Base.String -> a.

Axiom sorry : forall {a} `{GHC.Err.Default a}, GHC.Base.String -> a.

Axiom short_usage : GHC.Base.String.

Axiom progName : GHC.Base.String.

Axiom pgmErrorDoc : forall {a} `{GHC.Err.Default a},
                    GHC.Base.String -> GHC.Base.String -> a.

Axiom pgmError : forall {a} `{GHC.Err.Default a}, GHC.Base.String -> a.

Axiom panicDoc : forall {a} `{GHC.Err.Default a},
                 GHC.Base.String -> GHC.Base.String -> a.

Axiom panic : forall {a} `{GHC.Err.Default a}, GHC.Base.String -> a.

Axiom assertPanic : forall {a} `{GHC.Err.Default a},
                    GHC.Base.String -> GHC.Num.Int -> a.

(* Skipping all instances of class `GHC.Show.Show', including
   `Panic.Show__GhcException' *)

(* Skipping all instances of class `GHC.Exception.Exception', including
   `Panic.Exception__GhcException' *)

Axiom panicStr : forall {a} `{GHC.Err.Default a},
                 GHC.Base.String -> GHC.Base.String -> a.

Inductive panicked {a} : a -> Prop
  := | PlainPanic `{GHC.Err.Default a} {s} : panicked (panic s)
  |  StrPanic `{GHC.Err.Default a} {s} {d} : panicked (panicStr s d).

Axiom warnPprTrace : forall {a} `{GHC.Err.Default a},
                     bool -> GHC.Base.String -> GHC.Num.Integer -> GHC.Base.String -> a -> a.

Axiom assertPprPanic : forall {a} `{GHC.Err.Default a},
                       GHC.Base.String -> GHC.Num.Integer -> GHC.Base.String -> GHC.Base.String -> a.

Axiom noString : forall {a}, a -> GHC.Base.String.

Axiom someSDoc : GHC.Base.String.

(* External variables:
     Prop bool GHC.Base.String GHC.Err.Default GHC.Num.Int GHC.Num.Integer
*)
