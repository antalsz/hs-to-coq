(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Nat.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.Char.
Require GHC.Err.
Require GHC.Num.
Require GHC.Real.
Require UniqFM.

(* Converted type declarations: *)

Inductive Literal : Type
  := | MachChar : GHC.Char.Char -> Literal
  |  MachStr : GHC.Base.String -> Literal
  |  MachNullAddr : Literal
  |  MachInt : GHC.Num.Integer -> Literal
  |  MachInt64 : GHC.Num.Integer -> Literal
  |  MachWord : GHC.Num.Integer -> Literal
  |  MachWord64 : GHC.Num.Integer -> Literal
  |  MachFloat : GHC.Real.Rational -> Literal
  |  MachDouble : GHC.Real.Rational -> Literal
  |  MachLabel
   : FastString.FastString -> (option nat) -> BasicTypes.FunctionOrData -> Literal
  |  LitInteger : GHC.Num.Integer -> AxiomatizedTypes.Type_ -> Literal.

Instance Default__Literal : GHC.Err.Default Literal :=
  GHC.Err.Build_Default _ MachNullAddr.

(* Converted value declarations: *)

Axiom word2IntLit : DynFlags.DynFlags -> Literal -> Literal.

(* Skipping definition `Literal.pprLiteral' *)

(* Skipping definition `Literal.pprIntegerVal' *)

Axiom nullAddrLit : Literal.

(* Skipping definition `Literal.narrow8WordLit' *)

(* Skipping definition `Literal.narrow8IntLit' *)

(* Skipping definition `Literal.narrow32WordLit' *)

(* Skipping definition `Literal.narrow32IntLit' *)

(* Skipping definition `Literal.narrow16WordLit' *)

(* Skipping definition `Literal.narrow16IntLit' *)

(* Skipping definition `Literal.mkMachWordWrap' *)

(* Skipping definition `Literal.mkMachWord64Wrap' *)

(* Skipping definition `Literal.mkMachWord64' *)

(* Skipping definition `Literal.mkMachWord' *)

Axiom mkMachString : GHC.Base.String -> Literal.

(* Skipping definition `Literal.mkMachIntWrap' *)

(* Skipping definition `Literal.mkMachInt64Wrap' *)

(* Skipping definition `Literal.mkMachInt64' *)

(* Skipping definition `Literal.mkMachInt' *)

Axiom mkMachFloat : GHC.Real.Rational -> Literal.

Axiom mkMachDouble : GHC.Real.Rational -> Literal.

Axiom mkMachChar : GHC.Char.Char -> Literal.

Axiom mkLitInteger : GHC.Num.Integer -> AxiomatizedTypes.Type_ -> Literal.

(* Skipping definition `Literal.mapLitValue' *)

Axiom literalType : Literal -> AxiomatizedTypes.Type_.

Axiom litValue : Literal -> GHC.Num.Integer.

Axiom litTag : Literal -> nat.

Axiom litIsTrivial : Literal -> bool.

Axiom litIsLifted : Literal -> bool.

Axiom litIsDupable : DynFlags.DynFlags -> Literal -> bool.

Axiom litFitsInChar : Literal -> bool.

Axiom isZeroLit : Literal -> bool.

Axiom isLitValue_maybe : Literal -> option GHC.Num.Integer.

Axiom isLitValue : Literal -> bool.

Axiom int2WordLit : DynFlags.DynFlags -> Literal -> Literal.

Axiom int2FloatLit : Literal -> Literal.

Axiom int2DoubleLit : Literal -> Literal.

Axiom int2CharLit : Literal -> Literal.

Axiom inWordRange : DynFlags.DynFlags -> GHC.Num.Integer -> bool.

(* Skipping definition `Literal.inWord64Range' *)

Axiom inIntRange : DynFlags.DynFlags -> GHC.Num.Integer -> bool.

(* Skipping definition `Literal.inInt64Range' *)

Axiom inCharRange : GHC.Char.Char -> bool.

(* Skipping definition `Literal.float2IntLit' *)

Axiom float2DoubleLit : Literal -> Literal.

(* Skipping definition `Literal.double2IntLit' *)

Axiom double2FloatLit : Literal -> Literal.

Axiom cmpLit : Literal -> Literal -> comparison.

Axiom char2IntLit : Literal -> Literal.

Axiom absent_lits : UniqFM.UniqFM Literal.

(* Skipping definition `Literal.absentLiteralOf' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Literal.Data__Literal' *)

Instance Eq___Literal : GHC.Base.Eq_ Literal.
Proof.
Admitted.

Instance Ord__Literal : GHC.Base.Ord Literal.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `Literal.Outputable__Literal' *)

(* Skipping all instances of class `Binary.Binary', including
   `Literal.Binary__Literal' *)

(* External variables:
     bool comparison nat option AxiomatizedTypes.Type_ BasicTypes.FunctionOrData
     DynFlags.DynFlags FastString.FastString GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.String GHC.Char.Char GHC.Err.Build_Default GHC.Err.Default
     GHC.Num.Integer GHC.Real.Rational UniqFM.UniqFM
*)
