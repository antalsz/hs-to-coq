Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Base.
Require GHC.Enum.
Require Import Data.Set.Internal.
Require Import mathcomp.ssreflect.ssreflect.

Extraction Blacklist Prelude.
Extraction Blacklist Internal.
Extraction Language Haskell.


Set Warnings "-extraction-reserved-identifier".

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False" ].
Extract Inductive comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
Extract Inductive list => "[]" ["[]" "(:)"].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing"].
Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive Either.Either => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].

Extract Constant patternFailure => "GHC.Base.undefined".
Extract Constant PtrEquality.ptrEq => "\ x y -> Prelude.False".
Extract Constant PtrEquality.hetPtrEq => "\ x y -> Prelude.False".
Extract Constant Base.errorWithoutStackTrace => "errorWithoutStackTrace".
Extract Constant unsafeFix => "(\f -> let r = f r in r)".

Require Import Data.Set.Internal.
Recursive Extraction Library Internal.

Require Import Data.IntSet.Internal.
Recursive Extraction Library Internal.