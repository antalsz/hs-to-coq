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
Require Data.Either.
Require Utils.Containers.Internal.PtrEquality.

Require Import mathcomp.ssreflect.ssreflect.

Extraction Blacklist Prelude.
Extraction Language Haskell.

Set Warnings "-extraction-reserved-identifier".

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False" ].
Extract Inductive comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
Extract Inductive list => "[]" ["[]" "(:)"].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing"].
Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive Either.Either => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].

Require Import Data.Set.Internal.

Extract Constant patternFailure => "GHC.Base.undefined".
Extract Constant PtrEquality.ptrEq => "\ x y -> Prelude.False".
Extract Constant PtrEquality.hetPtrEq => "\ x y -> Prelude.False".
Extract Constant Base.errorWithoutStackTrace => "errorWithoutStackTrace".
Extract Constant unsafeFix => "(\f -> let r = f r in r)".

(*
-- I'm trying to convert Z to Int, but this does not work. 
Require Import GHC.Num.
Extract Constant Num.Int => "Prelude.Int".
Extract Constant Num.Num_Int__ => "Prelude.undefined".
Require GHC.Char.
Extract Constant Char.Char => "Prelude.Char".
Extract Constant Char.hs_char__ => "Prelude.undefined".
Extract Constant Char.chr => "Prelude.undefined".
Extract Constant Char.ord => "Prelude.undefined".
Require Import GHC.Base.
Extract Constant Base.Eq_Int___ => "Prelude.undefined".
Extract Constant Base.Ord_Int___ => "Prelude.undefined".
Extract Constant Base.Eq_Char___ => "Prelude.undefined".
Extract Constant Base.Ord_Char___ => "Prelude.undefined". *)

Recursive Extraction Library Internal.

Extraction Blacklist Internal.

Require Import Data.IntSet.Internal.
Recursive Extraction Library Internal.
