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
Require GHC.Err.
Require Data.Either.
Require GHC.DeferredFix.
Require Utils.Containers.Internal.PtrEquality.

Require Coq.Bool.Sumbool.

Require Import mathcomp.ssreflect.ssreflect.

Extraction Blacklist Prelude.
Extraction Language Haskell.

Set Warnings "-extraction-reserved-identifier".

(*
Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False" ].
Extract Inductive comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
Extract Inductive list => "[]" ["[]" "(:)"].
Extract Inductive option => "Prelude.Maybe" [ "Prelude.Just" "Prelude.Nothing"].
Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive Either.Either => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].
*)

Require Import Data.Set.Internal.

Require Import Coq.extraction.ExtrHaskellBasic.
Require Import Coq.extraction.ExtrHaskellZInt.
Require Import Coq.extraction.ExtrHaskellNatInt.
Require Import Coq.extraction.ExtrHaskellString. 

Extract Constant Datatypes.id => "Prelude.id".
Extract Constant Bool.Sumbool.sumbool_of_bool => "Prelude.id".
Extract Inductive comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].
Extract Inductive Either.Either => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].

Extract Constant PtrEquality.ptrEq => "\ x y -> Prelude.False".
Extract Constant PtrEquality.hetPtrEq => "\ x y -> Prelude.False".
Extract Constant Base.errorWithoutStackTrace => "errorWithoutStackTrace".
Extract Constant GHC.Err.patternFailure => "(\d -> Prelude.error ""patternFailure"")".
Extract Constant DeferredFix.deferredFix => "(\d f -> let r = f r in r)".
Extract Constant DeferredFix.deferredFix2 => "(\d f -> let r = f r in r)".
Extract Constant DeferredFix.deferredFix3 => "(\d f -> let r = f r in r)".

Recursive Extraction Library Internal.

Extraction Blacklist Internal.

Require Import Data.IntSet.Internal.
Recursive Extraction Library Internal.





