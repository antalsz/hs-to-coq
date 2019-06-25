(* This file is a handwritten stub of the FastString module, just using Coq Strings
   as FastStrings. For right now, just accumulate the interface that we need
   from other files. *)

Require GHC.List.
Require Import GHC.Base.
Require Import GHC.Err.
Require Import Coq.Numbers.BinNums.

Definition FastString := String.

Instance instance_FastString_Eq_ : Eq_ FastString := {}.
Admitted.

Instance instance_FastString_Ord : Ord FastString := {}.
Admitted.

Instance instance_FastString_Default : GHC.Err.Default FastString := {}.
Admitted.

Definition fsLit (s : String) : FastString := s.

Definition concatFS : list FastString -> FastString := GHC.List.concat.

Axiom uniqueOfFS : FastString -> BinNums.N.

Axiom unpackFS : FastString -> GHC.Base.String.

Axiom appendFS : FastString -> FastString -> FastString.

Definition LitString := String.
Definition sLit (s : String) : LitString := s.

Definition mkFastString (s : String) : FastString := s.

Axiom hashByteString : FastString -> nat.
Axiom fastStringToByteString : FastString -> GHC.Base.String.

Axiom nullFS : FastString -> bool.