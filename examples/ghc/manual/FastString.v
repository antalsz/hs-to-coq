(* This file is a handwritten stub of the FastString module, just using Coq Strings
   as FastStrings. For right now, just accumulate the interface that we need
   from other files. *)

Require Import GHC.Base.
Require Import Panic.

Definition FastString := String.

Instance instance_FastString_Eq_ : Eq_ FastString := {}.
Admitted.

Instance instance_FastString_Ord : Ord FastString := {}.
Admitted.

Instance instance_FastString_Default : Panic.Default FastString := {}.
Admitted.

Definition fsLit (s : String) : FastString := s.

Parameter uniqueOfFS : FastString -> GHC.Num.Int.

Parameter unpackFS : FastString -> GHC.Base.String.

Definition LitString := String.
Definition sLit (s : String) : LitString := s.

Definition mkFastString (s : String) : FastString := s.