(* This file is a handwritten stub of the FastString module, just using Coq Strings
   as FastStrings. For right now, just accumulate the interface that we need
   from other files. *)

Require GHC.List.
Require Import GHC.Base.
Require Import GHC.Err.

Definition FastString := String.

Instance instance_FastString_Eq_ : Eq_ FastString := {}.
Admitted.

Instance instance_FastString_Ord : Ord FastString := {}.
Admitted.

Instance instance_FastString_Default : GHC.Err.Default FastString := {}.
Admitted.

Definition fsLit (s : String) : FastString := s.

Definition concatFS : list FastString -> FastString := GHC.List.concat.

Parameter uniqueOfFS : FastString -> GHC.Num.Int.

Parameter unpackFS : FastString -> GHC.Base.String.

Parameter appendFS : FastString -> FastString -> FastString.

Definition LitString := String.
Definition sLit (s : String) : LitString := s.

Definition mkFastString (s : String) : FastString := s.

Parameter hashByteString : FastString -> GHC.Num.Int.
Parameter fastStringToByteString : FastString -> GHC.Base.String.
