(* This file is a handwritten stub of the FastString module, just using Coq Strings
   as FastStrings. For right now, just accumulate the interface that we need
   from other files. *)

Require GHC.List.
Require Import GHC.Base.
Require Import GHC.Err.
Require Import Coq.Numbers.BinNums.

Definition FastString := String.
Instance instance_FastString_Eq_ : Eq_ FastString.
eapply Eq_list.
Qed.

Instance instance_FastString_Ord : Ord FastString.
eapply Ord_list.
Qed.

Instance instance_FastString_Default : GHC.Err.Default FastString.
eapply default_list.
Qed.

Definition fsLit (s : String) : FastString := s.

Definition concatFS : list FastString -> FastString := GHC.List.concat.

Axiom uniqueOfFS : FastString -> BinNums.N.

Definition unpackFS (s : FastString) : GHC.Base.String := s.

Definition appendFS : FastString -> FastString -> FastString :=
    fun s1 s2 => GHC.List.concat (s1 :: s2 :: nil).

Definition LitString := String.
Definition sLit (s : String) : LitString := s.

Definition mkFastString (s : String) : FastString := s.

Axiom hashByteString : FastString -> nat.
Axiom fastStringToByteString : FastString -> GHC.Base.String.

Axiom nullFS : FastString -> bool.

(* These commands won't prevent Coq from using 'reflexivity' to solve goals. 
   But they will stop simpl from unfolding the definitions. *)
Global Opaque FastString.
Global Opaque fsLit.
Global Opaque concatFS.
Global Opaque appendFS.
Global Opaque LitString.
Global Opaque sLit.
Global Opaque mkFastString.