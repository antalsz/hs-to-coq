(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Bits.
Require GHC.Num.
Require GHC.Prim.
Import Data.Bits.Notations.
(* Import GHC.Prim.Notations. *)

(* No type declarations to convert. *)
(* Converted value declarations: *)

Parameter shiftLL : GHC.Num.Word -> GHC.Num.Int -> GHC.Num.Word.

Parameter shiftRL : GHC.Num.Word -> GHC.Num.Int -> GHC.Num.Word.

Parameter highestBitMask : GHC.Num.Word -> GHC.Num.Word.

Parameter wordSize : GHC.Num.Int.

(* Unbound variables:
     Data.Bits.finiteBitSize Data.Bits.op_zizbzi__ Data.Bits.xor GHC.Num.Int
     GHC.Num.Word GHC.Prim.op_uncheckedShiftLzh__ GHC.Prim.op_uncheckedShiftRLzh__
     GHC.Types.op_Izh__ GHC.Types.op_Wzh__
*)
