(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.ZArith.BinInt.
Require Data.IntSet.Internal.
Require GHC.Enum.

(* Converted type declarations: *)

Inductive EnumSet (a : Type) : Type
  := | Mk_EnumSet : Data.IntSet.Internal.IntSet -> EnumSet a.

Arguments Mk_EnumSet {_} _.

(* Converted value declarations: *)

Axiom toList : forall {a}, forall `{GHC.Enum.Enum a}, EnumSet a -> list a.

Axiom member : forall {a}, forall `{GHC.Enum.Enum a}, a -> EnumSet a -> bool.

Axiom insert : forall {a},
               forall `{GHC.Enum.Enum a}, a -> EnumSet a -> EnumSet a.

Axiom fromList : forall {a}, forall `{GHC.Enum.Enum a}, list a -> EnumSet a.

Axiom empty : forall {a}, EnumSet a.

Axiom delete : forall {a},
               forall `{GHC.Enum.Enum a}, a -> EnumSet a -> EnumSet a.

Definition fromEnumN {a} `{GHC.Enum.Enum a} (e : a) :=
  Coq.ZArith.BinInt.Z.to_N (GHC.Enum.fromEnum e).

Definition toEnumN {a} `{GHC.Enum.Enum a} n : a :=
  GHC.Enum.toEnum (Coq.ZArith.BinInt.Z.of_N n).

(* External variables:
     Type bool list Coq.ZArith.BinInt.Z.of_N Coq.ZArith.BinInt.Z.to_N
     Data.IntSet.Internal.IntSet GHC.Enum.Enum GHC.Enum.fromEnum GHC.Enum.toEnum
*)
