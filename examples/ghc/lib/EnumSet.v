(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.IntSet.Internal.
Require GHC.Base.
Require GHC.Enum.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive EnumSet (a : Type) : Type
  := Mk_EnumSet : Data.IntSet.Internal.IntSet -> EnumSet a.

Arguments Mk_EnumSet {_} _.
(* Midamble *)

Require Coq.ZArith.BinInt.
Require GHC.Enum.

Definition toEnumN  {a} `{GHC.Enum.Enum a} n : a := GHC.Enum.toEnum (Coq.ZArith.BinInt.Z.of_N n).
Definition fromEnumN {a} `{GHC.Enum.Enum a} (e : a) := Coq.ZArith.BinInt.Z.to_N (GHC.Enum.fromEnum e).

(* Converted value declarations: *)

Definition toList {a} `{GHC.Enum.Enum a} : EnumSet a -> list a :=
  fun '(Mk_EnumSet s) => GHC.Base.map toEnumN (Data.IntSet.Internal.toList s).

Definition member {a} `{GHC.Enum.Enum a} : a -> EnumSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, Mk_EnumSet s => Data.IntSet.Internal.member (fromEnumN x) s
    end.

Definition insert {a} `{GHC.Enum.Enum a} : a -> EnumSet a -> EnumSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, Mk_EnumSet s => Mk_EnumSet (Data.IntSet.Internal.insert (fromEnumN x) s)
    end.

Definition fromList {a} `{GHC.Enum.Enum a} : list a -> EnumSet a :=
  Mk_EnumSet GHC.Base.∘
  (Data.IntSet.Internal.fromList GHC.Base.∘ GHC.Base.map fromEnumN).

Definition empty {a} : EnumSet a :=
  Mk_EnumSet Data.IntSet.Internal.empty.

Definition delete {a} `{GHC.Enum.Enum a} : a -> EnumSet a -> EnumSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, Mk_EnumSet s => Mk_EnumSet (Data.IntSet.Internal.delete (fromEnumN x) s)
    end.

(* External variables:
     Type bool fromEnumN list toEnumN Data.IntSet.Internal.IntSet
     Data.IntSet.Internal.delete Data.IntSet.Internal.empty
     Data.IntSet.Internal.fromList Data.IntSet.Internal.insert
     Data.IntSet.Internal.member Data.IntSet.Internal.toList GHC.Base.map
     GHC.Base.op_z2218U__ GHC.Enum.Enum
*)
