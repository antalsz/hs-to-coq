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
(* Converted value declarations: *)

Definition delete {a} `{GHC.Enum.Enum a} : a -> EnumSet a -> EnumSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, Mk_EnumSet s =>
        Mk_EnumSet (Data.IntSet.Internal.delete (GHC.Enum.fromEnum x) s)
    end.

Definition empty {a} : EnumSet a :=
  Mk_EnumSet Data.IntSet.Internal.empty.

Definition fromList {a} `{GHC.Enum.Enum a} : list a -> EnumSet a :=
  Mk_EnumSet GHC.Base.∘
  (Data.IntSet.Internal.fromList GHC.Base.∘ GHC.Base.map GHC.Enum.fromEnum).

Definition insert {a} `{GHC.Enum.Enum a} : a -> EnumSet a -> EnumSet a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, Mk_EnumSet s =>
        Mk_EnumSet (Data.IntSet.Internal.insert (GHC.Enum.fromEnum x) s)
    end.

Definition member {a} `{GHC.Enum.Enum a} : a -> EnumSet a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | x, Mk_EnumSet s => Data.IntSet.Internal.member (GHC.Enum.fromEnum x) s
    end.

Definition toList {a} `{GHC.Enum.Enum a} : EnumSet a -> list a :=
  fun arg_0__ =>
    let 'Mk_EnumSet s := arg_0__ in
    GHC.Base.map GHC.Enum.toEnum (Data.IntSet.Internal.toList s).

(* External variables:
     Type bool list Data.IntSet.Internal.IntSet Data.IntSet.Internal.delete
     Data.IntSet.Internal.empty Data.IntSet.Internal.fromList
     Data.IntSet.Internal.insert Data.IntSet.Internal.member
     Data.IntSet.Internal.toList GHC.Base.map GHC.Base.op_z2218U__ GHC.Enum.Enum
     GHC.Enum.fromEnum GHC.Enum.toEnum
*)
