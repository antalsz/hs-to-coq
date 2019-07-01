(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.

(* Converted type declarations: *)

Inductive Width : Type
  := | W8 : Width
  |  W16 : Width
  |  W32 : Width
  |  W64 : Width
  |  W80 : Width
  |  W128 : Width
  |  W256 : Width
  |  W512 : Width.

Definition Length :=
  GHC.Num.Int%type.

Inductive ForeignHint : Type
  := | NoHint : ForeignHint
  |  AddrHint : ForeignHint
  |  SignedHint : ForeignHint.

Inductive CmmCat : Type
  := | GcPtrCat : CmmCat
  |  BitsCat : CmmCat
  |  FloatCat : CmmCat
  |  VecCat : Length -> CmmCat -> CmmCat.

Inductive CmmType : Type := | Mk_CmmType : CmmCat -> Width -> CmmType.

Instance Default__Width : GHC.Err.Default Width := GHC.Err.Build_Default _ W8.

Instance Default__ForeignHint : GHC.Err.Default ForeignHint :=
  GHC.Err.Build_Default _ NoHint.

Instance Default__CmmCat : GHC.Err.Default CmmCat :=
  GHC.Err.Build_Default _ GcPtrCat.

(* Midamble *)

Require Import GHC.Nat.

Instance Default__CmmType : GHC.Err.Default CmmType :=
	 { default := Mk_CmmType GHC.Err.default GHC.Err.default }.

(* Converted value declarations: *)

Axiom wordWidth : DynFlags.DynFlags -> Width.

Axiom widthInLog : Width -> GHC.Num.Int.

Axiom widthInBytes : Width -> GHC.Num.Int.

Axiom widthInBits : Width -> GHC.Num.Int.

Axiom widthFromBytes : GHC.Num.Int -> Width.

Axiom vecLength : CmmType -> Length.

Axiom vec8b16 : CmmType.

Axiom vec8 : CmmType -> CmmType.

Axiom vec4f32 : CmmType.

Axiom vec4b32 : CmmType.

Axiom vec4 : CmmType -> CmmType.

Axiom vec2f64 : CmmType.

Axiom vec2b64 : CmmType.

Axiom vec2 : CmmType -> CmmType.

Axiom vec16b8 : CmmType.

Axiom vec16 : CmmType -> CmmType.

Axiom vec : Length -> CmmType -> CmmType.

Axiom typeWidth : CmmType -> Width.

Axiom mrStr : Width -> FastString.LitString.

Axiom isWord64 : CmmType -> bool.

Axiom isWord32 : CmmType -> bool.

Axiom isVecType : CmmType -> bool.

Axiom isGcPtrType : CmmType -> bool.

Axiom isFloatType : CmmType -> bool.

Axiom isFloat64 : CmmType -> bool.

Axiom isFloat32 : CmmType -> bool.

Axiom halfWordWidth : DynFlags.DynFlags -> Width.

Axiom halfWordMask : DynFlags.DynFlags -> GHC.Num.Integer.

Axiom gcWord : DynFlags.DynFlags -> CmmType.

Axiom f64 : CmmType.

Axiom f32 : CmmType.

Axiom cmmVec : GHC.Num.Int -> CmmType -> CmmType.

Axiom cmmFloat : Width -> CmmType.

Instance Eq___CmmCat : GHC.Base.Eq_ CmmCat := {}.
Proof.
Admitted.

Instance Eq___Width : GHC.Base.Eq_ Width := {}.
Proof.
Admitted.

Axiom cmmEqType : CmmType -> CmmType -> bool.

Axiom cmmEqType_ignoring_ptrhood : CmmType -> CmmType -> bool.

Axiom cmmBits : Width -> CmmType.

Axiom bWord : DynFlags.DynFlags -> CmmType.

Axiom bHalfWord : DynFlags.DynFlags -> CmmType.

Axiom b8 : CmmType.

Axiom b64 : CmmType.

Axiom b512 : CmmType.

Axiom b32 : CmmType.

Axiom b256 : CmmType.

Axiom b16 : CmmType.

Axiom b128 : CmmType.

(* Skipping instance `CmmType.Ord__Width' of class `GHC.Base.Ord' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `CmmType.Show__Width' *)

Instance Eq___ForeignHint : GHC.Base.Eq_ ForeignHint := {}.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `CmmType.Outputable__Width' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CmmType.Outputable__CmmCat' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CmmType.Outputable__CmmType' *)

(* External variables:
     bool DynFlags.DynFlags FastString.LitString GHC.Base.Eq_ GHC.Err.Build_Default
     GHC.Err.Default GHC.Num.Int GHC.Num.Integer
*)
