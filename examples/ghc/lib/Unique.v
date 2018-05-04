(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import GHC.Nat.


(* Converted imports: *)

Require BasicTypes.
Require Coq.NArith.BinNat.
Require Coq.NArith.BinNatDef.
Require Coq.ZArith.BinInt.
Require Data.Bits.
Require FastString.
Require GHC.Base.
Require GHC.Char.
Require GHC.Num.
Require NArith.BinNat.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Unique : Type := MkUnique : GHC.Num.Word -> Unique.

Record Uniquable__Dict a := Uniquable__Dict_Build {
  getUnique__ : a -> Unique }.

Definition Uniquable a :=
  forall r, (Uniquable__Dict a -> r) -> r.

Existing Class Uniquable.

Definition getUnique `{g : Uniquable a} : a -> Unique :=
  g _ (getUnique__ a).
(* Midamble *)


Instance Default__Name : GHC.Err.Default Unique
  := GHC.Err.Build_Default _ (MkUnique GHC.Err.default).

Program Instance Uniquable__Word : Uniquable GHC.Num.Word :=
  fun _ k => k {| getUnique__ x := MkUnique x |}.

Parameter mkUnique : GHC.Char.Char -> nat -> Unique.

(* Converted value declarations: *)

Local Definition Uniquable__Unique_getUnique : Unique -> Unique :=
  fun u => u.

Program Instance Uniquable__Unique : Uniquable Unique :=
  fun _ k => k {| getUnique__ := Uniquable__Unique_getUnique |}.

(* Skipping instance Outputable__Unique of class Outputable *)

(* Skipping instance Show__Unique of class Show *)

Definition deriveUnique : Unique -> nat -> Unique :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique i, delta =>
        mkUnique (GHC.Char.hs_char__ "X") (NArith.BinNat.N.to_nat i GHC.Num.+ delta)
    end.

Definition eqUnique : Unique -> Unique -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique u1, MkUnique u2 => u1 GHC.Base.== u2
    end.

Local Definition Eq___Unique_op_zeze__ : Unique -> Unique -> bool :=
  fun a b => eqUnique a b.

Local Definition Eq___Unique_op_zsze__ : Unique -> Unique -> bool :=
  fun a b => negb (eqUnique a b).

Program Instance Eq___Unique : GHC.Base.Eq_ Unique :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Unique_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Unique_op_zsze__ |}.

Definition getKey : Unique -> nat :=
  fun '(MkUnique x) => Coq.NArith.BinNatDef.N.to_nat x.

Definition getWordKey : Unique -> GHC.Num.Word :=
  fun u => Coq.NArith.BinNat.N.of_nat (getKey u).

Definition hasKey {a} `{Uniquable a} : a -> Unique -> bool :=
  fun x k => getUnique x GHC.Base.== k.

Definition incrUnique : Unique -> Unique :=
  fun '(MkUnique i) => MkUnique (i GHC.Num.+ #1).

Definition tyConRepNameUnique : Unique -> Unique :=
  fun u => incrUnique u.

Definition dataConWorkerUnique : Unique -> Unique :=
  fun u => incrUnique u.

Definition initExitJoinUnique : Unique :=
  mkUnique (GHC.Char.hs_char__ "s") #0.

Definition initTyVarUnique : Unique :=
  mkUnique (GHC.Char.hs_char__ "t") #0.

Definition mkAlphaTyVarUnique : nat -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "1") i.

Definition mkBuiltinUnique : nat -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "B") i.

Definition mkCoVarUnique : nat -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "g") i.

Definition mkCostCentreUnique : nat -> Unique :=
  mkUnique (GHC.Char.hs_char__ "C").

Definition mkDataOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "d") (FastString.uniqueOfFS fs).

Definition mkPArrDataConUnique : nat -> Unique :=
  fun a => mkUnique (GHC.Char.hs_char__ ":") (#2 GHC.Num.* a).

Definition mkPreludeClassUnique : nat -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "2") i.

Definition mkPreludeDataConUnique : BasicTypes.Arity -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "6") (#3 GHC.Num.* i).

Definition mkPreludeMiscIdUnique : nat -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "0") i.

Definition mkPreludeTyConUnique : nat -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "3") (#2 GHC.Num.* i).

Definition mkPrimOpIdUnique : nat -> Unique :=
  fun op => mkUnique (GHC.Char.hs_char__ "9") op.

Definition mkPseudoUniqueD : nat -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "D") i.

Definition mkPseudoUniqueE : nat -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "E") i.

Definition mkPseudoUniqueH : nat -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "H") i.

Definition mkRegClassUnique : nat -> Unique :=
  mkUnique (GHC.Char.hs_char__ "L").

Definition mkRegPairUnique : nat -> Unique :=
  mkUnique (GHC.Char.hs_char__ "P").

Definition mkRegSingleUnique : nat -> Unique :=
  mkUnique (GHC.Char.hs_char__ "R").

Definition mkRegSubUnique : nat -> Unique :=
  mkUnique (GHC.Char.hs_char__ "S").

Definition mkTcOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "c") (FastString.uniqueOfFS fs).

Definition mkTvOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "v") (FastString.uniqueOfFS fs).

Definition mkUniqueGrimily : nat -> Unique :=
  fun n => MkUnique (Coq.NArith.BinNat.N.of_nat n).

Local Definition Uniquable__nat_getUnique : nat -> Unique :=
  fun i => mkUniqueGrimily i.

Program Instance Uniquable__nat : Uniquable nat :=
  fun _ k => k {| getUnique__ := Uniquable__nat_getUnique |}.

Local Definition Uniquable__FastString_getUnique
   : FastString.FastString -> Unique :=
  fun fs => mkUniqueGrimily (FastString.uniqueOfFS fs).

Program Instance Uniquable__FastString : Uniquable FastString.FastString :=
  fun _ k => k {| getUnique__ := Uniquable__FastString_getUnique |}.

Definition mkVarOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "i") (FastString.uniqueOfFS fs).

Definition nonDetCmpUnique : Unique -> Unique -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique u1, MkUnique u2 =>
        if u1 GHC.Base.== u2 : bool
        then Eq
        else if u1 GHC.Base.< u2 : bool
             then Lt
             else Gt
    end.

Definition stepUnique : Unique -> GHC.Num.Word -> Unique :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique i, n => MkUnique (i GHC.Num.+ n)
    end.

Definition dataConRepNameUnique : Unique -> Unique :=
  fun u => stepUnique u #2.

Definition uNIQUE_BITS : GHC.Num.Int :=
  #56.

Definition uniqueMask : GHC.Num.Int :=
  Data.Bits.shiftL #1 uNIQUE_BITS GHC.Num.- #1.

Definition unpkUnique : Unique -> GHC.Char.Char * GHC.Num.Int :=
  fun '(MkUnique u) =>
    let i := Coq.ZArith.BinInt.Z.land (Coq.ZArith.BinInt.Z.of_N u) uniqueMask in
    let tag :=
      GHC.Char.chr (Data.Bits.shiftR (Coq.ZArith.BinInt.Z.of_N u) uNIQUE_BITS) in
    pair tag i.

Definition isValidKnownKeyUnique : Unique -> bool :=
  fun u =>
    let 'pair c x := unpkUnique u in
    andb (GHC.Base.ord c GHC.Base.< #255) (x GHC.Base.<= (Data.Bits.shiftL #1 #22)).

(* External variables:
     Eq Gt Lt Type andb bool comparison mkUnique nat negb op_zt__ pair
     BasicTypes.Arity Coq.NArith.BinNat.N.of_nat Coq.NArith.BinNatDef.N.to_nat
     Coq.ZArith.BinInt.Z.land Coq.ZArith.BinInt.Z.of_N Data.Bits.shiftL
     Data.Bits.shiftR FastString.FastString FastString.uniqueOfFS GHC.Base.Eq_
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zl__ GHC.Base.op_zlze__
     GHC.Base.op_zsze____ GHC.Base.ord GHC.Char.Char GHC.Char.chr GHC.Char.hs_char__
     GHC.Num.Int GHC.Num.Word GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__
     GHC.Num.op_zt__ NArith.BinNat.N.to_nat
*)
