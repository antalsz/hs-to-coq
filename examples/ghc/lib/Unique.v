(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)




(* Converted imports: *)

Require BasicTypes.
Require BinNat.
Require BinNums.
Require Coq.ZArith.BinInt.
Require Data.Bits.
Require FastString.
Require GHC.Base.
Require GHC.Char.
Require GHC.Num.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Unique : Type := MkUnique : BinNums.N -> Unique.

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


(* Parameter mkUnique : GHC.Char.Char -> GHC.Num.Word -> Unique. *)

(* Converted value declarations: *)

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

Definition stepUnique : Unique -> BinNums.N -> Unique :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique i, n => MkUnique (i GHC.Num.+ n)
    end.

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

Definition mkUniqueGrimily : BinNums.N -> Unique :=
  MkUnique.

Definition mkUnique : GHC.Char.Char -> GHC.Num.Word -> Unique :=
  fun c i =>
    let bits := Coq.ZArith.BinInt.Z.land (Coq.ZArith.BinInt.Z.of_N i) uniqueMask in
    let tag := Data.Bits.shiftL (GHC.Base.ord c) uNIQUE_BITS in
    MkUnique (Coq.ZArith.BinInt.Z.to_N (Coq.ZArith.BinInt.Z.lor tag bits)).

Definition mkVarOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "i") (FastString.uniqueOfFS fs).

Definition mkTvOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "v") (FastString.uniqueOfFS fs).

Definition mkTcOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "c") (FastString.uniqueOfFS fs).

Definition mkRegSubUnique : BinNums.N -> Unique :=
  mkUnique (GHC.Char.hs_char__ "S").

Definition mkRegSingleUnique : BinNums.N -> Unique :=
  mkUnique (GHC.Char.hs_char__ "R").

Definition mkRegPairUnique : BinNums.N -> Unique :=
  mkUnique (GHC.Char.hs_char__ "P").

Definition mkRegClassUnique : BinNums.N -> Unique :=
  mkUnique (GHC.Char.hs_char__ "L").

Definition mkPseudoUniqueH : BinNums.N -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "H") i.

Definition mkPseudoUniqueE : BinNums.N -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "E") i.

Definition mkPseudoUniqueD : BinNums.N -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "D") i.

Definition mkPrimOpIdUnique : BinNums.N -> Unique :=
  fun op => mkUnique (GHC.Char.hs_char__ "9") op.

Definition mkPreludeTyConUnique : BinNums.N -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "3") (#2 GHC.Num.* i).

Definition mkPreludeMiscIdUnique : BinNums.N -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "0") i.

Definition mkPreludeDataConUnique : BasicTypes.Arity -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "6") (#3 GHC.Num.* BinNat.N.of_nat i).

Definition mkPreludeClassUnique : BinNums.N -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "2") i.

Definition mkPArrDataConUnique : BinNums.N -> Unique :=
  fun a => mkUnique (GHC.Char.hs_char__ ":") (#2 GHC.Num.* a).

Definition mkDataOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "d") (FastString.uniqueOfFS fs).

Definition mkCostCentreUnique : BinNums.N -> Unique :=
  mkUnique (GHC.Char.hs_char__ "C").

Definition mkCoVarUnique : BinNums.N -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "g") i.

Definition mkBuiltinUnique : BinNums.N -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "B") i.

Definition mkAlphaTyVarUnique : BinNums.N -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "1") i.

Definition isValidKnownKeyUnique : Unique -> bool :=
  fun u =>
    let 'pair c x := unpkUnique u in
    andb (GHC.Base.ord c GHC.Base.< #255) (x GHC.Base.<= (Data.Bits.shiftL #1 #22)).

Definition initTyVarUnique : Unique :=
  mkUnique (GHC.Char.hs_char__ "t") #0.

Definition initExitJoinUnique : Unique :=
  mkUnique (GHC.Char.hs_char__ "s") #0.

Definition incrUnique : Unique -> Unique :=
  fun '(MkUnique i) => MkUnique (i GHC.Num.+ #1).

Definition tyConRepNameUnique : Unique -> Unique :=
  fun u => incrUnique u.

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

Definition hasKey {a} `{Uniquable a} : a -> Unique -> bool :=
  fun x k => getUnique x GHC.Base.== k.

Definition getKey : Unique -> BinNums.N :=
  fun '(MkUnique x) => x.

Definition deriveUnique : Unique -> BinNums.N -> Unique :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique i, delta => mkUnique (GHC.Char.hs_char__ "X") (i GHC.Num.+ delta)
    end.

Definition dataConWorkerUnique : Unique -> Unique :=
  fun u => incrUnique u.

Definition dataConRepNameUnique : Unique -> Unique :=
  fun u => stepUnique u #2.

(* Skipping all instances of class `GHC.Show.Show', including
   `Unique.Show__Unique' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Unique.Outputable__Unique' *)

Local Definition Uniquable__Unique_getUnique : Unique -> Unique :=
  fun u => u.

Program Instance Uniquable__Unique : Uniquable Unique :=
  fun _ k => k {| getUnique__ := Uniquable__Unique_getUnique |}.

Local Definition Uniquable__N_getUnique : BinNums.N -> Unique :=
  fun i => mkUniqueGrimily i.

Program Instance Uniquable__N : Uniquable BinNums.N :=
  fun _ k => k {| getUnique__ := Uniquable__N_getUnique |}.

Local Definition Uniquable__FastString_getUnique
   : FastString.FastString -> Unique :=
  fun fs => mkUniqueGrimily (FastString.uniqueOfFS fs).

Program Instance Uniquable__FastString : Uniquable FastString.FastString :=
  fun _ k => k {| getUnique__ := Uniquable__FastString_getUnique |}.

Definition getWordKey : Unique -> GHC.Num.Word :=
  getKey.

(* External variables:
     Eq Gt Lt andb bool comparison negb op_zt__ pair BasicTypes.Arity BinNat.N.of_nat
     BinNums.N Coq.ZArith.BinInt.Z.land Coq.ZArith.BinInt.Z.lor
     Coq.ZArith.BinInt.Z.of_N Coq.ZArith.BinInt.Z.to_N Data.Bits.shiftL
     Data.Bits.shiftR FastString.FastString FastString.uniqueOfFS GHC.Base.Eq_
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zl__ GHC.Base.op_zlze__
     GHC.Base.op_zsze____ GHC.Base.ord GHC.Char.Char GHC.Char.chr GHC.Num.Int
     GHC.Num.Word GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__
*)
