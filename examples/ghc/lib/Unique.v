(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BasicTypes.
Require Coq.ZArith.BinInt.
Require Data.Bits.
Require FastString.
Require GHC.Base.
Require GHC.Char.
Require GHC.Num.
Import Data.Bits.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Unique : Type := MkUnique : GHC.Num.Int -> Unique.

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
  fun _ k => k {| getUnique__ x := MkUnique (Coq.ZArith.BinInt.Z.of_N x) |}.


(* Converted value declarations: *)

Local Definition Uniquable__Unique_getUnique : Unique -> Unique :=
  fun u => u.

Program Instance Uniquable__Unique : Uniquable Unique :=
  fun _ k => k {| getUnique__ := Uniquable__Unique_getUnique |}.

(* Translating `instance Outputable__Unique' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Show__Unique' failed: OOPS! Cannot find information for
   class Qualified "GHC.Show" "Show" unsupported *)

Definition eqUnique : Unique -> Unique -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique u1, MkUnique u2 => u1 GHC.Base.== u2
    end.

Local Definition Eq___Unique_op_zsze__ : Unique -> Unique -> bool :=
  fun a b => negb (eqUnique a b).

Local Definition Eq___Unique_op_zeze__ : Unique -> Unique -> bool :=
  fun a b => eqUnique a b.

Program Instance Eq___Unique : GHC.Base.Eq_ Unique :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Unique_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Unique_op_zsze__ |}.

Definition getKey : Unique -> GHC.Num.Int :=
  fun arg_0__ => let 'MkUnique x := arg_0__ in x.

Definition getWordKey : Unique -> GHC.Num.Word :=
  fun u => Coq.ZArith.BinInt.Z.to_N (getKey u).

Definition hasKey {a} `{Uniquable a} : a -> Unique -> bool :=
  fun x k => getUnique x GHC.Base.== k.

Definition incrUnique : Unique -> Unique :=
  fun arg_0__ => let 'MkUnique i := arg_0__ in MkUnique (i GHC.Num.+ #1).

Definition tyConRepNameUnique : Unique -> Unique :=
  fun u => incrUnique u.

Definition dataConWorkerUnique : Unique -> Unique :=
  fun u => incrUnique u.

Definition mkUniqueGrimily : GHC.Num.Int -> Unique :=
  MkUnique.

Local Definition Uniquable__Int_getUnique : GHC.Num.Int -> Unique :=
  fun i => mkUniqueGrimily i.

Program Instance Uniquable__Int : Uniquable GHC.Num.Int :=
  fun _ k => k {| getUnique__ := Uniquable__Int_getUnique |}.

Local Definition Uniquable__FastString_getUnique
   : FastString.FastString -> Unique :=
  fun fs => mkUniqueGrimily (FastString.uniqueOfFS fs).

Program Instance Uniquable__FastString : Uniquable FastString.FastString :=
  fun _ k => k {| getUnique__ := Uniquable__FastString_getUnique |}.

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

Definition stepUnique : Unique -> GHC.Num.Int -> Unique :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique i, n => MkUnique (i GHC.Num.+ n)
    end.

Definition dataConRepNameUnique : Unique -> Unique :=
  fun u => stepUnique u #2.

Definition uNIQUE_BITS : GHC.Num.Int :=
  #56.

Definition uniqueMask : GHC.Num.Int :=
  (Data.Bits.shiftL #1 uNIQUE_BITS) GHC.Num.- #1.

Definition unpkUnique : Unique -> (GHC.Char.Char * GHC.Num.Int)%type :=
  fun arg_0__ =>
    let 'MkUnique u := arg_0__ in
    let i := u Data.Bits..&.(**) uniqueMask in
    let tag := GHC.Char.chr (Data.Bits.shiftR u uNIQUE_BITS) in pair tag i.

Definition isValidKnownKeyUnique : Unique -> bool :=
  fun u =>
    let 'pair c x := unpkUnique u in
    andb (GHC.Base.ord c GHC.Base.< #255) (x GHC.Base.<= (Data.Bits.shiftL #1 #22)).

Definition mkUnique : GHC.Char.Char -> GHC.Num.Int -> Unique :=
  fun c i =>
    let bits := i Data.Bits..&.(**) uniqueMask in
    let tag := Data.Bits.shiftL (GHC.Base.ord c) uNIQUE_BITS in
    MkUnique (tag Data.Bits..|.(**) bits).

Definition mkVarOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "i") (FastString.uniqueOfFS fs).

Definition newTagUnique : Unique -> GHC.Char.Char -> Unique :=
  fun u c => let 'pair _ i := unpkUnique u in mkUnique c i.

Definition mkTvOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "v") (FastString.uniqueOfFS fs).

Definition mkTcOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "c") (FastString.uniqueOfFS fs).

Definition mkRegSubUnique : GHC.Num.Int -> Unique :=
  mkUnique (GHC.Char.hs_char__ "S").

Definition mkRegSingleUnique : GHC.Num.Int -> Unique :=
  mkUnique (GHC.Char.hs_char__ "R").

Definition mkRegPairUnique : GHC.Num.Int -> Unique :=
  mkUnique (GHC.Char.hs_char__ "P").

Definition mkRegClassUnique : GHC.Num.Int -> Unique :=
  mkUnique (GHC.Char.hs_char__ "L").

Definition mkPseudoUniqueH : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "H") i.

Definition mkPseudoUniqueE : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "E") i.

Definition mkPseudoUniqueD : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "D") i.

Definition mkPrimOpIdUnique : GHC.Num.Int -> Unique :=
  fun op => mkUnique (GHC.Char.hs_char__ "9") op.

Definition mkPreludeTyConUnique : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "3") (#2 GHC.Num.* i).

Definition mkPreludeMiscIdUnique : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "0") i.

Definition mkPreludeDataConUnique : BasicTypes.Arity -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "6") (#3 GHC.Num.* i).

Definition mkPreludeClassUnique : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "2") i.

Definition mkPArrDataConUnique : GHC.Num.Int -> Unique :=
  fun a => mkUnique (GHC.Char.hs_char__ ":") (#2 GHC.Num.* a).

Definition mkDataOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "d") (FastString.uniqueOfFS fs).

Definition mkCostCentreUnique : GHC.Num.Int -> Unique :=
  mkUnique (GHC.Char.hs_char__ "C").

Definition mkCoVarUnique : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "g") i.

Definition mkBuiltinUnique : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "B") i.

Definition mkAlphaTyVarUnique : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "1") i.

Definition initTyVarUnique : Unique :=
  mkUnique (GHC.Char.hs_char__ "t") #0.

Definition initExitJoinUnique : Unique :=
  mkUnique (GHC.Char.hs_char__ "s") #0.

Definition deriveUnique : Unique -> GHC.Num.Int -> Unique :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkUnique i, delta => mkUnique (GHC.Char.hs_char__ "X") (i GHC.Num.+ delta)
    end.

(* External variables:
     Eq Gt Lt andb bool comparison negb op_zt__ pair BasicTypes.Arity
     Coq.ZArith.BinInt.Z.to_N Data.Bits.op_zizazi__ Data.Bits.op_zizbzi__
     Data.Bits.shiftL Data.Bits.shiftR FastString.FastString FastString.uniqueOfFS
     GHC.Base.Eq_ GHC.Base.op_zeze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.ord
     GHC.Char.Char GHC.Char.chr GHC.Num.Int GHC.Num.Word GHC.Num.fromInteger
     GHC.Num.op_zm__ GHC.Num.op_zp__ GHC.Num.op_zt__
*)
