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
(* Converted value declarations: *)

Local Definition Uniquable__Unique_getUnique : Unique -> Unique :=
  fun u => u.

Program Instance Uniquable__Unique : Uniquable Unique := fun _ k =>
    k {|getUnique__ := Uniquable__Unique_getUnique |}.
Admit Obligations.

(* Translating `instance Outputable.Outputable Unique.Unique' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance GHC.Show.Show Unique.Unique' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

Definition eqUnique : Unique -> Unique -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | MkUnique u1 , MkUnique u2 => u1 GHC.Base.== u2
    end.

Local Definition Eq___Unique_op_zsze__ : Unique -> Unique -> bool :=
  fun a b => negb (eqUnique a b).

Local Definition Eq___Unique_op_zeze__ : Unique -> Unique -> bool :=
  fun a b => eqUnique a b.

Program Instance Eq___Unique : GHC.Base.Eq_ Unique := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Unique_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Unique_op_zsze__ |}.
Admit Obligations.

Definition getKey : Unique -> GHC.Num.Int :=
  fun arg_0__ => match arg_0__ with | MkUnique x => x end.

Definition hasKey {a} `{Uniquable a} : a -> Unique -> bool :=
  fun x k => getUnique x GHC.Base.== k.

Definition incrUnique : Unique -> Unique :=
  fun arg_0__ =>
    match arg_0__ with
      | MkUnique i => MkUnique (i GHC.Num.+ GHC.Num.fromInteger 1)
    end.

Definition tyConRepNameUnique : Unique -> Unique :=
  fun u => incrUnique u.

Definition dataConWorkerUnique : Unique -> Unique :=
  fun u => incrUnique u.

Definition leUnique : Unique -> Unique -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | MkUnique u1 , MkUnique u2 => u1 GHC.Base.<= u2
    end.

Local Definition Ord__Unique_op_zlze__ : Unique -> Unique -> bool :=
  fun a b => leUnique a b.

Local Definition Ord__Unique_min : Unique -> Unique -> Unique :=
  fun x y => if Ord__Unique_op_zlze__ x y : bool then x else y.

Local Definition Ord__Unique_max : Unique -> Unique -> Unique :=
  fun x y => if Ord__Unique_op_zlze__ x y : bool then y else x.

Local Definition Ord__Unique_op_zg__ : Unique -> Unique -> bool :=
  fun a b => negb (leUnique a b).

Definition ltUnique : Unique -> Unique -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | MkUnique u1 , MkUnique u2 => u1 GHC.Base.< u2
    end.

Local Definition Ord__Unique_op_zl__ : Unique -> Unique -> bool :=
  fun a b => ltUnique a b.

Local Definition Ord__Unique_op_zgze__ : Unique -> Unique -> bool :=
  fun a b => negb (ltUnique a b).

Definition mkUniqueGrimily : GHC.Num.Int -> Unique :=
  MkUnique.

Local Definition Uniquable__Int_getUnique : GHC.Num.Int -> Unique :=
  fun i => mkUniqueGrimily i.

Program Instance Uniquable__Int : Uniquable GHC.Num.Int := fun _ k =>
    k {|getUnique__ := Uniquable__Int_getUnique |}.
Admit Obligations.

Local Definition Uniquable__FastString_getUnique
    : FastString.FastString -> Unique :=
  fun fs => mkUniqueGrimily (FastString.uniqueOfFS fs).

Program Instance Uniquable__FastString : Uniquable FastString.FastString :=
  fun _ k => k {|getUnique__ := Uniquable__FastString_getUnique |}.
Admit Obligations.

Definition nonDetCmpUnique : Unique -> Unique -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | MkUnique u1 , MkUnique u2 => if u1 GHC.Base.== u2 : bool
                                     then Eq
                                     else if u1 GHC.Base.< u2 : bool
                                          then Lt
                                          else Gt
    end.

Local Definition Ord__Unique_compare : Unique -> Unique -> comparison :=
  fun a b => nonDetCmpUnique a b.

Program Instance Ord__Unique : GHC.Base.Ord Unique := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__Unique_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__Unique_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__Unique_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__Unique_op_zgze__ ;
      GHC.Base.compare__ := Ord__Unique_compare ;
      GHC.Base.max__ := Ord__Unique_max ;
      GHC.Base.min__ := Ord__Unique_min |}.
Admit Obligations.

Definition stepUnique : Unique -> GHC.Num.Int -> Unique :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | MkUnique i , n => MkUnique (i GHC.Num.+ n)
    end.

Definition dataConRepNameUnique : Unique -> Unique :=
  fun u => stepUnique u (GHC.Num.fromInteger 2).

Definition uniqueMask : GHC.Num.Int :=
  (Data.Bits.shiftL (GHC.Num.fromInteger 1) (GHC.Num.fromInteger 64 GHC.Num.-
                    GHC.Num.fromInteger 8)) GHC.Num.- GHC.Num.fromInteger 1.

Definition unpkUnique : Unique -> (GHC.Char.Char * GHC.Num.Int)%type :=
  fun arg_0__ =>
    match arg_0__ with
      | MkUnique u => let i := u Data.Bits..&.(**) uniqueMask in
                      let tag :=
                        GHC.Char.chr (Data.Bits.shiftR u (GHC.Num.fromInteger 64 GHC.Num.-
                                                       GHC.Num.fromInteger 8)) in
                      pair tag i
    end.

Definition mkUnique : GHC.Char.Char -> GHC.Num.Int -> Unique :=
  fun c i =>
    let bits := i Data.Bits..&.(**) uniqueMask in
    let tag :=
      Data.Bits.shiftL (GHC.Char.ord c) (GHC.Num.fromInteger 64 GHC.Num.-
                       GHC.Num.fromInteger 8) in
    MkUnique (tag Data.Bits..|.(**) bits).

Definition mkVarOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "i") (FastString.uniqueOfFS fs).

Definition newTagUnique : Unique -> GHC.Char.Char -> Unique :=
  fun u c => match unpkUnique u with | pair _ i => mkUnique c i end.

Definition mkTvOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "v") (FastString.uniqueOfFS fs).

Definition mkTupleTyConUnique
    : BasicTypes.Boxity -> BasicTypes.Arity -> Unique :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | BasicTypes.Boxed , a => mkUnique (GHC.Char.hs_char__ "4") (GHC.Num.fromInteger
                                                                  2 GHC.Num.* a)
      | BasicTypes.Unboxed , a => mkUnique (GHC.Char.hs_char__ "5")
                                  (GHC.Num.fromInteger 2 GHC.Num.* a)
    end.

Definition mkTupleDataConUnique
    : BasicTypes.Boxity -> BasicTypes.Arity -> Unique :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | BasicTypes.Boxed , a => mkUnique (GHC.Char.hs_char__ "7") (GHC.Num.fromInteger
                                                                  3 GHC.Num.* a)
      | BasicTypes.Unboxed , a => mkUnique (GHC.Char.hs_char__ "8")
                                  (GHC.Num.fromInteger 3 GHC.Num.* a)
    end.

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
  fun i => mkUnique (GHC.Char.hs_char__ "3") (GHC.Num.fromInteger 2 GHC.Num.* i).

Definition mkPreludeMiscIdUnique : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "0") i.

Definition mkPreludeDataConUnique : BasicTypes.Arity -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "6") (GHC.Num.fromInteger 3 GHC.Num.* i).

Definition mkPreludeClassUnique : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "2") i.

Definition mkPArrDataConUnique : GHC.Num.Int -> Unique :=
  fun a => mkUnique (GHC.Char.hs_char__ ":") (GHC.Num.fromInteger 2 GHC.Num.* a).

Definition mkDataOccUnique : FastString.FastString -> Unique :=
  fun fs => mkUnique (GHC.Char.hs_char__ "d") (FastString.uniqueOfFS fs).

Definition mkCostCentreUnique : GHC.Num.Int -> Unique :=
  mkUnique (GHC.Char.hs_char__ "C").

Definition mkCoVarUnique : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "g") i.

Definition mkCTupleTyConUnique : BasicTypes.Arity -> Unique :=
  fun a => mkUnique (GHC.Char.hs_char__ "k") (GHC.Num.fromInteger 2 GHC.Num.* a).

Definition mkBuiltinUnique : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "B") i.

Definition mkAlphaTyVarUnique : GHC.Num.Int -> Unique :=
  fun i => mkUnique (GHC.Char.hs_char__ "1") i.

Definition initTyVarUnique : Unique :=
  mkUnique (GHC.Char.hs_char__ "t") (GHC.Num.fromInteger 0).

Definition deriveUnique : Unique -> GHC.Num.Int -> Unique :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | MkUnique i , delta => mkUnique (GHC.Char.hs_char__ "X") (i GHC.Num.+ delta)
    end.

(* Unbound variables:
     Eq Gt Lt bool comparison negb op_zt__ pair BasicTypes.Arity BasicTypes.Boxed
     BasicTypes.Boxity BasicTypes.Unboxed Data.Bits.op_zizazi__ Data.Bits.op_zizbzi__
     Data.Bits.shiftL Data.Bits.shiftR FastString.FastString FastString.uniqueOfFS
     GHC.Base.Eq_ GHC.Base.Ord GHC.Base.op_zeze__ GHC.Base.op_zl__ GHC.Base.op_zlze__
     GHC.Char.Char GHC.Char.chr GHC.Char.ord GHC.Num.Int GHC.Num.op_zm__
     GHC.Num.op_zp__ GHC.Num.op_zt__
*)
