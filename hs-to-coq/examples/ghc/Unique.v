(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Preamble *)

Require Import GHC.Base.
Open Scope type_scope.

(* Converted imports: *)

Require BasicTypes.
Require Data.Bits.
Require FastString.
Require GHC.Base.
Require GHC.Char.
Require GHC.Num.

(* Converted declarations: *)

(* Translating `instance Outputable.Outputable Unique' failed: OOPS! Cannot find
   information for class "Outputable.Outputable" unsupported *)

(* Translating `instance GHC.Show.Show Unique' failed: OOPS! Cannot find
   information for class "GHC.Show.Show" unsupported *)

Definition uniqueMask : GHC.Num.Int :=
  GHC.Num.op_zm__ (Data.Bits.shiftL (GHC.Num.fromInteger 1) (GHC.Num.op_zm__
                                    (GHC.Num.fromInteger 64) (GHC.Num.fromInteger 8))) (GHC.Num.fromInteger 1).

Inductive Unique : Type := Mk_MkUnique : GHC.Num.Int -> Unique.

Class Uniquable a := {
  getUnique : a -> Unique }.

Definition unpkUnique : Unique -> GHC.Char.Char * GHC.Num.Int :=
  fun arg_94__ =>
    match arg_94__ with
      | Mk_MkUnique u => let i := Data.Bits.op_zizazi__ u uniqueMask in
                         let tag :=
                           GHC.Char.chr (Data.Bits.shiftR u (GHC.Num.op_zm__ (GHC.Num.fromInteger 64)
                                                                             (GHC.Num.fromInteger 8))) in
                         pair tag i
    end.

Definition stepUnique : Unique -> GHC.Num.Int -> Unique :=
  fun arg_108__ arg_109__ =>
    match arg_108__ , arg_109__ with
      | Mk_MkUnique i , n => Mk_MkUnique (GHC.Num.op_zp__ i n)
    end.

Definition nonDetCmpUnique : Unique -> Unique -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_MkUnique u1 , Mk_MkUnique u2 => if GHC.Base.op_zeze__ u1 u2 : bool
                                           then Eq
                                           else if GHC.Base.op_zl__ u1 u2 : bool
                                                then Lt
                                                else Gt
    end.

Definition mkUniqueGrimily : GHC.Num.Int -> Unique :=
  Mk_MkUnique.

Definition mkUnique : GHC.Char.Char -> GHC.Num.Int -> Unique :=
  fun arg_21__ arg_22__ =>
    match arg_21__ , arg_22__ with
      | c , i => let bits := Data.Bits.op_zizazi__ i uniqueMask in
                 let tag :=
                   Data.Bits.shiftL (GHC.Char.ord c) (GHC.Num.op_zm__ (GHC.Num.fromInteger 64)
                                                                      (GHC.Num.fromInteger 8)) in
                 Mk_MkUnique (Data.Bits.op_zizbzi__ tag bits)
    end.

Definition mkVarOccUnique : FastString.FastString -> Unique :=
  fun arg_82__ =>
    match arg_82__ with
      | fs => mkUnique (GHC.Char.hs_char__ "i") (FastString.uniqueOfFS fs)
    end.

Definition newTagUnique : Unique -> GHC.Char.Char -> Unique :=
  fun arg_99__ arg_100__ =>
    match arg_99__ , arg_100__ with
      | u , c => match unpkUnique u with
                   | pair _ i => mkUnique c i
                 end
    end.

Definition mkTvOccUnique : FastString.FastString -> Unique :=
  fun arg_88__ =>
    match arg_88__ with
      | fs => mkUnique (GHC.Char.hs_char__ "v") (FastString.uniqueOfFS fs)
    end.

Definition mkTupleTyConUnique
    : BasicTypes.Boxity -> BasicTypes.Arity -> Unique :=
  fun arg_39__ arg_40__ =>
    match arg_39__ , arg_40__ with
      | BasicTypes.Mk_Boxed , a => mkUnique (GHC.Char.hs_char__ "4") (GHC.Num.op_zt__
                                                                     (GHC.Num.fromInteger 2) a)
      | BasicTypes.Mk_Unboxed , a => mkUnique (GHC.Char.hs_char__ "5")
                                     (GHC.Num.op_zt__ (GHC.Num.fromInteger 2) a)
    end.

Definition mkTupleDataConUnique
    : BasicTypes.Boxity -> BasicTypes.Arity -> Unique :=
  fun arg_50__ arg_51__ =>
    match arg_50__ , arg_51__ with
      | BasicTypes.Mk_Boxed , a => mkUnique (GHC.Char.hs_char__ "7") (GHC.Num.op_zt__
                                                                     (GHC.Num.fromInteger 3) a)
      | BasicTypes.Mk_Unboxed , a => mkUnique (GHC.Char.hs_char__ "8")
                                     (GHC.Num.op_zt__ (GHC.Num.fromInteger 3) a)
    end.

Definition mkTcOccUnique : FastString.FastString -> Unique :=
  fun arg_91__ =>
    match arg_91__ with
      | fs => mkUnique (GHC.Char.hs_char__ "c") (FastString.uniqueOfFS fs)
    end.

Definition mkRegSubUnique : GHC.Num.Int -> Unique :=
  mkUnique (GHC.Char.hs_char__ "S").

Definition mkRegSingleUnique : GHC.Num.Int -> Unique :=
  mkUnique (GHC.Char.hs_char__ "R").

Definition mkRegPairUnique : GHC.Num.Int -> Unique :=
  mkUnique (GHC.Char.hs_char__ "P").

Definition mkRegClassUnique : GHC.Num.Int -> Unique :=
  mkUnique (GHC.Char.hs_char__ "L").

Definition mkPseudoUniqueH : GHC.Num.Int -> Unique :=
  fun arg_74__ =>
    match arg_74__ with
      | i => mkUnique (GHC.Char.hs_char__ "H") i
    end.

Definition mkPseudoUniqueE : GHC.Num.Int -> Unique :=
  fun arg_71__ =>
    match arg_71__ with
      | i => mkUnique (GHC.Char.hs_char__ "E") i
    end.

Definition mkPseudoUniqueD : GHC.Num.Int -> Unique :=
  fun arg_68__ =>
    match arg_68__ with
      | i => mkUnique (GHC.Char.hs_char__ "D") i
    end.

Definition mkPrimOpIdUnique : GHC.Num.Int -> Unique :=
  fun arg_55__ =>
    match arg_55__ with
      | op => mkUnique (GHC.Char.hs_char__ "9") op
    end.

Definition mkPreludeTyConUnique : GHC.Num.Int -> Unique :=
  fun arg_36__ =>
    match arg_36__ with
      | i => mkUnique (GHC.Char.hs_char__ "3") (GHC.Num.op_zt__ (GHC.Num.fromInteger
                                                                2) i)
    end.

Definition mkPreludeMiscIdUnique : GHC.Num.Int -> Unique :=
  fun arg_58__ =>
    match arg_58__ with
      | i => mkUnique (GHC.Char.hs_char__ "0") i
    end.

Definition mkPreludeDataConUnique : BasicTypes.Arity -> Unique :=
  fun arg_47__ =>
    match arg_47__ with
      | i => mkUnique (GHC.Char.hs_char__ "6") (GHC.Num.op_zt__ (GHC.Num.fromInteger
                                                                3) i)
    end.

Definition mkPreludeClassUnique : GHC.Num.Int -> Unique :=
  fun arg_33__ =>
    match arg_33__ with
      | i => mkUnique (GHC.Char.hs_char__ "2") i
    end.

Definition mkPArrDataConUnique : GHC.Num.Int -> Unique :=
  fun arg_61__ =>
    match arg_61__ with
      | a => mkUnique (GHC.Char.hs_char__ ":") (GHC.Num.op_zt__ (GHC.Num.fromInteger
                                                                2) a)
    end.

Definition mkDataOccUnique : FastString.FastString -> Unique :=
  fun arg_85__ =>
    match arg_85__ with
      | fs => mkUnique (GHC.Char.hs_char__ "d") (FastString.uniqueOfFS fs)
    end.

Definition mkCostCentreUnique : GHC.Num.Int -> Unique :=
  mkUnique (GHC.Char.hs_char__ "C").

Definition mkCoVarUnique : GHC.Num.Int -> Unique :=
  fun arg_30__ =>
    match arg_30__ with
      | i => mkUnique (GHC.Char.hs_char__ "g") i
    end.

Definition mkCTupleTyConUnique : BasicTypes.Arity -> Unique :=
  fun arg_44__ =>
    match arg_44__ with
      | a => mkUnique (GHC.Char.hs_char__ "k") (GHC.Num.op_zt__ (GHC.Num.fromInteger
                                                                2) a)
    end.

Definition mkBuiltinUnique : GHC.Num.Int -> Unique :=
  fun arg_65__ =>
    match arg_65__ with
      | i => mkUnique (GHC.Char.hs_char__ "B") i
    end.

Definition mkAlphaTyVarUnique : GHC.Num.Int -> Unique :=
  fun arg_27__ =>
    match arg_27__ with
      | i => mkUnique (GHC.Char.hs_char__ "1") i
    end.

Definition ltUnique : Unique -> Unique -> bool :=
  fun arg_8__ arg_9__ =>
    match arg_8__ , arg_9__ with
      | Mk_MkUnique u1 , Mk_MkUnique u2 => GHC.Base.op_zl__ u1 u2
    end.

Definition leUnique : Unique -> Unique -> bool :=
  fun arg_4__ arg_5__ =>
    match arg_4__ , arg_5__ with
      | Mk_MkUnique u1 , Mk_MkUnique u2 => GHC.Base.op_zlze__ u1 u2
    end.

Definition initTyVarUnique : Unique :=
  mkUnique (GHC.Char.hs_char__ "t") (GHC.Num.fromInteger 0).

Definition incrUnique : Unique -> Unique :=
  fun arg_115__ =>
    match arg_115__ with
      | Mk_MkUnique i => Mk_MkUnique (GHC.Num.op_zp__ i (GHC.Num.fromInteger 1))
    end.

Definition tyConRepNameUnique : Unique -> Unique :=
  fun arg_118__ => match arg_118__ with | u => incrUnique u end.

(*
Definition hasKey {a} `{Uniquable a} : a -> Unique -> bool :=
  fun arg_16__ arg_17__ =>
    match arg_16__ , arg_17__ with
      | x , k => GHC.Base.op_zeze__ (getUnique x) k
    end.
*)
Definition getKey : Unique -> GHC.Num.Int :=
  fun arg_124__ => match arg_124__ with | Mk_MkUnique x => x end.

Definition eqUnique : Unique -> Unique -> bool :=
  fun arg_12__ arg_13__ =>
    match arg_12__ , arg_13__ with
      | Mk_MkUnique u1 , Mk_MkUnique u2 => GHC.Base.op_zeze__ u1 u2
    end.

Definition deriveUnique : Unique -> GHC.Num.Int -> Unique :=
  fun arg_104__ arg_105__ =>
    match arg_104__ , arg_105__ with
      | Mk_MkUnique i , delta => mkUnique (GHC.Char.hs_char__ "X") (GHC.Num.op_zp__ i
                                                                                    delta)
    end.

Definition dataConWorkerUnique : Unique -> Unique :=
  fun arg_121__ => match arg_121__ with | u => incrUnique u end.

Definition dataConRepNameUnique : Unique -> Unique :=
  fun arg_112__ =>
    match arg_112__ with
      | u => stepUnique u (GHC.Num.fromInteger 2)
    end.

Local Definition instance_Uniquable_Unique_getUnique : Unique -> Unique :=
  fun arg_126__ => match arg_126__ with | u => u end.

Instance instance_Uniquable_Unique : Uniquable Unique := {
  getUnique := instance_Uniquable_Unique_getUnique }.

Local Definition instance_GHC_Base_Ord_Unique_op_zlze__
    : Unique -> Unique -> bool :=
  fun arg_132__ arg_133__ =>
    match arg_132__ , arg_133__ with
      | a , b => leUnique a b
    end.

Local Definition instance_GHC_Base_Ord_Unique_op_zl__
    : Unique -> Unique -> bool :=
  fun arg_128__ arg_129__ =>
    match arg_128__ , arg_129__ with
      | a , b => ltUnique a b
    end.

Local Definition instance_GHC_Base_Ord_Unique_op_zgze__
    : Unique -> Unique -> bool :=
  fun arg_140__ arg_141__ =>
    match arg_140__ , arg_141__ with
      | a , b => negb (ltUnique a b)
    end.

Local Definition instance_GHC_Base_Ord_Unique_op_zg__
    : Unique -> Unique -> bool :=
  fun arg_136__ arg_137__ =>
    match arg_136__ , arg_137__ with
      | a , b => negb (leUnique a b)
    end.

Local Definition instance_GHC_Base_Ord_Unique_min
    : Unique -> Unique -> Unique :=
  fun x y => if instance_GHC_Base_Ord_Unique_op_zlze__ x y : bool then x else y.

Local Definition instance_GHC_Base_Ord_Unique_max
    : Unique -> Unique -> Unique :=
  fun x y => if instance_GHC_Base_Ord_Unique_op_zlze__ x y : bool then y else x.

Local Definition instance_GHC_Base_Ord_Unique_compare
    : Unique -> Unique -> comparison :=
  fun arg_144__ arg_145__ =>
    match arg_144__ , arg_145__ with
      | a , b => nonDetCmpUnique a b
    end.


Local Definition instance_GHC_Base_Eq__Unique_op_zsze__
    : Unique -> Unique -> bool :=
  fun arg_152__ arg_153__ =>
    match arg_152__ , arg_153__ with
      | a , b => negb (eqUnique a b)
    end.

Local Definition instance_GHC_Base_Eq__Unique_op_zeze__
    : Unique -> Unique -> bool :=
  fun arg_148__ arg_149__ =>
    match arg_148__ , arg_149__ with
      | a , b => eqUnique a b
    end.

Instance instance_GHC_Base_Eq__Unique : GHC.Base.Eq_ Unique := {
  op_zeze__ := instance_GHC_Base_Eq__Unique_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__Unique_op_zsze__ }.

Instance instance_GHC_Base_Ord_Unique : GHC.Base.Ord Unique := {
  compare := instance_GHC_Base_Ord_Unique_compare ;
  max := instance_GHC_Base_Ord_Unique_max ;
  min := instance_GHC_Base_Ord_Unique_min ;
  op_zg__ := instance_GHC_Base_Ord_Unique_op_zg__ ;
  op_zgze__ := instance_GHC_Base_Ord_Unique_op_zgze__ ;
  op_zl__ := instance_GHC_Base_Ord_Unique_op_zl__ ;
  op_zlze__ := instance_GHC_Base_Ord_Unique_op_zlze__ }.


Local Definition instance_Uniquable_GHC_Num_Int_getUnique
    : GHC.Num.Int -> Unique :=
  fun arg_156__ => match arg_156__ with | i => mkUniqueGrimily i end.

Instance instance_Uniquable_GHC_Num_Int : Uniquable GHC.Num.Int := {
  getUnique := instance_Uniquable_GHC_Num_Int_getUnique }.

Local Definition instance_Uniquable_FastString_FastString_getUnique
    : FastString.FastString -> Unique :=
  fun arg_159__ =>
    match arg_159__ with
      | fs => mkUniqueGrimily (FastString.uniqueOfFS fs)
    end.

Instance instance_Uniquable_FastString_FastString : Uniquable
                                                    FastString.FastString := {
  getUnique := instance_Uniquable_FastString_FastString_getUnique }.

(* Unbound variables:
     * BasicTypes.Arity BasicTypes.Boxity Data.Bits.op_zizazi__ Data.Bits.op_zizbzi__
     Data.Bits.shiftL Data.Bits.shiftR Eq FastString.FastString FastString.uniqueOfFS
     GHC.Base.Eq_ GHC.Base.Ord GHC.Base.op_zeze__ GHC.Base.op_zl__ GHC.Base.op_zlze__
     GHC.Char.Char GHC.Char.chr GHC.Char.ord GHC.Num.Int GHC.Num.op_zm__
     GHC.Num.op_zp__ GHC.Num.op_zt__ Gt Lt bool comparison negb pair
*)
