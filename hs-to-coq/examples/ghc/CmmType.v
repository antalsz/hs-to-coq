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

Require FastString.
Require GHC.Base.
Require GHC.Num.

(* Converted declarations: *)

(* Translating `instance Outputable.Outputable CmmType' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable CmmCat' failed: OOPS! Cannot find
   information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable Width' failed: OOPS! Cannot find
   information for class "Outputable.Outputable" unsupported *)

(* Translating `instance GHC.Show.Show Width' failed: OOPS! Cannot find
   information for class "GHC.Show.Show" unsupported *)

(* Skipping instance instance_GHC_Base_Ord_Width *)

Inductive ForeignHint : Type := Mk_NoHint : ForeignHint
                             |  Mk_AddrHint : ForeignHint
                             |  Mk_SignedHint : ForeignHint.

Local Definition instance_GHC_Base_Eq__ForeignHint_op_zeze__
    : ForeignHint -> ForeignHint -> bool :=
  fun arg_180__ arg_181__ =>
    match arg_180__ , arg_181__ with
      | Mk_NoHint , Mk_NoHint => true
      | Mk_AddrHint , Mk_AddrHint => true
      | Mk_SignedHint , Mk_SignedHint => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__ForeignHint_op_zsze__
    : ForeignHint -> ForeignHint -> bool :=
  fun arg_272__ arg_273__ =>
    match arg_272__ , arg_273__ with
      | a , b => negb (instance_GHC_Base_Eq__ForeignHint_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__ForeignHint : GHC.Base.Eq_ ForeignHint := {
  op_zeze__ := instance_GHC_Base_Eq__ForeignHint_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__ForeignHint_op_zsze__ }.

Definition Length :=
  GHC.Num.Int%type.

Inductive CmmCat : Type := Mk_GcPtrCat : CmmCat
                        |  Mk_BitsCat : CmmCat
                        |  Mk_FloatCat : CmmCat
                        |  Mk_VecCat : Length -> CmmCat -> CmmCat.

Local Definition instance_GHC_Base_Eq__CmmCat_op_zeze__
    : CmmCat -> CmmCat -> bool :=
  fun x y => true.

Local Definition instance_GHC_Base_Eq__CmmCat_op_zsze__
    : CmmCat -> CmmCat -> bool :=
  fun arg_272__ arg_273__ =>
    match arg_272__ , arg_273__ with
      | a , b => negb (instance_GHC_Base_Eq__CmmCat_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__CmmCat : GHC.Base.Eq_ CmmCat := {
  op_zeze__ := instance_GHC_Base_Eq__CmmCat_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__CmmCat_op_zsze__ }.

Inductive Width : Type := Mk_W8 : Width
                       |  Mk_W16 : Width
                       |  Mk_W32 : Width
                       |  Mk_W64 : Width
                       |  Mk_W80 : Width
                       |  Mk_W128 : Width
                       |  Mk_W256 : Width
                       |  Mk_W512 : Width.

Inductive CmmType : Type := Mk_CmmType : CmmCat -> Width -> CmmType.

Definition isWord64 : CmmType -> bool :=
  fun arg_78__ =>
    match arg_78__ with
      | Mk_CmmType Mk_BitsCat Mk_W64 => true
      | Mk_CmmType Mk_GcPtrCat Mk_W64 => true
      | _other => false
    end.

Definition isWord32 : CmmType -> bool :=
  fun arg_76__ =>
    match arg_76__ with
      | Mk_CmmType Mk_BitsCat Mk_W32 => true
      | Mk_CmmType Mk_GcPtrCat Mk_W32 => true
      | _other => false
    end.

Definition isVecType : CmmType -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CmmType (Mk_VecCat _ _) _ => true
      | _ => false
    end.

Definition isGcPtrType : CmmType -> bool :=
  fun arg_80__ =>
    match arg_80__ with
      | Mk_CmmType Mk_GcPtrCat _ => true
      | _other => false
    end.

Definition isFloatType : CmmType -> bool :=
  fun arg_82__ =>
    match arg_82__ with
      | Mk_CmmType Mk_FloatCat _ => true
      | _other => false
    end.

Definition isFloat64 : CmmType -> bool :=
  fun arg_72__ =>
    match arg_72__ with
      | Mk_CmmType Mk_FloatCat Mk_W64 => true
      | _other => false
    end.

Definition isFloat32 : CmmType -> bool :=
  fun arg_74__ =>
    match arg_74__ with
      | Mk_CmmType Mk_FloatCat Mk_W32 => true
      | _other => false
    end.

Definition widthInBytes : Width -> GHC.Num.Int :=
  fun arg_29__ =>
    match arg_29__ with
      | Mk_W8 => GHC.Num.fromInteger 1
      | Mk_W16 => GHC.Num.fromInteger 2
      | Mk_W32 => GHC.Num.fromInteger 4
      | Mk_W64 => GHC.Num.fromInteger 8
      | Mk_W128 => GHC.Num.fromInteger 16
      | Mk_W256 => GHC.Num.fromInteger 32
      | Mk_W512 => GHC.Num.fromInteger 64
      | Mk_W80 => GHC.Num.fromInteger 10
    end.

Definition widthInBits : Width -> GHC.Num.Int :=
  fun arg_52__ =>
    match arg_52__ with
      | Mk_W8 => GHC.Num.fromInteger 8
      | Mk_W16 => GHC.Num.fromInteger 16
      | Mk_W32 => GHC.Num.fromInteger 32
      | Mk_W64 => GHC.Num.fromInteger 64
      | Mk_W128 => GHC.Num.fromInteger 128
      | Mk_W256 => GHC.Num.fromInteger 256
      | Mk_W512 => GHC.Num.fromInteger 512
      | Mk_W80 => GHC.Num.fromInteger 80
    end.

Definition widthFromBytes : GHC.Num.Int -> Width :=
  fun arg_2__ => Mk_W80.

Definition cmmVec : GHC.Num.Int -> CmmType -> CmmType :=
  fun arg_48__ arg_49__ =>
    match arg_48__ , arg_49__ with
      | n , Mk_CmmType cat w => Mk_CmmType (Mk_VecCat n cat) (widthFromBytes
                                                             (GHC.Num.op_zt__ n (widthInBytes w)))
    end.

Definition vec : Length -> CmmType -> CmmType :=
  fun arg_39__ arg_40__ =>
    match arg_39__ , arg_40__ with
      | l , Mk_CmmType cat w => let vecw : Width :=
                                  widthFromBytes (GHC.Num.op_zt__ l (widthInBytes w)) in
                                Mk_CmmType (Mk_VecCat l cat) vecw
    end.

Definition vec16 : CmmType -> CmmType :=
  vec (GHC.Num.fromInteger 16).

Definition vec2 : CmmType -> CmmType :=
  vec (GHC.Num.fromInteger 2).

Definition vec4 : CmmType -> CmmType :=
  vec (GHC.Num.fromInteger 4).

Definition vec8 : CmmType -> CmmType :=
  vec (GHC.Num.fromInteger 8).

Definition typeWidth : CmmType -> Width :=
  fun arg_101__ => match arg_101__ with | Mk_CmmType _ w => w end.

Definition mrStr : Width -> FastString.LitString :=
  fun arg_62__ =>
    match arg_62__ with
      | Mk_W8 => FastString.sLit (GHC.Base.hs_string__ "W8")
      | Mk_W16 => FastString.sLit (GHC.Base.hs_string__ "W16")
      | Mk_W32 => FastString.sLit (GHC.Base.hs_string__ "W32")
      | Mk_W64 => FastString.sLit (GHC.Base.hs_string__ "W64")
      | Mk_W128 => FastString.sLit (GHC.Base.hs_string__ "W128")
      | Mk_W256 => FastString.sLit (GHC.Base.hs_string__ "W256")
      | Mk_W512 => FastString.sLit (GHC.Base.hs_string__ "W512")
      | Mk_W80 => FastString.sLit (GHC.Base.hs_string__ "W80")
    end.

Definition cmmFloat : Width -> CmmType :=
  Mk_CmmType Mk_FloatCat.

Definition f32 : CmmType :=
  cmmFloat Mk_W32.

Definition vec4f32 : CmmType :=
  vec (GHC.Num.fromInteger 4) f32.

Definition f64 : CmmType :=
  cmmFloat Mk_W64.

Definition vec2f64 : CmmType :=
  vec (GHC.Num.fromInteger 2) f64.

Definition cmmBits : Width -> CmmType :=
  Mk_CmmType Mk_BitsCat.

Definition b8 : CmmType :=
  cmmBits Mk_W8.

Definition vec16b8 : CmmType :=
  vec (GHC.Num.fromInteger 16) b8.

Definition b64 : CmmType :=
  cmmBits Mk_W64.

Definition vec2b64 : CmmType :=
  vec (GHC.Num.fromInteger 2) b64.

Definition b512 : CmmType :=
  cmmBits Mk_W512.

Definition b32 : CmmType :=
  cmmBits Mk_W32.

Definition vec4b32 : CmmType :=
  vec (GHC.Num.fromInteger 4) b32.

Definition b256 : CmmType :=
  cmmBits Mk_W256.

Definition b16 : CmmType :=
  cmmBits Mk_W16.

Definition vec8b16 : CmmType :=
  vec (GHC.Num.fromInteger 8) b16.

Definition b128 : CmmType :=
  cmmBits Mk_W128.

Local Definition instance_GHC_Base_Eq__Width_op_zeze__
    : Width -> Width -> bool :=
  fun arg_115__ arg_116__ =>
    match arg_115__ , arg_116__ with
      | Mk_W8 , Mk_W8 => true
      | Mk_W16 , Mk_W16 => true
      | Mk_W32 , Mk_W32 => true
      | Mk_W64 , Mk_W64 => true
      | Mk_W80 , Mk_W80 => true
      | Mk_W128 , Mk_W128 => true
      | Mk_W256 , Mk_W256 => true
      | Mk_W512 , Mk_W512 => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__Width_op_zsze__
    : Width -> Width -> bool :=
  fun arg_272__ arg_273__ =>
    match arg_272__ , arg_273__ with
      | a , b => negb (instance_GHC_Base_Eq__Width_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__Width : GHC.Base.Eq_ Width := {
  op_zeze__ := instance_GHC_Base_Eq__Width_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__Width_op_zsze__ }.

Definition cmmEqType : CmmType -> CmmType -> bool :=
  fun arg_111__ arg_112__ =>
    match arg_111__ , arg_112__ with
      | Mk_CmmType c1 w1 , Mk_CmmType c2 w2 => andb (GHC.Base.op_zeze__ c1 c2)
                                                    (GHC.Base.op_zeze__ w1 w2)
    end.

Definition cmmEqType_ignoring_ptrhood : CmmType -> CmmType -> bool :=
  fun arg_103__ arg_104__ =>
    match arg_103__ , arg_104__ with
      | Mk_CmmType c1 w1 , Mk_CmmType c2 w2 => let weak_eq
                                                 : CmmCat -> CmmCat -> bool :=
                                                 fix weak_eq arg_105__ arg_106__
                                                       := match arg_105__ , arg_106__ with
                                                            | Mk_FloatCat , Mk_FloatCat => true
                                                            | Mk_FloatCat , _other => false
                                                            | _other , Mk_FloatCat => false
                                                            | Mk_VecCat l1 cat1 , Mk_VecCat l2 cat2 => andb
                                                                                                       (GHC.Base.op_zeze__
                                                                                                       l1 l2) (weak_eq
                                                                                                       cat1 cat2)
                                                            | Mk_VecCat _ _ , _other => false
                                                            | _other , Mk_VecCat _ _ => false
                                                            | _word1 , _word2 => true
                                                          end in
                                               andb (weak_eq c1 c2) (GHC.Base.op_zeze__ w1 w2)
    end.

(* Unbound variables:
     FastString.LitString FastString.sLit GHC.Base.Eq_ GHC.Base.op_zeze__ GHC.Num.Int
     GHC.Num.op_zt__ andb bool false negb true
*)
