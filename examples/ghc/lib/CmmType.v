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
Require GHC.Num.
Require GHC.Real.
Require Panic.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Width : Type := W8 : Width
                       |  W16 : Width
                       |  W32 : Width
                       |  W64 : Width
                       |  W80 : Width
                       |  W128 : Width
                       |  W256 : Width
                       |  W512 : Width.

Definition Length :=
  GHC.Num.Int%type.

Inductive ForeignHint : Type := NoHint : ForeignHint
                             |  AddrHint : ForeignHint
                             |  SignedHint : ForeignHint.

Inductive CmmCat : Type := GcPtrCat : CmmCat
                        |  BitsCat : CmmCat
                        |  FloatCat : CmmCat
                        |  VecCat : Length -> CmmCat -> CmmCat.

Inductive CmmType : Type := Mk_CmmType : CmmCat -> Width -> CmmType.
(* Midamble *)

Instance Default_CmmCat  : GHC.Err.Default CmmCat :=
	 { default := GcPtrCat }.
Instance Default_width   : GHC.Err.Default Width :=
	 { default := W80 }.
Instance Default_CmmType : GHC.Err.Default CmmType :=
	 { default := Mk_CmmType GHC.Err.default GHC.Err.default }.

(* Converted value declarations: *)

(* Translating `instance Outputable.Outputable CmmType.CmmType' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable CmmType.CmmCat' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable CmmType.Width' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

Local Definition Eq___ForeignHint_op_zeze__
    : ForeignHint -> ForeignHint -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | NoHint , NoHint => true
      | AddrHint , AddrHint => true
      | SignedHint , SignedHint => true
      | _ , _ => false
    end.

Local Definition Eq___ForeignHint_op_zsze__
    : ForeignHint -> ForeignHint -> bool :=
  fun a b => negb (Eq___ForeignHint_op_zeze__ a b).

Program Instance Eq___ForeignHint : GHC.Base.Eq_ ForeignHint := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___ForeignHint_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___ForeignHint_op_zsze__ |}.
Admit Obligations.

Local Definition Eq___CmmCat_op_zeze__ : CmmCat -> CmmCat -> bool :=
  fun x y => true.

Local Definition Eq___CmmCat_op_zsze__ : CmmCat -> CmmCat -> bool :=
  fun a b => negb (Eq___CmmCat_op_zeze__ a b).

Program Instance Eq___CmmCat : GHC.Base.Eq_ CmmCat := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___CmmCat_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___CmmCat_op_zsze__ |}.
Admit Obligations.

(* Translating `instance GHC.Show.Show CmmType.Width' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

(* Skipping instance Ord__Width *)

Local Definition Eq___Width_op_zeze__ : Width -> Width -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | W8 , W8 => true
      | W16 , W16 => true
      | W32 , W32 => true
      | W64 , W64 => true
      | W80 , W80 => true
      | W128 , W128 => true
      | W256 , W256 => true
      | W512 , W512 => true
      | _ , _ => false
    end.

Local Definition Eq___Width_op_zsze__ : Width -> Width -> bool :=
  fun a b => negb (Eq___Width_op_zeze__ a b).

Program Instance Eq___Width : GHC.Base.Eq_ Width := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Width_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Width_op_zsze__ |}.
Admit Obligations.

Definition cmmBits : Width -> CmmType :=
  Mk_CmmType BitsCat.

Definition b8 : CmmType :=
  cmmBits W8.

Definition b64 : CmmType :=
  cmmBits W64.

Definition b512 : CmmType :=
  cmmBits W512.

Definition b32 : CmmType :=
  cmmBits W32.

Definition b256 : CmmType :=
  cmmBits W256.

Definition b16 : CmmType :=
  cmmBits W16.

Definition b128 : CmmType :=
  cmmBits W128.

Definition cmmEqType : CmmType -> CmmType -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_CmmType c1 w1 , Mk_CmmType c2 w2 => andb (c1 GHC.Base.== c2) (w1
                                                    GHC.Base.== w2)
    end.

Definition cmmEqType_ignoring_ptrhood : CmmType -> CmmType -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Mk_CmmType c1 w1 , Mk_CmmType c2 w2 => let weak_eq
                                                 : CmmCat -> CmmCat -> bool :=
                                                 fix weak_eq arg_2__ arg_3__
                                                       := match arg_2__ , arg_3__ with
                                                            | FloatCat , FloatCat => true
                                                            | FloatCat , _other => false
                                                            | _other , FloatCat => false
                                                            | VecCat l1 cat1 , VecCat l2 cat2 => andb (l1 GHC.Base.==
                                                                                                      l2) (weak_eq cat1
                                                                                                                   cat2)
                                                            | VecCat _ _ , _other => false
                                                            | _other , VecCat _ _ => false
                                                            | _word1 , _word2 => true
                                                          end in
                                               andb (weak_eq c1 c2) (w1 GHC.Base.== w2)
    end.

Definition cmmFloat : Width -> CmmType :=
  Mk_CmmType FloatCat.

Definition f32 : CmmType :=
  cmmFloat W32.

Definition f64 : CmmType :=
  cmmFloat W64.

Definition halfWordMask : DynFlags.DynFlags -> GHC.Num.Integer :=
  fun dflags =>
    if DynFlags.wORD_SIZE dflags GHC.Base.== GHC.Num.fromInteger 4 : bool
    then GHC.Num.fromInteger 65535
    else if DynFlags.wORD_SIZE dflags GHC.Base.== GHC.Num.fromInteger 8 : bool
         then GHC.Num.fromInteger 4294967295
         else Panic.panic (GHC.Base.hs_string__
                          "MachOp.halfWordMask: Unknown word size").

Definition halfWordWidth : DynFlags.DynFlags -> Width :=
  fun dflags =>
    if DynFlags.wORD_SIZE dflags GHC.Base.== GHC.Num.fromInteger 4 : bool
    then W16
    else if DynFlags.wORD_SIZE dflags GHC.Base.== GHC.Num.fromInteger 8 : bool
         then W32
         else Panic.panic (GHC.Base.hs_string__ "MachOp.halfWordRep: Unknown word size").

Definition bHalfWord : DynFlags.DynFlags -> CmmType :=
  fun dflags => cmmBits (halfWordWidth dflags).

Definition isFloat32 : CmmType -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CmmType FloatCat W32 => true
      | _other => false
    end.

Definition isFloat64 : CmmType -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CmmType FloatCat W64 => true
      | _other => false
    end.

Definition isFloatType : CmmType -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CmmType FloatCat _ => true
      | _other => false
    end.

Definition isGcPtrType : CmmType -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CmmType GcPtrCat _ => true
      | _other => false
    end.

Definition isVecType : CmmType -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CmmType (VecCat _ _) _ => true
      | _ => false
    end.

Definition isWord32 : CmmType -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CmmType BitsCat W32 => true
      | Mk_CmmType GcPtrCat W32 => true
      | _other => false
    end.

Definition isWord64 : CmmType -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CmmType BitsCat W64 => true
      | Mk_CmmType GcPtrCat W64 => true
      | _other => false
    end.

Definition mrStr : Width -> FastString.LitString :=
  fun arg_0__ =>
    match arg_0__ with
      | W8 => FastString.sLit (GHC.Base.hs_string__ "W8")
      | W16 => FastString.sLit (GHC.Base.hs_string__ "W16")
      | W32 => FastString.sLit (GHC.Base.hs_string__ "W32")
      | W64 => FastString.sLit (GHC.Base.hs_string__ "W64")
      | W128 => FastString.sLit (GHC.Base.hs_string__ "W128")
      | W256 => FastString.sLit (GHC.Base.hs_string__ "W256")
      | W512 => FastString.sLit (GHC.Base.hs_string__ "W512")
      | W80 => FastString.sLit (GHC.Base.hs_string__ "W80")
    end.

Definition typeWidth : CmmType -> Width :=
  fun arg_0__ => match arg_0__ with | Mk_CmmType _ w => w end.

Definition vecLength : CmmType -> Length :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CmmType (VecCat l _) _ => l
      | _ => Panic.panic (GHC.Base.hs_string__ "vecLength: not a vector")
    end.

Definition widthFromBytes : GHC.Num.Int -> Width :=
  fun arg_0__ =>
    match arg_0__ with
      | num_1__ => if num_1__ GHC.Base.== GHC.Num.fromInteger 1 : bool
                   then W8
                   else match arg_0__ with
                          | num_2__ => if num_2__ GHC.Base.== GHC.Num.fromInteger 2 : bool
                                       then W16
                                       else match arg_0__ with
                                              | num_3__ => if num_3__ GHC.Base.== GHC.Num.fromInteger 4 : bool
                                                           then W32
                                                           else match arg_0__ with
                                                                  | num_4__ => if num_4__ GHC.Base.==
                                                                                  GHC.Num.fromInteger 8 : bool
                                                                               then W64
                                                                               else match arg_0__ with
                                                                                      | num_5__ => if num_5__
                                                                                                      GHC.Base.==
                                                                                                      GHC.Num.fromInteger
                                                                                                      16 : bool
                                                                                                   then W128
                                                                                                   else match arg_0__ with
                                                                                                          | num_6__ =>
                                                                                                            if num_6__
                                                                                                               GHC.Base.==
                                                                                                               GHC.Num.fromInteger
                                                                                                               32 : bool
                                                                                                            then W256
                                                                                                            else match arg_0__ with
                                                                                                                   | num_7__ =>
                                                                                                                     if num_7__
                                                                                                                        GHC.Base.==
                                                                                                                        GHC.Num.fromInteger
                                                                                                                        64 : bool
                                                                                                                     then W512
                                                                                                                     else match arg_0__ with
                                                                                                                            | num_8__ =>
                                                                                                                              if num_8__
                                                                                                                                 GHC.Base.==
                                                                                                                                 GHC.Num.fromInteger
                                                                                                                                 10 : bool
                                                                                                                              then W80
                                                                                                                              else match arg_0__ with
                                                                                                                                     | n =>
                                                                                                                                       Panic.panicStr
                                                                                                                                       (GHC.Base.hs_string__
                                                                                                                                       "no width for given number of bytes")
                                                                                                                                       (Panic.noString
                                                                                                                                       n)
                                                                                                                                   end
                                                                                                                          end
                                                                                                                 end
                                                                                                        end
                                                                                    end
                                                                end
                                            end
                        end
    end.

Definition widthInBits : Width -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
      | W8 => GHC.Num.fromInteger 8
      | W16 => GHC.Num.fromInteger 16
      | W32 => GHC.Num.fromInteger 32
      | W64 => GHC.Num.fromInteger 64
      | W128 => GHC.Num.fromInteger 128
      | W256 => GHC.Num.fromInteger 256
      | W512 => GHC.Num.fromInteger 512
      | W80 => GHC.Num.fromInteger 80
    end.

Definition widthInBytes : Width -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
      | W8 => GHC.Num.fromInteger 1
      | W16 => GHC.Num.fromInteger 2
      | W32 => GHC.Num.fromInteger 4
      | W64 => GHC.Num.fromInteger 8
      | W128 => GHC.Num.fromInteger 16
      | W256 => GHC.Num.fromInteger 32
      | W512 => GHC.Num.fromInteger 64
      | W80 => GHC.Num.fromInteger 10
    end.

Definition vecElemType : CmmType -> CmmType :=
  fun arg_0__ =>
    match arg_0__ with
      | Mk_CmmType (VecCat l cat) w => let scalw : Width :=
                                         widthFromBytes (GHC.Real.div (widthInBytes w) l) in
                                       Mk_CmmType cat scalw
      | _ => Panic.panic (GHC.Base.hs_string__ "vecElemType: not a vector")
    end.

Definition vec : Length -> CmmType -> CmmType :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | l , Mk_CmmType cat w => let vecw : Width :=
                                  widthFromBytes (l GHC.Num.* widthInBytes w) in
                                Mk_CmmType (VecCat l cat) vecw
    end.

Definition vec16 : CmmType -> CmmType :=
  vec (GHC.Num.fromInteger 16).

Definition vec2 : CmmType -> CmmType :=
  vec (GHC.Num.fromInteger 2).

Definition vec4 : CmmType -> CmmType :=
  vec (GHC.Num.fromInteger 4).

Definition vec8 : CmmType -> CmmType :=
  vec (GHC.Num.fromInteger 8).

Definition vec4f32 : CmmType :=
  vec (GHC.Num.fromInteger 4) f32.

Definition vec2f64 : CmmType :=
  vec (GHC.Num.fromInteger 2) f64.

Definition vec16b8 : CmmType :=
  vec (GHC.Num.fromInteger 16) b8.

Definition vec2b64 : CmmType :=
  vec (GHC.Num.fromInteger 2) b64.

Definition vec4b32 : CmmType :=
  vec (GHC.Num.fromInteger 4) b32.

Definition vec8b16 : CmmType :=
  vec (GHC.Num.fromInteger 8) b16.

Definition cmmVec : GHC.Num.Int -> CmmType -> CmmType :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | n , Mk_CmmType cat w => Mk_CmmType (VecCat n cat) (widthFromBytes (n GHC.Num.*
                                                                          widthInBytes w))
    end.

Definition widthInLog : Width -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
      | W8 => GHC.Num.fromInteger 0
      | W16 => GHC.Num.fromInteger 1
      | W32 => GHC.Num.fromInteger 2
      | W64 => GHC.Num.fromInteger 3
      | W128 => GHC.Num.fromInteger 4
      | W256 => GHC.Num.fromInteger 5
      | W512 => GHC.Num.fromInteger 6
      | W80 => Panic.panic (GHC.Base.hs_string__ "widthInLog: F80")
    end.

Definition wordWidth : DynFlags.DynFlags -> Width :=
  fun dflags =>
    if DynFlags.wORD_SIZE dflags GHC.Base.== GHC.Num.fromInteger 4 : bool
    then W32
    else if DynFlags.wORD_SIZE dflags GHC.Base.== GHC.Num.fromInteger 8 : bool
         then W64
         else Panic.panic (GHC.Base.hs_string__ "MachOp.wordRep: Unknown word size").

Definition gcWord : DynFlags.DynFlags -> CmmType :=
  fun dflags => Mk_CmmType GcPtrCat (wordWidth dflags).

Definition bWord : DynFlags.DynFlags -> CmmType :=
  fun dflags => cmmBits (wordWidth dflags).

(* Unbound variables:
     andb bool false negb true DynFlags.DynFlags DynFlags.wORD_SIZE
     FastString.LitString FastString.sLit GHC.Base.Eq_ GHC.Base.op_zeze__ GHC.Num.Int
     GHC.Num.Integer GHC.Num.op_zt__ GHC.Real.div Panic.noString Panic.panic
     Panic.panicStr
*)
