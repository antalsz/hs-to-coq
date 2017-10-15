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

Require Data.Function.
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Require SrcLoc.

(* Converted declarations: *)

(* Translating `instance Outputable.Outputable OneShotInfo' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable SwapFlag' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable FunctionOrData' failed: OOPS!
   Cannot find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable WarningTxt' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable Fixity' failed: OOPS! Cannot find
   information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable FixityDirection' failed: OOPS!
   Cannot find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable TopLevelFlag' failed: OOPS!
   Cannot find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable Boxity' failed: OOPS! Cannot find
   information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable RecFlag' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable Origin' failed: OOPS! Cannot find
   information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable OverlapFlag' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable OverlapMode' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable OccInfo' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance forall {ty}, Outputable.Outputable (DefMethSpec ty)'
   failed: OOPS! Cannot find information for class "Outputable.Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable SuccessFlag' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable CompilerPhase' failed: OOPS!
   Cannot find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable Activation' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable RuleMatchInfo' failed: OOPS!
   Cannot find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable InlineSpec' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable InlinePragma' failed: OOPS!
   Cannot find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable FractionalLit' failed: OOPS!
   Cannot find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance Outputable.Outputable IntWithInf' failed: OOPS! Cannot
   find information for class "Outputable.Outputable" unsupported *)

(* Translating `instance GHC.Num.Num IntWithInf' failed: OOPS! Cannot find
   information for class "GHC.Num.Num" unsupported *)

(* Translating `instance GHC.Show.Show FractionalLit' failed: OOPS! Cannot find
   information for class "GHC.Show.Show" unsupported *)

(* Translating `instance Data.Data.Data FractionalLit' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data InlinePragma' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance GHC.Show.Show InlineSpec' failed: OOPS! Cannot find
   information for class "GHC.Show.Show" unsupported *)

(* Translating `instance Data.Data.Data InlineSpec' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance GHC.Show.Show RuleMatchInfo' failed: OOPS! Cannot find
   information for class "GHC.Show.Show" unsupported *)

(* Translating `instance Data.Data.Data RuleMatchInfo' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data Activation' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data WarningTxt' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data StringLiteral' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data Fixity' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data OverlapFlag' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data OverlapMode' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data TupleSort' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data Origin' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data RecFlag' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data Boxity' failed: OOPS! Cannot find
   information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data FixityDirection' failed: OOPS! Cannot
   find information for class "Data.Data.Data" unsupported *)

(* Translating `instance Data.Data.Data FunctionOrData' failed: OOPS! Cannot
   find information for class "Data.Data.Data" unsupported *)

Definition maxPrecedence : GHC.Num.Int :=
  GHC.Num.fromInteger 9.

Definition minPrecedence : GHC.Num.Int :=
  GHC.Num.fromInteger 0.

Definition Alignment :=
  GHC.Num.Int%type.

Definition Arity :=
  GHC.Num.Int%type.

Inductive Boxity : Type := Mk_Boxed : Boxity
                        |  Mk_Unboxed : Boxity.

Definition isBoxed : Boxity -> bool :=
  fun arg_177__ =>
    match arg_177__ with
      | Mk_Boxed => true
      | Mk_Unboxed => false
    end.

Local Definition instance_GHC_Base_Eq__Boxity_op_zeze__
    : Boxity -> Boxity -> bool :=
  fun arg_292__ arg_293__ =>
    match arg_292__ , arg_293__ with
      | Mk_Boxed , Mk_Boxed => true
      | Mk_Unboxed , Mk_Unboxed => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__Boxity_op_zsze__
    : Boxity -> Boxity -> bool :=
  fun arg_319__ arg_320__ =>
    match arg_319__ , arg_320__ with
      | a , b => negb (instance_GHC_Base_Eq__Boxity_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__Boxity : GHC.Base.Eq_ Boxity := {
  op_zeze__ := instance_GHC_Base_Eq__Boxity_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__Boxity_op_zsze__ }.

Definition ConTag :=
  GHC.Num.Int%type.

Definition fIRST_TAG : ConTag :=
  GHC.Num.fromInteger 1.

Inductive DefMethSpec ty : Type := Mk_VanillaDM : DefMethSpec ty
                                |  Mk_GenericDM : ty -> DefMethSpec ty.

Arguments Mk_VanillaDM {_}.

Arguments Mk_GenericDM {_} _.

Inductive EP a : Type := Mk_EP : a -> a -> EP a.

Arguments Mk_EP {_} _ _.

Definition fromEP {a} (arg_6__ : EP a) :=
  match arg_6__ with
    | Mk_EP fromEP _ => fromEP
  end.

Definition toEP {a} (arg_7__ : EP a) :=
  match arg_7__ with
    | Mk_EP _ toEP => toEP
  end.

Inductive FixityDirection : Type := Mk_InfixL : FixityDirection
                                 |  Mk_InfixR : FixityDirection
                                 |  Mk_InfixN : FixityDirection.

Local Definition instance_GHC_Base_Eq__FixityDirection_op_zeze__
    : FixityDirection -> FixityDirection -> bool :=
  fun arg_285__ arg_286__ =>
    match arg_285__ , arg_286__ with
      | Mk_InfixL , Mk_InfixL => true
      | Mk_InfixR , Mk_InfixR => true
      | Mk_InfixN , Mk_InfixN => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__FixityDirection_op_zsze__
    : FixityDirection -> FixityDirection -> bool :=
  fun arg_312__ arg_313__ =>
    match arg_312__ , arg_313__ with
      | a , b => negb (instance_GHC_Base_Eq__FixityDirection_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__FixityDirection : GHC.Base.Eq_ FixityDirection :=
  {
  op_zeze__ := instance_GHC_Base_Eq__FixityDirection_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__FixityDirection_op_zsze__ }.

Inductive FractionalLit : Type := Mk_FL
                                 : GHC.Base.String -> GHC.Real.Rational -> FractionalLit.

Definition fl_text (arg_4__ : FractionalLit) :=
  match arg_4__ with
    | Mk_FL fl_text _ => fl_text
  end.

Definition fl_value (arg_5__ : FractionalLit) :=
  match arg_5__ with
    | Mk_FL _ fl_value => fl_value
  end.

Local Definition instance_GHC_Base_Eq__FractionalLit_op_zeze__
    : FractionalLit -> FractionalLit -> bool :=
  Data.Function.on GHC.Base.op_zeze__ fl_value.

Local Definition instance_GHC_Base_Eq__FractionalLit_op_zsze__
    : FractionalLit -> FractionalLit -> bool :=
  fun x y => negb (instance_GHC_Base_Eq__FractionalLit_op_zeze__ x y).

Instance instance_GHC_Base_Eq__FractionalLit : GHC.Base.Eq_ FractionalLit := {
  op_zeze__ := instance_GHC_Base_Eq__FractionalLit_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__FractionalLit_op_zsze__ }.

Local Definition instance_GHC_Base_Ord_FractionalLit_compare
    : FractionalLit -> FractionalLit -> comparison :=
  Data.Function.on GHC.Base.compare fl_value.

Local Definition instance_GHC_Base_Ord_FractionalLit_op_zg__
    : FractionalLit -> FractionalLit -> bool :=
  fun x y => op_zeze__ (instance_GHC_Base_Ord_FractionalLit_compare x y) Gt.

Local Definition instance_GHC_Base_Ord_FractionalLit_op_zgze__
    : FractionalLit -> FractionalLit -> bool :=
  fun x y => op_zsze__ (instance_GHC_Base_Ord_FractionalLit_compare x y) Lt.

Local Definition instance_GHC_Base_Ord_FractionalLit_op_zl__
    : FractionalLit -> FractionalLit -> bool :=
  fun x y => op_zeze__ (instance_GHC_Base_Ord_FractionalLit_compare x y) Lt.

Local Definition instance_GHC_Base_Ord_FractionalLit_op_zlze__
    : FractionalLit -> FractionalLit -> bool :=
  fun x y => op_zsze__ (instance_GHC_Base_Ord_FractionalLit_compare x y) Gt.

Local Definition instance_GHC_Base_Ord_FractionalLit_max
    : FractionalLit -> FractionalLit -> FractionalLit :=
  fun x y =>
    if instance_GHC_Base_Ord_FractionalLit_op_zlze__ x y : bool
    then y
    else x.

Local Definition instance_GHC_Base_Ord_FractionalLit_min
    : FractionalLit -> FractionalLit -> FractionalLit :=
  fun x y =>
    if instance_GHC_Base_Ord_FractionalLit_op_zlze__ x y : bool
    then x
    else y.

Instance instance_GHC_Base_Ord_FractionalLit : GHC.Base.Ord FractionalLit := {
  compare := instance_GHC_Base_Ord_FractionalLit_compare ;
  max := instance_GHC_Base_Ord_FractionalLit_max ;
  min := instance_GHC_Base_Ord_FractionalLit_min ;
  op_zg__ := instance_GHC_Base_Ord_FractionalLit_op_zg__ ;
  op_zgze__ := instance_GHC_Base_Ord_FractionalLit_op_zgze__ ;
  op_zl__ := instance_GHC_Base_Ord_FractionalLit_op_zl__ ;
  op_zlze__ := instance_GHC_Base_Ord_FractionalLit_op_zlze__ }.

Inductive FunctionOrData : Type := Mk_IsFunction : FunctionOrData
                                |  Mk_IsData : FunctionOrData.

Local Definition instance_GHC_Base_Eq__FunctionOrData_op_zeze__
    : FunctionOrData -> FunctionOrData -> bool :=
  fun arg_233__ arg_234__ =>
    match arg_233__ , arg_234__ with
      | Mk_IsFunction , Mk_IsFunction => true
      | Mk_IsData , Mk_IsData => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__FunctionOrData_op_zsze__
    : FunctionOrData -> FunctionOrData -> bool :=
  fun arg_243__ arg_244__ =>
    match arg_243__ , arg_244__ with
      | a , b => negb (instance_GHC_Base_Eq__FunctionOrData_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__FunctionOrData : GHC.Base.Eq_ FunctionOrData := {
  op_zeze__ := instance_GHC_Base_Eq__FunctionOrData_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__FunctionOrData_op_zsze__ }.

Local Definition instance_GHC_Base_Ord_FunctionOrData_op_zlze__
    : FunctionOrData -> FunctionOrData -> bool :=
  fun arg_258__ arg_259__ =>
    match arg_258__ , arg_259__ with
      | a , b => match a with
                   | Mk_IsFunction => match b with
                                        | Mk_IsFunction => true
                                        | _ => true
                                      end
                   | Mk_IsData => match b with
                                    | Mk_IsData => true
                                    | _ => false
                                  end
                 end
    end.

Local Definition instance_GHC_Base_Ord_FunctionOrData_op_zl__
    : FunctionOrData -> FunctionOrData -> bool :=
  fun arg_249__ arg_250__ =>
    match arg_249__ , arg_250__ with
      | a , b => match a with
                   | Mk_IsFunction => match b with
                                        | Mk_IsFunction => false
                                        | _ => true
                                      end
                   | Mk_IsData => match b with
                                    | Mk_IsData => false
                                    | _ => false
                                  end
                 end
    end.

Local Definition instance_GHC_Base_Ord_FunctionOrData_op_zgze__
    : FunctionOrData -> FunctionOrData -> bool :=
  fun arg_267__ arg_268__ =>
    match arg_267__ , arg_268__ with
      | a , b => match a with
                   | Mk_IsFunction => match b with
                                        | Mk_IsFunction => true
                                        | _ => false
                                      end
                   | Mk_IsData => match b with
                                    | Mk_IsData => true
                                    | _ => true
                                  end
                 end
    end.

Local Definition instance_GHC_Base_Ord_FunctionOrData_op_zg__
    : FunctionOrData -> FunctionOrData -> bool :=
  fun arg_276__ arg_277__ =>
    match arg_276__ , arg_277__ with
      | a , b => match a with
                   | Mk_IsFunction => match b with
                                        | Mk_IsFunction => false
                                        | _ => false
                                      end
                   | Mk_IsData => match b with
                                    | Mk_IsData => false
                                    | _ => true
                                  end
                 end
    end.

Local Definition instance_GHC_Base_Ord_FunctionOrData_min
    : FunctionOrData -> FunctionOrData -> FunctionOrData :=
  fun x y =>
    if instance_GHC_Base_Ord_FunctionOrData_op_zlze__ x y : bool
    then x
    else y.

Local Definition instance_GHC_Base_Ord_FunctionOrData_max
    : FunctionOrData -> FunctionOrData -> FunctionOrData :=
  fun x y =>
    if instance_GHC_Base_Ord_FunctionOrData_op_zlze__ x y : bool
    then y
    else x.

Local Definition instance_GHC_Base_Ord_FunctionOrData_compare
    : FunctionOrData -> FunctionOrData -> comparison :=
  fun arg_240__ arg_241__ =>
    match arg_240__ , arg_241__ with
      | a , b => match a with
                   | Mk_IsFunction => match b with
                                        | Mk_IsFunction => Eq
                                        | _ => Lt
                                      end
                   | Mk_IsData => match b with
                                    | Mk_IsData => Eq
                                    | _ => Gt
                                  end
                 end
    end.

Instance instance_GHC_Base_Ord_FunctionOrData : GHC.Base.Ord FunctionOrData := {
  compare := instance_GHC_Base_Ord_FunctionOrData_compare ;
  max := instance_GHC_Base_Ord_FunctionOrData_max ;
  min := instance_GHC_Base_Ord_FunctionOrData_min ;
  op_zg__ := instance_GHC_Base_Ord_FunctionOrData_op_zg__ ;
  op_zgze__ := instance_GHC_Base_Ord_FunctionOrData_op_zgze__ ;
  op_zl__ := instance_GHC_Base_Ord_FunctionOrData_op_zl__ ;
  op_zlze__ := instance_GHC_Base_Ord_FunctionOrData_op_zlze__ }.

Inductive InlineSpec : Type := Mk_Inline : InlineSpec
                            |  Mk_Inlinable : InlineSpec
                            |  Mk_NoInline : InlineSpec
                            |  Mk_EmptyInlineSpec : InlineSpec.

Definition isEmptyInlineSpec : InlineSpec -> bool :=
  fun arg_117__ =>
    match arg_117__ with
      | Mk_EmptyInlineSpec => true
      | _ => false
    end.

Local Definition instance_GHC_Base_Eq__InlineSpec_op_zeze__
    : InlineSpec -> InlineSpec -> bool :=
  fun arg_374__ arg_375__ =>
    match arg_374__ , arg_375__ with
      | Mk_Inline , Mk_Inline => true
      | Mk_Inlinable , Mk_Inlinable => true
      | Mk_NoInline , Mk_NoInline => true
      | Mk_EmptyInlineSpec , Mk_EmptyInlineSpec => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__InlineSpec_op_zsze__
    : InlineSpec -> InlineSpec -> bool :=
  fun arg_401__ arg_402__ =>
    match arg_401__ , arg_402__ with
      | a , b => negb (instance_GHC_Base_Eq__InlineSpec_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__InlineSpec : GHC.Base.Eq_ InlineSpec := {
  op_zeze__ := instance_GHC_Base_Eq__InlineSpec_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__InlineSpec_op_zsze__ }.

Definition InsideLam :=
  bool%type.

Definition notInsideLam : InsideLam :=
  false.

Definition insideLam : InsideLam :=
  true.

Inductive IntWithInf : Type := Mk_Int : GHC.Num.Int -> IntWithInf
                            |  Mk_Infinity : IntWithInf.

Definition treatZeroAsInf : GHC.Num.Int -> IntWithInf :=
  fun arg_13__ =>
    let j_16__ := match arg_13__ with | n => Mk_Int n end in
    match arg_13__ with
      | num_14__ => if (num_14__ == GHC.Num.fromInteger 0) : bool
                    then Mk_Infinity
                    else j_16__
    end.

Definition plusWithInf : IntWithInf -> IntWithInf -> IntWithInf :=
  fun arg_23__ arg_24__ =>
    match arg_23__ , arg_24__ with
      | Mk_Infinity , _ => Mk_Infinity
      | _ , Mk_Infinity => Mk_Infinity
      | Mk_Int a , Mk_Int b => Mk_Int (GHC.Num.op_zp__ a b)
    end.

Definition mulWithInf : IntWithInf -> IntWithInf -> IntWithInf :=
  fun arg_19__ arg_20__ =>
    match arg_19__ , arg_20__ with
      | Mk_Infinity , _ => Mk_Infinity
      | _ , Mk_Infinity => Mk_Infinity
      | Mk_Int a , Mk_Int b => Mk_Int (GHC.Num.op_zt__ a b)
    end.

Definition mkIntWithInf : GHC.Num.Int -> IntWithInf :=
  Mk_Int.

Definition intGtLimit : GHC.Num.Int -> IntWithInf -> bool :=
  fun arg_27__ arg_28__ =>
    match arg_27__ , arg_28__ with
      | _ , Mk_Infinity => false
      | n , Mk_Int m => GHC.Base.op_zg__ n m
    end.

Definition infinity : IntWithInf :=
  Mk_Infinity.

Local Definition instance_GHC_Base_Eq__IntWithInf_op_zeze__
    : IntWithInf -> IntWithInf -> bool :=
  fun arg_389__ arg_390__ =>
    match arg_389__ , arg_390__ with
      | Mk_Int a1 , Mk_Int b1 => ((GHC.Base.op_zeze__ a1 b1))
      | Mk_Infinity , Mk_Infinity => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__IntWithInf_op_zsze__
    : IntWithInf -> IntWithInf -> bool :=
  fun arg_400__ arg_401__ =>
    match arg_400__ , arg_401__ with
      | a , b => negb (instance_GHC_Base_Eq__IntWithInf_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__IntWithInf : GHC.Base.Eq_ IntWithInf := {
  op_zeze__ := instance_GHC_Base_Eq__IntWithInf_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__IntWithInf_op_zsze__ }.

Local Definition instance_GHC_Base_Ord_IntWithInf_compare
    : IntWithInf -> IntWithInf -> comparison :=
  fun arg_397__ arg_398__ =>
    match arg_397__ , arg_398__ with
      | Mk_Infinity , Mk_Infinity => Eq
      | Mk_Int _ , Mk_Infinity => Lt
      | Mk_Infinity , Mk_Int _ => Gt
      | Mk_Int a , Mk_Int b => GHC.Base.compare a b
    end.

Local Definition instance_GHC_Base_Ord_IntWithInf_op_zg__
    : IntWithInf -> IntWithInf -> bool :=
  fun x y => op_zeze__ (instance_GHC_Base_Ord_IntWithInf_compare x y) Gt.

Local Definition instance_GHC_Base_Ord_IntWithInf_op_zgze__
    : IntWithInf -> IntWithInf -> bool :=
  fun x y => op_zsze__ (instance_GHC_Base_Ord_IntWithInf_compare x y) Lt.

Local Definition instance_GHC_Base_Ord_IntWithInf_op_zl__
    : IntWithInf -> IntWithInf -> bool :=
  fun x y => op_zeze__ (instance_GHC_Base_Ord_IntWithInf_compare x y) Lt.

Local Definition instance_GHC_Base_Ord_IntWithInf_op_zlze__
    : IntWithInf -> IntWithInf -> bool :=
  fun x y => op_zsze__ (instance_GHC_Base_Ord_IntWithInf_compare x y) Gt.

Local Definition instance_GHC_Base_Ord_IntWithInf_max
    : IntWithInf -> IntWithInf -> IntWithInf :=
  fun x y =>
    if instance_GHC_Base_Ord_IntWithInf_op_zlze__ x y : bool
    then y
    else x.

Local Definition instance_GHC_Base_Ord_IntWithInf_min
    : IntWithInf -> IntWithInf -> IntWithInf :=
  fun x y =>
    if instance_GHC_Base_Ord_IntWithInf_op_zlze__ x y : bool
    then x
    else y.

Instance instance_GHC_Base_Ord_IntWithInf : GHC.Base.Ord IntWithInf := {
  compare := instance_GHC_Base_Ord_IntWithInf_compare ;
  max := instance_GHC_Base_Ord_IntWithInf_max ;
  min := instance_GHC_Base_Ord_IntWithInf_min ;
  op_zg__ := instance_GHC_Base_Ord_IntWithInf_op_zg__ ;
  op_zgze__ := instance_GHC_Base_Ord_IntWithInf_op_zgze__ ;
  op_zl__ := instance_GHC_Base_Ord_IntWithInf_op_zl__ ;
  op_zlze__ := instance_GHC_Base_Ord_IntWithInf_op_zlze__ }.

Definition InterestingCxt :=
  bool%type.

Definition OneBranch :=
  bool%type.

Definition oneBranch : OneBranch :=
  true.

Definition notOneBranch : OneBranch :=
  false.

Inductive OneShotInfo : Type := Mk_NoOneShotInfo : OneShotInfo
                             |  Mk_ProbOneShot : OneShotInfo
                             |  Mk_OneShotLam : OneShotInfo.

Definition worstOneShot : OneShotInfo -> OneShotInfo -> OneShotInfo :=
  fun arg_218__ arg_219__ =>
    match arg_218__ , arg_219__ with
      | Mk_NoOneShotInfo , _ => Mk_NoOneShotInfo
      | Mk_ProbOneShot , Mk_NoOneShotInfo => Mk_NoOneShotInfo
      | Mk_ProbOneShot , _ => Mk_ProbOneShot
      | Mk_OneShotLam , os => os
    end.

Definition noOneShotInfo : OneShotInfo :=
  Mk_NoOneShotInfo.

Definition isOneShotInfo : OneShotInfo -> bool :=
  fun arg_223__ => match arg_223__ with | Mk_OneShotLam => true | _ => false end.

Definition hasNoOneShotInfo : OneShotInfo -> bool :=
  fun arg_221__ =>
    match arg_221__ with
      | Mk_NoOneShotInfo => true
      | _ => false
    end.

Definition bestOneShot : OneShotInfo -> OneShotInfo -> OneShotInfo :=
  fun arg_215__ arg_216__ =>
    match arg_215__ , arg_216__ with
      | Mk_NoOneShotInfo , os => os
      | Mk_ProbOneShot , Mk_OneShotLam => Mk_OneShotLam
      | Mk_ProbOneShot , _ => Mk_ProbOneShot
      | Mk_OneShotLam , _ => Mk_OneShotLam
    end.

Local Definition instance_GHC_Base_Eq__OneShotInfo_op_zeze__
    : OneShotInfo -> OneShotInfo -> bool :=
  fun arg_226__ arg_227__ =>
    match arg_226__ , arg_227__ with
      | Mk_NoOneShotInfo , Mk_NoOneShotInfo => true
      | Mk_ProbOneShot , Mk_ProbOneShot => true
      | Mk_OneShotLam , Mk_OneShotLam => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__OneShotInfo_op_zsze__
    : OneShotInfo -> OneShotInfo -> bool :=
  fun arg_236__ arg_237__ =>
    match arg_236__ , arg_237__ with
      | a , b => negb (instance_GHC_Base_Eq__OneShotInfo_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__OneShotInfo : GHC.Base.Eq_ OneShotInfo := {
  op_zeze__ := instance_GHC_Base_Eq__OneShotInfo_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__OneShotInfo_op_zsze__ }.

Inductive Origin : Type := Mk_FromSource : Origin
                        |  Mk_Generated : Origin.

Definition isGenerated : Origin -> bool :=
  fun arg_169__ =>
    match arg_169__ with
      | Mk_Generated => true
      | Mk_FromSource => false
    end.

Local Definition instance_GHC_Base_Eq__Origin_op_zeze__
    : Origin -> Origin -> bool :=
  fun arg_306__ arg_307__ =>
    match arg_306__ , arg_307__ with
      | Mk_FromSource , Mk_FromSource => true
      | Mk_Generated , Mk_Generated => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__Origin_op_zsze__
    : Origin -> Origin -> bool :=
  fun arg_316__ arg_317__ =>
    match arg_316__ , arg_317__ with
      | a , b => negb (instance_GHC_Base_Eq__Origin_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__Origin : GHC.Base.Eq_ Origin := {
  op_zeze__ := instance_GHC_Base_Eq__Origin_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__Origin_op_zsze__ }.

Definition PhaseNum :=
  GHC.Num.Int%type.

Inductive CompilerPhase : Type := Mk_Phase : PhaseNum -> CompilerPhase
                               |  Mk_InitialPhase : CompilerPhase.

Inductive RecFlag : Type := Mk_Recursive : RecFlag
                         |  Mk_NonRecursive : RecFlag.

Definition isRec : RecFlag -> bool :=
  fun arg_175__ =>
    match arg_175__ with
      | Mk_Recursive => true
      | Mk_NonRecursive => false
    end.

Definition isNonRec : RecFlag -> bool :=
  fun arg_173__ =>
    match arg_173__ with
      | Mk_Recursive => false
      | Mk_NonRecursive => true
    end.

Definition boolToRecFlag : bool -> RecFlag :=
  fun arg_171__ =>
    match arg_171__ with
      | true => Mk_Recursive
      | false => Mk_NonRecursive
    end.

Local Definition instance_GHC_Base_Eq__RecFlag_op_zeze__
    : RecFlag -> RecFlag -> bool :=
  fun arg_299__ arg_300__ =>
    match arg_299__ , arg_300__ with
      | Mk_Recursive , Mk_Recursive => true
      | Mk_NonRecursive , Mk_NonRecursive => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__RecFlag_op_zsze__
    : RecFlag -> RecFlag -> bool :=
  fun arg_309__ arg_310__ =>
    match arg_309__ , arg_310__ with
      | a , b => negb (instance_GHC_Base_Eq__RecFlag_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__RecFlag : GHC.Base.Eq_ RecFlag := {
  op_zeze__ := instance_GHC_Base_Eq__RecFlag_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__RecFlag_op_zsze__ }.

Definition RepArity :=
  GHC.Num.Int%type.

Inductive RuleMatchInfo : Type := Mk_ConLike : RuleMatchInfo
                               |  Mk_FunLike : RuleMatchInfo.

Definition isFunLike : RuleMatchInfo -> bool :=
  fun arg_119__ => match arg_119__ with | Mk_FunLike => true | _ => false end.

Definition isConLike : RuleMatchInfo -> bool :=
  fun arg_124__ => match arg_124__ with | Mk_ConLike => true | _ => false end.

Local Definition instance_GHC_Base_Eq__RuleMatchInfo_op_zeze__
    : RuleMatchInfo -> RuleMatchInfo -> bool :=
  fun arg_367__ arg_368__ =>
    match arg_367__ , arg_368__ with
      | Mk_ConLike , Mk_ConLike => true
      | Mk_FunLike , Mk_FunLike => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__RuleMatchInfo_op_zsze__
    : RuleMatchInfo -> RuleMatchInfo -> bool :=
  fun arg_377__ arg_378__ =>
    match arg_377__ , arg_378__ with
      | a , b => negb (instance_GHC_Base_Eq__RuleMatchInfo_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__RuleMatchInfo : GHC.Base.Eq_ RuleMatchInfo := {
  op_zeze__ := instance_GHC_Base_Eq__RuleMatchInfo_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__RuleMatchInfo_op_zsze__ }.

Definition RuleName :=
  FastString.FastString%type.

Definition RulesOnly :=
  bool%type.

Inductive OccInfo : Type := Mk_NoOccInfo : OccInfo
                         |  Mk_IAmDead : OccInfo
                         |  Mk_OneOcc : InsideLam -> OneBranch -> InterestingCxt -> OccInfo
                         |  Mk_IAmALoopBreaker : RulesOnly -> OccInfo.

Definition zapFragileOcc : OccInfo -> OccInfo :=
  fun arg_132__ =>
    match arg_132__ with
      | Mk_OneOcc _ _ _ => Mk_NoOccInfo
      | occ => occ
    end.

Definition weakLoopBreaker : OccInfo :=
  Mk_IAmALoopBreaker true.

Definition strongLoopBreaker : OccInfo :=
  Mk_IAmALoopBreaker false.

Definition seqOccInfo : OccInfo -> unit :=
  fun arg_144__ => match arg_144__ with | occ => GHC.Prim.seq occ tt end.

Definition isWeakLoopBreaker : OccInfo -> bool :=
  fun arg_140__ =>
    match arg_140__ with
      | Mk_IAmALoopBreaker _ => true
      | _ => false
    end.

Definition isStrongLoopBreaker : OccInfo -> bool :=
  fun arg_138__ =>
    match arg_138__ with
      | Mk_IAmALoopBreaker false => true
      | _ => false
    end.

Definition isOneOcc : OccInfo -> bool :=
  fun arg_134__ =>
    match arg_134__ with
      | Mk_OneOcc _ _ _ => true
      | _ => false
    end.

Definition isNoOcc : OccInfo -> bool :=
  fun arg_147__ => match arg_147__ with | Mk_NoOccInfo => true | _ => false end.

Definition isDeadOcc : OccInfo -> bool :=
  fun arg_136__ => match arg_136__ with | Mk_IAmDead => true | _ => false end.

Local Definition instance_GHC_Base_Eq__OccInfo_op_zeze__
    : OccInfo -> OccInfo -> bool :=
  fun arg_320__ arg_321__ =>
    match arg_320__ , arg_321__ with
      | Mk_NoOccInfo , Mk_NoOccInfo => true
      | Mk_IAmDead , Mk_IAmDead => true
      | Mk_OneOcc a1 a2 a3 , Mk_OneOcc b1 b2 b3 => (andb (andb ((GHC.Base.op_zeze__ a1
                                                                                    b1)) ((GHC.Base.op_zeze__ a2 b2)))
                                                         ((GHC.Base.op_zeze__ a3 b3)))
      | Mk_IAmALoopBreaker a1 , Mk_IAmALoopBreaker b1 => ((GHC.Base.op_zeze__ a1 b1))
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__OccInfo_op_zsze__
    : OccInfo -> OccInfo -> bool :=
  fun arg_332__ arg_333__ =>
    match arg_332__ , arg_333__ with
      | a , b => negb (instance_GHC_Base_Eq__OccInfo_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__OccInfo : GHC.Base.Eq_ OccInfo := {
  op_zeze__ := instance_GHC_Base_Eq__OccInfo_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__OccInfo_op_zsze__ }.

Definition SourceText :=
  GHC.Base.String%type.

Inductive StringLiteral : Type := Mk_StringLiteral
                                 : SourceText -> FastString.FastString -> StringLiteral.

Definition sl_fs (arg_0__ : StringLiteral) :=
  match arg_0__ with
    | Mk_StringLiteral _ sl_fs => sl_fs
  end.

Definition sl_st (arg_1__ : StringLiteral) :=
  match arg_1__ with
    | Mk_StringLiteral sl_st _ => sl_st
  end.

Local Definition instance_GHC_Base_Eq__StringLiteral_op_zeze__
    : StringLiteral -> StringLiteral -> bool :=
  fun arg_407__ arg_408__ =>
    match arg_407__ , arg_408__ with
      | Mk_StringLiteral _ a , Mk_StringLiteral _ b => GHC.Base.op_zeze__ a b
    end.

Local Definition instance_GHC_Base_Eq__StringLiteral_op_zsze__
    : StringLiteral -> StringLiteral -> bool :=
  fun x y => negb (instance_GHC_Base_Eq__StringLiteral_op_zeze__ x y).

Instance instance_GHC_Base_Eq__StringLiteral : GHC.Base.Eq_ StringLiteral := {
  op_zeze__ := instance_GHC_Base_Eq__StringLiteral_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__StringLiteral_op_zsze__ }.

Inductive WarningTxt : Type := Mk_WarningTxt : (SrcLoc.Located
                                               SourceText) -> list (SrcLoc.Located StringLiteral) -> WarningTxt
                            |  Mk_DeprecatedTxt : (SrcLoc.Located SourceText) -> list (SrcLoc.Located
                                                                                      StringLiteral) -> WarningTxt.

Local Definition instance_GHC_Base_Eq__WarningTxt_op_zeze__
    : WarningTxt -> WarningTxt -> bool :=
  fun arg_349__ arg_350__ =>
    match arg_349__ , arg_350__ with
      | Mk_WarningTxt a1 a2 , Mk_WarningTxt b1 b2 => (andb ((GHC.Base.op_zeze__ a1
                                                                                b1)) ((GHC.Base.op_zeze__ a2 b2)))
      | Mk_DeprecatedTxt a1 a2 , Mk_DeprecatedTxt b1 b2 => (andb ((GHC.Base.op_zeze__
                                                                 a1 b1)) ((GHC.Base.op_zeze__ a2 b2)))
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__WarningTxt_op_zsze__
    : WarningTxt -> WarningTxt -> bool :=
  fun arg_361__ arg_362__ =>
    match arg_361__ , arg_362__ with
      | a , b => negb (instance_GHC_Base_Eq__WarningTxt_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__WarningTxt : GHC.Base.Eq_ WarningTxt := {
  op_zeze__ := instance_GHC_Base_Eq__WarningTxt_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__WarningTxt_op_zsze__ }.

Inductive OverlapMode : Type := Mk_NoOverlap : SourceText -> OverlapMode
                             |  Mk_Overlappable : SourceText -> OverlapMode
                             |  Mk_Overlapping : SourceText -> OverlapMode
                             |  Mk_Overlaps : SourceText -> OverlapMode
                             |  Mk_Incoherent : SourceText -> OverlapMode.

Inductive OverlapFlag : Type := Mk_OverlapFlag
                               : OverlapMode -> bool -> OverlapFlag.

Definition isSafeOverlap (arg_2__ : OverlapFlag) :=
  match arg_2__ with
    | Mk_OverlapFlag _ isSafeOverlap => isSafeOverlap
  end.

Definition overlapMode (arg_3__ : OverlapFlag) :=
  match arg_3__ with
    | Mk_OverlapFlag overlapMode _ => overlapMode
  end.

Definition setOverlapModeMaybe : OverlapFlag -> option
                                 OverlapMode -> OverlapFlag :=
  fun arg_161__ arg_162__ =>
    match arg_161__ , arg_162__ with
      | f , None => f
      | f , Some m => match f with
                        | Mk_OverlapFlag overlapMode_163__ isSafeOverlap_164__ => Mk_OverlapFlag m
                                                                                                 isSafeOverlap_164__
                      end
    end.

Definition hasOverlappingFlag : OverlapMode -> bool :=
  fun arg_153__ =>
    match arg_153__ with
      | mode => match mode with
                  | Mk_Overlapping _ => true
                  | Mk_Overlaps _ => true
                  | Mk_Incoherent _ => true
                  | _ => false
                end
    end.

Definition hasOverlappableFlag : OverlapMode -> bool :=
  fun arg_157__ =>
    match arg_157__ with
      | mode => match mode with
                  | Mk_Overlappable _ => true
                  | Mk_Overlaps _ => true
                  | Mk_Incoherent _ => true
                  | _ => false
                end
    end.

Local Definition instance_GHC_Base_Eq__OverlapMode_op_zeze__
    : OverlapMode -> OverlapMode -> bool :=
  fun arg_329__ arg_330__ =>
    match arg_329__ , arg_330__ with
      | Mk_NoOverlap a1 , Mk_NoOverlap b1 => ((GHC.Base.op_zeze__ a1 b1))
      | Mk_Overlappable a1 , Mk_Overlappable b1 => ((GHC.Base.op_zeze__ a1 b1))
      | Mk_Overlapping a1 , Mk_Overlapping b1 => ((GHC.Base.op_zeze__ a1 b1))
      | Mk_Overlaps a1 , Mk_Overlaps b1 => ((GHC.Base.op_zeze__ a1 b1))
      | Mk_Incoherent a1 , Mk_Incoherent b1 => ((GHC.Base.op_zeze__ a1 b1))
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__OverlapMode_op_zsze__
    : OverlapMode -> OverlapMode -> bool :=
  fun arg_344__ arg_345__ =>
    match arg_344__ , arg_345__ with
      | a , b => negb (instance_GHC_Base_Eq__OverlapMode_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__OverlapMode : GHC.Base.Eq_ OverlapMode := {
  op_zeze__ := instance_GHC_Base_Eq__OverlapMode_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__OverlapMode_op_zsze__ }.

Local Definition instance_GHC_Base_Eq__OverlapFlag_op_zeze__
    : OverlapFlag -> OverlapFlag -> bool :=
  fun arg_341__ arg_342__ =>
    match arg_341__ , arg_342__ with
      | Mk_OverlapFlag a1 a2 , Mk_OverlapFlag b1 b2 => (andb ((GHC.Base.op_zeze__ a1
                                                                                  b1)) ((GHC.Base.op_zeze__ a2 b2)))
    end.

Local Definition instance_GHC_Base_Eq__OverlapFlag_op_zsze__
    : OverlapFlag -> OverlapFlag -> bool :=
  fun arg_352__ arg_353__ =>
    match arg_352__ , arg_353__ with
      | a , b => negb (instance_GHC_Base_Eq__OverlapFlag_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__OverlapFlag : GHC.Base.Eq_ OverlapFlag := {
  op_zeze__ := instance_GHC_Base_Eq__OverlapFlag_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__OverlapFlag_op_zsze__ }.

Inductive Fixity : Type := Mk_Fixity
                          : SourceText -> GHC.Num.Int -> FixityDirection -> Fixity.

Definition negateFixity : Fixity :=
  Mk_Fixity (GHC.Base.hs_string__ "6") (GHC.Num.fromInteger 6) Mk_InfixL.

Definition funTyFixity : Fixity :=
  Mk_Fixity (GHC.Base.hs_string__ "0") (GHC.Num.fromInteger 0) Mk_InfixR.

(*
Definition defaultFixity : Fixity :=
  Mk_Fixity (GHC.Show.show maxPrecedence) maxPrecedence Mk_InfixL.
*)
Definition compareFixity : Fixity -> Fixity -> bool * bool :=
  fun arg_183__ arg_184__ =>
    match arg_183__ , arg_184__ with
      | Mk_Fixity _ prec1 dir1 , Mk_Fixity _ prec2 dir2 => let error_please :=
                                                             pair true false in
                                                           let left := pair false false in
                                                           let right := pair false true in
                                                           let scrut_188__ := GHC.Base.compare prec1 prec2 in
                                                           match scrut_188__ with
                                                             | Gt => left
                                                             | Lt => right
                                                             | Eq => let scrut_189__ := pair dir1 dir2 in
                                                                     match scrut_189__ with
                                                                       | pair Mk_InfixR Mk_InfixR => right
                                                                       | pair Mk_InfixL Mk_InfixL => left
                                                                       | _ => error_please
                                                                     end
                                                           end
    end.

Local Definition instance_GHC_Base_Eq__Fixity_op_zeze__
    : Fixity -> Fixity -> bool :=
  fun arg_403__ arg_404__ =>
    match arg_403__ , arg_404__ with
      | Mk_Fixity _ p1 dir1 , Mk_Fixity _ p2 dir2 => andb (GHC.Base.op_zeze__ p1 p2)
                                                          (GHC.Base.op_zeze__ dir1 dir2)
    end.

Local Definition instance_GHC_Base_Eq__Fixity_op_zsze__
    : Fixity -> Fixity -> bool :=
  fun x y => negb (instance_GHC_Base_Eq__Fixity_op_zeze__ x y).

Instance instance_GHC_Base_Eq__Fixity : GHC.Base.Eq_ Fixity := {
  op_zeze__ := instance_GHC_Base_Eq__Fixity_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__Fixity_op_zsze__ }.

Inductive Activation : Type := Mk_NeverActive : Activation
                            |  Mk_AlwaysActive : Activation
                            |  Mk_ActiveBefore : SourceText -> PhaseNum -> Activation
                            |  Mk_ActiveAfter : SourceText -> PhaseNum -> Activation.

Definition isNeverActive : Activation -> bool :=
  fun arg_35__ => match arg_35__ with | Mk_NeverActive => true | _ => false end.

Definition isEarlyActive : Activation -> bool :=
  fun arg_31__ =>
    match arg_31__ with
      | Mk_AlwaysActive => true
      | Mk_ActiveBefore _ _ => true
      | _ => false
    end.

Definition isAlwaysActive : Activation -> bool :=
  fun arg_33__ => match arg_33__ with | Mk_AlwaysActive => true | _ => false end.

Definition isActiveIn : PhaseNum -> Activation -> bool :=
  fun arg_42__ arg_43__ =>
    match arg_42__ , arg_43__ with
      | _ , Mk_NeverActive => false
      | _ , Mk_AlwaysActive => true
      | p , Mk_ActiveAfter _ n => GHC.Base.op_zlze__ p n
      | p , Mk_ActiveBefore _ n => GHC.Base.op_zg__ p n
    end.

Definition isActive : CompilerPhase -> Activation -> bool :=
  fun arg_47__ arg_48__ =>
    match arg_47__ , arg_48__ with
      | Mk_InitialPhase , Mk_AlwaysActive => true
      | Mk_InitialPhase , Mk_ActiveBefore _ _ => true
      | Mk_InitialPhase , _ => false
      | Mk_Phase p , act => isActiveIn p act
    end.

Definition competesWith : Activation -> Activation -> bool :=
  fun arg_37__ arg_38__ =>
    match arg_37__ , arg_38__ with
      | Mk_NeverActive , _ => false
      | _ , Mk_NeverActive => false
      | Mk_AlwaysActive , _ => true
      | Mk_ActiveBefore _ _ , Mk_AlwaysActive => true
      | Mk_ActiveBefore _ _ , Mk_ActiveBefore _ _ => true
      | Mk_ActiveBefore _ a , Mk_ActiveAfter _ b => GHC.Base.op_zl__ a b
      | Mk_ActiveAfter _ _ , Mk_AlwaysActive => false
      | Mk_ActiveAfter _ _ , Mk_ActiveBefore _ _ => false
      | Mk_ActiveAfter _ a , Mk_ActiveAfter _ b => GHC.Base.op_zgze__ a b
    end.

Local Definition instance_GHC_Base_Eq__Activation_op_zeze__
    : Activation -> Activation -> bool :=
  fun arg_358__ arg_359__ =>
    match arg_358__ , arg_359__ with
      | Mk_NeverActive , Mk_NeverActive => true
      | Mk_AlwaysActive , Mk_AlwaysActive => true
      | Mk_ActiveBefore a1 a2 , Mk_ActiveBefore b1 b2 => (andb ((GHC.Base.op_zeze__ a1
                                                                                    b1)) ((GHC.Base.op_zeze__ a2 b2)))
      | Mk_ActiveAfter a1 a2 , Mk_ActiveAfter b1 b2 => (andb ((GHC.Base.op_zeze__ a1
                                                                                  b1)) ((GHC.Base.op_zeze__ a2 b2)))
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__Activation_op_zsze__
    : Activation -> Activation -> bool :=
  fun arg_370__ arg_371__ =>
    match arg_370__ , arg_371__ with
      | a , b => negb (instance_GHC_Base_Eq__Activation_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__Activation : GHC.Base.Eq_ Activation := {
  op_zeze__ := instance_GHC_Base_Eq__Activation_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__Activation_op_zsze__ }.

Inductive InlinePragma : Type := Mk_InlinePragma
                                : SourceText -> InlineSpec -> option
                                  Arity -> Activation -> RuleMatchInfo -> InlinePragma.

Definition inl_act (arg_8__ : InlinePragma) :=
  match arg_8__ with
    | Mk_InlinePragma _ _ _ inl_act _ => inl_act
  end.

Definition inl_inline (arg_9__ : InlinePragma) :=
  match arg_9__ with
    | Mk_InlinePragma _ inl_inline _ _ _ => inl_inline
  end.

Definition inl_rule (arg_10__ : InlinePragma) :=
  match arg_10__ with
    | Mk_InlinePragma _ _ _ _ inl_rule => inl_rule
  end.

Definition inl_sat (arg_11__ : InlinePragma) :=
  match arg_11__ with
    | Mk_InlinePragma _ _ inl_sat _ _ => inl_sat
  end.

Definition inl_src (arg_12__ : InlinePragma) :=
  match arg_12__ with
    | Mk_InlinePragma inl_src _ _ _ _ => inl_src
  end.

Definition setInlinePragmaRuleMatchInfo
    : InlinePragma -> RuleMatchInfo -> InlinePragma :=
  fun arg_51__ arg_52__ =>
    match arg_51__ , arg_52__ with
      | prag , info => match prag with
                         | Mk_InlinePragma inl_src_53__ inl_inline_54__ inl_sat_55__ inl_act_56__
                                           inl_rule_57__ => Mk_InlinePragma inl_src_53__ inl_inline_54__ inl_sat_55__
                                                                            inl_act_56__ info
                       end
    end.

Definition setInlinePragmaActivation
    : InlinePragma -> Activation -> InlinePragma :=
  fun arg_62__ arg_63__ =>
    match arg_62__ , arg_63__ with
      | prag , activation => match prag with
                               | Mk_InlinePragma inl_src_64__ inl_inline_65__ inl_sat_66__ inl_act_67__
                                                 inl_rule_68__ => Mk_InlinePragma inl_src_64__ inl_inline_65__
                                                                                  inl_sat_66__ activation inl_rule_68__
                             end
    end.

Definition isInlinePragma : InlinePragma -> bool :=
  fun arg_87__ =>
    match arg_87__ with
      | prag => let scrut_88__ := inl_inline prag in
                match scrut_88__ with
                  | Mk_Inline => true
                  | _ => false
                end
    end.

Definition isInlinablePragma : InlinePragma -> bool :=
  fun arg_82__ =>
    match arg_82__ with
      | prag => let scrut_83__ := inl_inline prag in
                match scrut_83__ with
                  | Mk_Inlinable => true
                  | _ => false
                end
    end.

Definition isAnyInlinePragma : InlinePragma -> bool :=
  fun arg_77__ =>
    match arg_77__ with
      | prag => let scrut_78__ := inl_inline prag in
                match scrut_78__ with
                  | Mk_Inline => true
                  | Mk_Inlinable => true
                  | _ => false
                end
    end.

Definition isDefaultInlinePragma : InlinePragma -> bool :=
  fun arg_121__ =>
    match arg_121__ with
      | Mk_InlinePragma _ inline _ activation match_info => andb (isEmptyInlineSpec
                                                                 inline) (andb (isAlwaysActive activation) (isFunLike
                                                                               match_info))
    end.

Definition inlinePragmaSpec : InlinePragma -> InlineSpec :=
  inl_inline.

Definition inlinePragmaSat : InlinePragma -> option Arity :=
  inl_sat.

Definition inlinePragmaRuleMatchInfo : InlinePragma -> RuleMatchInfo :=
  fun arg_73__ => match arg_73__ with | Mk_InlinePragma _ _ _ _ info => info end.

Definition inlinePragmaActivation : InlinePragma -> Activation :=
  fun arg_75__ =>
    match arg_75__ with
      | Mk_InlinePragma _ _ _ activation _ => activation
    end.

Definition defaultInlinePragma : InlinePragma :=
  Mk_InlinePragma (GHC.Base.hs_string__ "{-# INLINE") Mk_EmptyInlineSpec None
                  Mk_AlwaysActive Mk_FunLike.

Definition dfunInlinePragma : InlinePragma :=
  match defaultInlinePragma with
    | Mk_InlinePragma inl_src_109__ inl_inline_110__ inl_sat_111__ inl_act_112__
                      inl_rule_113__ => Mk_InlinePragma inl_src_109__ inl_inline_110__ inl_sat_111__
                                                        Mk_AlwaysActive Mk_ConLike
  end.

Definition neverInlinePragma : InlinePragma :=
  match defaultInlinePragma with
    | Mk_InlinePragma inl_src_101__ inl_inline_102__ inl_sat_103__ inl_act_104__
                      inl_rule_105__ => Mk_InlinePragma inl_src_101__ inl_inline_102__ inl_sat_103__
                                                        Mk_NeverActive inl_rule_105__
  end.

Definition alwaysInlinePragma : InlinePragma :=
  match defaultInlinePragma with
    | Mk_InlinePragma inl_src_93__ inl_inline_94__ inl_sat_95__ inl_act_96__
                      inl_rule_97__ => Mk_InlinePragma inl_src_93__ Mk_Inline inl_sat_95__
                                                       inl_act_96__ inl_rule_97__
  end.

Local Definition instance_GHC_Base_Eq__InlinePragma_op_zeze__
    : InlinePragma -> InlinePragma -> bool :=
  fun arg_381__ arg_382__ =>
    match arg_381__ , arg_382__ with
      | Mk_InlinePragma a1 a2 a3 a4 a5 , Mk_InlinePragma b1 b2 b3 b4 b5 => (andb (andb
                                                                                 (andb (andb ((GHC.Base.op_zeze__ a1
                                                                                                                  b1))
                                                                                             ((GHC.Base.op_zeze__ a2
                                                                                                                  b2)))
                                                                                       ((GHC.Base.op_zeze__ a3 b3)))
                                                                                 ((GHC.Base.op_zeze__ a4 b4)))
                                                                                 ((GHC.Base.op_zeze__ a5 b5)))
    end.

Local Definition instance_GHC_Base_Eq__InlinePragma_op_zsze__
    : InlinePragma -> InlinePragma -> bool :=
  fun arg_370__ arg_371__ =>
    match arg_370__ , arg_371__ with
      | a , b => negb (instance_GHC_Base_Eq__InlinePragma_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__InlinePragma : GHC.Base.Eq_ InlinePragma := {
  op_zeze__ := instance_GHC_Base_Eq__InlinePragma_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__InlinePragma_op_zsze__ }.

Inductive SuccessFlag : Type := Mk_Succeeded : SuccessFlag
                             |  Mk_Failed : SuccessFlag.

Definition successIf : bool -> SuccessFlag :=
  fun arg_130__ =>
    match arg_130__ with
      | true => Mk_Succeeded
      | false => Mk_Failed
    end.

Definition succeeded : SuccessFlag -> bool :=
  fun arg_128__ =>
    match arg_128__ with
      | Mk_Succeeded => true
      | Mk_Failed => false
    end.

Definition failed : SuccessFlag -> bool :=
  fun arg_126__ =>
    match arg_126__ with
      | Mk_Succeeded => false
      | Mk_Failed => true
    end.

Inductive SwapFlag : Type := Mk_NotSwapped : SwapFlag
                          |  Mk_IsSwapped : SwapFlag.

Definition unSwap {a} {b} : SwapFlag -> (a -> a -> b) -> a -> a -> b :=
  fun arg_204__ arg_205__ arg_206__ arg_207__ =>
    match arg_204__ , arg_205__ , arg_206__ , arg_207__ with
      | Mk_NotSwapped , f , a , b => f a b
      | Mk_IsSwapped , f , a , b => f b a
    end.

Definition isSwapped : SwapFlag -> bool :=
  fun arg_211__ =>
    match arg_211__ with
      | Mk_IsSwapped => true
      | Mk_NotSwapped => false
    end.

Definition flipSwap : SwapFlag -> SwapFlag :=
  fun arg_213__ =>
    match arg_213__ with
      | Mk_IsSwapped => Mk_NotSwapped
      | Mk_NotSwapped => Mk_IsSwapped
    end.

Inductive TopLevelFlag : Type := Mk_TopLevel : TopLevelFlag
                              |  Mk_NotTopLevel : TopLevelFlag.

Definition isTopLevel : TopLevelFlag -> bool :=
  fun arg_179__ =>
    match arg_179__ with
      | Mk_TopLevel => true
      | Mk_NotTopLevel => false
    end.

Definition isNotTopLevel : TopLevelFlag -> bool :=
  fun arg_181__ =>
    match arg_181__ with
      | Mk_NotTopLevel => true
      | Mk_TopLevel => false
    end.

Inductive TupleSort : Type := Mk_BoxedTuple : TupleSort
                           |  Mk_UnboxedTuple : TupleSort
                           |  Mk_ConstraintTuple : TupleSort.

Definition tupleSortBoxity : TupleSort -> Boxity :=
  fun arg_151__ =>
    match arg_151__ with
      | Mk_BoxedTuple => Mk_Boxed
      | Mk_UnboxedTuple => Mk_Unboxed
      | Mk_ConstraintTuple => Mk_Boxed
    end.

Definition boxityTupleSort : Boxity -> TupleSort :=
  fun arg_149__ =>
    match arg_149__ with
      | Mk_Boxed => Mk_BoxedTuple
      | Mk_Unboxed => Mk_UnboxedTuple
    end.

Local Definition instance_GHC_Base_Eq__TupleSort_op_zeze__
    : TupleSort -> TupleSort -> bool :=
  fun arg_313__ arg_314__ =>
    match arg_313__ , arg_314__ with
      | Mk_BoxedTuple , Mk_BoxedTuple => true
      | Mk_UnboxedTuple , Mk_UnboxedTuple => true
      | Mk_ConstraintTuple , Mk_ConstraintTuple => true
      | _ , _ => false
    end.

Local Definition instance_GHC_Base_Eq__TupleSort_op_zsze__
    : TupleSort -> TupleSort -> bool :=
  fun arg_370__ arg_371__ =>
    match arg_370__ , arg_371__ with
      | a , b => negb (instance_GHC_Base_Eq__TupleSort_op_zeze__ a b)
    end.

Instance instance_GHC_Base_Eq__TupleSort : GHC.Base.Eq_ TupleSort := {
  op_zeze__ := instance_GHC_Base_Eq__TupleSort_op_zeze__ ;
  op_zsze__ := instance_GHC_Base_Eq__TupleSort_op_zsze__ }.

Definition Version :=
  GHC.Num.Int%type.

Definition initialVersion : Version :=
  GHC.Num.fromInteger 1.

Definition bumpVersion : Version -> Version :=
  fun arg_201__ =>
    match arg_201__ with
      | v => GHC.Num.op_zp__ v (GHC.Num.fromInteger 1)
    end.

(* Unbound variables:
     * == Data.Function.on Eq FastString.FastString GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.String GHC.Base.compare GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Num.Int
     GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.seq GHC.Real.Rational GHC.Show.show Gt
     Lt None Some SrcLoc.Located andb bool comparison false list negb op_zeze__
     op_zsze__ option pair true tt unit
*)
