(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Function.
Require Datatypes.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Require Panic.
Require SrcLoc.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Version :=
  GHC.Num.Int%type.

Inductive TyPrec : Type
  := | TopPrec : TyPrec
  |  FunPrec : TyPrec
  |  TyOpPrec : TyPrec
  |  TyConPrec : TyPrec.

Inductive TupleSort : Type
  := | BoxedTuple : TupleSort
  |  UnboxedTuple : TupleSort
  |  ConstraintTuple : TupleSort.

Inductive TopLevelFlag : Type
  := | TopLevel : TopLevelFlag
  |  NotTopLevel : TopLevelFlag.

Inductive SwapFlag : Type := | NotSwapped : SwapFlag |  IsSwapped : SwapFlag.

Inductive SuccessFlag : Type
  := | Succeeded : SuccessFlag
  |  Failed : SuccessFlag.

Inductive SpliceExplicitFlag : Type
  := | ExplicitSplice : SpliceExplicitFlag
  |  ImplicitSplice : SpliceExplicitFlag.

Inductive SourceText : Type
  := | Mk_SourceText : GHC.Base.String -> SourceText
  |  NoSourceText : SourceText.

Inductive StringLiteral : Type
  := | Mk_StringLiteral (sl_st : SourceText) (sl_fs : FastString.FastString)
   : StringLiteral.

Inductive WarningTxt : Type
  := | Mk_WarningTxt
   : (SrcLoc.Located SourceText) ->
     list (SrcLoc.Located StringLiteral) -> WarningTxt
  |  DeprecatedTxt
   : (SrcLoc.Located SourceText) ->
     list (SrcLoc.Located StringLiteral) -> WarningTxt.

Definition RulesOnly :=
  bool%type.

Definition RuleName :=
  FastString.FastString%type.

Inductive RuleMatchInfo : Type
  := | ConLike : RuleMatchInfo
  |  FunLike : RuleMatchInfo.

Definition RepArity :=
  nat.

Inductive RecFlag : Type := | Recursive : RecFlag |  NonRecursive : RecFlag.

Definition PhaseNum :=
  nat.

Inductive OverlapMode : Type
  := | NoOverlap : SourceText -> OverlapMode
  |  Overlappable : SourceText -> OverlapMode
  |  Overlapping : SourceText -> OverlapMode
  |  Overlaps : SourceText -> OverlapMode
  |  Incoherent : SourceText -> OverlapMode.

Inductive OverlapFlag : Type
  := | Mk_OverlapFlag (overlapMode : OverlapMode) (isSafeOverlap : bool)
   : OverlapFlag.

Inductive Origin : Type := | FromSource : Origin |  Generated : Origin.

Inductive OneShotInfo : Type
  := | NoOneShotInfo : OneShotInfo
  |  OneShotLam : OneShotInfo.

Definition OneBranch :=
  bool%type.

Inductive LexicalFixity : Type
  := | Prefix : LexicalFixity
  |  Infix : LexicalFixity.

Inductive LeftOrRight : Type := | CLeft : LeftOrRight |  CRight : LeftOrRight.

Definition JoinArity :=
  nat.

Inductive TailCallInfo : Type
  := | AlwaysTailCalled : JoinArity -> TailCallInfo
  |  NoTailCallInfo : TailCallInfo.

Definition InterestingCxt :=
  bool%type.

Inductive IntegralLit : Type
  := | IL (il_text : SourceText) (il_neg : bool) (il_value : GHC.Num.Integer)
   : IntegralLit.

Inductive IntWithInf : Type
  := | Int : GHC.Num.Int -> IntWithInf
  |  Infinity : IntWithInf.

Definition InsideLam :=
  bool%type.

Inductive OccInfo : Type
  := | ManyOccs (occ_tail : TailCallInfo) : OccInfo
  |  IAmDead : OccInfo
  |  OneOcc (occ_in_lam : InsideLam) (occ_one_br : OneBranch) (occ_int_cxt
    : InterestingCxt) (occ_tail : TailCallInfo)
   : OccInfo
  |  IAmALoopBreaker (occ_rules_only : RulesOnly) (occ_tail : TailCallInfo)
   : OccInfo.

Inductive InlineSpec : Type
  := | Inline : InlineSpec
  |  Inlinable : InlineSpec
  |  NoInline : InlineSpec
  |  NoUserInline : InlineSpec.

Inductive FunctionOrData : Type
  := | IsFunction : FunctionOrData
  |  IsData : FunctionOrData.

Inductive FractionalLit : Type
  := | FL (fl_text : SourceText) (fl_neg : bool) (fl_value : GHC.Real.Rational)
   : FractionalLit.

Inductive FixityDirection : Type
  := | InfixL : FixityDirection
  |  InfixR : FixityDirection
  |  InfixN : FixityDirection.

Inductive Fixity : Type
  := | Mk_Fixity : SourceText -> GHC.Num.Int -> FixityDirection -> Fixity.

Inductive EP a : Type := | Mk_EP (fromEP : a) (toEP : a) : EP a.

Inductive DerivStrategy : Type
  := | StockStrategy : DerivStrategy
  |  AnyclassStrategy : DerivStrategy
  |  NewtypeStrategy : DerivStrategy.

Inductive DefMethSpec ty : Type
  := | VanillaDM : DefMethSpec ty
  |  GenericDM : ty -> DefMethSpec ty.

Definition ConTagZ :=
  GHC.Num.Int%type.

Definition ConTag :=
  GHC.Num.Int%type.

Inductive CompilerPhase : Type
  := | Phase : PhaseNum -> CompilerPhase
  |  InitialPhase : CompilerPhase.

Inductive Boxity : Type := | Boxed : Boxity |  Unboxed : Boxity.

Definition Arity :=
  nat.

Definition Alignment :=
  GHC.Num.Int%type.

Inductive Activation : Type
  := | NeverActive : Activation
  |  AlwaysActive : Activation
  |  ActiveBefore : SourceText -> PhaseNum -> Activation
  |  ActiveAfter : SourceText -> PhaseNum -> Activation.

Inductive InlinePragma : Type
  := | Mk_InlinePragma (inl_src : SourceText) (inl_inline : InlineSpec) (inl_sat
    : option Arity) (inl_act : Activation) (inl_rule : RuleMatchInfo)
   : InlinePragma.

Arguments Mk_EP {_} _ _.

Arguments VanillaDM {_}.

Arguments GenericDM {_} _.

Instance Default__TyPrec : GHC.Err.Default TyPrec :=
  GHC.Err.Build_Default _ TopPrec.

Instance Default__TupleSort : GHC.Err.Default TupleSort :=
  GHC.Err.Build_Default _ BoxedTuple.

Instance Default__TopLevelFlag : GHC.Err.Default TopLevelFlag :=
  GHC.Err.Build_Default _ TopLevel.

Instance Default__SwapFlag : GHC.Err.Default SwapFlag :=
  GHC.Err.Build_Default _ NotSwapped.

Instance Default__SuccessFlag : GHC.Err.Default SuccessFlag :=
  GHC.Err.Build_Default _ Succeeded.

Instance Default__SpliceExplicitFlag : GHC.Err.Default SpliceExplicitFlag :=
  GHC.Err.Build_Default _ ExplicitSplice.

Instance Default__SourceText : GHC.Err.Default SourceText :=
  GHC.Err.Build_Default _ NoSourceText.

Instance Default__StringLiteral : GHC.Err.Default StringLiteral :=
  GHC.Err.Build_Default _ (Mk_StringLiteral GHC.Err.default GHC.Err.default).

Instance Default__RuleMatchInfo : GHC.Err.Default RuleMatchInfo :=
  GHC.Err.Build_Default _ ConLike.

Instance Default__RecFlag : GHC.Err.Default RecFlag :=
  GHC.Err.Build_Default _ Recursive.

Instance Default__Origin : GHC.Err.Default Origin :=
  GHC.Err.Build_Default _ FromSource.

Instance Default__OneShotInfo : GHC.Err.Default OneShotInfo :=
  GHC.Err.Build_Default _ NoOneShotInfo.

Instance Default__LexicalFixity : GHC.Err.Default LexicalFixity :=
  GHC.Err.Build_Default _ Prefix.

Instance Default__LeftOrRight : GHC.Err.Default LeftOrRight :=
  GHC.Err.Build_Default _ CLeft.

Instance Default__TailCallInfo : GHC.Err.Default TailCallInfo :=
  GHC.Err.Build_Default _ NoTailCallInfo.

Instance Default__IntegralLit : GHC.Err.Default IntegralLit :=
  GHC.Err.Build_Default _ (IL GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default__IntWithInf : GHC.Err.Default IntWithInf :=
  GHC.Err.Build_Default _ Infinity.

Instance Default__OccInfo : GHC.Err.Default OccInfo :=
  GHC.Err.Build_Default _ (ManyOccs GHC.Err.default).

Instance Default__InlineSpec : GHC.Err.Default InlineSpec :=
  GHC.Err.Build_Default _ Inline.

Instance Default__FunctionOrData : GHC.Err.Default FunctionOrData :=
  GHC.Err.Build_Default _ IsFunction.

Instance Default__FractionalLit : GHC.Err.Default FractionalLit :=
  GHC.Err.Build_Default _ (FL GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default__FixityDirection : GHC.Err.Default FixityDirection :=
  GHC.Err.Build_Default _ InfixL.

Instance Default__DerivStrategy : GHC.Err.Default DerivStrategy :=
  GHC.Err.Build_Default _ StockStrategy.

Instance Default__CompilerPhase : GHC.Err.Default CompilerPhase :=
  GHC.Err.Build_Default _ InitialPhase.

Instance Default__Boxity : GHC.Err.Default Boxity :=
  GHC.Err.Build_Default _ Boxed.

Instance Default__Activation : GHC.Err.Default Activation :=
  GHC.Err.Build_Default _ NeverActive.

Definition sl_fs (arg_0__ : StringLiteral) :=
  let 'Mk_StringLiteral _ sl_fs := arg_0__ in
  sl_fs.

Definition sl_st (arg_0__ : StringLiteral) :=
  let 'Mk_StringLiteral sl_st _ := arg_0__ in
  sl_st.

Definition isSafeOverlap (arg_0__ : OverlapFlag) :=
  let 'Mk_OverlapFlag _ isSafeOverlap := arg_0__ in
  isSafeOverlap.

Definition overlapMode (arg_0__ : OverlapFlag) :=
  let 'Mk_OverlapFlag overlapMode _ := arg_0__ in
  overlapMode.

Definition il_neg (arg_0__ : IntegralLit) :=
  let 'IL _ il_neg _ := arg_0__ in
  il_neg.

Definition il_text (arg_0__ : IntegralLit) :=
  let 'IL il_text _ _ := arg_0__ in
  il_text.

Definition il_value (arg_0__ : IntegralLit) :=
  let 'IL _ _ il_value := arg_0__ in
  il_value.

Definition occ_in_lam (arg_0__ : OccInfo) :=
  match arg_0__ with
  | ManyOccs _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_in_lam' has no match in constructor `ManyOccs' of type `OccInfo'")
  | IAmDead =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_in_lam' has no match in constructor `IAmDead' of type `OccInfo'")
  | OneOcc occ_in_lam _ _ _ => occ_in_lam
  | IAmALoopBreaker _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_in_lam' has no match in constructor `IAmALoopBreaker' of type `OccInfo'")
  end.

Definition occ_int_cxt (arg_0__ : OccInfo) :=
  match arg_0__ with
  | ManyOccs _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_int_cxt' has no match in constructor `ManyOccs' of type `OccInfo'")
  | IAmDead =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_int_cxt' has no match in constructor `IAmDead' of type `OccInfo'")
  | OneOcc _ _ occ_int_cxt _ => occ_int_cxt
  | IAmALoopBreaker _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_int_cxt' has no match in constructor `IAmALoopBreaker' of type `OccInfo'")
  end.

Definition occ_one_br (arg_0__ : OccInfo) :=
  match arg_0__ with
  | ManyOccs _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_one_br' has no match in constructor `ManyOccs' of type `OccInfo'")
  | IAmDead =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_one_br' has no match in constructor `IAmDead' of type `OccInfo'")
  | OneOcc _ occ_one_br _ _ => occ_one_br
  | IAmALoopBreaker _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_one_br' has no match in constructor `IAmALoopBreaker' of type `OccInfo'")
  end.

Definition occ_rules_only (arg_0__ : OccInfo) :=
  match arg_0__ with
  | ManyOccs _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_rules_only' has no match in constructor `ManyOccs' of type `OccInfo'")
  | IAmDead =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_rules_only' has no match in constructor `IAmDead' of type `OccInfo'")
  | OneOcc _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_rules_only' has no match in constructor `OneOcc' of type `OccInfo'")
  | IAmALoopBreaker occ_rules_only _ => occ_rules_only
  end.

Definition occ_tail (arg_0__ : OccInfo) :=
  match arg_0__ with
  | ManyOccs occ_tail => occ_tail
  | IAmDead =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `occ_tail' has no match in constructor `IAmDead' of type `OccInfo'")
  | OneOcc _ _ _ occ_tail => occ_tail
  | IAmALoopBreaker _ occ_tail => occ_tail
  end.

Definition fl_neg (arg_0__ : FractionalLit) :=
  let 'FL _ fl_neg _ := arg_0__ in
  fl_neg.

Definition fl_text (arg_0__ : FractionalLit) :=
  let 'FL fl_text _ _ := arg_0__ in
  fl_text.

Definition fl_value (arg_0__ : FractionalLit) :=
  let 'FL _ _ fl_value := arg_0__ in
  fl_value.

Definition fromEP {a} (arg_0__ : EP a) :=
  let 'Mk_EP fromEP _ := arg_0__ in
  fromEP.

Definition toEP {a} (arg_0__ : EP a) :=
  let 'Mk_EP _ toEP := arg_0__ in
  toEP.

Definition inl_act (arg_0__ : InlinePragma) :=
  let 'Mk_InlinePragma _ _ _ inl_act _ := arg_0__ in
  inl_act.

Definition inl_inline (arg_0__ : InlinePragma) :=
  let 'Mk_InlinePragma _ inl_inline _ _ _ := arg_0__ in
  inl_inline.

Definition inl_rule (arg_0__ : InlinePragma) :=
  let 'Mk_InlinePragma _ _ _ _ inl_rule := arg_0__ in
  inl_rule.

Definition inl_sat (arg_0__ : InlinePragma) :=
  let 'Mk_InlinePragma _ _ inl_sat _ _ := arg_0__ in
  inl_sat.

Definition inl_src (arg_0__ : InlinePragma) :=
  let 'Mk_InlinePragma inl_src _ _ _ _ := arg_0__ in
  inl_src.

(* Midamble *)

Require GHC.Err.

Instance Default__OverlapMode : GHC.Err.Default OverlapMode :=
  GHC.Err.Build_Default _ (NoOverlap GHC.Err.default).
Instance Default__OverlapFlag : GHC.Err.Default OverlapFlag :=
  GHC.Err.Build_Default _ (Mk_OverlapFlag GHC.Err.default GHC.Err.default).
Instance Default__Fixity : GHC.Err.Default Fixity :=
  GHC.Err.Build_Default _ (Mk_Fixity GHC.Err.default GHC.Err.default GHC.Err.default).
Instance Default__InlinePragma : GHC.Err.Default InlinePragma :=
  GHC.Err.Build_Default _ (Mk_InlinePragma GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

(* Converted value declarations: *)

Local Definition Eq___LeftOrRight_op_zeze__
   : LeftOrRight -> LeftOrRight -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CLeft, CLeft => true
    | CRight, CRight => true
    | _, _ => false
    end.

Local Definition Eq___LeftOrRight_op_zsze__
   : LeftOrRight -> LeftOrRight -> bool :=
  fun x y => negb (Eq___LeftOrRight_op_zeze__ x y).

Program Instance Eq___LeftOrRight : GHC.Base.Eq_ LeftOrRight :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___LeftOrRight_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___LeftOrRight_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__LeftOrRight' *)

Local Definition Eq___OneShotInfo_op_zeze__
   : OneShotInfo -> OneShotInfo -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoOneShotInfo, NoOneShotInfo => true
    | OneShotLam, OneShotLam => true
    | _, _ => false
    end.

Local Definition Eq___OneShotInfo_op_zsze__
   : OneShotInfo -> OneShotInfo -> bool :=
  fun x y => negb (Eq___OneShotInfo_op_zeze__ x y).

Program Instance Eq___OneShotInfo : GHC.Base.Eq_ OneShotInfo :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___OneShotInfo_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___OneShotInfo_op_zsze__ |}.

Local Definition Eq___FunctionOrData_op_zeze__
   : FunctionOrData -> FunctionOrData -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | IsFunction, IsFunction => true
    | IsData, IsData => true
    | _, _ => false
    end.

Local Definition Eq___FunctionOrData_op_zsze__
   : FunctionOrData -> FunctionOrData -> bool :=
  fun x y => negb (Eq___FunctionOrData_op_zeze__ x y).

Program Instance Eq___FunctionOrData : GHC.Base.Eq_ FunctionOrData :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___FunctionOrData_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___FunctionOrData_op_zsze__ |}.

Local Definition Ord__FunctionOrData_op_zl__
   : FunctionOrData -> FunctionOrData -> bool :=
  fun a b =>
    match a with
    | IsFunction => match b with | IsFunction => false | _ => true end
    | IsData => match b with | IsData => false | _ => false end
    end.

Local Definition Ord__FunctionOrData_op_zlze__
   : FunctionOrData -> FunctionOrData -> bool :=
  fun a b => negb (Ord__FunctionOrData_op_zl__ b a).

Local Definition Ord__FunctionOrData_op_zg__
   : FunctionOrData -> FunctionOrData -> bool :=
  fun a b => Ord__FunctionOrData_op_zl__ b a.

Local Definition Ord__FunctionOrData_op_zgze__
   : FunctionOrData -> FunctionOrData -> bool :=
  fun a b => negb (Ord__FunctionOrData_op_zl__ a b).

Local Definition Ord__FunctionOrData_compare
   : FunctionOrData -> FunctionOrData -> comparison :=
  fun a b =>
    match a with
    | IsFunction => match b with | IsFunction => Eq | _ => Lt end
    | IsData => match b with | IsData => Eq | _ => Gt end
    end.

Local Definition Ord__FunctionOrData_max
   : FunctionOrData -> FunctionOrData -> FunctionOrData :=
  fun x y => if Ord__FunctionOrData_op_zlze__ x y : bool then y else x.

Local Definition Ord__FunctionOrData_min
   : FunctionOrData -> FunctionOrData -> FunctionOrData :=
  fun x y => if Ord__FunctionOrData_op_zlze__ x y : bool then x else y.

Program Instance Ord__FunctionOrData : GHC.Base.Ord FunctionOrData :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__FunctionOrData_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__FunctionOrData_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__FunctionOrData_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__FunctionOrData_op_zgze__ ;
           GHC.Base.compare__ := Ord__FunctionOrData_compare ;
           GHC.Base.max__ := Ord__FunctionOrData_max ;
           GHC.Base.min__ := Ord__FunctionOrData_min |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__FunctionOrData' *)

Local Definition Eq___FixityDirection_op_zeze__
   : FixityDirection -> FixityDirection -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InfixL, InfixL => true
    | InfixR, InfixR => true
    | InfixN, InfixN => true
    | _, _ => false
    end.

Local Definition Eq___FixityDirection_op_zsze__
   : FixityDirection -> FixityDirection -> bool :=
  fun x y => negb (Eq___FixityDirection_op_zeze__ x y).

Program Instance Eq___FixityDirection : GHC.Base.Eq_ FixityDirection :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___FixityDirection_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___FixityDirection_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__FixityDirection' *)

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__LexicalFixity' *)

Local Definition Eq___LexicalFixity_op_zeze__
   : LexicalFixity -> LexicalFixity -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Prefix, Prefix => true
    | Infix, Infix => true
    | _, _ => false
    end.

Local Definition Eq___LexicalFixity_op_zsze__
   : LexicalFixity -> LexicalFixity -> bool :=
  fun x y => negb (Eq___LexicalFixity_op_zeze__ x y).

Program Instance Eq___LexicalFixity : GHC.Base.Eq_ LexicalFixity :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___LexicalFixity_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___LexicalFixity_op_zsze__ |}.

Local Definition Eq___Boxity_op_zeze__ : Boxity -> Boxity -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Boxed, Boxed => true
    | Unboxed, Unboxed => true
    | _, _ => false
    end.

Local Definition Eq___Boxity_op_zsze__ : Boxity -> Boxity -> bool :=
  fun x y => negb (Eq___Boxity_op_zeze__ x y).

Program Instance Eq___Boxity : GHC.Base.Eq_ Boxity :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Boxity_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Boxity_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__Boxity' *)

Local Definition Eq___RecFlag_op_zeze__ : RecFlag -> RecFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Recursive, Recursive => true
    | NonRecursive, NonRecursive => true
    | _, _ => false
    end.

Local Definition Eq___RecFlag_op_zsze__ : RecFlag -> RecFlag -> bool :=
  fun x y => negb (Eq___RecFlag_op_zeze__ x y).

Program Instance Eq___RecFlag : GHC.Base.Eq_ RecFlag :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___RecFlag_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___RecFlag_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__RecFlag' *)

Local Definition Eq___Origin_op_zeze__ : Origin -> Origin -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FromSource, FromSource => true
    | Generated, Generated => true
    | _, _ => false
    end.

Local Definition Eq___Origin_op_zsze__ : Origin -> Origin -> bool :=
  fun x y => negb (Eq___Origin_op_zeze__ x y).

Program Instance Eq___Origin : GHC.Base.Eq_ Origin :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Origin_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Origin_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__Origin' *)

Local Definition Eq___DerivStrategy_op_zeze__
   : DerivStrategy -> DerivStrategy -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | StockStrategy, StockStrategy => true
    | AnyclassStrategy, AnyclassStrategy => true
    | NewtypeStrategy, NewtypeStrategy => true
    | _, _ => false
    end.

Local Definition Eq___DerivStrategy_op_zsze__
   : DerivStrategy -> DerivStrategy -> bool :=
  fun x y => negb (Eq___DerivStrategy_op_zeze__ x y).

Program Instance Eq___DerivStrategy : GHC.Base.Eq_ DerivStrategy :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___DerivStrategy_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___DerivStrategy_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__DerivStrategy' *)

Local Definition Eq___TupleSort_op_zeze__ : TupleSort -> TupleSort -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | BoxedTuple, BoxedTuple => true
    | UnboxedTuple, UnboxedTuple => true
    | ConstraintTuple, ConstraintTuple => true
    | _, _ => false
    end.

Local Definition Eq___TupleSort_op_zsze__ : TupleSort -> TupleSort -> bool :=
  fun x y => negb (Eq___TupleSort_op_zeze__ x y).

Program Instance Eq___TupleSort : GHC.Base.Eq_ TupleSort :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TupleSort_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TupleSort_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__TupleSort' *)

Local Definition Eq___TailCallInfo_op_zeze__
   : TailCallInfo -> TailCallInfo -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | AlwaysTailCalled a1, AlwaysTailCalled b1 => ((a1 GHC.Base.== b1))
    | NoTailCallInfo, NoTailCallInfo => true
    | _, _ => false
    end.

Local Definition Eq___TailCallInfo_op_zsze__
   : TailCallInfo -> TailCallInfo -> bool :=
  fun x y => negb (Eq___TailCallInfo_op_zeze__ x y).

Program Instance Eq___TailCallInfo : GHC.Base.Eq_ TailCallInfo :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TailCallInfo_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TailCallInfo_op_zsze__ |}.

Local Definition Eq___OccInfo_op_zeze__ : OccInfo -> OccInfo -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | ManyOccs a1, ManyOccs b1 => ((a1 GHC.Base.== b1))
    | IAmDead, IAmDead => true
    | OneOcc a1 a2 a3 a4, OneOcc b1 b2 b3 b4 =>
        (andb (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.==
                      b3))) ((a4 GHC.Base.== b4)))
    | IAmALoopBreaker a1 a2, IAmALoopBreaker b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___OccInfo_op_zsze__ : OccInfo -> OccInfo -> bool :=
  fun x y => negb (Eq___OccInfo_op_zeze__ x y).

Program Instance Eq___OccInfo : GHC.Base.Eq_ OccInfo :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___OccInfo_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___OccInfo_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__SourceText' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `BasicTypes.Show__SourceText' *)

Local Definition Eq___SourceText_op_zeze__ : SourceText -> SourceText -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_SourceText a1, Mk_SourceText b1 => ((a1 GHC.Base.== b1))
    | NoSourceText, NoSourceText => true
    | _, _ => false
    end.

Local Definition Eq___SourceText_op_zsze__ : SourceText -> SourceText -> bool :=
  fun x y => negb (Eq___SourceText_op_zeze__ x y).

Program Instance Eq___SourceText : GHC.Base.Eq_ SourceText :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___SourceText_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___SourceText_op_zsze__ |}.

Local Definition Eq___OverlapMode_op_zeze__
   : OverlapMode -> OverlapMode -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoOverlap a1, NoOverlap b1 => ((a1 GHC.Base.== b1))
    | Overlappable a1, Overlappable b1 => ((a1 GHC.Base.== b1))
    | Overlapping a1, Overlapping b1 => ((a1 GHC.Base.== b1))
    | Overlaps a1, Overlaps b1 => ((a1 GHC.Base.== b1))
    | Incoherent a1, Incoherent b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___OverlapMode_op_zsze__
   : OverlapMode -> OverlapMode -> bool :=
  fun x y => negb (Eq___OverlapMode_op_zeze__ x y).

Program Instance Eq___OverlapMode : GHC.Base.Eq_ OverlapMode :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___OverlapMode_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___OverlapMode_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__OverlapMode' *)

Local Definition Eq___OverlapFlag_op_zeze__
   : OverlapFlag -> OverlapFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OverlapFlag a1 a2, Mk_OverlapFlag b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___OverlapFlag_op_zsze__
   : OverlapFlag -> OverlapFlag -> bool :=
  fun x y => negb (Eq___OverlapFlag_op_zeze__ x y).

Program Instance Eq___OverlapFlag : GHC.Base.Eq_ OverlapFlag :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___OverlapFlag_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___OverlapFlag_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__OverlapFlag' *)

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__Fixity' *)

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__StringLiteral' *)

Local Definition Eq___StringLiteral_op_zeze__
   : StringLiteral -> StringLiteral -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_StringLiteral _ a, Mk_StringLiteral _ b => a GHC.Base.== b
    end.

Local Definition Eq___StringLiteral_op_zsze__
   : StringLiteral -> StringLiteral -> bool :=
  fun x y => negb (Eq___StringLiteral_op_zeze__ x y).

Program Instance Eq___StringLiteral : GHC.Base.Eq_ StringLiteral :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___StringLiteral_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___StringLiteral_op_zsze__ |}.

Local Definition Eq___WarningTxt_op_zeze__ : WarningTxt -> WarningTxt -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_WarningTxt a1 a2, Mk_WarningTxt b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | DeprecatedTxt a1 a2, DeprecatedTxt b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___WarningTxt_op_zsze__ : WarningTxt -> WarningTxt -> bool :=
  fun x y => negb (Eq___WarningTxt_op_zeze__ x y).

Program Instance Eq___WarningTxt : GHC.Base.Eq_ WarningTxt :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___WarningTxt_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___WarningTxt_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__WarningTxt' *)

Local Definition Eq___Activation_op_zeze__ : Activation -> Activation -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NeverActive, NeverActive => true
    | AlwaysActive, AlwaysActive => true
    | ActiveBefore a1 a2, ActiveBefore b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | ActiveAfter a1 a2, ActiveAfter b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___Activation_op_zsze__ : Activation -> Activation -> bool :=
  fun x y => negb (Eq___Activation_op_zeze__ x y).

Program Instance Eq___Activation : GHC.Base.Eq_ Activation :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Activation_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Activation_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__Activation' *)

Local Definition Eq___RuleMatchInfo_op_zeze__
   : RuleMatchInfo -> RuleMatchInfo -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | ConLike, ConLike => true
    | FunLike, FunLike => true
    | _, _ => false
    end.

Local Definition Eq___RuleMatchInfo_op_zsze__
   : RuleMatchInfo -> RuleMatchInfo -> bool :=
  fun x y => negb (Eq___RuleMatchInfo_op_zeze__ x y).

Program Instance Eq___RuleMatchInfo : GHC.Base.Eq_ RuleMatchInfo :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___RuleMatchInfo_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___RuleMatchInfo_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__RuleMatchInfo' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `BasicTypes.Show__RuleMatchInfo' *)

Local Definition Eq___InlineSpec_op_zeze__ : InlineSpec -> InlineSpec -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Inline, Inline => true
    | Inlinable, Inlinable => true
    | NoInline, NoInline => true
    | NoUserInline, NoUserInline => true
    | _, _ => false
    end.

Local Definition Eq___InlineSpec_op_zsze__ : InlineSpec -> InlineSpec -> bool :=
  fun x y => negb (Eq___InlineSpec_op_zeze__ x y).

Program Instance Eq___InlineSpec : GHC.Base.Eq_ InlineSpec :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___InlineSpec_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___InlineSpec_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__InlineSpec' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `BasicTypes.Show__InlineSpec' *)

Local Definition Eq___InlinePragma_op_zeze__
   : InlinePragma -> InlinePragma -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_InlinePragma a1 a2 a3 a4 a5, Mk_InlinePragma b1 b2 b3 b4 b5 =>
        (andb (andb (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3
                            GHC.Base.==
                            b3))) ((a4 GHC.Base.== b4))) ((a5 GHC.Base.== b5)))
    end.

Local Definition Eq___InlinePragma_op_zsze__
   : InlinePragma -> InlinePragma -> bool :=
  fun x y => negb (Eq___InlinePragma_op_zeze__ x y).

Program Instance Eq___InlinePragma : GHC.Base.Eq_ InlinePragma :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___InlinePragma_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___InlinePragma_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__InlinePragma' *)

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__IntegralLit' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `BasicTypes.Show__IntegralLit' *)

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__FractionalLit' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `BasicTypes.Show__FractionalLit' *)

Local Definition Eq___IntWithInf_op_zeze__ : IntWithInf -> IntWithInf -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Int a1, Int b1 => ((a1 GHC.Base.== b1))
    | Infinity, Infinity => true
    | _, _ => false
    end.

Local Definition Eq___IntWithInf_op_zsze__ : IntWithInf -> IntWithInf -> bool :=
  fun x y => negb (Eq___IntWithInf_op_zeze__ x y).

Program Instance Eq___IntWithInf : GHC.Base.Eq_ IntWithInf :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___IntWithInf_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___IntWithInf_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `BasicTypes.Data__SpliceExplicitFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__LeftOrRight' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__OneShotInfo' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__SwapFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__FunctionOrData' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__StringLiteral' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__WarningTxt' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__Fixity' *)

Local Definition Eq___Fixity_op_zeze__ : Fixity -> Fixity -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Fixity _ p1 dir1, Mk_Fixity _ p2 dir2 =>
        andb (p1 GHC.Base.== p2) (dir1 GHC.Base.== dir2)
    end.

Local Definition Eq___Fixity_op_zsze__ : Fixity -> Fixity -> bool :=
  fun x y => negb (Eq___Fixity_op_zeze__ x y).

Program Instance Eq___Fixity : GHC.Base.Eq_ Fixity :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Fixity_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Fixity_op_zsze__ |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__FixityDirection' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__LexicalFixity' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__TopLevelFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__Boxity' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__RecFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__Origin' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__DerivStrategy' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__OverlapFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__OverlapMode' *)

(* Skipping instance `BasicTypes.Eq___TyPrec' of class `GHC.Base.Eq_' *)

(* Skipping instance `BasicTypes.Ord__TyPrec' of class `GHC.Base.Ord' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__TailCallInfo' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__OccInfo' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__DefMethSpec' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__SuccessFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__SourceText' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__CompilerPhase' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__Activation' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__RuleMatchInfo' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__InlineSpec' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__InlinePragma' *)

Local Definition Eq___IntegralLit_op_zeze__
   : IntegralLit -> IntegralLit -> bool :=
  Data.Function.on _GHC.Base.==_ il_value.

Local Definition Eq___IntegralLit_op_zsze__
   : IntegralLit -> IntegralLit -> bool :=
  fun x y => negb (Eq___IntegralLit_op_zeze__ x y).

Program Instance Eq___IntegralLit : GHC.Base.Eq_ IntegralLit :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___IntegralLit_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___IntegralLit_op_zsze__ |}.

Local Definition Ord__IntegralLit_compare
   : IntegralLit -> IntegralLit -> comparison :=
  Data.Function.on GHC.Base.compare il_value.

Local Definition Ord__IntegralLit_op_zl__
   : IntegralLit -> IntegralLit -> bool :=
  fun x y => Ord__IntegralLit_compare x y GHC.Base.== Lt.

Local Definition Ord__IntegralLit_op_zlze__
   : IntegralLit -> IntegralLit -> bool :=
  fun x y => Ord__IntegralLit_compare x y GHC.Base./= Gt.

Local Definition Ord__IntegralLit_op_zg__
   : IntegralLit -> IntegralLit -> bool :=
  fun x y => Ord__IntegralLit_compare x y GHC.Base.== Gt.

Local Definition Ord__IntegralLit_op_zgze__
   : IntegralLit -> IntegralLit -> bool :=
  fun x y => Ord__IntegralLit_compare x y GHC.Base./= Lt.

Local Definition Ord__IntegralLit_max
   : IntegralLit -> IntegralLit -> IntegralLit :=
  fun x y => if Ord__IntegralLit_op_zlze__ x y : bool then y else x.

Local Definition Ord__IntegralLit_min
   : IntegralLit -> IntegralLit -> IntegralLit :=
  fun x y => if Ord__IntegralLit_op_zlze__ x y : bool then x else y.

Program Instance Ord__IntegralLit : GHC.Base.Ord IntegralLit :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__IntegralLit_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__IntegralLit_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__IntegralLit_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__IntegralLit_op_zgze__ ;
           GHC.Base.compare__ := Ord__IntegralLit_compare ;
           GHC.Base.max__ := Ord__IntegralLit_max ;
           GHC.Base.min__ := Ord__IntegralLit_min |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__IntegralLit' *)

Local Definition Eq___FractionalLit_op_zeze__
   : FractionalLit -> FractionalLit -> bool :=
  Data.Function.on _GHC.Base.==_ fl_value.

Local Definition Eq___FractionalLit_op_zsze__
   : FractionalLit -> FractionalLit -> bool :=
  fun x y => negb (Eq___FractionalLit_op_zeze__ x y).

Program Instance Eq___FractionalLit : GHC.Base.Eq_ FractionalLit :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___FractionalLit_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___FractionalLit_op_zsze__ |}.

Local Definition Ord__FractionalLit_compare
   : FractionalLit -> FractionalLit -> comparison :=
  Data.Function.on GHC.Base.compare fl_value.

Local Definition Ord__FractionalLit_op_zl__
   : FractionalLit -> FractionalLit -> bool :=
  fun x y => Ord__FractionalLit_compare x y GHC.Base.== Lt.

Local Definition Ord__FractionalLit_op_zlze__
   : FractionalLit -> FractionalLit -> bool :=
  fun x y => Ord__FractionalLit_compare x y GHC.Base./= Gt.

Local Definition Ord__FractionalLit_op_zg__
   : FractionalLit -> FractionalLit -> bool :=
  fun x y => Ord__FractionalLit_compare x y GHC.Base.== Gt.

Local Definition Ord__FractionalLit_op_zgze__
   : FractionalLit -> FractionalLit -> bool :=
  fun x y => Ord__FractionalLit_compare x y GHC.Base./= Lt.

Local Definition Ord__FractionalLit_max
   : FractionalLit -> FractionalLit -> FractionalLit :=
  fun x y => if Ord__FractionalLit_op_zlze__ x y : bool then y else x.

Local Definition Ord__FractionalLit_min
   : FractionalLit -> FractionalLit -> FractionalLit :=
  fun x y => if Ord__FractionalLit_op_zlze__ x y : bool then x else y.

Program Instance Ord__FractionalLit : GHC.Base.Ord FractionalLit :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__FractionalLit_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__FractionalLit_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__FractionalLit_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__FractionalLit_op_zgze__ ;
           GHC.Base.compare__ := Ord__FractionalLit_compare ;
           GHC.Base.max__ := Ord__FractionalLit_max ;
           GHC.Base.min__ := Ord__FractionalLit_min |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__FractionalLit' *)

Local Definition Ord__IntWithInf_compare
   : IntWithInf -> IntWithInf -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Infinity, Infinity => Eq
    | Int _, Infinity => Lt
    | Infinity, Int _ => Gt
    | Int a, Int b => GHC.Base.compare a b
    end.

Local Definition Ord__IntWithInf_op_zl__ : IntWithInf -> IntWithInf -> bool :=
  fun x y => Ord__IntWithInf_compare x y GHC.Base.== Lt.

Local Definition Ord__IntWithInf_op_zlze__ : IntWithInf -> IntWithInf -> bool :=
  fun x y => Ord__IntWithInf_compare x y GHC.Base./= Gt.

Local Definition Ord__IntWithInf_op_zg__ : IntWithInf -> IntWithInf -> bool :=
  fun x y => Ord__IntWithInf_compare x y GHC.Base.== Gt.

Local Definition Ord__IntWithInf_op_zgze__ : IntWithInf -> IntWithInf -> bool :=
  fun x y => Ord__IntWithInf_compare x y GHC.Base./= Lt.

Local Definition Ord__IntWithInf_max : IntWithInf -> IntWithInf -> IntWithInf :=
  fun x y => if Ord__IntWithInf_op_zlze__ x y : bool then y else x.

Local Definition Ord__IntWithInf_min : IntWithInf -> IntWithInf -> IntWithInf :=
  fun x y => if Ord__IntWithInf_op_zlze__ x y : bool then x else y.

Program Instance Ord__IntWithInf : GHC.Base.Ord IntWithInf :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__IntWithInf_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__IntWithInf_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__IntWithInf_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__IntWithInf_op_zgze__ ;
           GHC.Base.compare__ := Ord__IntWithInf_compare ;
           GHC.Base.max__ := Ord__IntWithInf_max ;
           GHC.Base.min__ := Ord__IntWithInf_min |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `BasicTypes.Outputable__IntWithInf' *)

(* Skipping all instances of class `GHC.Num.Num', including
   `BasicTypes.Num__IntWithInf' *)

Definition pickLR {a} : LeftOrRight -> (a * a)%type -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CLeft, pair l _ => l
    | CRight, pair _ r => r
    end.

Definition fIRST_TAG : ConTag :=
  #1.

Definition noOneShotInfo : OneShotInfo :=
  NoOneShotInfo.

Definition isOneShotInfo : OneShotInfo -> bool :=
  fun arg_0__ => match arg_0__ with | OneShotLam => true | _ => false end.

Definition hasNoOneShotInfo : OneShotInfo -> bool :=
  fun arg_0__ => match arg_0__ with | NoOneShotInfo => true | _ => false end.

Definition worstOneShot : OneShotInfo -> OneShotInfo -> OneShotInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoOneShotInfo, _ => NoOneShotInfo
    | OneShotLam, os => os
    end.

Definition bestOneShot : OneShotInfo -> OneShotInfo -> OneShotInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoOneShotInfo, os => os
    | OneShotLam, _ => OneShotLam
    end.

(* Skipping definition `BasicTypes.pprOneShotInfo' *)

Definition flipSwap : SwapFlag -> SwapFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | IsSwapped => NotSwapped
    | NotSwapped => IsSwapped
    end.

Definition isSwapped : SwapFlag -> bool :=
  fun arg_0__ => match arg_0__ with | IsSwapped => true | NotSwapped => false end.

Definition unSwap {a} {b} : SwapFlag -> (a -> a -> b) -> a -> a -> b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | NotSwapped, f, a, b => f a b
    | IsSwapped, f, a, b => f b a
    end.

Definition bumpVersion : Version -> Version :=
  fun v => v GHC.Num.+ #1.

Definition initialVersion : Version :=
  #1.

Definition pp_ws : list (SrcLoc.Located StringLiteral) -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | cons l nil => Panic.someSDoc
    | ws =>
        GHC.Base.mappend (GHC.Base.mappend (Datatypes.id (GHC.Base.hs_string__ "["))
                                           Panic.someSDoc) (Datatypes.id (GHC.Base.hs_string__ "]"))
    end.

Definition pprWarningTxtForMsg : WarningTxt -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_WarningTxt _ ws => Panic.someSDoc
    | DeprecatedTxt _ ds =>
        GHC.Base.mappend (Datatypes.id (GHC.Base.hs_string__ "Deprecated:"))
                         Panic.someSDoc
    end.

(* Skipping definition `BasicTypes.pprRuleName' *)

Definition maxPrecedence : GHC.Num.Int :=
  #9.

Definition minPrecedence : GHC.Num.Int :=
  #0.

(* Skipping definition `BasicTypes.defaultFixity' *)

Definition negateFixity : Fixity :=
  Mk_Fixity NoSourceText #6 InfixL.

Definition funTyFixity : Fixity :=
  Mk_Fixity NoSourceText #0 InfixR.

Definition compareFixity : Fixity -> Fixity -> (bool * bool)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Fixity _ prec1 dir1, Mk_Fixity _ prec2 dir2 =>
        let error_please := pair true false in
        let left_ := pair false false in
        let right_ := pair false true in
        match GHC.Base.compare prec1 prec2 with
        | Gt => left_
        | Lt => right_
        | Eq =>
            match pair dir1 dir2 with
            | pair InfixR InfixR => right_
            | pair InfixL InfixL => left_
            | _ => error_please
            end
        end
    end.

Definition isNotTopLevel : TopLevelFlag -> bool :=
  fun arg_0__ => match arg_0__ with | NotTopLevel => true | TopLevel => false end.

Definition isTopLevel : TopLevelFlag -> bool :=
  fun arg_0__ => match arg_0__ with | TopLevel => true | NotTopLevel => false end.

Definition isBoxed : Boxity -> bool :=
  fun arg_0__ => match arg_0__ with | Boxed => true | Unboxed => false end.

Definition isRec : RecFlag -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Recursive => true
    | NonRecursive => false
    end.

Definition isNonRec : RecFlag -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Recursive => false
    | NonRecursive => true
    end.

Definition boolToRecFlag : bool -> RecFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | true => Recursive
    | false => NonRecursive
    end.

Definition isGenerated : Origin -> bool :=
  fun arg_0__ => match arg_0__ with | Generated => true | FromSource => false end.

Definition setOverlapModeMaybe
   : OverlapFlag -> option OverlapMode -> OverlapFlag :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, None => f
    | f, Some m =>
        let 'Mk_OverlapFlag overlapMode_2__ isSafeOverlap_3__ := f in
        Mk_OverlapFlag m isSafeOverlap_3__
    end.

Definition hasIncoherentFlag : OverlapMode -> bool :=
  fun mode => match mode with | Incoherent _ => true | _ => false end.

Definition hasOverlappableFlag : OverlapMode -> bool :=
  fun mode =>
    match mode with
    | Overlappable _ => true
    | Overlaps _ => true
    | Incoherent _ => true
    | _ => false
    end.

Definition hasOverlappingFlag : OverlapMode -> bool :=
  fun mode =>
    match mode with
    | Overlapping _ => true
    | Overlaps _ => true
    | Incoherent _ => true
    | _ => false
    end.

(* Skipping definition `BasicTypes.pprSafeOverlap' *)

(* Skipping definition `BasicTypes.maybeParen' *)

Definition tupleSortBoxity : TupleSort -> Boxity :=
  fun arg_0__ =>
    match arg_0__ with
    | BoxedTuple => Boxed
    | UnboxedTuple => Unboxed
    | ConstraintTuple => Boxed
    end.

Definition boxityTupleSort : Boxity -> TupleSort :=
  fun arg_0__ =>
    match arg_0__ with
    | Boxed => BoxedTuple
    | Unboxed => UnboxedTuple
    end.

(* Skipping definition `BasicTypes.tupleParens' *)

Definition sumParens : GHC.Base.String -> GHC.Base.String :=
  fun p => GHC.Base.mappend (GHC.Base.mappend Panic.someSDoc p) Panic.someSDoc.

(* Skipping definition `BasicTypes.pprAlternative' *)

Definition noOccInfo : OccInfo :=
  ManyOccs NoTailCallInfo.

Definition isManyOccs : OccInfo -> bool :=
  fun arg_0__ => match arg_0__ with | ManyOccs _ => true | _ => false end.

Definition seqOccInfo : OccInfo -> unit :=
  fun occ => GHC.Prim.seq occ tt.

Definition insideLam : InsideLam :=
  true.

Definition notInsideLam : InsideLam :=
  false.

Definition oneBranch : OneBranch :=
  true.

Definition notOneBranch : OneBranch :=
  false.

Definition tailCallInfo : OccInfo -> TailCallInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | IAmDead => NoTailCallInfo
    | other => occ_tail other
    end.

Definition zapOccTailCallInfo : OccInfo -> OccInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | IAmDead => IAmDead
    | occ =>
        match occ with
        | ManyOccs occ_tail_1__ => ManyOccs NoTailCallInfo
        | IAmDead => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | OneOcc occ_in_lam_2__ occ_one_br_3__ occ_int_cxt_4__ occ_tail_5__ =>
            OneOcc occ_in_lam_2__ occ_one_br_3__ occ_int_cxt_4__ NoTailCallInfo
        | IAmALoopBreaker occ_rules_only_6__ occ_tail_7__ =>
            IAmALoopBreaker occ_rules_only_6__ NoTailCallInfo
        end
    end.

Definition isAlwaysTailCalled : OccInfo -> bool :=
  fun occ =>
    match tailCallInfo occ with
    | AlwaysTailCalled _ => true
    | NoTailCallInfo => false
    end.

Definition strongLoopBreaker : OccInfo :=
  IAmALoopBreaker false NoTailCallInfo.

Definition weakLoopBreaker : OccInfo :=
  IAmALoopBreaker true NoTailCallInfo.

Definition isWeakLoopBreaker : OccInfo -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | IAmALoopBreaker _ _ => true
    | _ => false
    end.

Definition isStrongLoopBreaker : OccInfo -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | IAmALoopBreaker false _ => true
    | _ => false
    end.

Definition isDeadOcc : OccInfo -> bool :=
  fun arg_0__ => match arg_0__ with | IAmDead => true | _ => false end.

Definition isOneOcc : OccInfo -> bool :=
  fun arg_0__ => match arg_0__ with | OneOcc _ _ _ _ => true | _ => false end.

Definition zapFragileOcc : OccInfo -> OccInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | OneOcc _ _ _ _ => noOccInfo
    | occ => zapOccTailCallInfo occ
    end.

Definition pprShortTailCallInfo : TailCallInfo -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | AlwaysTailCalled ar => GHC.Base.mappend Panic.someSDoc Panic.someSDoc
    | NoTailCallInfo => Panic.someSDoc
    end.

Definition successIf : bool -> SuccessFlag :=
  fun arg_0__ => match arg_0__ with | true => Succeeded | false => Failed end.

Definition succeeded : SuccessFlag -> bool :=
  fun arg_0__ => match arg_0__ with | Succeeded => true | Failed => false end.

Definition failed : SuccessFlag -> bool :=
  fun arg_0__ => match arg_0__ with | Succeeded => false | Failed => true end.

Definition pprWithSourceText
   : SourceText -> GHC.Base.String -> GHC.Base.String :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoSourceText, d => d
    | Mk_SourceText src, _ => Datatypes.id src
    end.

Definition isConLike : RuleMatchInfo -> bool :=
  fun arg_0__ => match arg_0__ with | ConLike => true | _ => false end.

Definition isFunLike : RuleMatchInfo -> bool :=
  fun arg_0__ => match arg_0__ with | FunLike => true | _ => false end.

Definition noUserInlineSpec : InlineSpec -> bool :=
  fun arg_0__ => match arg_0__ with | NoUserInline => true | _ => false end.

Definition defaultInlinePragma : InlinePragma :=
  Mk_InlinePragma (Mk_SourceText (GHC.Base.hs_string__ "{-# INLINE")) NoUserInline
                  None AlwaysActive FunLike.

Definition alwaysInlinePragma : InlinePragma :=
  let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
     inl_rule_4__ := defaultInlinePragma in
  Mk_InlinePragma inl_src_0__ Inline inl_sat_2__ inl_act_3__ inl_rule_4__.

Definition neverInlinePragma : InlinePragma :=
  let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
     inl_rule_4__ := defaultInlinePragma in
  Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ NeverActive inl_rule_4__.

Definition inlinePragmaSpec : InlinePragma -> InlineSpec :=
  inl_inline.

Definition dfunInlinePragma : InlinePragma :=
  let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
     inl_rule_4__ := defaultInlinePragma in
  Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ AlwaysActive ConLike.

Definition isAlwaysActive : Activation -> bool :=
  fun arg_0__ => match arg_0__ with | AlwaysActive => true | _ => false end.

Definition isDefaultInlinePragma : InlinePragma -> bool :=
  fun '(Mk_InlinePragma _ inline _ activation match_info) =>
    andb (noUserInlineSpec inline) (andb (isAlwaysActive activation) (isFunLike
                                          match_info)).

Definition isInlinePragma : InlinePragma -> bool :=
  fun prag => match inl_inline prag with | Inline => true | _ => false end.

Definition isInlinablePragma : InlinePragma -> bool :=
  fun prag => match inl_inline prag with | Inlinable => true | _ => false end.

Definition isAnyInlinePragma : InlinePragma -> bool :=
  fun prag =>
    match inl_inline prag with
    | Inline => true
    | Inlinable => true
    | _ => false
    end.

Definition inlinePragmaSat : InlinePragma -> option Arity :=
  inl_sat.

Definition inlinePragmaActivation : InlinePragma -> Activation :=
  fun '(Mk_InlinePragma _ _ _ activation _) => activation.

Definition inlinePragmaRuleMatchInfo : InlinePragma -> RuleMatchInfo :=
  fun '(Mk_InlinePragma _ _ _ _ info) => info.

Definition setInlinePragmaActivation
   : InlinePragma -> Activation -> InlinePragma :=
  fun prag activation =>
    let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
       inl_rule_4__ := prag in
    Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ activation inl_rule_4__.

Definition setInlinePragmaRuleMatchInfo
   : InlinePragma -> RuleMatchInfo -> InlinePragma :=
  fun prag info =>
    let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
       inl_rule_4__ := prag in
    Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__ info.

Definition pprInline' : bool -> InlinePragma -> GHC.Base.String :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | emptyInline, Mk_InlinePragma _ inline mb_arity activation info =>
        let pp_info :=
          if isFunLike info : bool then Panic.someSDoc else
          Panic.someSDoc in
        let pp_sat :=
          match mb_arity with
          | Some ar =>
              GHC.Base.mappend (Datatypes.id (GHC.Base.hs_string__ "sat-args="))
                               Panic.someSDoc
          | _ => Panic.someSDoc
          end in
        let pp_act :=
          fun arg_4__ arg_5__ =>
            match arg_4__, arg_5__ with
            | Inline, AlwaysActive => Panic.someSDoc
            | NoInline, NeverActive => Panic.someSDoc
            | _, act => Panic.someSDoc
            end in
        let pp_inl :=
          fun x => if emptyInline : bool then Panic.someSDoc else Panic.someSDoc in
        GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend (pp_inl inline) (pp_act
                                                              inline activation)) pp_sat) pp_info
    end.

Definition pprInline : InlinePragma -> GHC.Base.String :=
  pprInline' true.

Definition pprInlineDebug : InlinePragma -> GHC.Base.String :=
  pprInline' false.

Definition isActiveIn : PhaseNum -> Activation -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, NeverActive => false
    | _, AlwaysActive => true
    | p, ActiveAfter _ n => p GHC.Base.<= n
    | p, ActiveBefore _ n => p GHC.Base.> n
    end.

Definition isActive : CompilerPhase -> Activation -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InitialPhase, AlwaysActive => true
    | InitialPhase, ActiveBefore _ _ => true
    | InitialPhase, _ => false
    | Phase p, act => isActiveIn p act
    end.

Definition competesWith : Activation -> Activation -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NeverActive, _ => false
    | _, NeverActive => false
    | AlwaysActive, _ => true
    | ActiveBefore _ _, AlwaysActive => true
    | ActiveBefore _ _, ActiveBefore _ _ => true
    | ActiveBefore _ a, ActiveAfter _ b => a GHC.Base.< b
    | ActiveAfter _ _, AlwaysActive => false
    | ActiveAfter _ _, ActiveBefore _ _ => false
    | ActiveAfter _ a, ActiveAfter _ b => a GHC.Base.>= b
    end.

Definition isNeverActive : Activation -> bool :=
  fun arg_0__ => match arg_0__ with | NeverActive => true | _ => false end.

Definition isEarlyActive : Activation -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlwaysActive => true
    | ActiveBefore _ _ => true
    | _ => false
    end.

(* Skipping definition `BasicTypes.mkIntegralLit' *)

(* Skipping definition `BasicTypes.negateIntegralLit' *)

(* Skipping definition `BasicTypes.mkFractionalLit' *)

(* Skipping definition `BasicTypes.negateFractionalLit' *)

(* Skipping definition `BasicTypes.integralFractionalLit' *)

Definition infinity : IntWithInf :=
  Infinity.

Definition intGtLimit : GHC.Num.Int -> IntWithInf -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Infinity => false
    | n, Int m => n GHC.Base.> m
    end.

Definition plusWithInf : IntWithInf -> IntWithInf -> IntWithInf :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Infinity, _ => Infinity
    | _, Infinity => Infinity
    | Int a, Int b => Int (a GHC.Num.+ b)
    end.

Definition mulWithInf : IntWithInf -> IntWithInf -> IntWithInf :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Infinity, _ => Infinity
    | _, Infinity => Infinity
    | Int a, Int b => Int (a GHC.Num.* b)
    end.

Definition treatZeroAsInf : GHC.Num.Int -> IntWithInf :=
  fun arg_0__ =>
    let 'num_1__ := arg_0__ in
    if num_1__ GHC.Base.== #0 : bool then Infinity else
    let 'n := arg_0__ in
    Int n.

Definition mkIntWithInf : GHC.Num.Int -> IntWithInf :=
  Int.

(* External variables:
     Eq Gt Lt None Some andb bool comparison cons false list nat negb op_zt__ option
     pair true tt unit Data.Function.on Datatypes.id FastString.FastString
     GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.compare__
     GHC.Base.mappend GHC.Base.max__ GHC.Base.min__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____ GHC.Base.op_zgze__
     GHC.Base.op_zgze____ GHC.Base.op_zl__ GHC.Base.op_zl____ GHC.Base.op_zlze__
     GHC.Base.op_zlze____ GHC.Base.op_zsze__ GHC.Base.op_zsze____
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.default GHC.Err.error GHC.Num.Int
     GHC.Num.Integer GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.seq
     GHC.Real.Rational Panic.someSDoc SrcLoc.Located
*)
