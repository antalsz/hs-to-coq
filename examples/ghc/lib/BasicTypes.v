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
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Require SrcLoc.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition Version :=
  GHC.Num.Int%type.

Inductive TupleSort : Type
  := BoxedTuple : TupleSort
  |  UnboxedTuple : TupleSort
  |  ConstraintTuple : TupleSort.

Inductive TopLevelFlag : Type
  := TopLevel : TopLevelFlag
  |  NotTopLevel : TopLevelFlag.

Inductive SwapFlag : Type := NotSwapped : SwapFlag |  IsSwapped : SwapFlag.

Inductive SuccessFlag : Type := Succeeded : SuccessFlag |  Failed : SuccessFlag.

Definition SourceText :=
  GHC.Base.String%type.

Inductive StringLiteral : Type
  := Mk_StringLiteral : SourceText -> FastString.FastString -> StringLiteral.

Inductive WarningTxt : Type
  := Mk_WarningTxt
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
  := ConLike : RuleMatchInfo
  |  FunLike : RuleMatchInfo.

Definition RepArity :=
  GHC.Num.Int%type.

Inductive RecFlag : Type := Recursive : RecFlag |  NonRecursive : RecFlag.

Definition PhaseNum :=
  GHC.Num.Int%type.

Inductive OverlapMode : Type
  := NoOverlap : SourceText -> OverlapMode
  |  Overlappable : SourceText -> OverlapMode
  |  Overlapping : SourceText -> OverlapMode
  |  Overlaps : SourceText -> OverlapMode
  |  Incoherent : SourceText -> OverlapMode.

Inductive OverlapFlag : Type
  := Mk_OverlapFlag : OverlapMode -> bool -> OverlapFlag.

Inductive Origin : Type := FromSource : Origin |  Generated : Origin.

Inductive OneShotInfo : Type
  := NoOneShotInfo : OneShotInfo
  |  ProbOneShot : OneShotInfo
  |  OneShotLam : OneShotInfo.

Definition OneBranch :=
  bool%type.

Definition InterestingCxt :=
  bool%type.

Inductive IntWithInf : Type
  := Int : GHC.Num.Int -> IntWithInf
  |  Infinity : IntWithInf.

Definition InsideLam :=
  bool%type.

Inductive OccInfo : Type
  := NoOccInfo : OccInfo
  |  IAmDead : OccInfo
  |  OneOcc : InsideLam -> OneBranch -> InterestingCxt -> OccInfo
  |  IAmALoopBreaker : RulesOnly -> OccInfo.

Inductive InlineSpec : Type
  := Inline : InlineSpec
  |  Inlinable : InlineSpec
  |  NoInline : InlineSpec
  |  EmptyInlineSpec : InlineSpec.

Inductive FunctionOrData : Type
  := IsFunction : FunctionOrData
  |  IsData : FunctionOrData.

Inductive FractionalLit : Type
  := FL : GHC.Base.String -> GHC.Real.Rational -> FractionalLit.

Inductive FixityDirection : Type
  := InfixL : FixityDirection
  |  InfixR : FixityDirection
  |  InfixN : FixityDirection.

Inductive Fixity : Type
  := Mk_Fixity : SourceText -> GHC.Num.Int -> FixityDirection -> Fixity.

Inductive EP a : Type := Mk_EP : a -> a -> EP a.

Inductive DefMethSpec ty : Type
  := VanillaDM : DefMethSpec ty
  |  GenericDM : ty -> DefMethSpec ty.

Definition ConTag :=
  GHC.Num.Int%type.

Inductive CompilerPhase : Type
  := Phase : PhaseNum -> CompilerPhase
  |  InitialPhase : CompilerPhase.

Inductive Boxity : Type := Boxed : Boxity |  Unboxed : Boxity.

Definition Arity :=
  GHC.Num.Int%type.

Definition Alignment :=
  GHC.Num.Int%type.

Inductive Activation : Type
  := NeverActive : Activation
  |  AlwaysActive : Activation
  |  ActiveBefore : SourceText -> PhaseNum -> Activation
  |  ActiveAfter : SourceText -> PhaseNum -> Activation.

Inductive InlinePragma : Type
  := Mk_InlinePragma
   : SourceText ->
     InlineSpec -> option Arity -> Activation -> RuleMatchInfo -> InlinePragma.

Arguments Mk_EP {_} _ _.

Arguments VanillaDM {_}.

Arguments GenericDM {_} _.

Definition sl_fs (arg_0__ : StringLiteral) :=
  let 'Mk_StringLiteral _ sl_fs := arg_0__ in
  sl_fs.

Definition sl_st (arg_1__ : StringLiteral) :=
  let 'Mk_StringLiteral sl_st _ := arg_1__ in
  sl_st.

Definition isSafeOverlap (arg_2__ : OverlapFlag) :=
  let 'Mk_OverlapFlag _ isSafeOverlap := arg_2__ in
  isSafeOverlap.

Definition overlapMode (arg_3__ : OverlapFlag) :=
  let 'Mk_OverlapFlag overlapMode _ := arg_3__ in
  overlapMode.

Definition fl_text (arg_4__ : FractionalLit) :=
  let 'FL fl_text _ := arg_4__ in
  fl_text.

Definition fl_value (arg_5__ : FractionalLit) :=
  let 'FL _ fl_value := arg_5__ in
  fl_value.

Definition fromEP {a} (arg_6__ : EP a) :=
  let 'Mk_EP fromEP _ := arg_6__ in
  fromEP.

Definition toEP {a} (arg_7__ : EP a) :=
  let 'Mk_EP _ toEP := arg_7__ in
  toEP.

Definition inl_act (arg_8__ : InlinePragma) :=
  let 'Mk_InlinePragma _ _ _ inl_act _ := arg_8__ in
  inl_act.

Definition inl_inline (arg_9__ : InlinePragma) :=
  let 'Mk_InlinePragma _ inl_inline _ _ _ := arg_9__ in
  inl_inline.

Definition inl_rule (arg_10__ : InlinePragma) :=
  let 'Mk_InlinePragma _ _ _ _ inl_rule := arg_10__ in
  inl_rule.

Definition inl_sat (arg_11__ : InlinePragma) :=
  let 'Mk_InlinePragma _ _ inl_sat _ _ := arg_11__ in
  inl_sat.

Definition inl_src (arg_12__ : InlinePragma) :=
  let 'Mk_InlinePragma inl_src _ _ _ _ := arg_12__ in
  inl_src.

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom missingValue : forall {a}, a.
(* Midamble *)

Require GHC.Err.


Instance Default_Origin : GHC.Err.Default Origin :=
  GHC.Err.Build_Default _ Generated.

Instance Default_OverlapMode : GHC.Err.Default OverlapMode :=
  GHC.Err.Build_Default _ (NoOverlap GHC.Err.default).

Instance Default_RecFlag : GHC.Err.Default RecFlag :=
  GHC.Err.Build_Default _ Recursive.

Instance Default_RuleMatchInfo : GHC.Err.Default RuleMatchInfo :=
  GHC.Err.Build_Default _ ConLike.


Instance Default_SuccessFlag : GHC.Err.Default SuccessFlag :=
  GHC.Err.Build_Default _ Succeeded.


Instance Default_SwapFlag : GHC.Err.Default SwapFlag :=
  GHC.Err.Build_Default _ NotSwapped.


Instance Default_TopLevelFlag : GHC.Err.Default TopLevelFlag :=
  GHC.Err.Build_Default _ TopLevel.


Instance Default_TupleSort : GHC.Err.Default TupleSort :=
  GHC.Err.Build_Default _ BoxedTuple.

Instance Default_OverlapFlag : GHC.Err.Default OverlapFlag :=
  GHC.Err.Build_Default _ (Mk_OverlapFlag GHC.Err.default GHC.Err.default).

Instance Default_OneShotInfo : GHC.Err.Default OneShotInfo :=
  GHC.Err.Build_Default _ NoOneShotInfo.


Instance Default_IntWithInf : GHC.Err.Default IntWithInf :=
  GHC.Err.Build_Default _ Infinity.


Instance Default_OccInfo : GHC.Err.Default OccInfo :=
  GHC.Err.Build_Default _ NoOccInfo.


Instance Default_InlineSpec : GHC.Err.Default InlineSpec :=
  GHC.Err.Build_Default _ Inline.



Instance Default_FixityDirection : GHC.Err.Default FixityDirection :=
  GHC.Err.Build_Default _ InfixL.


Instance Default_Fixity : GHC.Err.Default Fixity :=
  GHC.Err.Build_Default _ (Mk_Fixity GHC.Err.default GHC.Err.default GHC.Err.default).



Instance Default_DefMethSpec {ty} : GHC.Err.Default (DefMethSpec ty) :=
  GHC.Err.Build_Default _ VanillaDM.

Instance Default_CompilerPhase : GHC.Err.Default CompilerPhase :=
  GHC.Err.Build_Default _ InitialPhase.



Instance Default_Boxity : GHC.Err.Default Boxity :=
  GHC.Err.Build_Default _ Boxed.


Instance Default_Activation : GHC.Err.Default Activation :=
  GHC.Err.Build_Default _ NeverActive.


Instance Default_InlinePragma : GHC.Err.Default InlinePragma :=
  GHC.Err.Build_Default _ (Mk_InlinePragma GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

(* Converted value declarations: *)

(* Translating `instance Outputable.Outputable BasicTypes.OneShotInfo' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.SwapFlag' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.FunctionOrData'
   failed: OOPS! Cannot find information for class Qualified "Outputable"
   "Outputable" unsupported *)

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
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___StringLiteral_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___StringLiteral_op_zsze__ |}.

(* Translating `instance Outputable.Outputable BasicTypes.WarningTxt' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.Fixity' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.FixityDirection'
   failed: OOPS! Cannot find information for class Qualified "Outputable"
   "Outputable" unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.TopLevelFlag' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.Boxity' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.RecFlag' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.Origin' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.OverlapFlag' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.OverlapMode' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.OccInfo' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance forall {ty}, Outputable.Outputable
   (BasicTypes.DefMethSpec ty)' failed: OOPS! Cannot find information for class
   Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.SuccessFlag' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.CompilerPhase' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.Activation' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.RuleMatchInfo' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.InlineSpec' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable BasicTypes.InlinePragma' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

Local Definition Eq___FractionalLit_op_zeze__
   : FractionalLit -> FractionalLit -> bool :=
  Data.Function.on _GHC.Base.==_ fl_value.

Local Definition Eq___FractionalLit_op_zsze__
   : FractionalLit -> FractionalLit -> bool :=
  fun x y => negb (Eq___FractionalLit_op_zeze__ x y).

Program Instance Eq___FractionalLit : GHC.Base.Eq_ FractionalLit :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___FractionalLit_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___FractionalLit_op_zsze__ |}.

Local Definition Ord__FractionalLit_compare
   : FractionalLit -> FractionalLit -> comparison :=
  Data.Function.on GHC.Base.compare fl_value.

Local Definition Ord__FractionalLit_op_zg__
   : FractionalLit -> FractionalLit -> bool :=
  fun x y => _GHC.Base.==_ (Ord__FractionalLit_compare x y) Gt.

Local Definition Ord__FractionalLit_op_zgze__
   : FractionalLit -> FractionalLit -> bool :=
  fun x y => _GHC.Base./=_ (Ord__FractionalLit_compare x y) Lt.

Local Definition Ord__FractionalLit_op_zl__
   : FractionalLit -> FractionalLit -> bool :=
  fun x y => _GHC.Base.==_ (Ord__FractionalLit_compare x y) Lt.

Local Definition Ord__FractionalLit_op_zlze__
   : FractionalLit -> FractionalLit -> bool :=
  fun x y => _GHC.Base./=_ (Ord__FractionalLit_compare x y) Gt.

Local Definition Ord__FractionalLit_max
   : FractionalLit -> FractionalLit -> FractionalLit :=
  fun x y => if Ord__FractionalLit_op_zlze__ x y : bool then y else x.

Local Definition Ord__FractionalLit_min
   : FractionalLit -> FractionalLit -> FractionalLit :=
  fun x y => if Ord__FractionalLit_op_zlze__ x y : bool then x else y.

Program Instance Ord__FractionalLit : GHC.Base.Ord FractionalLit :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__FractionalLit_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__FractionalLit_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__FractionalLit_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__FractionalLit_op_zgze__ ;
         GHC.Base.compare__ := Ord__FractionalLit_compare ;
         GHC.Base.max__ := Ord__FractionalLit_max ;
         GHC.Base.min__ := Ord__FractionalLit_min |}.

(* Translating `instance Outputable.Outputable BasicTypes.FractionalLit' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

Local Definition Ord__IntWithInf_compare
   : IntWithInf -> IntWithInf -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Infinity, Infinity => Eq
    | Int _, Infinity => Lt
    | Infinity, Int _ => Gt
    | Int a, Int b => GHC.Base.compare a b
    end.

Local Definition Ord__IntWithInf_op_zg__ : IntWithInf -> IntWithInf -> bool :=
  fun x y => _GHC.Base.==_ (Ord__IntWithInf_compare x y) Gt.

Local Definition Ord__IntWithInf_op_zgze__ : IntWithInf -> IntWithInf -> bool :=
  fun x y => _GHC.Base./=_ (Ord__IntWithInf_compare x y) Lt.

Local Definition Ord__IntWithInf_op_zl__ : IntWithInf -> IntWithInf -> bool :=
  fun x y => _GHC.Base.==_ (Ord__IntWithInf_compare x y) Lt.

Local Definition Ord__IntWithInf_op_zlze__ : IntWithInf -> IntWithInf -> bool :=
  fun x y => _GHC.Base./=_ (Ord__IntWithInf_compare x y) Gt.

Local Definition Ord__IntWithInf_max : IntWithInf -> IntWithInf -> IntWithInf :=
  fun x y => if Ord__IntWithInf_op_zlze__ x y : bool then y else x.

Local Definition Ord__IntWithInf_min : IntWithInf -> IntWithInf -> IntWithInf :=
  fun x y => if Ord__IntWithInf_op_zlze__ x y : bool then x else y.

(* Translating `instance Outputable.Outputable BasicTypes.IntWithInf' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance GHC.Num.Num BasicTypes.IntWithInf' failed: OOPS! Cannot
   find information for class Qualified "GHC.Num" "Num" unsupported *)

Local Definition Eq___IntWithInf_op_zeze__ : IntWithInf -> IntWithInf -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Int a1, Int b1 => ((a1 GHC.Base.== b1))
    | Infinity, Infinity => true
    | _, _ => false
    end.

Local Definition Eq___IntWithInf_op_zsze__ : IntWithInf -> IntWithInf -> bool :=
  fun a b => negb (Eq___IntWithInf_op_zeze__ a b).

Program Instance Eq___IntWithInf : GHC.Base.Eq_ IntWithInf :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___IntWithInf_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___IntWithInf_op_zsze__ |}.

Program Instance Ord__IntWithInf : GHC.Base.Ord IntWithInf :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__IntWithInf_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__IntWithInf_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__IntWithInf_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__IntWithInf_op_zgze__ ;
         GHC.Base.compare__ := Ord__IntWithInf_compare ;
         GHC.Base.max__ := Ord__IntWithInf_max ;
         GHC.Base.min__ := Ord__IntWithInf_min |}.

(* Translating `instance GHC.Show.Show BasicTypes.FractionalLit' failed: OOPS!
   Cannot find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Data.Data.Data BasicTypes.FractionalLit' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data BasicTypes.InlinePragma' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance GHC.Show.Show BasicTypes.InlineSpec' failed: OOPS!
   Cannot find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Data.Data.Data BasicTypes.InlineSpec' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___InlineSpec_op_zeze__ : InlineSpec -> InlineSpec -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Inline, Inline => true
    | Inlinable, Inlinable => true
    | NoInline, NoInline => true
    | EmptyInlineSpec, EmptyInlineSpec => true
    | _, _ => false
    end.

Local Definition Eq___InlineSpec_op_zsze__ : InlineSpec -> InlineSpec -> bool :=
  fun a b => negb (Eq___InlineSpec_op_zeze__ a b).

Program Instance Eq___InlineSpec : GHC.Base.Eq_ InlineSpec :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___InlineSpec_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___InlineSpec_op_zsze__ |}.

(* Translating `instance GHC.Show.Show BasicTypes.RuleMatchInfo' failed: OOPS!
   Cannot find information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance Data.Data.Data BasicTypes.RuleMatchInfo' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

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
  fun a b => negb (Eq___RuleMatchInfo_op_zeze__ a b).

Program Instance Eq___RuleMatchInfo : GHC.Base.Eq_ RuleMatchInfo :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___RuleMatchInfo_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___RuleMatchInfo_op_zsze__ |}.

(* Translating `instance Data.Data.Data BasicTypes.Activation' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

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
  fun a b => negb (Eq___Activation_op_zeze__ a b).

Program Instance Eq___Activation : GHC.Base.Eq_ Activation :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Activation_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Activation_op_zsze__ |}.

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
  fun a b => negb (Eq___InlinePragma_op_zeze__ a b).

Program Instance Eq___InlinePragma : GHC.Base.Eq_ InlinePragma :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___InlinePragma_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___InlinePragma_op_zsze__ |}.

(* Translating `instance Data.Data.Data BasicTypes.WarningTxt' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

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
  fun a b => negb (Eq___WarningTxt_op_zeze__ a b).

Program Instance Eq___WarningTxt : GHC.Base.Eq_ WarningTxt :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___WarningTxt_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___WarningTxt_op_zsze__ |}.

(* Translating `instance Data.Data.Data BasicTypes.StringLiteral' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data BasicTypes.Fixity' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data BasicTypes.OverlapFlag' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data.Data.Data BasicTypes.OverlapMode' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

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
  fun a b => negb (Eq___OverlapMode_op_zeze__ a b).

Program Instance Eq___OverlapMode : GHC.Base.Eq_ OverlapMode :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___OverlapMode_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___OverlapMode_op_zsze__ |}.

Local Definition Eq___OverlapFlag_op_zeze__
   : OverlapFlag -> OverlapFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_OverlapFlag a1 a2, Mk_OverlapFlag b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___OverlapFlag_op_zsze__
   : OverlapFlag -> OverlapFlag -> bool :=
  fun a b => negb (Eq___OverlapFlag_op_zeze__ a b).

Program Instance Eq___OverlapFlag : GHC.Base.Eq_ OverlapFlag :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___OverlapFlag_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___OverlapFlag_op_zsze__ |}.

Local Definition Eq___OccInfo_op_zeze__ : OccInfo -> OccInfo -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoOccInfo, NoOccInfo => true
    | IAmDead, IAmDead => true
    | OneOcc a1 a2 a3, OneOcc b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    | IAmALoopBreaker a1, IAmALoopBreaker b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___OccInfo_op_zsze__ : OccInfo -> OccInfo -> bool :=
  fun a b => negb (Eq___OccInfo_op_zeze__ a b).

Program Instance Eq___OccInfo : GHC.Base.Eq_ OccInfo :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___OccInfo_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___OccInfo_op_zsze__ |}.

(* Translating `instance Data.Data.Data BasicTypes.TupleSort' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___TupleSort_op_zeze__ : TupleSort -> TupleSort -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | BoxedTuple, BoxedTuple => true
    | UnboxedTuple, UnboxedTuple => true
    | ConstraintTuple, ConstraintTuple => true
    | _, _ => false
    end.

Local Definition Eq___TupleSort_op_zsze__ : TupleSort -> TupleSort -> bool :=
  fun a b => negb (Eq___TupleSort_op_zeze__ a b).

Program Instance Eq___TupleSort : GHC.Base.Eq_ TupleSort :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TupleSort_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TupleSort_op_zsze__ |}.

(* Translating `instance Data.Data.Data BasicTypes.Origin' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___Origin_op_zeze__ : Origin -> Origin -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FromSource, FromSource => true
    | Generated, Generated => true
    | _, _ => false
    end.

Local Definition Eq___Origin_op_zsze__ : Origin -> Origin -> bool :=
  fun a b => negb (Eq___Origin_op_zeze__ a b).

Program Instance Eq___Origin : GHC.Base.Eq_ Origin :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Origin_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Origin_op_zsze__ |}.

(* Translating `instance Data.Data.Data BasicTypes.RecFlag' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___RecFlag_op_zeze__ : RecFlag -> RecFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Recursive, Recursive => true
    | NonRecursive, NonRecursive => true
    | _, _ => false
    end.

Local Definition Eq___RecFlag_op_zsze__ : RecFlag -> RecFlag -> bool :=
  fun a b => negb (Eq___RecFlag_op_zeze__ a b).

Program Instance Eq___RecFlag : GHC.Base.Eq_ RecFlag :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___RecFlag_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___RecFlag_op_zsze__ |}.

(* Translating `instance Data.Data.Data BasicTypes.Boxity' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___Boxity_op_zeze__ : Boxity -> Boxity -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Boxed, Boxed => true
    | Unboxed, Unboxed => true
    | _, _ => false
    end.

Local Definition Eq___Boxity_op_zsze__ : Boxity -> Boxity -> bool :=
  fun a b => negb (Eq___Boxity_op_zeze__ a b).

Program Instance Eq___Boxity : GHC.Base.Eq_ Boxity :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Boxity_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Boxity_op_zsze__ |}.

(* Translating `instance Data.Data.Data BasicTypes.FixityDirection' failed:
   OOPS! Cannot find information for class Qualified "Data.Data" "Data"
   unsupported *)

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
  fun a b => negb (Eq___FixityDirection_op_zeze__ a b).

Program Instance Eq___FixityDirection : GHC.Base.Eq_ FixityDirection :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___FixityDirection_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___FixityDirection_op_zsze__ |}.

Local Definition Eq___Fixity_op_zeze__ : Fixity -> Fixity -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_Fixity _ p1 dir1, Mk_Fixity _ p2 dir2 =>
        andb (p1 GHC.Base.== p2) (dir1 GHC.Base.== dir2)
    end.

Local Definition Eq___Fixity_op_zsze__ : Fixity -> Fixity -> bool :=
  fun x y => negb (Eq___Fixity_op_zeze__ x y).

Program Instance Eq___Fixity : GHC.Base.Eq_ Fixity :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Fixity_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Fixity_op_zsze__ |}.

(* Translating `instance Data.Data.Data BasicTypes.FunctionOrData' failed: OOPS!
   Cannot find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Ord__FunctionOrData_compare
   : FunctionOrData -> FunctionOrData -> comparison :=
  fun a b =>
    match a with
    | IsFunction => match b with | IsFunction => Eq | _ => Lt end
    | IsData => match b with | IsData => Eq | _ => Gt end
    end.

Local Definition Ord__FunctionOrData_op_zg__
   : FunctionOrData -> FunctionOrData -> bool :=
  fun a b =>
    match a with
    | IsFunction => match b with | IsFunction => false | _ => false end
    | IsData => match b with | IsData => false | _ => true end
    end.

Local Definition Ord__FunctionOrData_op_zgze__
   : FunctionOrData -> FunctionOrData -> bool :=
  fun a b =>
    match a with
    | IsFunction => match b with | IsFunction => true | _ => false end
    | IsData => match b with | IsData => true | _ => true end
    end.

Local Definition Ord__FunctionOrData_op_zl__
   : FunctionOrData -> FunctionOrData -> bool :=
  fun a b =>
    match a with
    | IsFunction => match b with | IsFunction => false | _ => true end
    | IsData => match b with | IsData => false | _ => false end
    end.

Local Definition Ord__FunctionOrData_op_zlze__
   : FunctionOrData -> FunctionOrData -> bool :=
  fun a b =>
    match a with
    | IsFunction => match b with | IsFunction => true | _ => true end
    | IsData => match b with | IsData => true | _ => false end
    end.

Local Definition Ord__FunctionOrData_min
   : FunctionOrData -> FunctionOrData -> FunctionOrData :=
  fun x y => if Ord__FunctionOrData_op_zlze__ x y : bool then x else y.

Local Definition Ord__FunctionOrData_max
   : FunctionOrData -> FunctionOrData -> FunctionOrData :=
  fun x y => if Ord__FunctionOrData_op_zlze__ x y : bool then y else x.

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
  fun a b => negb (Eq___FunctionOrData_op_zeze__ a b).

Program Instance Eq___FunctionOrData : GHC.Base.Eq_ FunctionOrData :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___FunctionOrData_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___FunctionOrData_op_zsze__ |}.

Program Instance Ord__FunctionOrData : GHC.Base.Ord FunctionOrData :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__FunctionOrData_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__FunctionOrData_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__FunctionOrData_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__FunctionOrData_op_zgze__ ;
         GHC.Base.compare__ := Ord__FunctionOrData_compare ;
         GHC.Base.max__ := Ord__FunctionOrData_max ;
         GHC.Base.min__ := Ord__FunctionOrData_min |}.

Local Definition Eq___OneShotInfo_op_zeze__
   : OneShotInfo -> OneShotInfo -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoOneShotInfo, NoOneShotInfo => true
    | ProbOneShot, ProbOneShot => true
    | OneShotLam, OneShotLam => true
    | _, _ => false
    end.

Local Definition Eq___OneShotInfo_op_zsze__
   : OneShotInfo -> OneShotInfo -> bool :=
  fun a b => negb (Eq___OneShotInfo_op_zeze__ a b).

Program Instance Eq___OneShotInfo : GHC.Base.Eq_ OneShotInfo :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___OneShotInfo_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___OneShotInfo_op_zsze__ |}.

Definition bestOneShot : OneShotInfo -> OneShotInfo -> OneShotInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoOneShotInfo, os => os
    | ProbOneShot, OneShotLam => OneShotLam
    | ProbOneShot, _ => ProbOneShot
    | OneShotLam, _ => OneShotLam
    end.

Definition boolToRecFlag : bool -> RecFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | true => Recursive
    | false => NonRecursive
    end.

Definition boxityTupleSort : Boxity -> TupleSort :=
  fun arg_0__ =>
    match arg_0__ with
    | Boxed => BoxedTuple
    | Unboxed => UnboxedTuple
    end.

Definition bumpVersion : Version -> Version :=
  fun v => v GHC.Num.+ #1.

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

Definition defaultInlinePragma : InlinePragma :=
  Mk_InlinePragma missingValue missingValue missingValue missingValue
                  missingValue.

Definition dfunInlinePragma : InlinePragma :=
  let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
     inl_rule_4__ := defaultInlinePragma in
  Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ AlwaysActive ConLike.

Definition neverInlinePragma : InlinePragma :=
  let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
     inl_rule_4__ := defaultInlinePragma in
  Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ NeverActive inl_rule_4__.

Definition alwaysInlinePragma : InlinePragma :=
  let 'Mk_InlinePragma inl_src_0__ inl_inline_1__ inl_sat_2__ inl_act_3__
     inl_rule_4__ := defaultInlinePragma in
  Mk_InlinePragma inl_src_0__ Inline inl_sat_2__ inl_act_3__ inl_rule_4__.

Definition fIRST_TAG : ConTag :=
  #1.

Definition failed : SuccessFlag -> bool :=
  fun arg_0__ => match arg_0__ with | Succeeded => false | Failed => true end.

Definition flipSwap : SwapFlag -> SwapFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | IsSwapped => NotSwapped
    | NotSwapped => IsSwapped
    end.

Definition funTyFixity : Fixity :=
  Mk_Fixity (GHC.Base.hs_string__ "0") #0 InfixR.

Definition hasNoOneShotInfo : OneShotInfo -> bool :=
  fun arg_0__ => match arg_0__ with | NoOneShotInfo => true | _ => false end.

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

Definition infinity : IntWithInf :=
  Infinity.

Definition initialVersion : Version :=
  #1.

Definition inlinePragmaActivation : InlinePragma -> Activation :=
  fun arg_0__ => let 'Mk_InlinePragma _ _ _ activation _ := arg_0__ in activation.

Definition inlinePragmaRuleMatchInfo : InlinePragma -> RuleMatchInfo :=
  fun arg_0__ => let 'Mk_InlinePragma _ _ _ _ info := arg_0__ in info.

Definition inlinePragmaSat : InlinePragma -> option Arity :=
  inl_sat.

Definition inlinePragmaSpec : InlinePragma -> InlineSpec :=
  inl_inline.

Definition insideLam : InsideLam :=
  true.

Definition intGtLimit : GHC.Num.Int -> IntWithInf -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Infinity => false
    | n, Int m => n GHC.Base.> m
    end.

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

Definition isAlwaysActive : Activation -> bool :=
  fun arg_0__ => match arg_0__ with | AlwaysActive => true | _ => false end.

Definition isAnyInlinePragma : InlinePragma -> bool :=
  fun prag =>
    match inl_inline prag with
    | Inline => true
    | Inlinable => true
    | _ => false
    end.

Definition isBoxed : Boxity -> bool :=
  fun arg_0__ => match arg_0__ with | Boxed => true | Unboxed => false end.

Definition isConLike : RuleMatchInfo -> bool :=
  fun arg_0__ => match arg_0__ with | ConLike => true | _ => false end.

Definition isDeadOcc : OccInfo -> bool :=
  fun arg_0__ => match arg_0__ with | IAmDead => true | _ => false end.

Definition isEarlyActive : Activation -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlwaysActive => true
    | ActiveBefore _ _ => true
    | _ => false
    end.

Definition isEmptyInlineSpec : InlineSpec -> bool :=
  fun arg_0__ => match arg_0__ with | EmptyInlineSpec => true | _ => false end.

Definition isFunLike : RuleMatchInfo -> bool :=
  fun arg_0__ => match arg_0__ with | FunLike => true | _ => false end.

Definition isDefaultInlinePragma : InlinePragma -> bool :=
  fun arg_0__ =>
    let 'Mk_InlinePragma _ inline _ activation match_info := arg_0__ in
    andb (isEmptyInlineSpec inline) (andb (isAlwaysActive activation) (isFunLike
                                           match_info)).

Definition isGenerated : Origin -> bool :=
  fun arg_0__ => match arg_0__ with | Generated => true | FromSource => false end.

Definition isInlinablePragma : InlinePragma -> bool :=
  fun prag => match inl_inline prag with | Inlinable => true | _ => false end.

Definition isInlinePragma : InlinePragma -> bool :=
  fun prag => match inl_inline prag with | Inline => true | _ => false end.

Definition isNeverActive : Activation -> bool :=
  fun arg_0__ => match arg_0__ with | NeverActive => true | _ => false end.

Definition isNoOcc : OccInfo -> bool :=
  fun arg_0__ => match arg_0__ with | NoOccInfo => true | _ => false end.

Definition isNonRec : RecFlag -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Recursive => false
    | NonRecursive => true
    end.

Definition isNotTopLevel : TopLevelFlag -> bool :=
  fun arg_0__ => match arg_0__ with | NotTopLevel => true | TopLevel => false end.

Definition isOneOcc : OccInfo -> bool :=
  fun arg_0__ => match arg_0__ with | OneOcc _ _ _ => true | _ => false end.

Definition isOneShotInfo : OneShotInfo -> bool :=
  fun arg_0__ => match arg_0__ with | OneShotLam => true | _ => false end.

Definition isRec : RecFlag -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Recursive => true
    | NonRecursive => false
    end.

Definition isStrongLoopBreaker : OccInfo -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | IAmALoopBreaker false => true
    | _ => false
    end.

Definition isSwapped : SwapFlag -> bool :=
  fun arg_0__ => match arg_0__ with | IsSwapped => true | NotSwapped => false end.

Definition isTopLevel : TopLevelFlag -> bool :=
  fun arg_0__ => match arg_0__ with | TopLevel => true | NotTopLevel => false end.

Definition isWeakLoopBreaker : OccInfo -> bool :=
  fun arg_0__ => match arg_0__ with | IAmALoopBreaker _ => true | _ => false end.

Definition maxPrecedence : GHC.Num.Int :=
  #9.

Definition minPrecedence : GHC.Num.Int :=
  #0.

Definition mkIntWithInf : GHC.Num.Int -> IntWithInf :=
  Int.

Definition mulWithInf : IntWithInf -> IntWithInf -> IntWithInf :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Infinity, _ => Infinity
    | _, Infinity => Infinity
    | Int a, Int b => Int (a GHC.Num.* b)
    end.

Definition negateFixity : Fixity :=
  Mk_Fixity (GHC.Base.hs_string__ "6") #6 InfixL.

Definition noOneShotInfo : OneShotInfo :=
  NoOneShotInfo.

Definition notInsideLam : InsideLam :=
  false.

Definition notOneBranch : OneBranch :=
  false.

Definition oneBranch : OneBranch :=
  true.

Definition plusWithInf : IntWithInf -> IntWithInf -> IntWithInf :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Infinity, _ => Infinity
    | _, Infinity => Infinity
    | Int a, Int b => Int (a GHC.Num.+ b)
    end.

Definition seqOccInfo : OccInfo -> unit :=
  fun occ => GHC.Prim.seq occ tt.

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

Definition setOverlapModeMaybe
   : OverlapFlag -> option OverlapMode -> OverlapFlag :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, None => f
    | f, Some m =>
        let 'Mk_OverlapFlag overlapMode_2__ isSafeOverlap_3__ := f in
        Mk_OverlapFlag m isSafeOverlap_3__
    end.

Definition strongLoopBreaker : OccInfo :=
  IAmALoopBreaker false.

Definition succeeded : SuccessFlag -> bool :=
  fun arg_0__ => match arg_0__ with | Succeeded => true | Failed => false end.

Definition successIf : bool -> SuccessFlag :=
  fun arg_0__ => match arg_0__ with | true => Succeeded | false => Failed end.

Definition treatZeroAsInf : GHC.Num.Int -> IntWithInf :=
  fun arg_0__ =>
    let 'num_1__ := arg_0__ in
    if num_1__ GHC.Base.== #0 : bool
    then Infinity
    else let 'n := arg_0__ in
         Int n.

Definition tupleSortBoxity : TupleSort -> Boxity :=
  fun arg_0__ =>
    match arg_0__ with
    | BoxedTuple => Boxed
    | UnboxedTuple => Unboxed
    | ConstraintTuple => Boxed
    end.

Definition unSwap {a} {b} : SwapFlag -> (a -> a -> b) -> a -> a -> b :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | NotSwapped, f, a, b => f a b
    | IsSwapped, f, a, b => f b a
    end.

Definition weakLoopBreaker : OccInfo :=
  IAmALoopBreaker true.

Definition worstOneShot : OneShotInfo -> OneShotInfo -> OneShotInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoOneShotInfo, _ => NoOneShotInfo
    | ProbOneShot, NoOneShotInfo => NoOneShotInfo
    | ProbOneShot, _ => ProbOneShot
    | OneShotLam, os => os
    end.

Definition zapFragileOcc : OccInfo -> OccInfo :=
  fun arg_0__ => match arg_0__ with | OneOcc _ _ _ => NoOccInfo | occ => occ end.

(* Unbound variables:
     Eq Gt Lt None Some andb bool comparison false list negb op_zt__ option pair true
     tt unit Data.Function.on FastString.FastString GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.String GHC.Base.compare GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zsze__
     GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.seq
     GHC.Real.Rational SrcLoc.Located
*)
