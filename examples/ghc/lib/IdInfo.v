(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Err.
Require GHC.Base.

(* We might put these elsewhere, but these are some types that we 
   can use for untying the knots in DataCon/Class/PatSyn/TyCon *)

Parameter DataConId : Type.
Parameter ClassId   : Type.
Parameter PatSynId  : Type.
Parameter TyConId   : Type.

Parameter Default_DataConId : GHC.Err.Default DataConId.
Parameter Default_ClassId   : GHC.Err.Default ClassId.
Parameter Default_PatSynId  : GHC.Err.Default PatSynId.
Parameter Default_TyConId   : GHC.Err.Default TyConId.

Parameter Eq_PatSynId  : Base.Eq_ PatSynId.
Parameter Eq_ClassId   : Base.Eq_ ClassId.
Parameter Eq_DataConId : Base.Eq_ DataConId.
Parameter Eq_TyConId   : Base.Eq_ TyConId.

Parameter Ord_PatSynId  : Base.Ord PatSynId.
Parameter Ord_ClassId   : Base.Ord ClassId.
Parameter Ord_DataConId : Base.Ord DataConId.
Parameter Ord_TyConId   : Base.Ord TyConId.


(*
-- An 'IdInfo' gives /optional/ information about an 'Id'.  If
-- present it never lies, but it may not be present, in which case there
-- is always a conservative assumption which can be made.

-- Most of the 'IdInfo' gives information about the value, or definition, of
-- the 'Id', independent of its usage. Exceptions to this
-- are 'demandInfo', 'occInfo', 'oneShotInfo' and 'callArityInfo'.
--

data IdInfo
  = IdInfo {
        arityInfo       :: !ArityInfo,          -- ^ 'Id' arity
        ruleInfo        :: RuleInfo,            -- ^ Specialisations of the 'Id's function which exist
                                                -- See Note [Specialisations and RULES in IdInfo]
        unfoldingInfo   :: Unfolding,           -- ^ The 'Id's unfolding
        cafInfo         :: CafInfo,             -- ^ 'Id' CAF info
        oneShotInfo     :: OneShotInfo,         -- ^ Info about a lambda-bound variable, if the 'Id' is one
        inlinePragInfo  :: InlinePragma,        -- ^ Any inline pragma atached to the 'Id'
        occInfo         :: OccInfo,             -- ^ How the 'Id' occurs in the program

        strictnessInfo  :: StrictSig,      --  ^ A strictness signature

        demandInfo      :: Demand,       -- ^ ID demand information
        callArityInfo   :: !ArityInfo,   -- ^ How this is called.
                                         -- n <=> all calls have at least n arguments

        levityInfo      :: LevityInfo    -- ^ when applied, will this Id ever have a levity-polymorphic type?
    }

*)

Parameter IdInfo        : Type.
Parameter vanillaIdInfo : IdInfo.
Parameter noCafIdInfo   : IdInfo.

Instance Default_IdInfo : GHC.Err.Default IdInfo :=
  GHC.Err.Build_Default _ vanillaIdInfo.

(* -------------------- *)

Parameter RuleInfo : Type.
Parameter emptyRuleInfo : RuleInfo.
Parameter isEmptyRuleInfo : RuleInfo -> bool.

Instance Default_RuleInfo : GHC.Err.Default RuleInfo :=
  GHC.Err.Build_Default _ emptyRuleInfo.


(* -------------------- *)

(*
Parameter RecSelParent : Type.
Parameter Default_RecSelParent : GHC.Err.Default RecSelParent.

Parameter Eq___RecSelParent : GHC.Base.Eq_ RecSelParent.
*)

(* Converted imports: *)

Require BasicTypes.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require Module.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition TickBoxId :=
  GHC.Num.Int%type.

Inductive TickBoxOp : Type := TickBox : Module.Module -> TickBoxId -> TickBoxOp.

Inductive RecSelParent : Type
  := RecSelData : TyConId -> RecSelParent
  |  RecSelPatSyn : PatSynId -> RecSelParent.

Inductive LevityInfo : Type
  := NoLevityInfo : LevityInfo
  |  NeverLevityPolymorphic : LevityInfo.

Definition InlinePragInfo :=
  BasicTypes.InlinePragma%type.

Inductive IdDetails : Type
  := VanillaId : IdDetails
  |  RecSelId : RecSelParent -> bool -> IdDetails
  |  DataConWorkId : DataConId -> IdDetails
  |  DataConWrapId : DataConId -> IdDetails
  |  ClassOpId : ClassId -> IdDetails
  |  PrimOpId : unit -> IdDetails
  |  FCallId : unit -> IdDetails
  |  TickBoxOpId : TickBoxOp -> IdDetails
  |  DFunId : bool -> IdDetails
  |  CoVarId : IdDetails
  |  JoinId : BasicTypes.JoinArity -> IdDetails.

Inductive CafInfo : Type := MayHaveCafRefs : CafInfo |  NoCafRefs : CafInfo.

Definition ArityInfo :=
  BasicTypes.Arity%type.

Instance Default__LevityInfo : GHC.Err.Default LevityInfo :=
  GHC.Err.Build_Default _ NoLevityInfo.

Instance Default__IdDetails : GHC.Err.Default IdDetails :=
  GHC.Err.Build_Default _ VanillaId.

Instance Default__CafInfo : GHC.Err.Default CafInfo :=
  GHC.Err.Build_Default _ MayHaveCafRefs.

Definition sel_naughty (arg_0__ : IdDetails) :=
  match arg_0__ with
  | VanillaId =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `VanillaId' of type `IdDetails'")
  | RecSelId _ sel_naughty => sel_naughty
  | DataConWorkId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `DataConWorkId' of type `IdDetails'")
  | DataConWrapId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `DataConWrapId' of type `IdDetails'")
  | ClassOpId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `ClassOpId' of type `IdDetails'")
  | PrimOpId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `PrimOpId' of type `IdDetails'")
  | FCallId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `FCallId' of type `IdDetails'")
  | TickBoxOpId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `TickBoxOpId' of type `IdDetails'")
  | DFunId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `DFunId' of type `IdDetails'")
  | CoVarId =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `CoVarId' of type `IdDetails'")
  | JoinId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `JoinId' of type `IdDetails'")
  end.
(* Midamble *)

Require GHC.Err.


Instance Default_TickBoxOp : GHC.Err.Default TickBoxOp :=
  GHC.Err.Build_Default _ (TickBox GHC.Err.default GHC.Err.default).

Instance Default_CafInfo : GHC.Err.Default CafInfo :=
  GHC.Err.Build_Default _ MayHaveCafRefs.

(*
Instance Default_IdInfo : GHC.Err.Default IdInfo :=
  GHC.Err.Build_Default _ (Mk_IdInfo GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default).
*)
(* Converted value declarations: *)

(* Translating `instance Outputable__LevityInfo' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__IdDetails' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__TickBoxOp' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__CafInfo' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__RecSelParent' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

Local Definition Eq___LevityInfo_op_zeze__ : LevityInfo -> LevityInfo -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoLevityInfo, NoLevityInfo => true
    | NeverLevityPolymorphic, NeverLevityPolymorphic => true
    | _, _ => false
    end.

Local Definition Eq___LevityInfo_op_zsze__ : LevityInfo -> LevityInfo -> bool :=
  fun x y => negb (Eq___LevityInfo_op_zeze__ x y).

Program Instance Eq___LevityInfo : GHC.Base.Eq_ LevityInfo :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___LevityInfo_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___LevityInfo_op_zsze__ |}.

Local Definition Ord__CafInfo_compare : CafInfo -> CafInfo -> comparison :=
  fun a b =>
    match a with
    | MayHaveCafRefs => match b with | MayHaveCafRefs => Eq | _ => Lt end
    | NoCafRefs => match b with | NoCafRefs => Eq | _ => Gt end
    end.

Local Definition Ord__CafInfo_op_zl__ : CafInfo -> CafInfo -> bool :=
  fun a b =>
    match a with
    | MayHaveCafRefs => match b with | MayHaveCafRefs => false | _ => true end
    | NoCafRefs => match b with | NoCafRefs => false | _ => false end
    end.

Local Definition Ord__CafInfo_op_zlze__ : CafInfo -> CafInfo -> bool :=
  fun a b => negb (Ord__CafInfo_op_zl__ b a).

Local Definition Ord__CafInfo_min : CafInfo -> CafInfo -> CafInfo :=
  fun x y => if Ord__CafInfo_op_zlze__ x y : bool then x else y.

Local Definition Ord__CafInfo_max : CafInfo -> CafInfo -> CafInfo :=
  fun x y => if Ord__CafInfo_op_zlze__ x y : bool then y else x.

Local Definition Ord__CafInfo_op_zgze__ : CafInfo -> CafInfo -> bool :=
  fun a b => negb (Ord__CafInfo_op_zl__ a b).

Local Definition Ord__CafInfo_op_zg__ : CafInfo -> CafInfo -> bool :=
  fun a b => Ord__CafInfo_op_zl__ b a.

Local Definition Eq___CafInfo_op_zeze__ : CafInfo -> CafInfo -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MayHaveCafRefs, MayHaveCafRefs => true
    | NoCafRefs, NoCafRefs => true
    | _, _ => false
    end.

Local Definition Eq___CafInfo_op_zsze__ : CafInfo -> CafInfo -> bool :=
  fun x y => negb (Eq___CafInfo_op_zeze__ x y).

Program Instance Eq___CafInfo : GHC.Base.Eq_ CafInfo :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___CafInfo_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___CafInfo_op_zsze__ |}.

Program Instance Ord__CafInfo : GHC.Base.Ord CafInfo :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__CafInfo_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__CafInfo_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__CafInfo_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__CafInfo_op_zgze__ ;
         GHC.Base.compare__ := Ord__CafInfo_compare ;
         GHC.Base.max__ := Ord__CafInfo_max ;
         GHC.Base.min__ := Ord__CafInfo_min |}.

Local Definition Eq___RecSelParent_op_zeze__
   : RecSelParent -> RecSelParent -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RecSelData a1, RecSelData b1 => ((a1 GHC.Base.== b1))
    | RecSelPatSyn a1, RecSelPatSyn b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___RecSelParent_op_zsze__
   : RecSelParent -> RecSelParent -> bool :=
  fun x y => negb (Eq___RecSelParent_op_zeze__ x y).

Program Instance Eq___RecSelParent : GHC.Base.Eq_ RecSelParent :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___RecSelParent_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___RecSelParent_op_zsze__ |}.

Definition coVarDetails : IdDetails :=
  CoVarId.

Definition isCoVarDetails : IdDetails -> bool :=
  fun arg_0__ => match arg_0__ with | CoVarId => true | _ => false end.

Definition isJoinIdDetails_maybe : IdDetails -> option BasicTypes.JoinArity :=
  fun arg_0__ =>
    match arg_0__ with
    | JoinId join_arity => Some join_arity
    | _ => None
    end.

Definition mayHaveCafRefs : CafInfo -> bool :=
  fun arg_0__ => match arg_0__ with | MayHaveCafRefs => true | _ => false end.

Definition unknownArity : BasicTypes.Arity :=
  #0.

(* External variables:
     ClassId DataConId Eq Gt Lt None PatSynId Some TyConId bool comparison false negb
     option true unit BasicTypes.Arity BasicTypes.InlinePragma BasicTypes.JoinArity
     GHC.Base.Eq_ GHC.Base.Ord GHC.Base.op_zeze__ GHC.Err.Build_Default
     GHC.Err.Default GHC.Err.error GHC.Num.Int GHC.Num.fromInteger Module.Module
*)
