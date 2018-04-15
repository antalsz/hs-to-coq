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

data RuleInfo
  = RuleInfo
        [CoreRule]
        DVarSet         -- Locally-defined free vars of *both* LHS and RHS


*)

(* -------------------- *)


Parameter RuleInfo : Type.
Parameter emptyRuleInfo : RuleInfo.
Parameter isEmptyRuleInfo : RuleInfo -> bool.

Instance Default_RuleInfo : GHC.Err.Default RuleInfo :=
  GHC.Err.Build_Default _ emptyRuleInfo.


(* -------------------- *)

(* Converted imports: *)

Require BasicTypes.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require Module.
Require Util.
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

Inductive IdInfo : Type
  := Mk_IdInfo
   : ArityInfo ->
     RuleInfo ->
     unit ->
     CafInfo ->
     BasicTypes.OneShotInfo ->
     BasicTypes.InlinePragma ->
     BasicTypes.OccInfo -> unit -> unit -> ArityInfo -> LevityInfo -> IdInfo.

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

Definition arityInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo arityInfo _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  arityInfo.

Definition cafInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ cafInfo _ _ _ _ _ _ _ := arg_0__ in
  cafInfo.

Definition callArityInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ _ _ _ callArityInfo _ := arg_0__ in
  callArityInfo.

Definition demandInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ _ _ demandInfo _ _ := arg_0__ in
  demandInfo.

Definition inlinePragInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ inlinePragInfo _ _ _ _ _ := arg_0__ in
  inlinePragInfo.

Definition levityInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ _ _ _ _ levityInfo := arg_0__ in
  levityInfo.

Definition occInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ occInfo _ _ _ _ := arg_0__ in
  occInfo.

Definition oneShotInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ oneShotInfo _ _ _ _ _ _ := arg_0__ in
  oneShotInfo.

Definition ruleInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ ruleInfo _ _ _ _ _ _ _ _ _ := arg_0__ in
  ruleInfo.

Definition strictnessInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ _ _ _ _ _ strictnessInfo _ _ _ := arg_0__ in
  strictnessInfo.

Definition unfoldingInfo (arg_0__ : IdInfo) :=
  let 'Mk_IdInfo _ _ unfoldingInfo _ _ _ _ _ _ _ _ := arg_0__ in
  unfoldingInfo.
(* Midamble *)

Require GHC.Err.


Instance Default_TickBoxOp : GHC.Err.Default TickBoxOp :=
  GHC.Err.Build_Default _ (TickBox GHC.Err.default GHC.Err.default).

Instance Default_CafInfo : GHC.Err.Default CafInfo :=
  GHC.Err.Build_Default _ MayHaveCafRefs.

Instance Default_IdInfo : GHC.Err.Default IdInfo :=
  GHC.Err.Build_Default _ (Mk_IdInfo GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default_RecSelParent : GHC.Err.Default RecSelParent :=
  GHC.Err.Build_Default _ (RecSelData GHC.Err.default).


(* Converted value declarations: *)

(* Skipping instance Outputable__LevityInfo of class Outputable *)

(* Skipping instance Outputable__IdDetails of class Outputable *)

(* Skipping instance Outputable__TickBoxOp of class Outputable *)

(* Skipping instance Outputable__CafInfo of class Outputable *)

(* Skipping instance Outputable__RecSelParent of class Outputable *)

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

Local Definition Ord__CafInfo_max : CafInfo -> CafInfo -> CafInfo :=
  fun x y => if Ord__CafInfo_op_zlze__ x y : bool then y else x.

Local Definition Ord__CafInfo_min : CafInfo -> CafInfo -> CafInfo :=
  fun x y => if Ord__CafInfo_op_zlze__ x y : bool then x else y.

Local Definition Ord__CafInfo_op_zg__ : CafInfo -> CafInfo -> bool :=
  fun a b => Ord__CafInfo_op_zl__ b a.

Local Definition Ord__CafInfo_op_zgze__ : CafInfo -> CafInfo -> bool :=
  fun a b => negb (Ord__CafInfo_op_zl__ a b).

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

Definition setArityInfo : IdInfo -> ArityInfo -> IdInfo :=
  fun info ar =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo ar ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__ oneShotInfo_4__
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

Definition setCafInfo : IdInfo -> CafInfo -> IdInfo :=
  fun info caf =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ caf oneShotInfo_4__
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

Definition setCallArityInfo : IdInfo -> ArityInfo -> IdInfo :=
  fun info ar =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
              oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              ar levityInfo_10__.

Definition zapCallArityInfo : IdInfo -> IdInfo :=
  fun info => setCallArityInfo info #0.

Definition setDemandInfo : IdInfo -> unit -> IdInfo :=
  fun info dd =>
    GHC.Prim.seq dd (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                            oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ dd
                            callArityInfo_9__ levityInfo_10__).

Definition setInlinePragInfo : IdInfo -> BasicTypes.InlinePragma -> IdInfo :=
  fun info pr =>
    GHC.Prim.seq pr (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                            oneShotInfo_4__ pr occInfo_6__ strictnessInfo_7__ demandInfo_8__
                            callArityInfo_9__ levityInfo_10__).

Definition setNeverLevPoly `{Util.HasDebugCallStack}
   : IdInfo -> unit -> IdInfo :=
  fun info ty =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
              oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ NeverLevityPolymorphic.

Definition setOccInfo : IdInfo -> BasicTypes.OccInfo -> IdInfo :=
  fun info oc =>
    GHC.Prim.seq oc (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                            oneShotInfo_4__ inlinePragInfo_5__ oc strictnessInfo_7__ demandInfo_8__
                            callArityInfo_9__ levityInfo_10__).

Definition zapTailCallInfo : IdInfo -> option IdInfo :=
  fun info =>
    let 'occ := occInfo info in
    let safe_occ :=
      match occ with
      | BasicTypes.ManyOccs occ_tail_1__ =>
          BasicTypes.ManyOccs BasicTypes.NoTailCallInfo
      | BasicTypes.IAmDead =>
          GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
      | BasicTypes.OneOcc occ_in_lam_2__ occ_one_br_3__ occ_int_cxt_4__
      occ_tail_5__ =>
          BasicTypes.OneOcc occ_in_lam_2__ occ_one_br_3__ occ_int_cxt_4__
                            BasicTypes.NoTailCallInfo
      | BasicTypes.IAmALoopBreaker occ_rules_only_6__ occ_tail_7__ =>
          BasicTypes.IAmALoopBreaker occ_rules_only_6__ BasicTypes.NoTailCallInfo
      end in
    if BasicTypes.isAlwaysTailCalled occ : bool
    then Some (setOccInfo info safe_occ) else
    None.

Definition setOneShotInfo : IdInfo -> BasicTypes.OneShotInfo -> IdInfo :=
  fun info lb =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__ lb
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

Definition setRuleInfo : IdInfo -> RuleInfo -> IdInfo :=
  fun info sp =>
    GHC.Prim.seq sp (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ sp unfoldingInfo_2__ cafInfo_3__ oneShotInfo_4__
                            inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
                            callArityInfo_9__ levityInfo_10__).

Definition setStrictnessInfo : IdInfo -> unit -> IdInfo :=
  fun info dd =>
    GHC.Prim.seq dd (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                            oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ dd demandInfo_8__
                            callArityInfo_9__ levityInfo_10__).

Definition setUnfoldingInfo : IdInfo -> unit -> IdInfo :=
  fun info uf =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ uf cafInfo_3__ oneShotInfo_4__
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

Definition unknownArity : BasicTypes.Arity :=
  #0.

Definition vanillaCafInfo : CafInfo :=
  MayHaveCafRefs.

Definition vanillaIdInfo : IdInfo :=
  Mk_IdInfo unknownArity emptyRuleInfo tt vanillaCafInfo BasicTypes.NoOneShotInfo
            BasicTypes.defaultInlinePragma BasicTypes.noOccInfo tt tt unknownArity
            NoLevityInfo.

Definition noCafIdInfo : IdInfo :=
  setCafInfo vanillaIdInfo NoCafRefs.

Definition zapDemandInfo : IdInfo -> option IdInfo :=
  fun info =>
    Some (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
             oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
             callArityInfo_9__ levityInfo_10__ := info in
          Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                    oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ tt
                    callArityInfo_9__ levityInfo_10__).

Definition zapLamInfo : IdInfo -> option IdInfo :=
  fun '((Mk_IdInfo _ _ _ _ _ _ occ _ demand _ _ as info)) =>
    let is_safe_dmd := fun dmd => negb (false) in
    let safe_occ :=
      match occ with
      | BasicTypes.OneOcc _ _ _ _ =>
          match occ with
          | BasicTypes.ManyOccs _ =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          | BasicTypes.IAmDead =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          | BasicTypes.OneOcc occ_in_lam_2__ occ_one_br_3__ occ_int_cxt_4__
          occ_tail_5__ =>
              BasicTypes.OneOcc true occ_one_br_3__ occ_int_cxt_4__ BasicTypes.NoTailCallInfo
          | BasicTypes.IAmALoopBreaker _ _ =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          end
      | BasicTypes.IAmALoopBreaker _ _ =>
          match occ with
          | BasicTypes.ManyOccs occ_tail_12__ =>
              BasicTypes.ManyOccs BasicTypes.NoTailCallInfo
          | BasicTypes.IAmDead =>
              GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
          | BasicTypes.OneOcc occ_in_lam_13__ occ_one_br_14__ occ_int_cxt_15__
          occ_tail_16__ =>
              BasicTypes.OneOcc occ_in_lam_13__ occ_one_br_14__ occ_int_cxt_15__
                                BasicTypes.NoTailCallInfo
          | BasicTypes.IAmALoopBreaker occ_rules_only_17__ occ_tail_18__ =>
              BasicTypes.IAmALoopBreaker occ_rules_only_17__ BasicTypes.NoTailCallInfo
          end
      | _other => occ
      end in
    let is_safe_occ :=
      fun arg_27__ =>
        let 'occ := arg_27__ in
        if BasicTypes.isAlwaysTailCalled occ : bool then false else
        match arg_27__ with
        | BasicTypes.OneOcc in_lam _ _ _ => in_lam
        | _other => true
        end in
    if andb (is_safe_occ occ) (is_safe_dmd demand) : bool then None else
    Some (let 'Mk_IdInfo arityInfo_31__ ruleInfo_32__ unfoldingInfo_33__
             cafInfo_34__ oneShotInfo_35__ inlinePragInfo_36__ occInfo_37__
             strictnessInfo_38__ demandInfo_39__ callArityInfo_40__ levityInfo_41__ :=
            info in
          Mk_IdInfo arityInfo_31__ ruleInfo_32__ unfoldingInfo_33__ cafInfo_34__
                    oneShotInfo_35__ inlinePragInfo_36__ safe_occ strictnessInfo_38__ tt
                    callArityInfo_40__ levityInfo_41__).

Definition zapUsageInfo : IdInfo -> option IdInfo :=
  fun info =>
    Some (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
             oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
             callArityInfo_9__ levityInfo_10__ := info in
          Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                    oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ tt
                    callArityInfo_9__ levityInfo_10__).

Definition zapUsedOnceInfo : IdInfo -> option IdInfo :=
  fun info =>
    Some (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
             oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
             callArityInfo_9__ levityInfo_10__ := info in
          Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                    oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ tt tt callArityInfo_9__
                    levityInfo_10__).

(* External variables:
     ClassId DataConId Eq Gt Lt None PatSynId RuleInfo Some TyConId andb bool
     comparison emptyRuleInfo false negb option true tt unit BasicTypes.Arity
     BasicTypes.IAmALoopBreaker BasicTypes.IAmDead BasicTypes.InlinePragma
     BasicTypes.JoinArity BasicTypes.ManyOccs BasicTypes.NoOneShotInfo
     BasicTypes.NoTailCallInfo BasicTypes.OccInfo BasicTypes.OneOcc
     BasicTypes.OneShotInfo BasicTypes.defaultInlinePragma
     BasicTypes.isAlwaysTailCalled BasicTypes.noOccInfo GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.compare__ GHC.Base.max__ GHC.Base.min__ GHC.Base.op_zeze__
     GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____ GHC.Base.op_zl____
     GHC.Base.op_zlze____ GHC.Base.op_zsze____ GHC.Err.Build_Default GHC.Err.Default
     GHC.Err.error GHC.Num.Int GHC.Num.fromInteger GHC.Prim.seq Module.Module
     Util.HasDebugCallStack
*)
