(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Axiom error : forall {a}, a.

(* Converted imports: *)

Require BasicTypes.
(*Require Class.
Require CoreSyn. *)
Require Data.Foldable.
(*Require DataCon.
Require Demand. *)
Require GHC.Base.
Require GHC.Num.
Require Module.
Require Name.
(* Require PatSyn.
Require VarSet. *)
Import GHC.Base.Notations.

(* Converted type declarations: *)

Definition TickBoxId :=
  GHC.Num.Int%type.

Inductive TickBoxOp : Type := TickBox : Module.Module -> TickBoxId -> TickBoxOp.

Parameter RuleInfo : Type.

(*
Inductive RuleInfo : Type := Mk_RuleInfo : list
                                           CoreSyn.CoreRule -> VarSet.DVarSet -> RuleInfo. *)

Parameter RecSelParent : Type.

(*
Inductive RecSelParent : Type := RecSelData : unit -> RecSelParent
                              |  RecSelPatSyn : PatSyn.PatSyn -> RecSelParent.
*)

Definition InlinePragInfo :=
  BasicTypes.InlinePragma%type.

Parameter IdDetails : Type.

(*

Inductive IdDetails : Type := VanillaId : IdDetails
                           |  RecSelId : RecSelParent -> bool -> IdDetails
                           |  DataConWorkId : DataCon.DataCon -> IdDetails
                           |  DataConWrapId : DataCon.DataCon -> IdDetails
                           |  ClassOpId : Class.Class -> IdDetails
                           |  PrimOpId : unit -> IdDetails
                           |  FCallId : unit -> IdDetails
                           |  TickBoxOpId : TickBoxOp -> IdDetails
                           |  DFunId : bool -> IdDetails
                           |  CoVarId : IdDetails.
*)

Inductive CafInfo : Type := MayHaveCafRefs : CafInfo
                         |  NoCafRefs : CafInfo.

Definition ArityInfo :=
  BasicTypes.Arity%type.


Parameter IdInfo : Type.

(*
Inductive IdInfo : Type := Mk_IdInfo
                          : ArityInfo -> RuleInfo -> CoreSyn.Unfolding -> CafInfo -> BasicTypes.OneShotInfo -> BasicTypes.InlinePragma -> BasicTypes.OccInfo -> Demand.StrictSig -> Demand.Demand -> ArityInfo -> IdInfo. *)

(* AUTOMATICALLY GENERATED RECORD CONSTRUCTORS *)

Parameter sel_naughty : IdDetails -> bool.

(*
Definition sel_naughty (arg_0__ : IdDetails) :=
  match arg_0__ with
    | VanillaId => error (GHC.Base.hs_string__
                         "Partial record selector: field `sel_naughty' has no match in constructor `VanillaId' of type `IdDetails'")
    | RecSelId _ sel_naughty => sel_naughty
    | DataConWorkId _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `sel_naughty' has no match in constructor `DataConWorkId' of type `IdDetails'")
    | DataConWrapId _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `sel_naughty' has no match in constructor `DataConWrapId' of type `IdDetails'")
    | ClassOpId _ => error (GHC.Base.hs_string__
                           "Partial record selector: field `sel_naughty' has no match in constructor `ClassOpId' of type `IdDetails'")
    | PrimOpId _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `sel_naughty' has no match in constructor `PrimOpId' of type `IdDetails'")
    | FCallId _ => error (GHC.Base.hs_string__
                         "Partial record selector: field `sel_naughty' has no match in constructor `FCallId' of type `IdDetails'")
    | TickBoxOpId _ => error (GHC.Base.hs_string__
                             "Partial record selector: field `sel_naughty' has no match in constructor `TickBoxOpId' of type `IdDetails'")
    | DFunId _ => error (GHC.Base.hs_string__
                        "Partial record selector: field `sel_naughty' has no match in constructor `DFunId' of type `IdDetails'")
    | CoVarId => error (GHC.Base.hs_string__
                       "Partial record selector: field `sel_naughty' has no match in constructor `CoVarId' of type `IdDetails'")
  end. *)

Parameter sel_tycon : IdDetails -> RecSelParent.

(*
Definition sel_tycon (arg_1__ : IdDetails) :=
  match arg_1__ with
    | VanillaId => error (GHC.Base.hs_string__
                         "Partial record selector: field `sel_tycon' has no match in constructor `VanillaId' of type `IdDetails'")
    | RecSelId sel_tycon _ => sel_tycon
    | DataConWorkId _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `sel_tycon' has no match in constructor `DataConWorkId' of type `IdDetails'")
    | DataConWrapId _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `sel_tycon' has no match in constructor `DataConWrapId' of type `IdDetails'")
    | ClassOpId _ => error (GHC.Base.hs_string__
                           "Partial record selector: field `sel_tycon' has no match in constructor `ClassOpId' of type `IdDetails'")
    | PrimOpId _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `sel_tycon' has no match in constructor `PrimOpId' of type `IdDetails'")
    | FCallId _ => error (GHC.Base.hs_string__
                         "Partial record selector: field `sel_tycon' has no match in constructor `FCallId' of type `IdDetails'")
    | TickBoxOpId _ => error (GHC.Base.hs_string__
                             "Partial record selector: field `sel_tycon' has no match in constructor `TickBoxOpId' of type `IdDetails'")
    | DFunId _ => error (GHC.Base.hs_string__
                        "Partial record selector: field `sel_tycon' has no match in constructor `DFunId' of type `IdDetails'")
    | CoVarId => error (GHC.Base.hs_string__
                       "Partial record selector: field `sel_tycon' has no match in constructor `CoVarId' of type `IdDetails'")
  end. *)

Parameter arityInfo : IdInfo -> ArityInfo.
Parameter cafInfo   : IdInfo -> CafInfo.
Parameter callArityInfo : IdInfo -> ArityInfo.
Parameter inlinePragInfo : IdInfo -> BasicTypes.InlinePragma.
Parameter occInfo : IdInfo -> BasicTypes.OccInfo.
Parameter oneShotInfo : IdInfo -> BasicTypes.OneShotInfo.
Parameter ruleInfo : IdInfo -> RuleInfo.

Parameter setArityInfo : IdInfo -> ArityInfo -> IdInfo.
Parameter setCafInfo   : IdInfo -> CafInfo   -> IdInfo.
Parameter setCallArityInfo : IdInfo -> ArityInfo -> IdInfo.
Parameter setInlinePragInfo : IdInfo -> BasicTypes.InlinePragma -> IdInfo.
Parameter setOccInfo : IdInfo -> BasicTypes.OccInfo -> IdInfo.
Parameter setOneShotInfo : IdInfo -> BasicTypes.OneShotInfo -> IdInfo.
Parameter setRuleInfo : IdInfo -> RuleInfo -> IdInfo.


(*
Definition arityInfo (arg_2__ : IdInfo) :=
  match arg_2__ with
    | Mk_IdInfo arityInfo _ _ _ _ _ _ _ _ _ => arityInfo
  end.

Definition cafInfo (arg_3__ : IdInfo) :=
  match arg_3__ with
    | Mk_IdInfo _ _ _ cafInfo _ _ _ _ _ _ => cafInfo
  end.

Definition callArityInfo (arg_4__ : IdInfo) :=
  match arg_4__ with
    | Mk_IdInfo _ _ _ _ _ _ _ _ _ callArityInfo => callArityInfo
  end.

Definition demandInfo (arg_5__ : IdInfo) :=
  match arg_5__ with
    | Mk_IdInfo _ _ _ _ _ _ _ _ demandInfo _ => demandInfo
  end.

Definition inlinePragInfo (arg_6__ : IdInfo) :=
  match arg_6__ with
    | Mk_IdInfo _ _ _ _ _ inlinePragInfo _ _ _ _ => inlinePragInfo
  end.

Definition occInfo (arg_7__ : IdInfo) :=
  match arg_7__ with
    | Mk_IdInfo _ _ _ _ _ _ occInfo _ _ _ => occInfo
  end.

Definition oneShotInfo (arg_8__ : IdInfo) :=
  match arg_8__ with
    | Mk_IdInfo _ _ _ _ oneShotInfo _ _ _ _ _ => oneShotInfo
  end.

Definition ruleInfo (arg_9__ : IdInfo) :=
  match arg_9__ with
    | Mk_IdInfo _ ruleInfo _ _ _ _ _ _ _ _ => ruleInfo
  end.

Definition strictnessInfo (arg_10__ : IdInfo) :=
  match arg_10__ with
    | Mk_IdInfo _ _ _ _ _ _ _ strictnessInfo _ _ => strictnessInfo
  end.

Definition unfoldingInfo (arg_11__ : IdInfo) :=
  match arg_11__ with
    | Mk_IdInfo _ _ unfoldingInfo _ _ _ _ _ _ _ => unfoldingInfo
  end.
*)

(* Midamble *)

Require Panic.

Instance Default_IdDetails : Panic.Default IdDetails := {}.
Admitted.

Instance Default_RuleInfo : Panic.Default RuleInfo := {}.
Admitted.

Instance Default_RecSelParent : Panic.Default RecSelParent := {}.
Admitted.

Instance Default_TickBoxOp : Panic.Default TickBoxOp :=
  Panic.Build_Default _ (TickBox Panic.default Panic.default).

Instance Default_CafInfo : Panic.Default CafInfo :=
  Panic.Build_Default _ MayHaveCafRefs.

Instance Default_IdInfo : Panic.Default IdInfo := {}.
Admitted.

(* Converted value declarations: *)

Parameter zapLamInfo     : IdInfo -> option IdInfo.
Parameter zapDemandInfo  : IdInfo -> option IdInfo.
Parameter zapUsageInfo   : IdInfo -> option IdInfo.
Parameter zapFragileInfo : IdInfo -> option IdInfo.



(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom missingValue : forall {a}, a.

(* Translating `instance Outputable.Outputable IdInfo.RecSelParent' failed:
   OOPS! Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable IdInfo.IdDetails' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable IdInfo.CafInfo' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable IdInfo.TickBoxOp' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

Local Definition Ord__CafInfo_compare : CafInfo -> CafInfo -> comparison :=
  fun a b =>
    match a with
      | MayHaveCafRefs => match b with
                            | MayHaveCafRefs => Eq
                            | _ => Lt
                          end
      | NoCafRefs => match b with
                       | NoCafRefs => Eq
                       | _ => Gt
                     end
    end.

Local Definition Ord__CafInfo_op_zg__ : CafInfo -> CafInfo -> bool :=
  fun a b =>
    match a with
      | MayHaveCafRefs => match b with
                            | MayHaveCafRefs => false
                            | _ => false
                          end
      | NoCafRefs => match b with
                       | NoCafRefs => false
                       | _ => true
                     end
    end.

Local Definition Ord__CafInfo_op_zgze__ : CafInfo -> CafInfo -> bool :=
  fun a b =>
    match a with
      | MayHaveCafRefs => match b with
                            | MayHaveCafRefs => true
                            | _ => false
                          end
      | NoCafRefs => match b with
                       | NoCafRefs => true
                       | _ => true
                     end
    end.

Local Definition Ord__CafInfo_op_zl__ : CafInfo -> CafInfo -> bool :=
  fun a b =>
    match a with
      | MayHaveCafRefs => match b with
                            | MayHaveCafRefs => false
                            | _ => true
                          end
      | NoCafRefs => match b with
                       | NoCafRefs => false
                       | _ => false
                     end
    end.

Local Definition Ord__CafInfo_op_zlze__ : CafInfo -> CafInfo -> bool :=
  fun a b =>
    match a with
      | MayHaveCafRefs => match b with
                            | MayHaveCafRefs => true
                            | _ => true
                          end
      | NoCafRefs => match b with
                       | NoCafRefs => true
                       | _ => false
                     end
    end.

Local Definition Ord__CafInfo_min : CafInfo -> CafInfo -> CafInfo :=
  fun x y => if Ord__CafInfo_op_zlze__ x y : bool then x else y.

Local Definition Ord__CafInfo_max : CafInfo -> CafInfo -> CafInfo :=
  fun x y => if Ord__CafInfo_op_zlze__ x y : bool then y else x.

Local Definition Eq___CafInfo_op_zeze__ : CafInfo -> CafInfo -> bool :=
  fun arg_48__ arg_49__ =>
    match arg_48__ , arg_49__ with
      | MayHaveCafRefs , MayHaveCafRefs => true
      | NoCafRefs , NoCafRefs => true
      | _ , _ => false
    end.

Local Definition Eq___CafInfo_op_zsze__ : CafInfo -> CafInfo -> bool :=
  fun a b => negb (Eq___CafInfo_op_zeze__ a b).

Program Instance Eq___CafInfo : GHC.Base.Eq_ CafInfo := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___CafInfo_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___CafInfo_op_zsze__ |}.

Program Instance Ord__CafInfo : GHC.Base.Ord CafInfo := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__CafInfo_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__CafInfo_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__CafInfo_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__CafInfo_op_zgze__ ;
      GHC.Base.compare__ := Ord__CafInfo_compare ;
      GHC.Base.max__ := Ord__CafInfo_max ;
      GHC.Base.min__ := Ord__CafInfo_min |}.

Parameter Eq___RecSelParent_op_zeze__
    : RecSelParent -> RecSelParent -> bool.
(*
  fun arg_42__ arg_43__ =>
    match arg_42__ , arg_43__ with
      | RecSelData a1 , RecSelData b1 => ((a1 GHC.Base.== b1))
      | RecSelPatSyn a1 , RecSelPatSyn b1 => ((a1 GHC.Base.== b1))
      | _ , _ => false
    end. *)

Local Definition Eq___RecSelParent_op_zsze__
    : RecSelParent -> RecSelParent -> bool :=
  fun a b => negb (Eq___RecSelParent_op_zeze__ a b).

Program Instance Eq___RecSelParent : GHC.Base.Eq_ RecSelParent := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___RecSelParent_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___RecSelParent_op_zsze__ |}.





Parameter coVarDetails : IdDetails.

Parameter emptyRuleInfo : RuleInfo.
Parameter isCoVarDetails : IdDetails -> bool.
Parameter isEmptyRuleInfo : RuleInfo -> bool.

Definition mayHaveCafRefs : CafInfo -> bool :=
  fun arg_15__ => match arg_15__ with | MayHaveCafRefs => true | _ => false end.

(*
Definition ppArityInfo : GHC.Num.Int -> Outputable.SDoc :=
  fun arg_29__ =>
    let j_32__ :=
      match arg_29__ with
        | n => Outputable.hsep (cons (id (GHC.Base.hs_string__ "Arity")) (cons
                                     (Outputable.int n) nil))
      end in
    match arg_29__ with
      | num_30__ => if num_30__ GHC.Base.== GHC.Num.fromInteger 0 : bool
                    then Outputable.empty
                    else j_32__
    end.

Definition ppCafInfo : CafInfo -> Outputable.SDoc :=
  fun arg_12__ =>
    match arg_12__ with
      | NoCafRefs => id (GHC.Base.hs_string__ "NoCafRefs")
      | MayHaveCafRefs => Outputable.empty
    end. *)

Parameter setRuleInfoHead : Name.Name -> RuleInfo -> RuleInfo.

Definition unknownArity : BasicTypes.Arity :=
  GHC.Num.fromInteger 0 : BasicTypes.Arity.

Definition vanillaCafInfo : CafInfo :=
  MayHaveCafRefs.

Parameter vanillaIdInfo : IdInfo.

Definition noCafIdInfo : IdInfo :=
  setCafInfo vanillaIdInfo NoCafRefs.
