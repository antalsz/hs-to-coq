(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require String.
Import String.StringSyntax.

(* Converted imports: *)

Require BasicTypes.
Require Core.
Require Data.Map.Internal.
Require DynFlags.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require Module.
Require SrcLoc.
Require UniqSupply.

(* Converted type declarations: *)

Inductive Tick : Type
  := | PreInlineUnconditionally : Core.Id -> Tick
  |  PostInlineUnconditionally : Core.Id -> Tick
  |  UnfoldingDone : Core.Id -> Tick
  |  RuleFired : FastString.FastString -> Tick
  |  LetFloatFromLet : Tick
  |  EtaExpansion : Core.Id -> Tick
  |  EtaReduction : Core.Id -> Tick
  |  BetaReduction : Core.Id -> Tick
  |  CaseOfCase : Core.Id -> Tick
  |  KnownBranch : Core.Id -> Tick
  |  CaseMerge : Core.Id -> Tick
  |  AltMerge : Core.Id -> Tick
  |  CaseElim : Core.Id -> Tick
  |  CaseIdentity : Core.Id -> Tick
  |  FillInCaseDefault : Core.Id -> Tick
  |  BottomFound : Tick
  |  SimplifierDone : Tick.

Definition TickCounts :=
  (Data.Map.Internal.Map Tick nat)%type.

Inductive SimplMode : Type
  := | Mk_SimplMode (sm_names : list GHC.Base.String) (sm_phase
    : BasicTypes.CompilerPhase) (sm_dflags : DynFlags.DynFlags) (sm_rules : bool)
  (sm_inline : bool) (sm_case_case : bool) (sm_eta_expand : bool)
   : SimplMode.

Inductive SimplCount : Type
  := | VerySimplCount : nat -> SimplCount
  |  Mk_SimplCount (ticks : nat) (details : TickCounts) (n_log : nat) (log1
    : list Tick) (log2 : list Tick)
   : SimplCount.

Axiom PluginPass : Type.

Inductive FloatOutSwitches : Type
  := | Mk_FloatOutSwitches (floatOutLambdas : option nat) (floatOutConstants
    : bool) (floatOutOverSatApps : bool) (floatToTopLevelOnly : bool)
   : FloatOutSwitches.

Inductive CoreWriter : Type
  := | Mk_CoreWriter (cw_simpl_count : SimplCount) : CoreWriter.

Inductive CoreToDo : Type
  := | CoreDoSimplify : nat -> SimplMode -> CoreToDo
  |  CoreDoPluginPass : GHC.Base.String -> PluginPass -> CoreToDo
  |  CoreDoFloatInwards : CoreToDo
  |  CoreDoFloatOutwards : FloatOutSwitches -> CoreToDo
  |  CoreLiberateCase : CoreToDo
  |  CoreDoPrintCore : CoreToDo
  |  CoreDoStaticArgs : CoreToDo
  |  CoreDoCallArity : CoreToDo
  |  CoreDoExitify : CoreToDo
  |  CoreDoStrictness : CoreToDo
  |  CoreDoWorkerWrapper : CoreToDo
  |  CoreDoSpecialising : CoreToDo
  |  CoreDoSpecConstr : CoreToDo
  |  CoreCSE : CoreToDo
  |  CoreDoRuleCheck : BasicTypes.CompilerPhase -> GHC.Base.String -> CoreToDo
  |  CoreDoVectorisation : CoreToDo
  |  CoreDoNothing : CoreToDo
  |  CoreDoPasses : list CoreToDo -> CoreToDo
  |  CoreDesugar : CoreToDo
  |  CoreDesugarOpt : CoreToDo
  |  CoreTidy : CoreToDo
  |  CorePrep : CoreToDo
  |  CoreOccurAnal : CoreToDo.

Inductive CoreState : Type
  := | Mk_CoreState (cs_uniq_supply : UniqSupply.UniqSupply) : CoreState.

Axiom CoreReader : Type.

Axiom CoreIOEnv : Type -> Type.

Inductive CoreM a : Type
  := | Mk_CoreM (unCoreM
    : CoreState -> CoreIOEnv (a * CoreState * CoreWriter)%type)
   : CoreM a.

Arguments Mk_CoreM {_} _.

Instance Default__Tick : GHC.Err.Default Tick :=
  GHC.Err.Build_Default _ LetFloatFromLet.

Instance Default__SimplMode : GHC.Err.Default SimplMode :=
  GHC.Err.Build_Default _ (Mk_SimplMode GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default).

Instance Default__SimplCount : GHC.Err.Default SimplCount :=
  GHC.Err.Build_Default _ (Mk_SimplCount GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default__FloatOutSwitches : GHC.Err.Default FloatOutSwitches :=
  GHC.Err.Build_Default _ (Mk_FloatOutSwitches GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default).

Instance Default__CoreWriter : GHC.Err.Default CoreWriter :=
  GHC.Err.Build_Default _ (Mk_CoreWriter GHC.Err.default).

Instance Default__CoreToDo : GHC.Err.Default CoreToDo :=
  GHC.Err.Build_Default _ CoreDoFloatInwards.

Instance Default__CoreState : GHC.Err.Default CoreState :=
  GHC.Err.Build_Default _ (Mk_CoreState GHC.Err.default).

Definition sm_case_case (arg_0__ : SimplMode) :=
  let 'Mk_SimplMode _ _ _ _ _ sm_case_case _ := arg_0__ in
  sm_case_case.

Definition sm_dflags (arg_0__ : SimplMode) :=
  let 'Mk_SimplMode _ _ sm_dflags _ _ _ _ := arg_0__ in
  sm_dflags.

Definition sm_eta_expand (arg_0__ : SimplMode) :=
  let 'Mk_SimplMode _ _ _ _ _ _ sm_eta_expand := arg_0__ in
  sm_eta_expand.

Definition sm_inline (arg_0__ : SimplMode) :=
  let 'Mk_SimplMode _ _ _ _ sm_inline _ _ := arg_0__ in
  sm_inline.

Definition sm_names (arg_0__ : SimplMode) :=
  let 'Mk_SimplMode sm_names _ _ _ _ _ _ := arg_0__ in
  sm_names.

Definition sm_phase (arg_0__ : SimplMode) :=
  let 'Mk_SimplMode _ sm_phase _ _ _ _ _ := arg_0__ in
  sm_phase.

Definition sm_rules (arg_0__ : SimplMode) :=
  let 'Mk_SimplMode _ _ _ sm_rules _ _ _ := arg_0__ in
  sm_rules.

Definition details (arg_0__ : SimplCount) :=
  match arg_0__ with
  | VerySimplCount _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `details' has no match in constructor `VerySimplCount' of type `SimplCount'")
  | Mk_SimplCount _ details _ _ _ => details
  end.

Definition log1 (arg_0__ : SimplCount) :=
  match arg_0__ with
  | VerySimplCount _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `log1' has no match in constructor `VerySimplCount' of type `SimplCount'")
  | Mk_SimplCount _ _ _ log1 _ => log1
  end.

Definition log2 (arg_0__ : SimplCount) :=
  match arg_0__ with
  | VerySimplCount _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `log2' has no match in constructor `VerySimplCount' of type `SimplCount'")
  | Mk_SimplCount _ _ _ _ log2 => log2
  end.

Definition n_log (arg_0__ : SimplCount) :=
  match arg_0__ with
  | VerySimplCount _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `n_log' has no match in constructor `VerySimplCount' of type `SimplCount'")
  | Mk_SimplCount _ _ n_log _ _ => n_log
  end.

Definition ticks (arg_0__ : SimplCount) :=
  match arg_0__ with
  | VerySimplCount _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ticks' has no match in constructor `VerySimplCount' of type `SimplCount'")
  | Mk_SimplCount ticks _ _ _ _ => ticks
  end.

Definition floatOutConstants (arg_0__ : FloatOutSwitches) :=
  let 'Mk_FloatOutSwitches _ floatOutConstants _ _ := arg_0__ in
  floatOutConstants.

Definition floatOutLambdas (arg_0__ : FloatOutSwitches) :=
  let 'Mk_FloatOutSwitches floatOutLambdas _ _ _ := arg_0__ in
  floatOutLambdas.

Definition floatOutOverSatApps (arg_0__ : FloatOutSwitches) :=
  let 'Mk_FloatOutSwitches _ _ floatOutOverSatApps _ := arg_0__ in
  floatOutOverSatApps.

Definition floatToTopLevelOnly (arg_0__ : FloatOutSwitches) :=
  let 'Mk_FloatOutSwitches _ _ _ floatToTopLevelOnly := arg_0__ in
  floatToTopLevelOnly.

Definition cw_simpl_count (arg_0__ : CoreWriter) :=
  let 'Mk_CoreWriter cw_simpl_count := arg_0__ in
  cw_simpl_count.

Definition cs_uniq_supply (arg_0__ : CoreState) :=
  let 'Mk_CoreState cs_uniq_supply := arg_0__ in
  cs_uniq_supply.

Definition unCoreM {a} (arg_0__ : CoreM a) :=
  let 'Mk_CoreM unCoreM := arg_0__ in
  unCoreM.

(* Converted value declarations: *)

Axiom zeroSimplCount : DynFlags.DynFlags -> SimplCount.

Axiom write : CoreWriter -> CoreM unit.

Axiom warnMsg : GHC.Base.String -> CoreM unit.

Axiom tickToTag : Tick -> nat.

Axiom tickString : Tick -> GHC.Base.String.

(* Skipping definition `CoreMonad.thNameToGhcName' *)

Axiom simplCountN : SimplCount -> nat.

Axiom runWhen : bool -> CoreToDo -> CoreToDo.

Axiom runMaybe : forall {a}, option a -> (a -> CoreToDo) -> CoreToDo.

(* Skipping definition `CoreMonad.runCoreM' *)

Axiom reinitializeGlobals : CoreM unit.

Axiom read : forall {a}, (CoreReader -> a) -> CoreM a.

Axiom putMsgS : GHC.Base.String -> CoreM unit.

Axiom putMsg : GHC.Base.String -> CoreM unit.

Axiom pprTickGroup : list (Tick * nat)%type -> GHC.Base.String.

Axiom pprTickCts : Tick -> GHC.Base.String.

Axiom pprTickCounts : Data.Map.Internal.Map Tick nat -> GHC.Base.String.

Axiom pprSimplCount : SimplCount -> GHC.Base.String.

Axiom pprPassDetails : CoreToDo -> GHC.Base.String.

Axiom pprFloatOutSwitches : FloatOutSwitches -> GHC.Base.String.

Axiom plusWriter : CoreWriter -> CoreWriter -> CoreWriter.

Axiom plusSimplCount : SimplCount -> SimplCount -> SimplCount.

Axiom nop : forall {a},
            CoreState -> a -> CoreIOEnv (a * CoreState * CoreWriter)%type.

(* Skipping definition `CoreMonad.msg' *)

Axiom modifyS : (CoreState -> CoreState) -> CoreM unit.

(* Skipping definition `CoreMonad.liftIOWithCount' *)

Axiom liftIOEnv : forall {a}, CoreIOEnv a -> CoreM a.

Axiom isZeroSimplCount : SimplCount -> bool.

Axiom hasDetailedCounts : SimplCount -> bool.

Axiom getVisibleOrphanMods : CoreM Module.ModuleSet.

Axiom getVerboseSimplStats : (bool -> GHC.Base.String) -> GHC.Base.String.

Axiom getSrcSpanM : CoreM SrcLoc.SrcSpan.

Axiom getS : forall {a}, (CoreState -> a) -> CoreM a.

Axiom getRuleBase : CoreM Core.RuleBase.

(* Skipping definition `CoreMonad.getPrintUnqualified' *)

(* Skipping definition `CoreMonad.getPackageFamInstEnv' *)

(* Skipping definition `CoreMonad.getOrigNameCache' *)

(* Skipping definition `CoreMonad.getHscEnv' *)

(* Skipping definition `CoreMonad.getFirstAnnotations' *)

(* Skipping definition `CoreMonad.getAnnotations' *)

Axiom fatalErrorMsgS : GHC.Base.String -> CoreM unit.

Axiom fatalErrorMsg : GHC.Base.String -> CoreM unit.

Axiom errorMsgS : GHC.Base.String -> CoreM unit.

Axiom errorMsg : GHC.Base.String -> CoreM unit.

Axiom emptyWriter : DynFlags.DynFlags -> CoreWriter.

Axiom dumpIfSet_dyn : DynFlags.DumpFlag ->
                      GHC.Base.String -> GHC.Base.String -> CoreM unit.

Axiom doSimplTick : DynFlags.DynFlags -> Tick -> SimplCount -> SimplCount.

Axiom doFreeSimplTick : Tick -> SimplCount -> SimplCount.

Axiom debugTraceMsgS : GHC.Base.String -> CoreM unit.

Axiom debugTraceMsg : GHC.Base.String -> CoreM unit.

Axiom cmpTick : Tick -> Tick -> comparison.

Axiom cmpEqTick : Tick -> Tick -> comparison.

(* Skipping definition `CoreMonad.bindsOnlyPass' *)

Axiom addTick : TickCounts -> Tick -> TickCounts.

Axiom addSimplCount : SimplCount -> CoreM unit.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreMonad.Outputable__SimplMode' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreMonad.Outputable__FloatOutSwitches' *)

Instance Eq___Tick : GHC.Base.Eq_ Tick.
Proof.
Admitted.

Instance Ord__Tick : GHC.Base.Ord Tick.
Proof.
Admitted.

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreMonad.Outputable__Tick' *)

(* Skipping all instances of class `HscTypes.MonadThings', including
   `CoreMonad.MonadThings__CoreM' *)

Instance HasModule__CoreM : Module.HasModule CoreM.
Proof.
Admitted.

Instance HasDynFlags__CoreM : DynFlags.HasDynFlags CoreM.
Proof.
Admitted.

(* Skipping all instances of class `Control.Monad.IO.Class.MonadIO', including
   `CoreMonad.MonadIO__CoreM' *)

Instance Functor__CoreM : GHC.Base.Functor CoreM.
Proof.
Admitted.

Instance Applicative__CoreM : GHC.Base.Applicative CoreM.
Proof.
Admitted.

Instance Monad__CoreM : GHC.Base.Monad CoreM.
Proof.
Admitted.

Instance MonadUnique__CoreM : UniqSupply.MonadUnique CoreM.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `CoreMonad.MonadPlus__CoreM' *)

(* Skipping all instances of class `GHC.Base.Alternative', including
   `CoreMonad.Alternative__CoreM' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `CoreMonad.Outputable__CoreToDo' *)

(* External variables:
     Type bool comparison list nat op_zt__ option unit BasicTypes.CompilerPhase
     Core.Id Core.RuleBase Data.Map.Internal.Map DynFlags.DumpFlag DynFlags.DynFlags
     DynFlags.HasDynFlags FastString.FastString GHC.Base.Applicative GHC.Base.Eq_
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Ord GHC.Base.String
     GHC.Err.Build_Default GHC.Err.Default GHC.Err.default GHC.Err.error
     Module.HasModule Module.ModuleSet SrcLoc.SrcSpan UniqSupply.MonadUnique
     UniqSupply.UniqSupply
*)
