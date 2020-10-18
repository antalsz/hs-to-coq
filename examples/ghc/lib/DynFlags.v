(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BinNums.
Require Data.Either.
Require Data.Set.Internal.
Require EnumSet.
Require GHC.Base.
Require GHC.Char.
Require GHC.Err.
Require GHC.Num.
Require Module.
Require SrcLoc.

(* Converted type declarations: *)

Inductive Way : Type
  := | WayCustom : GHC.Base.String -> Way
  |  WayThreaded : Way
  |  WayDebug : Way
  |  WayProf : Way
  |  WayEventLog : Way
  |  WayDyn : Way.

Inductive WarningFlag : Type
  := | Opt_WarnDuplicateExports : WarningFlag
  |  Opt_WarnDuplicateConstraints : WarningFlag
  |  Opt_WarnRedundantConstraints : WarningFlag
  |  Opt_WarnHiShadows : WarningFlag
  |  Opt_WarnImplicitPrelude : WarningFlag
  |  Opt_WarnIncompletePatterns : WarningFlag
  |  Opt_WarnIncompleteUniPatterns : WarningFlag
  |  Opt_WarnIncompletePatternsRecUpd : WarningFlag
  |  Opt_WarnOverflowedLiterals : WarningFlag
  |  Opt_WarnEmptyEnumerations : WarningFlag
  |  Opt_WarnMissingFields : WarningFlag
  |  Opt_WarnMissingImportList : WarningFlag
  |  Opt_WarnMissingMethods : WarningFlag
  |  Opt_WarnMissingSignatures : WarningFlag
  |  Opt_WarnMissingLocalSignatures : WarningFlag
  |  Opt_WarnNameShadowing : WarningFlag
  |  Opt_WarnOverlappingPatterns : WarningFlag
  |  Opt_WarnTypeDefaults : WarningFlag
  |  Opt_WarnMonomorphism : WarningFlag
  |  Opt_WarnUnusedTopBinds : WarningFlag
  |  Opt_WarnUnusedLocalBinds : WarningFlag
  |  Opt_WarnUnusedPatternBinds : WarningFlag
  |  Opt_WarnUnusedImports : WarningFlag
  |  Opt_WarnUnusedMatches : WarningFlag
  |  Opt_WarnUnusedTypePatterns : WarningFlag
  |  Opt_WarnUnusedForalls : WarningFlag
  |  Opt_WarnWarningsDeprecations : WarningFlag
  |  Opt_WarnDeprecatedFlags : WarningFlag
  |  Opt_WarnAMP : WarningFlag
  |  Opt_WarnMissingMonadFailInstances : WarningFlag
  |  Opt_WarnSemigroup : WarningFlag
  |  Opt_WarnDodgyExports : WarningFlag
  |  Opt_WarnDodgyImports : WarningFlag
  |  Opt_WarnOrphans : WarningFlag
  |  Opt_WarnAutoOrphans : WarningFlag
  |  Opt_WarnIdentities : WarningFlag
  |  Opt_WarnTabs : WarningFlag
  |  Opt_WarnUnrecognisedPragmas : WarningFlag
  |  Opt_WarnDodgyForeignImports : WarningFlag
  |  Opt_WarnUnusedDoBind : WarningFlag
  |  Opt_WarnWrongDoBind : WarningFlag
  |  Opt_WarnAlternativeLayoutRuleTransitional : WarningFlag
  |  Opt_WarnUnsafe : WarningFlag
  |  Opt_WarnSafe : WarningFlag
  |  Opt_WarnTrustworthySafe : WarningFlag
  |  Opt_WarnMissedSpecs : WarningFlag
  |  Opt_WarnAllMissedSpecs : WarningFlag
  |  Opt_WarnUnsupportedCallingConventions : WarningFlag
  |  Opt_WarnUnsupportedLlvmVersion : WarningFlag
  |  Opt_WarnInlineRuleShadowing : WarningFlag
  |  Opt_WarnTypedHoles : WarningFlag
  |  Opt_WarnPartialTypeSignatures : WarningFlag
  |  Opt_WarnMissingExportedSignatures : WarningFlag
  |  Opt_WarnUntickedPromotedConstructors : WarningFlag
  |  Opt_WarnDerivingTypeable : WarningFlag
  |  Opt_WarnDeferredTypeErrors : WarningFlag
  |  Opt_WarnDeferredOutOfScopeVariables : WarningFlag
  |  Opt_WarnNonCanonicalMonadInstances : WarningFlag
  |  Opt_WarnNonCanonicalMonadFailInstances : WarningFlag
  |  Opt_WarnNonCanonicalMonoidInstances : WarningFlag
  |  Opt_WarnMissingPatternSynonymSignatures : WarningFlag
  |  Opt_WarnUnrecognisedWarningFlags : WarningFlag
  |  Opt_WarnSimplifiableClassConstraints : WarningFlag
  |  Opt_WarnCPPUndef : WarningFlag
  |  Opt_WarnUnbangedStrictPatterns : WarningFlag
  |  Opt_WarnMissingHomeModules : WarningFlag
  |  Opt_WarnPartialFields : WarningFlag
  |  Opt_WarnMissingExportList : WarningFlag.

Inductive WarnReason : Type
  := | NoReason : WarnReason
  |  Reason : WarningFlag -> WarnReason
  |  ErrReason : (option WarningFlag) -> WarnReason.

Definition TurnOnFlag :=
  bool%type.

Inductive TrustFlag : Type
  := | TrustPackage : GHC.Base.String -> TrustFlag
  |  DistrustPackage : GHC.Base.String -> TrustFlag.

Inductive SseVersion : Type
  := | SSE1 : SseVersion
  |  SSE2 : SseVersion
  |  SSE3 : SseVersion
  |  SSE4 : SseVersion
  |  SSE42 : SseVersion.

Axiom Settings : Type.

Inductive SafeHaskellMode : Type
  := | Sf_None : SafeHaskellMode
  |  Sf_Unsafe : SafeHaskellMode
  |  Sf_Trustworthy : SafeHaskellMode
  |  Sf_Safe : SafeHaskellMode.

Inductive RtsOptsEnabled : Type
  := | RtsOptsNone : RtsOptsEnabled
  |  RtsOptsIgnore : RtsOptsEnabled
  |  RtsOptsIgnoreAll : RtsOptsEnabled
  |  RtsOptsSafeOnly : RtsOptsEnabled
  |  RtsOptsAll : RtsOptsEnabled.

Inductive ProfAuto : Type
  := | NoProfAuto : ProfAuto
  |  ProfAutoAll : ProfAuto
  |  ProfAutoTop : ProfAuto
  |  ProfAutoExports : ProfAuto
  |  ProfAutoCalls : ProfAuto.

Inductive PkgConfRef : Type
  := | GlobalPkgConf : PkgConfRef
  |  UserPkgConf : PkgConfRef
  |  PkgConfFile : GHC.Base.String -> PkgConfRef.

Inductive PackageDBFlag : Type
  := | PackageDB : PkgConfRef -> PackageDBFlag
  |  NoUserPackageDB : PackageDBFlag
  |  NoGlobalPackageDB : PackageDBFlag
  |  ClearPackageDBs : PackageDBFlag.

Inductive PackageArg : Type
  := | Mk_PackageArg : GHC.Base.String -> PackageArg
  |  UnitIdArg : Module.UnitId -> PackageArg.

Inductive Option : Type
  := | FileOption : GHC.Base.String -> GHC.Base.String -> Option
  |  Mk_Option : GHC.Base.String -> Option.

Inductive OnOff a : Type := | On : a -> OnOff a |  Off : a -> OnOff a.

Inductive ModRenaming : Type
  := | Mk_ModRenaming (modRenamingWithImplicit : bool) (modRenamings
    : list (Module.ModuleName * Module.ModuleName)%type)
   : ModRenaming.

Inductive PackageFlag : Type
  := | ExposePackage : GHC.Base.String -> PackageArg -> ModRenaming -> PackageFlag
  |  HidePackage : GHC.Base.String -> PackageFlag.

Inductive LlvmTarget : Type
  := | Mk_LlvmTarget (lDataLayout : GHC.Base.String) (lCPU : GHC.Base.String)
  (lAttributes : list GHC.Base.String)
   : LlvmTarget.

Definition LlvmTargets :=
  (list (GHC.Base.String * LlvmTarget)%type)%type.

Inductive LinkerInfo : Type
  := | GnuLD : list Option -> LinkerInfo
  |  GnuGold : list Option -> LinkerInfo
  |  LlvmLLD : list Option -> LinkerInfo
  |  DarwinLD : list Option -> LinkerInfo
  |  SolarisLD : list Option -> LinkerInfo
  |  AixLD : list Option -> LinkerInfo
  |  UnknownLD : LinkerInfo.

Inductive Language : Type := | Haskell98 : Language |  Haskell2010 : Language.

Inductive IgnorePackageFlag : Type
  := | IgnorePackage : GHC.Base.String -> IgnorePackageFlag.

Inductive HscTarget : Type
  := | HscC : HscTarget
  |  HscAsm : HscTarget
  |  HscLlvm : HscTarget
  |  HscInterpreted : HscTarget
  |  HscNothing : HscTarget.

Inductive GhcMode : Type
  := | CompManager : GhcMode
  |  OneShot : GhcMode
  |  MkDepend : GhcMode.

Inductive GhcLink : Type
  := | NoLink : GhcLink
  |  LinkBinary : GhcLink
  |  LinkInMemory : GhcLink
  |  LinkDynLib : GhcLink
  |  LinkStaticLib : GhcLink.

Inductive GeneralFlag : Type
  := | Opt_DumpToFile : GeneralFlag
  |  Opt_D_faststring_stats : GeneralFlag
  |  Opt_D_dump_minimal_imports : GeneralFlag
  |  Opt_DoCoreLinting : GeneralFlag
  |  Opt_DoStgLinting : GeneralFlag
  |  Opt_DoCmmLinting : GeneralFlag
  |  Opt_DoAsmLinting : GeneralFlag
  |  Opt_DoAnnotationLinting : GeneralFlag
  |  Opt_NoLlvmMangler : GeneralFlag
  |  Opt_FastLlvm : GeneralFlag
  |  Opt_WarnIsError : GeneralFlag
  |  Opt_ShowWarnGroups : GeneralFlag
  |  Opt_HideSourcePaths : GeneralFlag
  |  Opt_PrintExplicitForalls : GeneralFlag
  |  Opt_PrintExplicitKinds : GeneralFlag
  |  Opt_PrintExplicitCoercions : GeneralFlag
  |  Opt_PrintExplicitRuntimeReps : GeneralFlag
  |  Opt_PrintEqualityRelations : GeneralFlag
  |  Opt_PrintUnicodeSyntax : GeneralFlag
  |  Opt_PrintExpandedSynonyms : GeneralFlag
  |  Opt_PrintPotentialInstances : GeneralFlag
  |  Opt_PrintTypecheckerElaboration : GeneralFlag
  |  Opt_CallArity : GeneralFlag
  |  Opt_Exitification : GeneralFlag
  |  Opt_Strictness : GeneralFlag
  |  Opt_LateDmdAnal : GeneralFlag
  |  Opt_KillAbsence : GeneralFlag
  |  Opt_KillOneShot : GeneralFlag
  |  Opt_FullLaziness : GeneralFlag
  |  Opt_FloatIn : GeneralFlag
  |  Opt_Specialise : GeneralFlag
  |  Opt_SpecialiseAggressively : GeneralFlag
  |  Opt_CrossModuleSpecialise : GeneralFlag
  |  Opt_StaticArgumentTransformation : GeneralFlag
  |  Opt_CSE : GeneralFlag
  |  Opt_StgCSE : GeneralFlag
  |  Opt_LiberateCase : GeneralFlag
  |  Opt_SpecConstr : GeneralFlag
  |  Opt_SpecConstrKeen : GeneralFlag
  |  Opt_DoLambdaEtaExpansion : GeneralFlag
  |  Opt_IgnoreAsserts : GeneralFlag
  |  Opt_DoEtaReduction : GeneralFlag
  |  Opt_CaseMerge : GeneralFlag
  |  Opt_CaseFolding : GeneralFlag
  |  Opt_UnboxStrictFields : GeneralFlag
  |  Opt_UnboxSmallStrictFields : GeneralFlag
  |  Opt_DictsCheap : GeneralFlag
  |  Opt_EnableRewriteRules : GeneralFlag
  |  Opt_Vectorise : GeneralFlag
  |  Opt_VectorisationAvoidance : GeneralFlag
  |  Opt_RegsGraph : GeneralFlag
  |  Opt_RegsIterative : GeneralFlag
  |  Opt_PedanticBottoms : GeneralFlag
  |  Opt_LlvmTBAA : GeneralFlag
  |  Opt_LlvmPassVectorsInRegisters : GeneralFlag
  |  Opt_LlvmFillUndefWithGarbage : GeneralFlag
  |  Opt_IrrefutableTuples : GeneralFlag
  |  Opt_CmmSink : GeneralFlag
  |  Opt_CmmElimCommonBlocks : GeneralFlag
  |  Opt_OmitYields : GeneralFlag
  |  Opt_FunToThunk : GeneralFlag
  |  Opt_DictsStrict : GeneralFlag
  |  Opt_DmdTxDictSel : GeneralFlag
  |  Opt_Loopification : GeneralFlag
  |  Opt_CprAnal : GeneralFlag
  |  Opt_WorkerWrapper : GeneralFlag
  |  Opt_SolveConstantDicts : GeneralFlag
  |  Opt_AlignmentSanitisation : GeneralFlag
  |  Opt_CatchBottoms : GeneralFlag
  |  Opt_SimplPreInlining : GeneralFlag
  |  Opt_IgnoreInterfacePragmas : GeneralFlag
  |  Opt_OmitInterfacePragmas : GeneralFlag
  |  Opt_ExposeAllUnfoldings : GeneralFlag
  |  Opt_WriteInterface : GeneralFlag
  |  Opt_AutoSccsOnIndividualCafs : GeneralFlag
  |  Opt_ProfCountEntries : GeneralFlag
  |  Opt_Pp : GeneralFlag
  |  Opt_ForceRecomp : GeneralFlag
  |  Opt_IgnoreOptimChanges : GeneralFlag
  |  Opt_IgnoreHpcChanges : GeneralFlag
  |  Opt_ExcessPrecision : GeneralFlag
  |  Opt_EagerBlackHoling : GeneralFlag
  |  Opt_NoHsMain : GeneralFlag
  |  Opt_SplitObjs : GeneralFlag
  |  Opt_SplitSections : GeneralFlag
  |  Opt_StgStats : GeneralFlag
  |  Opt_HideAllPackages : GeneralFlag
  |  Opt_HideAllPluginPackages : GeneralFlag
  |  Opt_PrintBindResult : GeneralFlag
  |  Opt_Haddock : GeneralFlag
  |  Opt_HaddockOptions : GeneralFlag
  |  Opt_BreakOnException : GeneralFlag
  |  Opt_BreakOnError : GeneralFlag
  |  Opt_PrintEvldWithShow : GeneralFlag
  |  Opt_PrintBindContents : GeneralFlag
  |  Opt_GenManifest : GeneralFlag
  |  Opt_EmbedManifest : GeneralFlag
  |  Opt_SharedImplib : GeneralFlag
  |  Opt_BuildingCabalPackage : GeneralFlag
  |  Opt_IgnoreDotGhci : GeneralFlag
  |  Opt_GhciSandbox : GeneralFlag
  |  Opt_GhciHistory : GeneralFlag
  |  Opt_LocalGhciHistory : GeneralFlag
  |  Opt_HelpfulErrors : GeneralFlag
  |  Opt_DeferTypeErrors : GeneralFlag
  |  Opt_DeferTypedHoles : GeneralFlag
  |  Opt_DeferOutOfScopeVariables : GeneralFlag
  |  Opt_PIC : GeneralFlag
  |  Opt_PIE : GeneralFlag
  |  Opt_PICExecutable : GeneralFlag
  |  Opt_SccProfilingOn : GeneralFlag
  |  Opt_Ticky : GeneralFlag
  |  Opt_Ticky_Allocd : GeneralFlag
  |  Opt_Ticky_LNE : GeneralFlag
  |  Opt_Ticky_Dyn_Thunk : GeneralFlag
  |  Opt_RPath : GeneralFlag
  |  Opt_RelativeDynlibPaths : GeneralFlag
  |  Opt_Hpc : GeneralFlag
  |  Opt_FlatCache : GeneralFlag
  |  Opt_ExternalInterpreter : GeneralFlag
  |  Opt_OptimalApplicativeDo : GeneralFlag
  |  Opt_VersionMacros : GeneralFlag
  |  Opt_WholeArchiveHsLibs : GeneralFlag
  |  Opt_ErrorSpans : GeneralFlag
  |  Opt_DiagnosticsShowCaret : GeneralFlag
  |  Opt_PprCaseAsLet : GeneralFlag
  |  Opt_PprShowTicks : GeneralFlag
  |  Opt_ShowHoleConstraints : GeneralFlag
  |  Opt_ShowLoadedModules : GeneralFlag
  |  Opt_SuppressCoercions : GeneralFlag
  |  Opt_SuppressVarKinds : GeneralFlag
  |  Opt_SuppressModulePrefixes : GeneralFlag
  |  Opt_SuppressTypeApplications : GeneralFlag
  |  Opt_SuppressIdInfo : GeneralFlag
  |  Opt_SuppressUnfoldings : GeneralFlag
  |  Opt_SuppressTypeSignatures : GeneralFlag
  |  Opt_SuppressUniques : GeneralFlag
  |  Opt_SuppressStgFreeVars : GeneralFlag
  |  Opt_SuppressTicks : GeneralFlag
  |  Opt_AutoLinkPackages : GeneralFlag
  |  Opt_ImplicitImportQualified : GeneralFlag
  |  Opt_KeepHiDiffs : GeneralFlag
  |  Opt_KeepHcFiles : GeneralFlag
  |  Opt_KeepSFiles : GeneralFlag
  |  Opt_KeepTmpFiles : GeneralFlag
  |  Opt_KeepRawTokenStream : GeneralFlag
  |  Opt_KeepLlvmFiles : GeneralFlag
  |  Opt_KeepHiFiles : GeneralFlag
  |  Opt_KeepOFiles : GeneralFlag
  |  Opt_BuildDynamicToo : GeneralFlag
  |  Opt_DistrustAllPackages : GeneralFlag
  |  Opt_PackageTrust : GeneralFlag
  |  Opt_G_NoStateHack : GeneralFlag
  |  Opt_G_NoOptCoercion : GeneralFlag.

Axiom FlushOut : Type.

Axiom FlushErr : Type.

Axiom FlagSpec : Type -> Type.

Inductive FilesToClean : Type
  := | Mk_FilesToClean (ftcGhcSession : (Data.Set.Internal.Set_ GHC.Base.String))
  (ftcCurrentModule : (Data.Set.Internal.Set_ GHC.Base.String))
   : FilesToClean.

Inductive DynLibLoader : Type
  := | Deployable : DynLibLoader
  |  SystemDependent : DynLibLoader.

Axiom DynFlags : Type.

Record HasDynFlags__Dict m := HasDynFlags__Dict_Build {
  getDynFlags__ : m DynFlags }.

Definition HasDynFlags m :=
  forall r__, (HasDynFlags__Dict m -> r__) -> r__.
Existing Class HasDynFlags.

Definition getDynFlags `{g__0__ : HasDynFlags m} : m DynFlags :=
  g__0__ _ (getDynFlags__ m).

Inductive DumpFlag : Type
  := | Opt_D_dump_cmm : DumpFlag
  |  Opt_D_dump_cmm_from_stg : DumpFlag
  |  Opt_D_dump_cmm_raw : DumpFlag
  |  Opt_D_dump_cmm_verbose : DumpFlag
  |  Opt_D_dump_cmm_cfg : DumpFlag
  |  Opt_D_dump_cmm_cbe : DumpFlag
  |  Opt_D_dump_cmm_switch : DumpFlag
  |  Opt_D_dump_cmm_proc : DumpFlag
  |  Opt_D_dump_cmm_sp : DumpFlag
  |  Opt_D_dump_cmm_sink : DumpFlag
  |  Opt_D_dump_cmm_caf : DumpFlag
  |  Opt_D_dump_cmm_procmap : DumpFlag
  |  Opt_D_dump_cmm_split : DumpFlag
  |  Opt_D_dump_cmm_info : DumpFlag
  |  Opt_D_dump_cmm_cps : DumpFlag
  |  Opt_D_dump_asm : DumpFlag
  |  Opt_D_dump_asm_native : DumpFlag
  |  Opt_D_dump_asm_liveness : DumpFlag
  |  Opt_D_dump_asm_regalloc : DumpFlag
  |  Opt_D_dump_asm_regalloc_stages : DumpFlag
  |  Opt_D_dump_asm_conflicts : DumpFlag
  |  Opt_D_dump_asm_stats : DumpFlag
  |  Opt_D_dump_asm_expanded : DumpFlag
  |  Opt_D_dump_llvm : DumpFlag
  |  Opt_D_dump_core_stats : DumpFlag
  |  Opt_D_dump_deriv : DumpFlag
  |  Opt_D_dump_ds : DumpFlag
  |  Opt_D_dump_foreign : DumpFlag
  |  Opt_D_dump_inlinings : DumpFlag
  |  Opt_D_dump_rule_firings : DumpFlag
  |  Opt_D_dump_rule_rewrites : DumpFlag
  |  Opt_D_dump_simpl_trace : DumpFlag
  |  Opt_D_dump_occur_anal : DumpFlag
  |  Opt_D_dump_parsed : DumpFlag
  |  Opt_D_dump_parsed_ast : DumpFlag
  |  Opt_D_dump_rn : DumpFlag
  |  Opt_D_dump_rn_ast : DumpFlag
  |  Opt_D_dump_shape : DumpFlag
  |  Opt_D_dump_simpl : DumpFlag
  |  Opt_D_dump_simpl_iterations : DumpFlag
  |  Opt_D_dump_spec : DumpFlag
  |  Opt_D_dump_prep : DumpFlag
  |  Opt_D_dump_stg : DumpFlag
  |  Opt_D_dump_call_arity : DumpFlag
  |  Opt_D_dump_exitify : DumpFlag
  |  Opt_D_dump_stranal : DumpFlag
  |  Opt_D_dump_str_signatures : DumpFlag
  |  Opt_D_dump_tc : DumpFlag
  |  Opt_D_dump_tc_ast : DumpFlag
  |  Opt_D_dump_types : DumpFlag
  |  Opt_D_dump_rules : DumpFlag
  |  Opt_D_dump_cse : DumpFlag
  |  Opt_D_dump_worker_wrapper : DumpFlag
  |  Opt_D_dump_rn_trace : DumpFlag
  |  Opt_D_dump_rn_stats : DumpFlag
  |  Opt_D_dump_opt_cmm : DumpFlag
  |  Opt_D_dump_simpl_stats : DumpFlag
  |  Opt_D_dump_cs_trace : DumpFlag
  |  Opt_D_dump_tc_trace : DumpFlag
  |  Opt_D_dump_ec_trace : DumpFlag
  |  Opt_D_dump_if_trace : DumpFlag
  |  Opt_D_dump_vt_trace : DumpFlag
  |  Opt_D_dump_splices : DumpFlag
  |  Opt_D_th_dec_file : DumpFlag
  |  Opt_D_dump_BCOs : DumpFlag
  |  Opt_D_dump_vect : DumpFlag
  |  Opt_D_dump_ticked : DumpFlag
  |  Opt_D_dump_rtti : DumpFlag
  |  Opt_D_source_stats : DumpFlag
  |  Opt_D_verbose_stg2stg : DumpFlag
  |  Opt_D_dump_hi : DumpFlag
  |  Opt_D_dump_hi_diffs : DumpFlag
  |  Opt_D_dump_mod_cycles : DumpFlag
  |  Opt_D_dump_mod_map : DumpFlag
  |  Opt_D_dump_timings : DumpFlag
  |  Opt_D_dump_view_pattern_commoning : DumpFlag
  |  Opt_D_verbose_core2core : DumpFlag
  |  Opt_D_dump_debug : DumpFlag
  |  Opt_D_dump_json : DumpFlag
  |  Opt_D_ppr_debug : DumpFlag
  |  Opt_D_no_debug_output : DumpFlag.

Inductive Deprecation : Type
  := | NotDeprecated : Deprecation
  |  Deprecated : Deprecation.

Record ContainsDynFlags__Dict t := ContainsDynFlags__Dict_Build {
  extractDynFlags__ : t -> DynFlags }.

Definition ContainsDynFlags t :=
  forall r__, (ContainsDynFlags__Dict t -> r__) -> r__.
Existing Class ContainsDynFlags.

Definition extractDynFlags `{g__0__ : ContainsDynFlags t} : t -> DynFlags :=
  g__0__ _ (extractDynFlags__ t).

Inductive CompilerInfo : Type
  := | GCC : CompilerInfo
  |  Clang : CompilerInfo
  |  AppleClang : CompilerInfo
  |  AppleClang51 : CompilerInfo
  |  UnknownCC : CompilerInfo.

Inductive BmiVersion : Type := | BMI1 : BmiVersion |  BMI2 : BmiVersion.

Arguments On {_} _.

Arguments Off {_} _.

Instance Default__Way : GHC.Err.Default Way :=
  GHC.Err.Build_Default _ WayThreaded.

Instance Default__WarningFlag : GHC.Err.Default WarningFlag :=
  GHC.Err.Build_Default _ Opt_WarnDuplicateExports.

Instance Default__WarnReason : GHC.Err.Default WarnReason :=
  GHC.Err.Build_Default _ NoReason.

Instance Default__SseVersion : GHC.Err.Default SseVersion :=
  GHC.Err.Build_Default _ SSE1.

Instance Default__SafeHaskellMode : GHC.Err.Default SafeHaskellMode :=
  GHC.Err.Build_Default _ Sf_None.

Instance Default__RtsOptsEnabled : GHC.Err.Default RtsOptsEnabled :=
  GHC.Err.Build_Default _ RtsOptsNone.

Instance Default__ProfAuto : GHC.Err.Default ProfAuto :=
  GHC.Err.Build_Default _ NoProfAuto.

Instance Default__PkgConfRef : GHC.Err.Default PkgConfRef :=
  GHC.Err.Build_Default _ GlobalPkgConf.

Instance Default__PackageDBFlag : GHC.Err.Default PackageDBFlag :=
  GHC.Err.Build_Default _ NoUserPackageDB.

Instance Default__ModRenaming : GHC.Err.Default ModRenaming :=
  GHC.Err.Build_Default _ (Mk_ModRenaming GHC.Err.default GHC.Err.default).

Instance Default__LlvmTarget : GHC.Err.Default LlvmTarget :=
  GHC.Err.Build_Default _ (Mk_LlvmTarget GHC.Err.default GHC.Err.default
                         GHC.Err.default).

Instance Default__LinkerInfo : GHC.Err.Default LinkerInfo :=
  GHC.Err.Build_Default _ UnknownLD.

Instance Default__Language : GHC.Err.Default Language :=
  GHC.Err.Build_Default _ Haskell98.

Instance Default__HscTarget : GHC.Err.Default HscTarget :=
  GHC.Err.Build_Default _ HscC.

Instance Default__GhcMode : GHC.Err.Default GhcMode :=
  GHC.Err.Build_Default _ CompManager.

Instance Default__GhcLink : GHC.Err.Default GhcLink :=
  GHC.Err.Build_Default _ NoLink.

Instance Default__GeneralFlag : GHC.Err.Default GeneralFlag :=
  GHC.Err.Build_Default _ Opt_DumpToFile.

Instance Default__FilesToClean : GHC.Err.Default FilesToClean :=
  GHC.Err.Build_Default _ (Mk_FilesToClean GHC.Err.default GHC.Err.default).

Instance Default__DynLibLoader : GHC.Err.Default DynLibLoader :=
  GHC.Err.Build_Default _ Deployable.

Instance Default__DumpFlag : GHC.Err.Default DumpFlag :=
  GHC.Err.Build_Default _ Opt_D_dump_cmm.

Instance Default__Deprecation : GHC.Err.Default Deprecation :=
  GHC.Err.Build_Default _ NotDeprecated.

Instance Default__CompilerInfo : GHC.Err.Default CompilerInfo :=
  GHC.Err.Build_Default _ GCC.

Instance Default__BmiVersion : GHC.Err.Default BmiVersion :=
  GHC.Err.Build_Default _ BMI1.

(* Midamble *)

Instance Unpeel_IgnorePackageFlag : Prim.Unpeel IgnorePackageFlag GHC.Base.String :=
  Prim.Build_Unpeel _ _ (fun x => match x with | IgnorePackage y => y end) IgnorePackage.


Instance Default__DynFlags
   : GHC.Err.Default DynFlags.
Admitted.

(* Converted value declarations: *)

(* Skipping definition `DynFlags.xopt_unset' *)

(* Skipping definition `DynFlags.xopt_set' *)

(* Skipping definition `DynFlags.xopt' *)

(* Skipping definition `DynFlags.xFlagsDeps' *)

(* Skipping definition `DynFlags.xFlags' *)

Axiom wopt_unset_fatal : DynFlags -> WarningFlag -> DynFlags.

(* Skipping definition `DynFlags.wopt_unset' *)

Axiom wopt_set_fatal : DynFlags -> WarningFlag -> DynFlags.

(* Skipping definition `DynFlags.wopt_set' *)

Axiom wopt_fatal : WarningFlag -> DynFlags -> bool.

(* Skipping definition `DynFlags.wopt' *)

(* Skipping definition `DynFlags.whenGeneratingDynamicToo' *)

(* Skipping definition `DynFlags.whenCannotGenerateDynamicToo' *)

(* Skipping definition `DynFlags.wayUnsetGeneralFlags' *)

Axiom wayTag : Way -> GHC.Base.String.

Axiom wayRTSOnly : Way -> bool.

(* Skipping definition `DynFlags.wayOptl' *)

(* Skipping definition `DynFlags.wayOptc' *)

(* Skipping definition `DynFlags.wayOptP' *)

(* Skipping definition `DynFlags.wayGeneralFlags' *)

Axiom wayDesc : Way -> GHC.Base.String.

Axiom warningHierarchies : list (list GHC.Base.String).

Axiom warningGroups : list (GHC.Base.String * list WarningFlag)%type.

Axiom wWarningFlagsDeps : list (Deprecation * FlagSpec WarningFlag)%type.

Axiom wWarningFlags : list (FlagSpec WarningFlag).

Axiom wORD_SIZE_IN_BITS : DynFlags -> BinNums.N.

Axiom wORD_SIZE : DynFlags -> BinNums.N.

Axiom wORDS_BIGENDIAN : DynFlags -> bool.

Axiom versionedFilePath : DynFlags -> GHC.Base.String.

(* Skipping definition `DynFlags.versionedAppDir' *)

(* Skipping definition `DynFlags.v_unsafeGlobalDynFlags' *)

Axiom useUnicodeSyntax : DynFlags -> bool.

(* Skipping definition `DynFlags.useInstead' *)

Axiom updateWays : DynFlags -> DynFlags.

(* Skipping definition `DynFlags.updOptLevel' *)

(* Skipping definition `DynFlags.updM' *)

(* Skipping definition `DynFlags.upd' *)

(* Skipping definition `DynFlags.unusedBindsFlags' *)

Axiom unsafeGlobalDynFlags : DynFlags.

Axiom unsafeFlagsForInfer : list (GHC.Base.String * (DynFlags -> SrcLoc.SrcSpan)
                                  *
                                  (DynFlags -> bool) *
                                  (DynFlags -> DynFlags))%type.

Axiom unsafeFlags : list (GHC.Base.String * (DynFlags -> SrcLoc.SrcSpan) *
                          (DynFlags -> bool) *
                          (DynFlags -> DynFlags))%type.

(* Skipping definition `DynFlags.unrecognisedWarning' *)

(* Skipping definition `DynFlags.unSetWarningFlag' *)

(* Skipping definition `DynFlags.unSetGeneralFlag'' *)

(* Skipping definition `DynFlags.unSetGeneralFlag' *)

(* Skipping definition `DynFlags.unSetFatalWarningFlag' *)

(* Skipping definition `DynFlags.unSetExtensionFlag'' *)

(* Skipping definition `DynFlags.unSetExtensionFlag' *)

Axiom turnOn : TurnOnFlag.

Axiom turnOff : TurnOnFlag.

(* Skipping definition `DynFlags.trustPackage' *)

Axiom topDir : DynFlags -> GHC.Base.String.

Axiom tmpDir : DynFlags -> GHC.Base.String.

Axiom thisUnitIdInsts : DynFlags ->
                        list (Module.ModuleName * Module.Module)%type.

Axiom thisPackage : DynFlags -> Module.UnitId.

Axiom thisComponentId : DynFlags -> Module.ComponentId.

Axiom targetRetainsAllBindings : HscTarget -> bool.

(* Skipping definition `DynFlags.targetPlatform' *)

Axiom tablesNextToCode : DynFlags -> bool.

Axiom tICKY_BIN_COUNT : DynFlags -> BinNums.N.

Axiom tARGET_MIN_INT : DynFlags -> GHC.Num.Integer.

Axiom tARGET_MAX_WORD : DynFlags -> GHC.Num.Integer.

Axiom tARGET_MAX_INT : DynFlags -> GHC.Num.Integer.

Axiom tAG_MASK : DynFlags -> BinNums.N.

Axiom tAG_BITS : DynFlags -> BinNums.N.

Axiom systemPackageConfig : DynFlags -> GHC.Base.String.

Axiom supportedLanguagesAndExtensions : list GHC.Base.String.

Axiom supportedLanguages : list GHC.Base.String.

(* Skipping definition `DynFlags.supportedLanguageOverlays' *)

(* Skipping definition `DynFlags.supportedExtensions' *)

Axiom standardWarnings : list WarningFlag.

Axiom split_marker : GHC.Char.Char.

Axiom splitPathList : GHC.Base.String -> list GHC.Base.String.

Axiom smallestGroups : WarningFlag -> list GHC.Base.String.

Axiom showOpt : Option -> GHC.Base.String.

Axiom shouldUseColor : DynFlags -> bool.

(* Skipping definition `DynFlags.setWarningFlag' *)

(* Skipping definition `DynFlags.setWarnUnsafe' *)

(* Skipping definition `DynFlags.setWarnSafe' *)

(* Skipping definition `DynFlags.setVerbosity' *)

(* Skipping definition `DynFlags.setVerboseCore2Core' *)

(* Skipping definition `DynFlags.setUnsafeGlobalDynFlags' *)

Axiom setUnitIdInsts : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.setUnitId' *)

(* Skipping definition `DynFlags.setTmpDir' *)

(* Skipping definition `DynFlags.setTargetWithPlatform' *)

(* Skipping definition `DynFlags.setTarget' *)

Axiom setStubDir : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.setSafeHaskell' *)

(* Skipping definition `DynFlags.setRtsOptsEnabled' *)

(* Skipping definition `DynFlags.setRtsOpts' *)

Axiom setPgmP : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.setPackageTrust' *)

(* Skipping definition `DynFlags.setOverlappingInsts' *)

Axiom setOutputHi : option GHC.Base.String -> DynFlags -> DynFlags.

Axiom setOutputFile : option GHC.Base.String -> DynFlags -> DynFlags.

Axiom setOutputDir : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.setOptLevel' *)

(* Skipping definition `DynFlags.setOptHpcDir' *)

Axiom setObjectSuf : GHC.Base.String -> DynFlags -> DynFlags.

Axiom setObjectDir : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.setObjTarget' *)

(* Skipping definition `DynFlags.setMainIs' *)

(* Skipping definition `DynFlags.setLogAction' *)

(* Skipping definition `DynFlags.setLanguage' *)

Axiom setJsonLogAction : DynFlags -> DynFlags.

Axiom setInteractivePrint : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.setIncoherentInsts' *)

Axiom setHiSuf : GHC.Base.String -> DynFlags -> DynFlags.

Axiom setHiDir : GHC.Base.String -> DynFlags -> DynFlags.

Axiom setHcSuf : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.setGeneralFlag'' *)

(* Skipping definition `DynFlags.setGeneralFlag' *)

(* Skipping definition `DynFlags.setGenDeriving' *)

(* Skipping definition `DynFlags.setFatalWarningFlag' *)

(* Skipping definition `DynFlags.setExtensionFlag'' *)

(* Skipping definition `DynFlags.setExtensionFlag' *)

Axiom setDynOutputFile : option GHC.Base.String -> DynFlags -> DynFlags.

Axiom setDynObjectSuf : GHC.Base.String -> DynFlags -> DynFlags.

Axiom setDynHiSuf : GHC.Base.String -> DynFlags -> DynFlags.

Axiom setDylibInstallName : GHC.Base.String -> DynFlags -> DynFlags.

Axiom setDumpPrefixForce : option GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.setDumpFlag'' *)

(* Skipping definition `DynFlags.setDumpFlag' *)

Axiom setDumpDir : GHC.Base.String -> DynFlags -> DynFlags.

Axiom setDepMakefile : GHC.Base.String -> DynFlags -> DynFlags.

Axiom setDepIncludePkgDeps : bool -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.setDebugLevel' *)

(* Skipping definition `DynFlags.setDPHOpt' *)

Axiom setComponentId : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.sepArg' *)

Axiom safeLanguageOn : DynFlags -> bool.

Axiom safeInferOn : DynFlags -> bool.

(* Skipping definition `DynFlags.safeImportsOn' *)

Axiom safeImplicitImpsReq : DynFlags -> bool.

Axiom safeHaskellOn : DynFlags -> bool.

Axiom safeHaskellFlagsDeps : list (Deprecation * FlagSpec SafeHaskellMode)%type.

Axiom safeFlagCheck : bool ->
                      DynFlags -> (DynFlags * list (SrcLoc.Located GHC.Base.String))%type.

Axiom safeDirectImpsReq : DynFlags -> bool.

Axiom sTD_HDR_SIZE : DynFlags -> BinNums.N.

Axiom sIZEOF_StgUpdateFrame_NoHdr : DynFlags -> BinNums.N.

Axiom sIZEOF_StgSmallMutArrPtrs_NoHdr : DynFlags -> BinNums.N.

Axiom sIZEOF_StgSMPThunkHeader : DynFlags -> BinNums.N.

Axiom sIZEOF_StgMutArrPtrs_NoHdr : DynFlags -> BinNums.N.

Axiom sIZEOF_StgFunInfoExtraRev : DynFlags -> BinNums.N.

Axiom sIZEOF_StgArrBytes_NoHdr : DynFlags -> BinNums.N.

Axiom sIZEOF_CostCentreStack : DynFlags -> BinNums.N.

(* Skipping definition `DynFlags.rtsIsProfiled' *)

(* Skipping definition `DynFlags.removeWayDyn' *)

(* Skipping definition `DynFlags.removeUserPkgConf' *)

(* Skipping definition `DynFlags.removeGlobalPkgConf' *)

Axiom rawSettings : DynFlags -> list (GHC.Base.String * GHC.Base.String)%type.

Axiom rESERVED_STACK_WORDS : DynFlags -> BinNums.N.

Axiom rESERVED_C_STACK_BYTES : DynFlags -> BinNums.N.

(* Skipping definition `DynFlags.putLogMsg' *)

Axiom projectVersion : DynFlags -> GHC.Base.String.

Axiom programName : DynFlags -> GHC.Base.String.

Axiom positionIndependent : DynFlags -> bool.

Axiom picPOpts : DynFlags -> list GHC.Base.String.

Axiom picCCOpts : DynFlags -> list GHC.Base.String.

Axiom pgm_windres : DynFlags -> GHC.Base.String.

Axiom pgm_s : DynFlags -> (GHC.Base.String * list Option)%type.

Axiom pgm_ranlib : DynFlags -> GHC.Base.String.

Axiom pgm_lo : DynFlags -> (GHC.Base.String * list Option)%type.

Axiom pgm_libtool : DynFlags -> GHC.Base.String.

Axiom pgm_lcc : DynFlags -> (GHC.Base.String * list Option)%type.

Axiom pgm_lc : DynFlags -> (GHC.Base.String * list Option)%type.

Axiom pgm_l : DynFlags -> (GHC.Base.String * list Option)%type.

Axiom pgm_i : DynFlags -> GHC.Base.String.

Axiom pgm_dll : DynFlags -> (GHC.Base.String * list Option)%type.

Axiom pgm_c : DynFlags -> (GHC.Base.String * list Option)%type.

Axiom pgm_ar : DynFlags -> GHC.Base.String.

Axiom pgm_a : DynFlags -> (GHC.Base.String * list Option)%type.

Axiom pgm_T : DynFlags -> GHC.Base.String.

Axiom pgm_P : DynFlags -> (GHC.Base.String * list Option)%type.

Axiom pgm_L : DynFlags -> GHC.Base.String.

Axiom pgm_F : DynFlags -> GHC.Base.String.

Axiom parseUnitIdInsts : GHC.Base.String ->
                         list (Module.ModuleName * Module.Module)%type.

(* Skipping definition `DynFlags.parseUnitIdArg' *)

(* Skipping definition `DynFlags.parsePackageFlag' *)

(* Skipping definition `DynFlags.parsePackageArg' *)

(* Skipping definition `DynFlags.parseDynamicFlagsFull' *)

(* Skipping definition `DynFlags.parseDynamicFlagsCmdLine' *)

(* Skipping definition `DynFlags.parseDynamicFilePragma' *)

Axiom parseDynLibLoaderMode : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.package_flags_deps' *)

Axiom packageTrustOn : DynFlags -> bool.

Axiom packageFlagsChanged : DynFlags -> DynFlags -> bool.

Axiom pROF_HDR_SIZE : DynFlags -> BinNums.N.

Axiom optimisationFlags : EnumSet.EnumSet GeneralFlag.

Axiom opt_windres : DynFlags -> list GHC.Base.String.

Axiom opt_lo : DynFlags -> list GHC.Base.String.

Axiom opt_lcc : DynFlags -> list GHC.Base.String.

Axiom opt_lc : DynFlags -> list GHC.Base.String.

Axiom opt_l : DynFlags -> list GHC.Base.String.

Axiom opt_i : DynFlags -> list GHC.Base.String.

Axiom opt_c : DynFlags -> list GHC.Base.String.

Axiom opt_a : DynFlags -> list GHC.Base.String.

Axiom opt_P : DynFlags -> list GHC.Base.String.

Axiom opt_L : DynFlags -> list GHC.Base.String.

Axiom opt_F : DynFlags -> list GHC.Base.String.

Axiom optLevelFlags : list (list BinNums.N * GeneralFlag)%type.

(* Skipping definition `DynFlags.optIntSuffixM' *)

Axiom oFFSET_stgGCFun : DynFlags -> BinNums.N.

Axiom oFFSET_stgGCEnter1 : DynFlags -> BinNums.N.

Axiom oFFSET_stgEagerBlackholeInfo : DynFlags -> BinNums.N.

Axiom oFFSET_bdescr_start : DynFlags -> BinNums.N.

Axiom oFFSET_bdescr_free : DynFlags -> BinNums.N.

Axiom oFFSET_bdescr_flags : DynFlags -> BinNums.N.

Axiom oFFSET_bdescr_blocks : DynFlags -> BinNums.N.

Axiom oFFSET_StgUpdateFrame_updatee : DynFlags -> BinNums.N.

Axiom oFFSET_StgTSO_stackobj : DynFlags -> BinNums.N.

Axiom oFFSET_StgTSO_cccs : DynFlags -> BinNums.N.

Axiom oFFSET_StgTSO_alloc_limit : DynFlags -> BinNums.N.

Axiom oFFSET_StgStack_stack : DynFlags -> BinNums.N.

Axiom oFFSET_StgStack_sp : DynFlags -> BinNums.N.

Axiom oFFSET_StgSmallMutArrPtrs_ptrs : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rZMM6 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rZMM5 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rZMM4 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rZMM3 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rZMM2 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rZMM1 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rYMM6 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rYMM5 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rYMM4 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rYMM3 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rYMM2 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rYMM1 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rXMM6 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rXMM5 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rXMM4 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rXMM3 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rXMM2 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rXMM1 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rSpLim : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rSp : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rR9 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rR8 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rR7 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rR6 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rR5 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rR4 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rR3 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rR2 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rR10 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rR1 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rL1 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rHpLim : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rHpAlloc : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rHp : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rF6 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rF5 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rF4 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rF3 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rF2 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rF1 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rD6 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rD5 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rD4 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rD3 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rD2 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rD1 : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rCurrentTSO : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rCurrentNursery : DynFlags -> BinNums.N.

Axiom oFFSET_StgRegTable_rCCCS : DynFlags -> BinNums.N.

Axiom oFFSET_StgMutArrPtrs_size : DynFlags -> BinNums.N.

Axiom oFFSET_StgMutArrPtrs_ptrs : DynFlags -> BinNums.N.

Axiom oFFSET_StgHeader_ldvw : DynFlags -> BinNums.N.

Axiom oFFSET_StgHeader_ccs : DynFlags -> BinNums.N.

Axiom oFFSET_StgFunInfoExtraRev_arity : DynFlags -> BinNums.N.

Axiom oFFSET_StgFunInfoExtraFwd_arity : DynFlags -> BinNums.N.

Axiom oFFSET_StgEntCounter_registeredp : DynFlags -> BinNums.N.

Axiom oFFSET_StgEntCounter_link : DynFlags -> BinNums.N.

Axiom oFFSET_StgEntCounter_entry_count : DynFlags -> BinNums.N.

Axiom oFFSET_StgEntCounter_allocs : DynFlags -> BinNums.N.

Axiom oFFSET_StgEntCounter_allocd : DynFlags -> BinNums.N.

Axiom oFFSET_StgArrBytes_bytes : DynFlags -> BinNums.N.

Axiom oFFSET_CostCentreStack_scc_count : DynFlags -> BinNums.N.

Axiom oFFSET_CostCentreStack_mem_alloc : DynFlags -> BinNums.N.

Axiom oFFSET_Capability_r : DynFlags -> BinNums.N.

(* Skipping definition `DynFlags.nop' *)

(* Skipping definition `DynFlags.noArgM' *)

(* Skipping definition `DynFlags.noArg' *)

Axiom negatableFlagsDeps : list (Deprecation * FlagSpec GeneralFlag)%type.

Axiom mkTablesNextToCode : bool -> bool.

(* Skipping definition `DynFlags.mkFlag' *)

Axiom mkBuildTag : list Way -> GHC.Base.String.

Axiom minusWeverythingOpts : list WarningFlag.

Axiom minusWcompatOpts : list WarningFlag.

Axiom minusWallOpts : list WarningFlag.

Axiom minusWOpts : list WarningFlag.

(* Skipping definition `DynFlags.make_ord_flag' *)

(* Skipping definition `DynFlags.make_dep_flag' *)

Axiom makeDynFlagsConsistent : DynFlags ->
                               (DynFlags * list (SrcLoc.Located GHC.Base.String))%type.

Axiom mUT_ARR_PTRS_CARD_BITS : DynFlags -> BinNums.N.

Axiom mIN_PAYLOAD_SIZE : DynFlags -> BinNums.N.

Axiom mIN_INTLIKE : DynFlags -> BinNums.N.

Axiom mIN_CHARLIKE : DynFlags -> BinNums.N.

Axiom mAX_XMM_REG : DynFlags -> BinNums.N.

Axiom mAX_Vanilla_REG : DynFlags -> BinNums.N.

Axiom mAX_SPEC_SELECTEE_SIZE : DynFlags -> BinNums.N.

Axiom mAX_SPEC_AP_SIZE : DynFlags -> BinNums.N.

Axiom mAX_Real_XMM_REG : DynFlags -> BinNums.N.

Axiom mAX_Real_Vanilla_REG : DynFlags -> BinNums.N.

Axiom mAX_Real_Long_REG : DynFlags -> BinNums.N.

Axiom mAX_Real_Float_REG : DynFlags -> BinNums.N.

Axiom mAX_Real_Double_REG : DynFlags -> BinNums.N.

Axiom mAX_PTR_TAG : DynFlags -> BinNums.N.

Axiom mAX_Long_REG : DynFlags -> BinNums.N.

Axiom mAX_INTLIKE : DynFlags -> BinNums.N.

Axiom mAX_Float_REG : DynFlags -> BinNums.N.

Axiom mAX_Double_REG : DynFlags -> BinNums.N.

Axiom mAX_CHARLIKE : DynFlags -> BinNums.N.

Axiom languageFlagsDeps : list (Deprecation * FlagSpec Language)%type.

(* Skipping definition `DynFlags.languageExtensions' *)

(* Skipping definition `DynFlags.lang_set' *)

Axiom lDV_SHIFT : DynFlags -> BinNums.N.

(* Skipping definition `DynFlags.jsonLogOutput' *)

(* Skipping definition `DynFlags.jsonLogFinaliser' *)

(* Skipping definition `DynFlags.jsonLogAction' *)

Axiom isSseEnabled : DynFlags -> bool.

Axiom isSse4_2Enabled : DynFlags -> bool.

Axiom isSse2Enabled : DynFlags -> bool.

Axiom isOneShot : GhcMode -> bool.

Axiom isObjectTarget : HscTarget -> bool.

Axiom isNoLink : GhcLink -> bool.

Axiom isBmiEnabled : DynFlags -> bool.

Axiom isBmi2Enabled : DynFlags -> bool.

Axiom isAvxEnabled : DynFlags -> bool.

Axiom isAvx512pfEnabled : DynFlags -> bool.

Axiom isAvx512fEnabled : DynFlags -> bool.

Axiom isAvx512erEnabled : DynFlags -> bool.

Axiom isAvx512cdEnabled : DynFlags -> bool.

Axiom isAvx2Enabled : DynFlags -> bool.

Axiom interpreterProfiled : DynFlags -> bool.

(* Skipping definition `DynFlags.interpreterDynamic' *)

(* Skipping definition `DynFlags.interpretPackageEnv' *)

Axiom interpWays : list Way.

(* Skipping definition `DynFlags.intSuffixM' *)

(* Skipping definition `DynFlags.intSuffix' *)

(* Skipping definition `DynFlags.initDynFlags' *)

(* Skipping definition `DynFlags.impliedXFlags' *)

Axiom impliedOffGFlags : list (GeneralFlag * TurnOnFlag * GeneralFlag)%type.

(* Skipping definition `DynFlags.impliedGFlags' *)

(* Skipping definition `DynFlags.ignorePackage' *)

(* Skipping definition `DynFlags.ifGeneratingDynamicToo' *)

(* Skipping definition `DynFlags.ifCannotGenerateDynamicToo' *)

Axiom iLDV_STATE_USE : DynFlags -> GHC.Num.Integer.

Axiom iLDV_STATE_CREATE : DynFlags -> GHC.Num.Integer.

Axiom iLDV_CREATE_MASK : DynFlags -> GHC.Num.Integer.

(* Skipping definition `DynFlags.hidePackage' *)

Axiom hideFlag : forall {a},
                 (Deprecation * FlagSpec a)%type -> (Deprecation * FlagSpec a)%type.

Axiom hasPprDebug : DynFlags -> bool.

Axiom hasNoStateHack : DynFlags -> bool.

Axiom hasNoOptCoercion : DynFlags -> bool.

Axiom hasNoDebugOutput : DynFlags -> bool.

(* Skipping definition `DynFlags.hasArg' *)

(* Skipping definition `DynFlags.gopt_unset' *)

Axiom gopt_set : DynFlags -> GeneralFlag -> DynFlags.

Axiom gopt : GeneralFlag -> DynFlags -> bool.

(* Skipping definition `DynFlags.glasgowExtsFlags' *)

Axiom ghciUsagePath : DynFlags -> GHC.Base.String.

Axiom ghcUsagePath : DynFlags -> GHC.Base.String.

Axiom getVerbFlags : DynFlags -> list GHC.Base.String.

Axiom getOpts : forall {a}, DynFlags -> (DynFlags -> list a) -> list a.

(* Skipping definition `DynFlags.generateDynamicTooConditional' *)

(* Skipping definition `DynFlags.forceRecompile' *)

(* Skipping definition `DynFlags.floatSuffix' *)

(* Skipping definition `DynFlags.flattenExtensionFlags' *)

(* Skipping definition `DynFlags.flagsPackage' *)

Axiom flagsForCompletion : bool -> list GHC.Base.String.

(* Skipping definition `DynFlags.flagsDynamic' *)

(* Skipping definition `DynFlags.flagsAllDeps' *)

(* Skipping definition `DynFlags.flagsAll' *)

Axiom flagSpecOf : WarningFlag -> option (FlagSpec WarningFlag).

(* Skipping definition `DynFlags.flagSpec'' *)

Axiom flagSpec : forall {flag},
                 GHC.Base.String -> flag -> (Deprecation * FlagSpec flag)%type.

(* Skipping definition `DynFlags.flagHiddenSpec'' *)

Axiom flagHiddenSpec : forall {flag},
                       GHC.Base.String -> flag -> (Deprecation * FlagSpec flag)%type.

(* Skipping definition `DynFlags.flagGhciSpec'' *)

Axiom flagGhciSpec : forall {flag},
                     GHC.Base.String -> flag -> (Deprecation * FlagSpec flag)%type.

(* Skipping definition `DynFlags.fLangFlagsDeps' *)

(* Skipping definition `DynFlags.fLangFlags' *)

Axiom fFlagsDeps : list (Deprecation * FlagSpec GeneralFlag)%type.

Axiom fFlags : list (FlagSpec GeneralFlag).

Axiom extraGccViaCFlags : DynFlags -> list GHC.Base.String.

(* Skipping definition `DynFlags.exposePluginPackageId' *)

(* Skipping definition `DynFlags.exposePluginPackage' *)

(* Skipping definition `DynFlags.exposePackageId' *)

Axiom exposePackage' : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.exposePackage' *)

(* Skipping definition `DynFlags.enableUnusedBinds' *)

(* Skipping definition `DynFlags.enableGlasgowExts' *)

Axiom emptyFilesToClean : FilesToClean.

(* Skipping definition `DynFlags.dynamic_flags_deps' *)

Axiom dynamicTooMkDynamicDynFlags : DynFlags -> DynFlags.

(* Skipping definition `DynFlags.dynamicGhc' *)

(* Skipping definition `DynFlags.dynFlagDependencies' *)

Axiom dopt_unset : DynFlags -> DumpFlag -> DynFlags.

Axiom dopt_set : DynFlags -> DumpFlag -> DynFlags.

(* Skipping definition `DynFlags.dopt' *)

(* Skipping definition `DynFlags.distrustPackage' *)

(* Skipping definition `DynFlags.disableUnusedBinds' *)

(* Skipping definition `DynFlags.disableGlasgowExts' *)

Axiom deprecatedForExtension : GHC.Base.String -> TurnOnFlag -> GHC.Base.String.

(* Skipping definition `DynFlags.depFlagSpecOp'' *)

(* Skipping definition `DynFlags.depFlagSpecOp' *)

Axiom depFlagSpecCond : forall {flag},
                        GHC.Base.String ->
                        flag ->
                        (TurnOnFlag -> bool) -> GHC.Base.String -> (Deprecation * FlagSpec flag)%type.

(* Skipping definition `DynFlags.depFlagSpec'' *)

Axiom depFlagSpec : forall {flag},
                    GHC.Base.String ->
                    flag -> GHC.Base.String -> (Deprecation * FlagSpec flag)%type.

(* Skipping definition `DynFlags.default_PIC' *)

Axiom defaultWays : Settings -> list Way.

(* Skipping definition `DynFlags.defaultObjectTarget' *)

(* Skipping definition `DynFlags.defaultLogOutput' *)

(* Skipping definition `DynFlags.defaultLogActionHPutStrDoc' *)

(* Skipping definition `DynFlags.defaultLogActionHPrintDoc' *)

(* Skipping definition `DynFlags.defaultLogAction' *)

(* Skipping definition `DynFlags.defaultHscTarget' *)

Axiom defaultGlobalDynFlags : DynFlags.

Axiom defaultFlushOut : FlushOut.

(* Skipping definition `DynFlags.defaultFlushErr' *)

Axiom defaultFlags : Settings -> list GeneralFlag.

(* Skipping definition `DynFlags.defaultFatalMessager' *)

Axiom defaultDynFlags : Settings -> LlvmTargets -> DynFlags.

Axiom decodeSize : GHC.Base.String -> GHC.Num.Integer.

Axiom dYNAMIC_BY_DEFAULT : DynFlags -> bool.

Axiom dOUBLE_SIZE : DynFlags -> BinNums.N.

Axiom dFlagsDeps : list (Deprecation * FlagSpec GeneralFlag)%type.

Axiom compilerInfo : DynFlags -> list (GHC.Base.String * GHC.Base.String)%type.

(* Skipping definition `DynFlags.combineSafeFlags' *)

(* Skipping definition `DynFlags.clearPkgConf' *)

(* Skipping definition `DynFlags.checkTemplateHaskellOk' *)

Axiom checkOptLevel : BinNums.N ->
                      DynFlags -> Data.Either.Either GHC.Base.String DynFlags.

Axiom canonicalizeHomeModule : DynFlags -> Module.ModuleName -> Module.Module.

Axiom can_split : bool.

Axiom cONTROL_GROUP_CONST_291 : DynFlags -> BinNums.N.

Axiom cLONG_SIZE : DynFlags -> BinNums.N.

Axiom cLONG_LONG_SIZE : DynFlags -> BinNums.N.

Axiom cINT_SIZE : DynFlags -> BinNums.N.

Axiom bLOCK_SIZE_W : DynFlags -> BinNums.N.

Axiom bLOCK_SIZE : DynFlags -> BinNums.N.

Axiom bLOCKS_PER_MBLOCK : DynFlags -> BinNums.N.

Axiom bITMAP_BITS_SHIFT : DynFlags -> BinNums.N.

Axiom alterSettings : (Settings -> Settings) -> DynFlags -> DynFlags.

Axiom allowed_combination : list Way -> bool.

Axiom allNonDeprecatedFlags : list GHC.Base.String.

(* Skipping definition `DynFlags.allFlagsDeps' *)

(* Skipping definition `DynFlags.add_dep_message' *)

Axiom addWay' : Way -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.addWay' *)

Axiom addPluginModuleNameOption : GHC.Base.String -> DynFlags -> DynFlags.

Axiom addPluginModuleName : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.addPkgConfRef' *)

Axiom addOptl : GHC.Base.String -> DynFlags -> DynFlags.

Axiom addOptc : GHC.Base.String -> DynFlags -> DynFlags.

Axiom addOptP : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.addLibraryPath' *)

Axiom addLdInputs : Option -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.addIncludePath' *)

(* Skipping definition `DynFlags.addImportPath' *)

Axiom addHaddockOpts : GHC.Base.String -> DynFlags -> DynFlags.

Axiom addGhciScript : GHC.Base.String -> DynFlags -> DynFlags.

Axiom addGhcVersionFile : GHC.Base.String -> DynFlags -> DynFlags.

Axiom addFrontendPluginOption : GHC.Base.String -> DynFlags -> DynFlags.

(* Skipping definition `DynFlags.addFrameworkPath' *)

Axiom addDepSuffix : GHC.Base.String -> DynFlags -> DynFlags.

Axiom addDepExcludeMod : GHC.Base.String -> DynFlags -> DynFlags.

Axiom addCmdlineFramework : GHC.Base.String -> DynFlags -> DynFlags.

Axiom aP_STACK_SPLIM : DynFlags -> BinNums.N.

(* Skipping instance `DynFlags.Eq___DumpFlag' of class `GHC.Base.Eq_' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__DumpFlag' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `DynFlags.Enum__DumpFlag' *)

(* Skipping instance `DynFlags.Eq___GeneralFlag' of class `GHC.Base.Eq_' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__GeneralFlag' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `DynFlags.Enum__GeneralFlag' *)

(* Skipping instance `DynFlags.Eq___WarningFlag' of class `GHC.Base.Eq_' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__WarningFlag' *)

(* Skipping all instances of class `GHC.Enum.Enum', including
   `DynFlags.Enum__WarningFlag' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__WarnReason' *)

Instance Eq___Language : GHC.Base.Eq_ Language.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Enum.Enum', including
   `DynFlags.Enum__Language' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__Language' *)

Instance Eq___SafeHaskellMode : GHC.Base.Eq_ SafeHaskellMode.
Proof.
Admitted.

Instance Eq___ProfAuto : GHC.Base.Eq_ ProfAuto.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Enum.Enum', including
   `DynFlags.Enum__ProfAuto' *)

Instance Eq___HscTarget : GHC.Base.Eq_ HscTarget.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__HscTarget' *)

Instance Eq___GhcMode : GHC.Base.Eq_ GhcMode.
Proof.
Admitted.

Instance Eq___GhcLink : GHC.Base.Eq_ GhcLink.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__GhcLink' *)

Instance Eq___PackageArg : GHC.Base.Eq_ PackageArg.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__PackageArg' *)

Instance Eq___ModRenaming : GHC.Base.Eq_ ModRenaming.
Proof.
Admitted.

Instance Eq___IgnorePackageFlag : GHC.Base.Eq_ IgnorePackageFlag.
Proof.
Admitted.

Instance Eq___TrustFlag : GHC.Base.Eq_ TrustFlag.
Proof.
Admitted.

Instance Eq___PackageFlag : GHC.Base.Eq_ PackageFlag.
Proof.
Admitted.

Instance Eq___DynLibLoader : GHC.Base.Eq_ DynLibLoader.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__RtsOptsEnabled' *)

Instance Eq___Way : GHC.Base.Eq_ Way.
Proof.
Admitted.

(* Skipping instance `DynFlags.Ord__Way' of class `GHC.Base.Ord' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__Way' *)

Instance Eq___OnOff
   : forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_ (OnOff a).
Proof.
Admitted.

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__OnOff' *)

Instance Eq___Option : GHC.Base.Eq_ Option.
Proof.
Admitted.

Instance Eq___Deprecation : GHC.Base.Eq_ Deprecation.
Proof.
Admitted.

Instance Ord__Deprecation : GHC.Base.Ord Deprecation.
Proof.
Admitted.

Instance Eq___PkgConfRef : GHC.Base.Eq_ PkgConfRef.
Proof.
Admitted.

Instance Eq___PackageDBFlag : GHC.Base.Eq_ PackageDBFlag.
Proof.
Admitted.

Instance Eq___SseVersion : GHC.Base.Eq_ SseVersion.
Proof.
Admitted.

(* Skipping instance `DynFlags.Ord__SseVersion' of class `GHC.Base.Ord' *)

Instance Eq___BmiVersion : GHC.Base.Eq_ BmiVersion.
Proof.
Admitted.

Instance Ord__BmiVersion : GHC.Base.Ord BmiVersion.
Proof.
Admitted.

Instance Eq___LinkerInfo : GHC.Base.Eq_ LinkerInfo.
Proof.
Admitted.

Instance Eq___CompilerInfo : GHC.Base.Eq_ CompilerInfo.
Proof.
Admitted.

(* Skipping all instances of class `Json.ToJson', including
   `DynFlags.ToJson__WarnReason' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__WarnReason' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__Language' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__SafeHaskellMode' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `DynFlags.Show__SafeHaskellMode' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__GhcMode' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__PackageArg' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__ModRenaming' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__PackageFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `DynFlags.Outputable__OnOff' *)

(* Skipping instance `DynFlags.HasDynFlags__ExceptT' of class
   `DynFlags.HasDynFlags' *)

(* Skipping instance `DynFlags.HasDynFlags__MaybeT' of class
   `DynFlags.HasDynFlags' *)

(* Skipping instance `DynFlags.HasDynFlags__ReaderT' of class
   `DynFlags.HasDynFlags' *)

(* Skipping instance `DynFlags.HasDynFlags__WriterT' of class
   `DynFlags.HasDynFlags' *)

(* External variables:
     Type bool list op_zt__ option BinNums.N Data.Either.Either
     Data.Set.Internal.Set_ EnumSet.EnumSet GHC.Base.Eq_ GHC.Base.Ord GHC.Base.String
     GHC.Char.Char GHC.Err.Build_Default GHC.Err.Default GHC.Err.default
     GHC.Num.Integer Module.ComponentId Module.Module Module.ModuleName Module.UnitId
     SrcLoc.Located SrcLoc.SrcSpan
*)
