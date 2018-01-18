(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require GHC.Base.
Require Module.

(* Converted type declarations: *)

Inductive Way : Type := WayCustom : GHC.Base.String -> Way
                     |  WayThreaded : Way
                     |  WayDebug : Way
                     |  WayProf : Way
                     |  WayEventLog : Way
                     |  WayDyn : Way.

Inductive WarningFlag : Type := Opt_WarnDuplicateExports : WarningFlag
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
                             |  Opt_WarnContextQuantification : WarningFlag
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
                             |  Opt_WarnUnrecognisedWarningFlags : WarningFlag.

Inductive WarnReason : Type := NoReason : WarnReason
                            |  Reason : WarningFlag -> WarnReason.

Definition TurnOnFlag :=
  bool%type.

Inductive TrustFlag : Type := TrustPackage : GHC.Base.String -> TrustFlag
                           |  DistrustPackage : GHC.Base.String -> TrustFlag.

Inductive SseVersion : Type := SSE1 : SseVersion
                            |  SSE2 : SseVersion
                            |  SSE3 : SseVersion
                            |  SSE4 : SseVersion
                            |  SSE42 : SseVersion.

Definition SigOf :=
  (Module.ModuleNameEnv Module.Module)%type.

Inductive Settings : Type := Mk_Settings.

Inductive SafeHaskellMode : Type := Sf_None : SafeHaskellMode
                                 |  Sf_Unsafe : SafeHaskellMode
                                 |  Sf_Trustworthy : SafeHaskellMode
                                 |  Sf_Safe : SafeHaskellMode.

Inductive RtsOptsEnabled : Type := RtsOptsNone : RtsOptsEnabled
                                |  RtsOptsSafeOnly : RtsOptsEnabled
                                |  RtsOptsAll : RtsOptsEnabled.

Inductive ProfAuto : Type := NoProfAuto : ProfAuto
                          |  ProfAutoAll : ProfAuto
                          |  ProfAutoTop : ProfAuto
                          |  ProfAutoExports : ProfAuto
                          |  ProfAutoCalls : ProfAuto.

Inductive PkgConfRef : Type := GlobalPkgConf : PkgConfRef
                            |  UserPkgConf : PkgConfRef
                            |  PkgConfFile : GHC.Base.String -> PkgConfRef.

Inductive PackageArg : Type := Mk_PackageArg : GHC.Base.String -> PackageArg
                            |  UnitIdArg : GHC.Base.String -> PackageArg.

Inductive Option : Type := FileOption
                          : GHC.Base.String -> GHC.Base.String -> Option
                        |  Mk_Option : GHC.Base.String -> Option.

Inductive OnOff a : Type := On : a -> OnOff a
                         |  Off : a -> OnOff a.

Inductive ModRenaming : Type := Mk_ModRenaming : bool -> list (Module.ModuleName
                                                              * Module.ModuleName)%type -> ModRenaming.

Inductive PackageFlag : Type := ExposePackage
                               : GHC.Base.String -> PackageArg -> ModRenaming -> PackageFlag
                             |  HidePackage : GHC.Base.String -> PackageFlag.

Inductive LinkerInfo : Type := GnuLD : list Option -> LinkerInfo
                            |  GnuGold : list Option -> LinkerInfo
                            |  DarwinLD : list Option -> LinkerInfo
                            |  SolarisLD : list Option -> LinkerInfo
                            |  AixLD : list Option -> LinkerInfo
                            |  UnknownLD : LinkerInfo.

Inductive Language : Type := Haskell98 : Language
                          |  Haskell2010 : Language.

Inductive IgnorePackageFlag : Type := IgnorePackage
                                     : GHC.Base.String -> IgnorePackageFlag.

Inductive HscTarget : Type := HscC : HscTarget
                           |  HscAsm : HscTarget
                           |  HscLlvm : HscTarget
                           |  HscInterpreted : HscTarget
                           |  HscNothing : HscTarget.

Inductive GhcMode : Type := CompManager : GhcMode
                         |  OneShot : GhcMode
                         |  MkDepend : GhcMode.

Inductive GhcLink : Type := NoLink : GhcLink
                         |  LinkBinary : GhcLink
                         |  LinkInMemory : GhcLink
                         |  LinkDynLib : GhcLink
                         |  LinkStaticLib : GhcLink.

Inductive GeneralFlag : Type := Opt_DumpToFile : GeneralFlag
                             |  Opt_D_faststring_stats : GeneralFlag
                             |  Opt_D_dump_minimal_imports : GeneralFlag
                             |  Opt_DoCoreLinting : GeneralFlag
                             |  Opt_DoStgLinting : GeneralFlag
                             |  Opt_DoCmmLinting : GeneralFlag
                             |  Opt_DoAsmLinting : GeneralFlag
                             |  Opt_DoAnnotationLinting : GeneralFlag
                             |  Opt_NoLlvmMangler : GeneralFlag
                             |  Opt_WarnIsError : GeneralFlag
                             |  Opt_ShowWarnGroups : GeneralFlag
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
                             |  Opt_LiberateCase : GeneralFlag
                             |  Opt_SpecConstr : GeneralFlag
                             |  Opt_DoLambdaEtaExpansion : GeneralFlag
                             |  Opt_IgnoreAsserts : GeneralFlag
                             |  Opt_DoEtaReduction : GeneralFlag
                             |  Opt_CaseMerge : GeneralFlag
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
                             |  Opt_IgnoreInterfacePragmas : GeneralFlag
                             |  Opt_OmitInterfacePragmas : GeneralFlag
                             |  Opt_ExposeAllUnfoldings : GeneralFlag
                             |  Opt_WriteInterface : GeneralFlag
                             |  Opt_AutoSccsOnIndividualCafs : GeneralFlag
                             |  Opt_ProfCountEntries : GeneralFlag
                             |  Opt_Pp : GeneralFlag
                             |  Opt_ForceRecomp : GeneralFlag
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
                             |  Opt_HelpfulErrors : GeneralFlag
                             |  Opt_DeferTypeErrors : GeneralFlag
                             |  Opt_DeferTypedHoles : GeneralFlag
                             |  Opt_DeferOutOfScopeVariables : GeneralFlag
                             |  Opt_PIC : GeneralFlag
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
                             |  Opt_VersionMacros : GeneralFlag
                             |  Opt_OptimalApplicativeDo : GeneralFlag
                             |  Opt_SimplPreInlining : GeneralFlag
                             |  Opt_ErrorSpans : GeneralFlag
                             |  Opt_PprCaseAsLet : GeneralFlag
                             |  Opt_PprShowTicks : GeneralFlag
                             |  Opt_SuppressCoercions : GeneralFlag
                             |  Opt_SuppressVarKinds : GeneralFlag
                             |  Opt_SuppressModulePrefixes : GeneralFlag
                             |  Opt_SuppressTypeApplications : GeneralFlag
                             |  Opt_SuppressIdInfo : GeneralFlag
                             |  Opt_SuppressUnfoldings : GeneralFlag
                             |  Opt_SuppressTypeSignatures : GeneralFlag
                             |  Opt_SuppressUniques : GeneralFlag
                             |  Opt_AutoLinkPackages : GeneralFlag
                             |  Opt_ImplicitImportQualified : GeneralFlag
                             |  Opt_KeepHiDiffs : GeneralFlag
                             |  Opt_KeepHcFiles : GeneralFlag
                             |  Opt_KeepSFiles : GeneralFlag
                             |  Opt_KeepTmpFiles : GeneralFlag
                             |  Opt_KeepRawTokenStream : GeneralFlag
                             |  Opt_KeepLlvmFiles : GeneralFlag
                             |  Opt_BuildDynamicToo : GeneralFlag
                             |  Opt_DistrustAllPackages : GeneralFlag
                             |  Opt_PackageTrust : GeneralFlag.

Inductive FlushOut : Type := Mk_FlushOut.

Inductive FlushErr : Type := Mk_FlushErr.

Inductive FlagSpec (flag : Type) : Type := Mk_FlagSpec.

Inductive DynLibLoader : Type := Deployable : DynLibLoader
                              |  SystemDependent : DynLibLoader.

Inductive DynFlags : Type := Mk_DynFlags.

Record HasDynFlags__Dict m := HasDynFlags__Dict_Build {
  getDynFlags__ : m DynFlags }.

Definition HasDynFlags m :=
  forall r, (HasDynFlags__Dict m -> r) -> r.

Existing Class HasDynFlags.

Definition getDynFlags `{g : HasDynFlags m} : m DynFlags :=
  g _ (getDynFlags__ m).

Inductive DumpFlag : Type := Opt_D_dump_cmm : DumpFlag
                          |  Opt_D_dump_cmm_raw : DumpFlag
                          |  Opt_D_dump_cmm_cfg : DumpFlag
                          |  Opt_D_dump_cmm_cbe : DumpFlag
                          |  Opt_D_dump_cmm_switch : DumpFlag
                          |  Opt_D_dump_cmm_proc : DumpFlag
                          |  Opt_D_dump_cmm_sink : DumpFlag
                          |  Opt_D_dump_cmm_sp : DumpFlag
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
                          |  Opt_D_dump_rn : DumpFlag
                          |  Opt_D_dump_simpl : DumpFlag
                          |  Opt_D_dump_simpl_iterations : DumpFlag
                          |  Opt_D_dump_spec : DumpFlag
                          |  Opt_D_dump_prep : DumpFlag
                          |  Opt_D_dump_stg : DumpFlag
                          |  Opt_D_dump_call_arity : DumpFlag
                          |  Opt_D_dump_stranal : DumpFlag
                          |  Opt_D_dump_str_signatures : DumpFlag
                          |  Opt_D_dump_tc : DumpFlag
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
                          |  Opt_D_dump_view_pattern_commoning : DumpFlag
                          |  Opt_D_verbose_core2core : DumpFlag
                          |  Opt_D_dump_debug : DumpFlag.

Inductive Deprecation : Type := Deprecated : Deprecation
                             |  NotDeprecated : Deprecation.

Record ContainsDynFlags__Dict t := ContainsDynFlags__Dict_Build {
  extractDynFlags__ : t -> DynFlags }.

Definition ContainsDynFlags t :=
  forall r, (ContainsDynFlags__Dict t -> r) -> r.

Existing Class ContainsDynFlags.

Definition extractDynFlags `{g : ContainsDynFlags t} : t -> DynFlags :=
  g _ (extractDynFlags__ t).

Inductive CompilerInfo : Type := GCC : CompilerInfo
                              |  Clang : CompilerInfo
                              |  AppleClang : CompilerInfo
                              |  AppleClang51 : CompilerInfo
                              |  UnknownCC : CompilerInfo.

Arguments On {_} _.

Arguments Off {_} _.

Definition modRenamingWithImplicit (arg_0__ : ModRenaming) :=
  match arg_0__ with
    | Mk_ModRenaming modRenamingWithImplicit _ => modRenamingWithImplicit
  end.

Definition modRenamings (arg_1__ : ModRenaming) :=
  match arg_1__ with
    | Mk_ModRenaming _ modRenamings => modRenamings
  end.
(* Midamble *)

Instance Unpeel_IgnorePackageFlag : Prim.Unpeel IgnorePackageFlag GHC.Base.String :=
  Prim.Build_Unpeel _ _ (fun x => match x with | IgnorePackage y => y end) IgnorePackage.

(* Converted value declarations: *)

Instance Eq___CompilerInfo : GHC.Base.Eq_ CompilerInfo := {}.
Proof.
Admitted.

Instance Eq___LinkerInfo : GHC.Base.Eq_ LinkerInfo := {}.
Proof.
Admitted.

Instance Eq___SseVersion : GHC.Base.Eq_ SseVersion := {}.
Proof.
Admitted.

Instance Eq___Option : GHC.Base.Eq_ Option := {}.
Proof.
Admitted.

Instance Eq___Way : GHC.Base.Eq_ Way := {}.
Proof.
Admitted.

Instance Eq___DynLibLoader : GHC.Base.Eq_ DynLibLoader := {}.
Proof.
Admitted.

Instance Eq___PackageFlag : GHC.Base.Eq_ PackageFlag := {}.
Proof.
Admitted.

Instance Eq___TrustFlag : GHC.Base.Eq_ TrustFlag := {}.
Proof.
Admitted.

Instance Eq___IgnorePackageFlag : GHC.Base.Eq_ IgnorePackageFlag := {}.
Proof.
Admitted.

Instance Eq___PackageArg : GHC.Base.Eq_ PackageArg := {}.
Proof.
Admitted.

Instance Eq___ModRenaming : GHC.Base.Eq_ ModRenaming := {}.
Proof.
Admitted.

Instance Eq___GhcLink : GHC.Base.Eq_ GhcLink := {}.
Proof.
Admitted.

Instance Eq___GhcMode : GHC.Base.Eq_ GhcMode := {}.
Proof.
Admitted.

Instance Eq___HscTarget : GHC.Base.Eq_ HscTarget := {}.
Proof.
Admitted.

Instance Eq___ProfAuto : GHC.Base.Eq_ ProfAuto := {}.
Proof.
Admitted.

Instance Eq___SafeHaskellMode : GHC.Base.Eq_ SafeHaskellMode := {}.
Proof.
Admitted.

Axiom getSigOf : forall {A : Type}, A.

Axiom isSse2Enabled : forall {A : Type}, A.

Axiom isSseEnabled : forall {A : Type}, A.

Axiom parseDynamicFilePragma : forall {A : Type}, A.

Axiom parseDynamicFlagsCmdLine : forall {A : Type}, A.

Axiom parseDynamicFlagsFull : forall {A : Type}, A.

Axiom makeDynFlagsConsistent : forall {A : Type}, A.

Axiom tARGET_MAX_WORD : forall {A : Type}, A.

Axiom tARGET_MAX_INT : forall {A : Type}, A.

Axiom tARGET_MIN_INT : forall {A : Type}, A.

Axiom compilerInfo : forall {A : Type}, A.

Axiom picCCOpts : forall {A : Type}, A.

Axiom flagsDynamic : forall {A : Type}, A.

Axiom flagsForCompletion : forall {A : Type}, A.

Axiom flagsAll : forall {A : Type}, A.

Axiom allNonDeprecatedFlags : forall {A : Type}, A.

Axiom allFlagsDeps : forall {A : Type}, A.

Axiom flagsAllDeps : forall {A : Type}, A.

Axiom dynamic_flags_deps : forall {A : Type}, A.

Axiom setTarget : forall {A : Type}, A.

Axiom setTargetWithPlatform : forall {A : Type}, A.

Axiom addWay : forall {A : Type}, A.

Axiom dynamicTooMkDynamicDynFlags : forall {A : Type}, A.

Axiom addWay' : forall {A : Type}, A.

Axiom initDynFlags : forall {A : Type}, A.

Axiom tablesNextToCode : forall {A : Type}, A.

Axiom opt_l : forall {A : Type}, A.

Axiom opt_c : forall {A : Type}, A.

Axiom opt_P : forall {A : Type}, A.

Axiom targetPlatform : forall {A : Type}, A.

Axiom interpretPackageEnv : forall {A : Type}, A.

Axiom versionedAppDir : forall {A : Type}, A.

Axiom programName : forall {A : Type}, A.

Axiom versionedFilePath : forall {A : Type}, A.

Axiom projectVersion : forall {A : Type}, A.

Axiom ghcUsagePath : forall {A : Type}, A.

Axiom ghciUsagePath : forall {A : Type}, A.

Axiom topDir : forall {A : Type}, A.

Axiom tmpDir : forall {A : Type}, A.

Axiom rawSettings : forall {A : Type}, A.

Axiom extraGccViaCFlags : forall {A : Type}, A.

Axiom systemPackageConfig : forall {A : Type}, A.

Axiom pgm_L : forall {A : Type}, A.

Axiom pgm_P : forall {A : Type}, A.

Axiom pgm_F : forall {A : Type}, A.

Axiom pgm_c : forall {A : Type}, A.

Axiom pgm_s : forall {A : Type}, A.

Axiom pgm_a : forall {A : Type}, A.

Axiom pgm_l : forall {A : Type}, A.

Axiom pgm_dll : forall {A : Type}, A.

Axiom pgm_T : forall {A : Type}, A.

Axiom pgm_windres : forall {A : Type}, A.

Axiom pgm_libtool : forall {A : Type}, A.

Axiom pgm_lo : forall {A : Type}, A.

Axiom pgm_lc : forall {A : Type}, A.

Axiom pgm_i : forall {A : Type}, A.

Axiom opt_L : forall {A : Type}, A.

Axiom opt_F : forall {A : Type}, A.

Axiom opt_a : forall {A : Type}, A.

Axiom opt_windres : forall {A : Type}, A.

Axiom opt_lo : forall {A : Type}, A.

Axiom opt_lc : forall {A : Type}, A.

Axiom opt_i : forall {A : Type}, A.

Axiom setObjTarget : forall {A : Type}, A.

Axiom isObjectTarget : forall {A : Type}, A.

Axiom targetRetainsAllBindings : forall {A : Type}, A.

Axiom setVerboseCore2Core : forall {A : Type}, A.

Axiom setDumpFlag : forall {A : Type}, A.

Axiom setDumpFlag' : forall {A : Type}, A.

Axiom forceRecompile : forall {A : Type}, A.

Axiom isOneShot : forall {A : Type}, A.

Axiom isNoLink : forall {A : Type}, A.

Axiom setUnsafeGlobalDynFlags : forall {A : Type}, A.

Axiom unsafeGlobalDynFlags : forall {A : Type}, A.

Axiom v_unsafeGlobalDynFlags : forall {A : Type}, A.

Axiom defaultGlobalDynFlags : forall {A : Type}, A.

Axiom defaultDynFlags : forall {A : Type}, A.

Axiom defaultHscTarget : forall {A : Type}, A.

Axiom defaultObjectTarget : forall {A : Type}, A.

Axiom mkTablesNextToCode : forall {A : Type}, A.

Axiom allowed_combination : forall {A : Type}, A.

Axiom updateWays : forall {A : Type}, A.

Axiom mkBuildTag : forall {A : Type}, A.

Axiom wayTag : forall {A : Type}, A.

Axiom wayRTSOnly : forall {A : Type}, A.

Axiom wayDesc : forall {A : Type}, A.

Axiom defaultFlags : forall {A : Type}, A.

Axiom wayGeneralFlags : forall {A : Type}, A.

Axiom wayUnsetGeneralFlags : forall {A : Type}, A.

Axiom wayOptc : forall {A : Type}, A.

Axiom wayOptl : forall {A : Type}, A.

Axiom wayOptP : forall {A : Type}, A.

Axiom whenGeneratingDynamicToo : forall {A : Type}, A.

Axiom ifGeneratingDynamicToo : forall {A : Type}, A.

Axiom whenCannotGenerateDynamicToo : forall {A : Type}, A.

Axiom ifCannotGenerateDynamicToo : forall {A : Type}, A.

Axiom generateDynamicTooConditional : forall {A : Type}, A.

Axiom defaultWays : forall {A : Type}, A.

Axiom interpWays : forall {A : Type}, A.

Axiom interpreterProfiled : forall {A : Type}, A.

Axiom interpreterDynamic : forall {A : Type}, A.

Axiom defaultFatalMessager : forall {A : Type}, A.

Axiom defaultLogAction : forall {A : Type}, A.

Axiom defaultLogActionHPrintDoc : forall {A : Type}, A.

Axiom defaultLogActionHPutStrDoc : forall {A : Type}, A.

Axiom defaultFlushOut : forall {A : Type}, A.

Axiom defaultFlushErr : forall {A : Type}, A.

Axiom setLanguage : forall {A : Type}, A.

Axiom lang_set : forall {A : Type}, A.

Axiom enableGlasgowExts : forall {A : Type}, A.

Axiom setExtensionFlag : forall {A : Type}, A.

Axiom setExtensionFlag' : forall {A : Type}, A.

Axiom disableGlasgowExts : forall {A : Type}, A.

Axiom unSetExtensionFlag : forall {A : Type}, A.

Axiom unSetExtensionFlag' : forall {A : Type}, A.

Axiom safeFlagCheck : forall {A : Type}, A.

Axiom unsafeFlagsForInfer : forall {A : Type}, A.

Axiom unsafeFlags : forall {A : Type}, A.

Axiom xopt_unset : forall {A : Type}, A.

Axiom xopt_set : forall {A : Type}, A.

Axiom flattenExtensionFlags : forall {A : Type}, A.

Axiom languageExtensions : forall {A : Type}, A.

Axiom dopt : forall {A : Type}, A.

Axiom dopt_set : forall {A : Type}, A.

Axiom dopt_unset : forall {A : Type}, A.

Axiom picPOpts : forall {A : Type}, A.

Axiom packageTrustOn : forall {A : Type}, A.

Axiom useUnicodeSyntax : forall {A : Type}, A.

Axiom gopt : forall {A : Type}, A.

Axiom unSetGeneralFlag : forall {A : Type}, A.

Axiom setPackageTrust : forall {A : Type}, A.

Axiom flagsPackage : forall {A : Type}, A.

Axiom package_flags_deps : forall {A : Type}, A.

Axiom setGeneralFlag : forall {A : Type}, A.

Axiom unSetGeneralFlag' : forall {A : Type}, A.

Axiom setGeneralFlag' : forall {A : Type}, A.

Axiom setDPHOpt : forall {A : Type}, A.

Axiom setOptLevel : forall {A : Type}, A.

Axiom updOptLevel : forall {A : Type}, A.

Axiom gopt_set : forall {A : Type}, A.

Axiom gopt_unset : forall {A : Type}, A.

Axiom unrecognisedWarning : forall {A : Type}, A.

Axiom wopt : forall {A : Type}, A.

Axiom enableUnusedBinds : forall {A : Type}, A.

Axiom setWarningFlag : forall {A : Type}, A.

Axiom wopt_set : forall {A : Type}, A.

Axiom disableUnusedBinds : forall {A : Type}, A.

Axiom unSetWarningFlag : forall {A : Type}, A.

Axiom wopt_unset : forall {A : Type}, A.

Axiom xopt : forall {A : Type}, A.

Axiom dynFlagDependencies : forall {A : Type}, A.

Axiom safeHaskellOn : forall {A : Type}, A.

Axiom safeImplicitImpsReq : forall {A : Type}, A.

Axiom safeDirectImpsReq : forall {A : Type}, A.

Axiom safeLanguageOn : forall {A : Type}, A.

Axiom safeInferOn : forall {A : Type}, A.

Axiom safeImportsOn : forall {A : Type}, A.

Axiom setSafeHaskell : forall {A : Type}, A.

Axiom combineSafeFlags : forall {A : Type}, A.

Axiom getOpts : forall {A : Type}, A.

Axiom getVerbFlags : forall {A : Type}, A.

Axiom setOutputDir : forall {A : Type}, A.

Axiom setObjectDir : forall {A : Type}, A.

Axiom setHiDir : forall {A : Type}, A.

Axiom setStubDir : forall {A : Type}, A.

Axiom setDumpDir : forall {A : Type}, A.

Axiom setDylibInstallName : forall {A : Type}, A.

Axiom setObjectSuf : forall {A : Type}, A.

Axiom setDynObjectSuf : forall {A : Type}, A.

Axiom setHiSuf : forall {A : Type}, A.

Axiom setDynHiSuf : forall {A : Type}, A.

Axiom setHcSuf : forall {A : Type}, A.

Axiom setOutputFile : forall {A : Type}, A.

Axiom setDynOutputFile : forall {A : Type}, A.

Axiom setOutputHi : forall {A : Type}, A.

Axiom setSigOf : forall {A : Type}, A.

Axiom parseSigOf : forall {A : Type}, A.

Axiom addPluginModuleName : forall {A : Type}, A.

Axiom addPluginModuleNameOption : forall {A : Type}, A.

Axiom addFrontendPluginOption : forall {A : Type}, A.

Axiom parseDynLibLoaderMode : forall {A : Type}, A.

Axiom setDumpPrefixForce : forall {A : Type}, A.

Axiom setPgmP : forall {A : Type}, A.

Axiom addOptl : forall {A : Type}, A.

Axiom addOptc : forall {A : Type}, A.

Axiom addOptP : forall {A : Type}, A.

Axiom setDepMakefile : forall {A : Type}, A.

Axiom setDepIncludePkgDeps : forall {A : Type}, A.

Axiom addDepExcludeMod : forall {A : Type}, A.

Axiom addDepSuffix : forall {A : Type}, A.

Axiom addCmdlineFramework : forall {A : Type}, A.

Axiom addHaddockOpts : forall {A : Type}, A.

Axiom addGhciScript : forall {A : Type}, A.

Axiom setInteractivePrint : forall {A : Type}, A.

Axiom showOpt : forall {A : Type}, A.

Axiom make_ord_flag : forall {A : Type}, A.

Axiom make_dep_flag : forall {A : Type}, A.

Axiom add_dep_message : forall {A : Type}, A.

Axiom impliedXFlags : forall {A : Type}, A.

Axiom impliedGFlags : forall {A : Type}, A.

Axiom turnOn : forall {A : Type}, A.

Axiom impliedOffGFlags : forall {A : Type}, A.

Axiom turnOff : forall {A : Type}, A.

Axiom supportedLanguagesAndExtensions : forall {A : Type}, A.

Axiom supportedExtensions : forall {A : Type}, A.

Axiom xFlags : forall {A : Type}, A.

Axiom xFlagsDeps : forall {A : Type}, A.

Axiom supportedLanguageOverlays : forall {A : Type}, A.

Axiom safeHaskellFlagsDeps : forall {A : Type}, A.

Axiom supportedLanguages : forall {A : Type}, A.

Axiom languageFlagsDeps : forall {A : Type}, A.

Axiom fFlags : forall {A : Type}, A.

Axiom fFlagsDeps : forall {A : Type}, A.

Axiom dFlagsDeps : forall {A : Type}, A.

Axiom flagSpecOf : forall {A : Type}, A.

Axiom wWarningFlags : forall {A : Type}, A.

Axiom wWarningFlagsDeps : forall {A : Type}, A.

Axiom flagSpec : forall {A : Type}, A.

Axiom depFlagSpec : forall {A : Type}, A.

Axiom depFlagSpecOp : forall {A : Type}, A.

Axiom flagSpec' : forall {A : Type}, A.

Axiom fLangFlags : forall {A : Type}, A.

Axiom fLangFlagsDeps : forall {A : Type}, A.

Axiom depFlagSpec' : forall {A : Type}, A.

Axiom depFlagSpecOp' : forall {A : Type}, A.

Axiom depFlagSpecCond : forall {A : Type}, A.

Axiom negatableFlagsDeps : forall {A : Type}, A.

Axiom flagGhciSpec : forall {A : Type}, A.

Axiom flagGhciSpec' : forall {A : Type}, A.

Axiom flagHiddenSpec : forall {A : Type}, A.

Axiom flagHiddenSpec' : forall {A : Type}, A.

Axiom hideFlag : forall {A : Type}, A.

Axiom mkFlag : forall {A : Type}, A.

Axiom deprecatedForExtension : forall {A : Type}, A.

Axiom useInstead : forall {A : Type}, A.

Axiom nop : forall {A : Type}, A.

Axiom default_PIC : forall {A : Type}, A.

Axiom optLevelFlags : forall {A : Type}, A.

Axiom smallestGroups : forall {A : Type}, A.

Axiom warningHierarchies : forall {A : Type}, A.

Axiom warningGroups : forall {A : Type}, A.

Axiom minusWallOpts : forall {A : Type}, A.

Axiom minusWOpts : forall {A : Type}, A.

Axiom standardWarnings : forall {A : Type}, A.

Axiom minusWeverythingOpts : forall {A : Type}, A.

Axiom minusWcompatOpts : forall {A : Type}, A.

Axiom unusedBindsFlags : forall {A : Type}, A.

Axiom glasgowExtsFlags : forall {A : Type}, A.

Axiom rtsIsProfiled : forall {A : Type}, A.

Axiom dynamicGhc : forall {A : Type}, A.

Axiom setWarnSafe : forall {A : Type}, A.

Axiom setWarnUnsafe : forall {A : Type}, A.

Axiom setGenDeriving : forall {A : Type}, A.

Axiom setOverlappingInsts : forall {A : Type}, A.

Axiom setIncoherentInsts : forall {A : Type}, A.

Axiom checkTemplateHaskellOk : forall {A : Type}, A.

Axiom setOptHpcDir : forall {A : Type}, A.

Axiom setRtsOptsEnabled : forall {A : Type}, A.

Axiom setRtsOpts : forall {A : Type}, A.

Axiom addFrameworkPath : forall {A : Type}, A.

Axiom addIncludePath : forall {A : Type}, A.

Axiom addLibraryPath : forall {A : Type}, A.

Axiom addImportPath : forall {A : Type}, A.

Axiom setMainIs : forall {A : Type}, A.

Axiom distrustPackage : forall {A : Type}, A.

Axiom trustPackage : forall {A : Type}, A.

Axiom ignorePackage : forall {A : Type}, A.

Axiom hidePackage : forall {A : Type}, A.

Axiom exposePluginPackageId : forall {A : Type}, A.

Axiom exposePluginPackage : forall {A : Type}, A.

Axiom exposePackageId : forall {A : Type}, A.

Axiom exposePackage : forall {A : Type}, A.

Axiom clearPkgConf : forall {A : Type}, A.

Axiom removeGlobalPkgConf : forall {A : Type}, A.

Axiom removeUserPkgConf : forall {A : Type}, A.

Axiom addPkgConfRef : forall {A : Type}, A.

Axiom setDebugLevel : forall {A : Type}, A.

Axiom setVerbosity : forall {A : Type}, A.

Axiom removeWayDyn : forall {A : Type}, A.

Axiom floatSuffix : forall {A : Type}, A.

Axiom intSuffix : forall {A : Type}, A.

Axiom sepArg : forall {A : Type}, A.

Axiom hasArg : forall {A : Type}, A.

Axiom noArg : forall {A : Type}, A.

Axiom upd : forall {A : Type}, A.

Axiom optIntSuffixM : forall {A : Type}, A.

Axiom intSuffixM : forall {A : Type}, A.

Axiom noArgM : forall {A : Type}, A.

Axiom updM : forall {A : Type}, A.

Axiom setTmpDir : forall {A : Type}, A.

Axiom alterSettings : forall {A : Type}, A.

Axiom exposePackage' : forall {A : Type}, A.

Axiom parsePackageFlag : forall {A : Type}, A.

Axiom parseModuleName : forall {A : Type}, A.

Axiom setUnitId : forall {A : Type}, A.

Axiom checkOptLevel : forall {A : Type}, A.

Axiom addLdInputs : forall {A : Type}, A.

Axiom splitPathList : forall {A : Type}, A.

Axiom split_marker : forall {A : Type}, A.

Axiom can_split : forall {A : Type}, A.

Axiom cONTROL_GROUP_CONST_291 : forall {A : Type}, A.

Axiom sTD_HDR_SIZE : forall {A : Type}, A.

Axiom pROF_HDR_SIZE : forall {A : Type}, A.

Axiom bLOCK_SIZE_W : forall {A : Type}, A.

Axiom bLOCK_SIZE : forall {A : Type}, A.

Axiom bLOCKS_PER_MBLOCK : forall {A : Type}, A.

Axiom tICKY_BIN_COUNT : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rR1 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rR2 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rR3 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rR4 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rR5 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rR6 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rR7 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rR8 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rR9 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rR10 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rF1 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rF2 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rF3 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rF4 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rF5 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rF6 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rD1 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rD2 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rD3 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rD4 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rD5 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rD6 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rXMM1 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rXMM2 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rXMM3 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rXMM4 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rXMM5 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rXMM6 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rYMM1 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rYMM2 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rYMM3 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rYMM4 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rYMM5 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rYMM6 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rZMM1 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rZMM2 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rZMM3 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rZMM4 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rZMM5 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rZMM6 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rL1 : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rSp : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rSpLim : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rHp : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rHpLim : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rCCCS : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rCurrentTSO : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rCurrentNursery : forall {A : Type}, A.

Axiom oFFSET_StgRegTable_rHpAlloc : forall {A : Type}, A.

Axiom oFFSET_stgEagerBlackholeInfo : forall {A : Type}, A.

Axiom oFFSET_stgGCEnter1 : forall {A : Type}, A.

Axiom oFFSET_stgGCFun : forall {A : Type}, A.

Axiom oFFSET_Capability_r : forall {A : Type}, A.

Axiom oFFSET_bdescr_start : forall {A : Type}, A.

Axiom oFFSET_bdescr_free : forall {A : Type}, A.

Axiom oFFSET_bdescr_blocks : forall {A : Type}, A.

Axiom sIZEOF_CostCentreStack : forall {A : Type}, A.

Axiom oFFSET_CostCentreStack_mem_alloc : forall {A : Type}, A.

Axiom oFFSET_CostCentreStack_scc_count : forall {A : Type}, A.

Axiom oFFSET_StgHeader_ccs : forall {A : Type}, A.

Axiom oFFSET_StgHeader_ldvw : forall {A : Type}, A.

Axiom sIZEOF_StgSMPThunkHeader : forall {A : Type}, A.

Axiom oFFSET_StgEntCounter_allocs : forall {A : Type}, A.

Axiom oFFSET_StgEntCounter_allocd : forall {A : Type}, A.

Axiom oFFSET_StgEntCounter_registeredp : forall {A : Type}, A.

Axiom oFFSET_StgEntCounter_link : forall {A : Type}, A.

Axiom oFFSET_StgEntCounter_entry_count : forall {A : Type}, A.

Axiom sIZEOF_StgUpdateFrame_NoHdr : forall {A : Type}, A.

Axiom sIZEOF_StgMutArrPtrs_NoHdr : forall {A : Type}, A.

Axiom oFFSET_StgMutArrPtrs_ptrs : forall {A : Type}, A.

Axiom oFFSET_StgMutArrPtrs_size : forall {A : Type}, A.

Axiom sIZEOF_StgSmallMutArrPtrs_NoHdr : forall {A : Type}, A.

Axiom oFFSET_StgSmallMutArrPtrs_ptrs : forall {A : Type}, A.

Axiom sIZEOF_StgArrBytes_NoHdr : forall {A : Type}, A.

Axiom oFFSET_StgArrBytes_bytes : forall {A : Type}, A.

Axiom oFFSET_StgTSO_alloc_limit : forall {A : Type}, A.

Axiom oFFSET_StgTSO_cccs : forall {A : Type}, A.

Axiom oFFSET_StgTSO_stackobj : forall {A : Type}, A.

Axiom oFFSET_StgStack_sp : forall {A : Type}, A.

Axiom oFFSET_StgStack_stack : forall {A : Type}, A.

Axiom oFFSET_StgUpdateFrame_updatee : forall {A : Type}, A.

Axiom oFFSET_StgFunInfoExtraFwd_arity : forall {A : Type}, A.

Axiom sIZEOF_StgFunInfoExtraRev : forall {A : Type}, A.

Axiom oFFSET_StgFunInfoExtraRev_arity : forall {A : Type}, A.

Axiom mAX_SPEC_SELECTEE_SIZE : forall {A : Type}, A.

Axiom mAX_SPEC_AP_SIZE : forall {A : Type}, A.

Axiom mIN_PAYLOAD_SIZE : forall {A : Type}, A.

Axiom mIN_INTLIKE : forall {A : Type}, A.

Axiom mAX_INTLIKE : forall {A : Type}, A.

Axiom mIN_CHARLIKE : forall {A : Type}, A.

Axiom mAX_CHARLIKE : forall {A : Type}, A.

Axiom mUT_ARR_PTRS_CARD_BITS : forall {A : Type}, A.

Axiom mAX_Vanilla_REG : forall {A : Type}, A.

Axiom mAX_Float_REG : forall {A : Type}, A.

Axiom mAX_Double_REG : forall {A : Type}, A.

Axiom mAX_Long_REG : forall {A : Type}, A.

Axiom mAX_XMM_REG : forall {A : Type}, A.

Axiom mAX_Real_Vanilla_REG : forall {A : Type}, A.

Axiom mAX_Real_Float_REG : forall {A : Type}, A.

Axiom mAX_Real_Double_REG : forall {A : Type}, A.

Axiom mAX_Real_XMM_REG : forall {A : Type}, A.

Axiom mAX_Real_Long_REG : forall {A : Type}, A.

Axiom rESERVED_C_STACK_BYTES : forall {A : Type}, A.

Axiom rESERVED_STACK_WORDS : forall {A : Type}, A.

Axiom aP_STACK_SPLIM : forall {A : Type}, A.

Axiom wORD_SIZE_IN_BITS : forall {A : Type}, A.

Axiom wORD_SIZE : forall {A : Type}, A.

Axiom dOUBLE_SIZE : forall {A : Type}, A.

Axiom cINT_SIZE : forall {A : Type}, A.

Axiom cLONG_SIZE : forall {A : Type}, A.

Axiom cLONG_LONG_SIZE : forall {A : Type}, A.

Axiom bITMAP_BITS_SHIFT : forall {A : Type}, A.

Axiom mAX_PTR_TAG : forall {A : Type}, A.

Axiom tAG_MASK : forall {A : Type}, A.

Axiom tAG_BITS : forall {A : Type}, A.

Axiom wORDS_BIGENDIAN : forall {A : Type}, A.

Axiom dYNAMIC_BY_DEFAULT : forall {A : Type}, A.

Axiom lDV_SHIFT : forall {A : Type}, A.

Axiom iLDV_CREATE_MASK : forall {A : Type}, A.

Axiom iLDV_STATE_CREATE : forall {A : Type}, A.

Axiom iLDV_STATE_USE : forall {A : Type}, A.

Axiom isSse4_2Enabled : forall {A : Type}, A.

Axiom isAvxEnabled : forall {A : Type}, A.

Axiom isAvx2Enabled : forall {A : Type}, A.

Axiom isAvx512cdEnabled : forall {A : Type}, A.

Axiom isAvx512erEnabled : forall {A : Type}, A.

Axiom isAvx512fEnabled : forall {A : Type}, A.

Axiom isAvx512pfEnabled : forall {A : Type}, A.

Axiom decodeSize : forall {A : Type}, A.

(* Unbound variables:
     Type bool list op_zt__ GHC.Base.Eq_ GHC.Base.String Module.Module
     Module.ModuleName Module.ModuleNameEnv
*)
