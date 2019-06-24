(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require FastString.
Require GHC.Base.
Require GHC.Enum.
Require GHC.Num.
Require Module.
Require Name.
Require OccName.
Require SrcLoc.
Require Unique.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition zipIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #33.

Definition xorIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #93.

Definition wordTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #60.

Definition wordToIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #97.

Definition wordPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #59.

Definition wordDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #16.

Definition word8X64PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #320.

Definition word8X32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #316.

Definition word8X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #312.

Definition word8TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #61.

Definition word8DataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #13.

Definition word64X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #323.

Definition word64X4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #319.

Definition word64X2PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #315.

Definition word64TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #66.

Definition word64ToIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #98.

Definition word64PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #65.

Definition word32X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #318.

Definition word32X4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #314.

Definition word32X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #322.

Definition word32TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #64.

Definition word32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #63.

Definition word16X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #313.

Definition word16X32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #321.

Definition word16X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #317.

Definition word16TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #62.

Definition wildCardKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #0.

Definition wildCardName : Name.Name :=
  Name.mkSystemVarName wildCardKey (FastString.fsLit (GHC.Base.hs_string__
                                                      "wild")).

Definition weakPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #27.

Definition voidPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #58.

Definition voidPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #21.

Definition voidArgIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #40.

Definition vecRepDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #71.

Definition vecElemTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #97.

Definition vecElemDataConKeys : list Unique.Unique :=
  GHC.Base.map Unique.mkPreludeDataConUnique (GHC.Enum.enumFromTo #89 #98).

Definition vecCountTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #96.

Definition vecCountDataConKeys : list Unique.Unique :=
  GHC.Base.map Unique.mkPreludeDataConUnique (GHC.Enum.enumFromTo #83 #88).

Axiom RdrName : Type.

Axiom varQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Definition v1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #135.

Definition unsafeCoerceIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #30.

Definition unpackCStringUtf8IdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #17.

Definition unpackCStringIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #20.

Definition unpackCStringFoldrIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #19.

Definition unpackCStringAppendIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #18.

Definition unmarshalStringIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #153.

Definition unmarshalObjectIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #150.

Definition unliftedConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #68.

Definition unknownTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #129.

Definition unknown3TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #132.

Definition unknown2TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #131.

Definition unknown1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #130.

Definition unicodeStarKindTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #94.

Definition undefinedKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #155.

Definition unboundKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #158.

Definition uWordTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #163.

Definition uRecTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #157.

Definition uIntTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #162.

Definition uFloatTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #161.

Definition uDoubleTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #160.

Definition uCharTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #159.

Definition uAddrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #158.

Definition u1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #136.

Definition typeableClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #20.

Definition typeable7ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #27.

Definition typeable6ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #26.

Definition typeable5ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #25.

Definition typeable4ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #24.

Definition typeable3ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #23.

Definition typeable2ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #22.

Definition typeable1ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #21.

Definition typeSymbolTypeRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #508.

Definition typeSymbolKindConNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #165.

Definition typeSymbolCmpTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #171.

Definition typeSymbolAppendFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #190.

Definition typeRepTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #187.

Definition typeRepIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #509.

Definition typeNatTypeRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #507.

Definition typeNatSubTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #170.

Definition typeNatMulTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #167.

Definition typeNatModTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #174.

Definition typeNatLogTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #175.

Definition typeNatLeqTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #169.

Definition typeNatKindConNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #164.

Definition typeNatExpTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #168.

Definition typeNatDivTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #173.

Definition typeNatCmpTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #172.

Definition typeNatAddTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #166.

Definition typeLitSymbolDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #107.

Definition typeLitSortTyConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #49.

Definition typeLitNatDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #108.

Definition typeErrorVAppendDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #52.

Definition typeErrorTextDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #50.

Definition typeErrorShowTypeDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #53.

Definition typeErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #22.

Definition typeErrorAppendDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #51.

Definition typeConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #72.

Definition tupleRepDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #72.

Definition trueDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #15.

Definition traversableClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #36.

Definition traceKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #108.

Definition trTyConTyConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #40.

Definition trTyConDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #41.

Definition trTYPEKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #511.

Definition trTYPE'PtrRepLiftedKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #512.

Definition trRuntimeRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #513.

Definition trNameTyConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #44.

Definition trNameSDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #45.

Definition trNameDDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #46.

Definition trModuleTyConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #42.

Definition trModuleDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #43.

Definition trGhcPrimModuleKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #47.

Definition tr'PtrRepLiftedKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #514.

Definition toRationalClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #193.

Definition toListClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #501.

Definition toIntegerClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #192.

Definition toDynIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #550.

Definition toAnnotationWrapperIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #187.

Definition timesIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #67.

Definition threadIdPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #73.

Definition thenMClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #172.

Definition thenIOIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #103.

Definition thenAClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #753.

Axiom tcQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Definition tYPETyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #88.

Definition tVarPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #77.

Definition sumTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #141.

Definition sumRepDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #73.

Definition staticPtrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #184.

Definition staticPtrInfoTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #185.

Definition staticPtrInfoDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #34.

Definition staticPtrDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #33.

Definition statePrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #50.

Definition starKindTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #93.

Definition starKindRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #520.

Definition starArrStarKindRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #521.

Definition starArrStarArrStarKindRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #522.

Definition stablePtrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #36.

Definition stablePtrPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #35.

Definition stableNameTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #52.

Definition stableNamePrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #51.

Definition stableNameDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #14.

Definition srcLocDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #37.

Definition specTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #180.

Definition sourceUnpackDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #59.

Definition sourceStrictDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #63.

Definition sourceNoUnpackDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #60.

Definition sourceLazyDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #62.

Definition someTypeRepTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #188.

Definition someTypeRepDataConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #189.

Definition sndIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #42.

Definition smallMutableArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #183.

Definition smallIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #61.

Definition smallArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #182.

Definition signumIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #73.

Definition showClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #17.

Definition shiftRIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #96.

Definition shiftLIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #95.

Definition seqIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #8.

Definition semigroupClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #46.

Definition selectorClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #41.

Definition sappendClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #554.

Definition sTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #148.

Definition s1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #153.

Definition runtimeRepTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #95.

Definition runtimeErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #13.

Definition runRWKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #107.

Definition runMainKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #102.

Definition rootMainKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #101.

Definition rightDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #26.

Definition rightAssociativeDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #57.

Definition returnMClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #174.

Definition returnIOIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #35.

Definition repTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #155.

Definition rep1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #156.

Definition remIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #80.

Definition recSelErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #7.

Definition recConErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #16.

Definition rec1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #138.

Definition rec0TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #149.

Definition realWorldTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #34.

Definition realWorldPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #15.

Definition realToFracIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #191.

Definition realFracClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #16.

Definition realFloatClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #15.

Definition realClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #14.

Definition readClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #13.

Definition rationalTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #33.

Definition rationalToFloatIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #130.

Definition rationalToDoubleIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #131.

Definition ratioTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #32.

Definition ratioDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #12.

Definition randomGenClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #32.

Definition randomClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #31.

Definition rTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #144.

Definition quotRemIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #84.

Definition quotIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #79.

Definition pushCallStackKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #559.

Definition pureAClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #752.

Definition ptrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #75.

Definition proxyPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #179.

Definition proxyHashKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #502.

Definition prodTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #142.

Definition printIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #37.

Axiom pretendNameIsInScope : Name.Name -> bool.

Definition prefixIDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #54.

Definition plusIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #66.

Definition pluginTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #102.

Definition patErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #14.

Definition parrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #82.

Definition parrDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #24.

Definition par1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #137.

Definition pRELUDE_NAME : Module.ModuleName :=
  Module.mkModuleNameFS (FastString.fsLit (GHC.Base.hs_string__ "Prelude")).

Definition otherwiseIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #43.

Definition orderingTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #30.

Definition ordClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #12.

Definition orIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #92.

Definition opaqueTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #133.

Definition oneShotKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #106.

Definition objectTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #83.

Definition numClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #11.

Definition nullAddrIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #39.

Definition ntTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #177.

Definition nothingDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #8.

Definition notAssociativeDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #58.

Definition nonExhaustiveGuardsErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #12.

Definition noinlineIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #125.

Definition noSourceUnpackednessDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #61.

Definition noSourceStrictnessDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #64.

Definition noSelTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #154.

Definition noMethodBindingErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #11.

Definition nilDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #11.

Definition newStablePtrIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #36.

Definition neqIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #71.

Definition negateIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #69.

Definition negateClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #169.

Definition naturalTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #23.

Definition naturalFromIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #562.

Definition mzipIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #196.

Definition mutableByteArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #29.

Definition mutableArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #28.

Definition mutableArrayArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #41.

Definition mutVarPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #56.

Definition monoidClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #47.

Definition monadPlusClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #30.

Definition monadFixClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #28.

Definition monadFailClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #29.

Definition monadClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #8.

Definition modIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #82.

Definition modIntIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #24.

Definition mk_known_key_name
   : OccName.NameSpace ->
     Module.Module -> FastString.FastString -> Unique.Unique -> Name.Name :=
  fun space modu str unique =>
    Name.mkExternalName unique modu (OccName.mkOccNameFS space str)
    SrcLoc.noSrcSpan.

Definition tcQual
   : Module.Module -> FastString.FastString -> Unique.Unique -> Name.Name :=
  mk_known_key_name OccName.tcName.

Definition varQual
   : Module.Module -> FastString.FastString -> Unique.Unique -> Name.Name :=
  mk_known_key_name OccName.varName.

Definition mkUnboundName : OccName.OccName -> Name.Name :=
  fun occ => Name.mkInternalName unboundKey occ SrcLoc.noSrcSpan.

Definition mkTyConKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #503.

Definition mkTrTypeKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #504.

Definition mkTrFunKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #510.

Definition mkTrConKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #505.

Definition mkTrAppKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #506.

Definition mkThisGhcModule_ : Module.ModuleName -> Module.Module :=
  fun m => Module.mkModule Module.thisGhcUnitId m.

Definition mkThisGhcModule : FastString.FastString -> Module.Module :=
  fun m => Module.mkModule Module.thisGhcUnitId (Module.mkModuleNameFS m).

Definition pLUGINS : Module.Module :=
  mkThisGhcModule (FastString.fsLit (GHC.Base.hs_string__ "Plugins")).

Definition pluginTyConName : Name.Name :=
  tcQual pLUGINS (FastString.fsLit (GHC.Base.hs_string__ "Plugin"))
  pluginTyConKey.

Definition mkPrimModule : FastString.FastString -> Module.Module :=
  fun m => Module.mkModule Module.primUnitId (Module.mkModuleNameFS m).

Definition mkMainModule_ : Module.ModuleName -> Module.Module :=
  fun m => Module.mkModule Module.mainUnitId m.

Definition mkMainModule : FastString.FastString -> Module.Module :=
  fun m => Module.mkModule Module.mainUnitId (Module.mkModuleNameFS m).

Definition rOOT_MAIN : Module.Module :=
  mkMainModule (FastString.fsLit (GHC.Base.hs_string__ ":Main")).

Axiom mkInteractiveModule : nat -> Module.Module.

Axiom mkIntegerModule : FastString.FastString -> Module.Module.

Definition mkIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #60.

Definition mkBaseModule_ : Module.ModuleName -> Module.Module :=
  fun m => Module.mkModule Module.baseUnitId m.

Definition pRELUDE : Module.Module :=
  mkBaseModule_ pRELUDE_NAME.

Definition mkBaseModule : FastString.FastString -> Module.Module :=
  fun m => Module.mkModule Module.baseUnitId (Module.mkModuleNameFS m).

Definition rANDOM : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "System.Random")).

Definition rEAD_PREC : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__
                                  "Text.ParserCombinators.ReadPrec")).

Definition pfail_RDR : RdrName :=
  varQual_RDR rEAD_PREC (FastString.fsLit (GHC.Base.hs_string__ "pfail")).

Definition prec_RDR : RdrName :=
  varQual_RDR rEAD_PREC (FastString.fsLit (GHC.Base.hs_string__ "prec")).

Definition reset_RDR : RdrName :=
  varQual_RDR rEAD_PREC (FastString.fsLit (GHC.Base.hs_string__ "reset")).

Definition step_RDR : RdrName :=
  varQual_RDR rEAD_PREC (FastString.fsLit (GHC.Base.hs_string__ "step")).

Definition sYSTEM_IO : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "System.IO")).

Definition printName : Name.Name :=
  varQual sYSTEM_IO (FastString.fsLit (GHC.Base.hs_string__ "print")) printIdKey.

Definition tYPEABLE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Typeable")).

Definition tYPEABLE_INTERNAL : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Typeable.Internal")).

Definition mkTrAppName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "mkTrApp"))
  mkTrAppKey.

Definition mkTrConName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "mkTrCon"))
  mkTrConKey.

Definition mkTrFunName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "mkTrFun"))
  mkTrFunKey.

Definition mkTrTypeName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "mkTrType"))
  mkTrTypeKey.

Definition someTypeRepTyConName : Name.Name :=
  tcQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "SomeTypeRep"))
  someTypeRepTyConKey.

Definition typeNatTypeRepName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__
                                               "typeNatTypeRep")) typeNatTypeRepKey.

Definition typeRepIdName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "typeRep#"))
  typeRepIdKey.

Definition typeRepTyConName : Name.Name :=
  tcQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "TypeRep"))
  typeRepTyConKey.

Definition typeSymbolTypeRepName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__
                                               "typeSymbolTypeRep")) typeSymbolTypeRepKey.

Definition minusIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #68.

Definition minusClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #161.

Definition mfixIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #175.

Definition metaSelDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #70.

Definition metaDataDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #68.

Definition metaConsDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #69.

Definition memptyClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #555.

Definition mconcatClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #557.

Definition maybeTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #26.

Definition marshalStringIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #152.

Definition marshalObjectIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #151.

Definition mappendClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #556.

Definition mapIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #121.

Definition makeStaticKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #561.

Axiom main_RDR_Unqual : RdrName.

Definition magicDictKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #156.

Definition mVarPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #31.

Definition mONAD_ZIP : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Monad.Zip")).

Definition mzipName : Name.Name :=
  varQual mONAD_ZIP (FastString.fsLit (GHC.Base.hs_string__ "mzip")) mzipIdKey.

Definition mONAD_FIX : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Monad.Fix")).

Definition mfixName : Name.Name :=
  varQual mONAD_FIX (FastString.fsLit (GHC.Base.hs_string__ "mfix")) mfixIdKey.

Definition mONAD_FAIL : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Monad.Fail")).

Definition mONAD : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Monad")).

Definition mAIN_NAME : Module.ModuleName :=
  Module.mkModuleNameFS (FastString.fsLit (GHC.Base.hs_string__ "Main")).

Definition mAIN : Module.Module :=
  mkMainModule_ mAIN_NAME.

Definition m1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #140.

Definition ltIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #76.

Definition ltDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #27.

Definition loopAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #185.

Definition listTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #24.

Definition liftedTypeKindTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #87.

Definition liftedConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #67.

Definition liftMIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #195.

Definition liftMName : Name.Name :=
  varQual mONAD (FastString.fsLit (GHC.Base.hs_string__ "liftM")) liftMIdKey.

Definition leftDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #25.

Definition leftAssociativeDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #56.

Definition leIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #74.

Definition lcmIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #90.

Definition lazyIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #104.

Definition lEX : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Text.Read.Lex")).

Definition knownSymbolClassNameKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #43.

Definition knownNatClassNameKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #42.

Definition kindRepVarDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #101.

Definition kindRepTypeLitSDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #105.

Definition kindRepTypeLitDDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #106.

Definition kindRepTyConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #48.

Definition kindRepTyConAppDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #100.

Definition kindRepTYPEDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #104.

Definition kindRepFunDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #103.

Definition kindRepAppDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #102.

Definition kindConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #70.

Definition k1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #139.

Definition justDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #9.

Definition joinMIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #750.

Definition ixClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #18.

Definition itName : Unique.Unique -> SrcLoc.SrcSpan -> Name.Name :=
  fun uniq loc =>
    Name.mkInternalName uniq (OccName.mkOccNameFS OccName.varName (FastString.fsLit
                                                                   (GHC.Base.hs_string__ "it"))) loc.

Definition isUnboundName : Name.Name -> bool :=
  fun name => Unique.hasKey name unboundKey.

Definition isStringClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #33.

Definition isListClassKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #198.

Definition isLabelClassNameKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #45.

Definition irrefutPatErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #9.

Definition ipClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #48.

Definition ioTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #57.

Definition ioDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #17.

Definition integralClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #7.

Definition integerTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #22.

Definition integerToWordIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #62.

Definition integerToWord64IdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #64.

Definition integerToIntIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #63.

Definition integerToInt64IdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #65.

Axiom integerSDataConName : Name.Name.

Definition integerSDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #7.

Definition integerDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #18.

Definition intTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #15.

Definition intPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #14.

Definition intDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #6.

Definition int8X64PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #308.

Definition int8X32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #304.

Definition int8X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #300.

Definition int8TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #16.

Definition int64X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #311.

Definition int64X4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #307.

Definition int64X2PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #303.

Definition int64TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #21.

Definition int64ToIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #99.

Definition int64PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #20.

Definition int32X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #306.

Definition int32X4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #302.

Definition int32X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #310.

Definition int32TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #19.

Definition int32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #18.

Definition int16X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #301.

Definition int16X32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #309.

Definition int16X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #305.

Definition int16TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #17.

Definition inrDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #22.

Definition inlineIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #120.

Definition inlDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #21.

Definition infixIDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #55.

Definition heqTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #39.

Definition heqSCSelIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #552.

Definition heqDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #19.

Definition hasFieldClassNameKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #49.

Definition guardMIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #194.

Definition guardMName : Name.Name :=
  varQual mONAD (FastString.fsLit (GHC.Base.hs_string__ "guard")) guardMIdKey.

Definition gtIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #75.

Definition gtDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #29.

Definition groupWithIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #122.

Definition ghciStepIoMClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #197.

Definition ghciIoClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #44.

Axiom genericTyConNames : list Name.Name.

Definition genUnitDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #23.

Definition genClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #37.

Definition gen1ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #38.

Definition geIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #77.

Definition geClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #168.

Definition gcdIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #89.

Definition gHC_WORD : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Word")).

Definition word16TyConName : Name.Name :=
  tcQual gHC_WORD (FastString.fsLit (GHC.Base.hs_string__ "Word16"))
  word16TyConKey.

Definition word32TyConName : Name.Name :=
  tcQual gHC_WORD (FastString.fsLit (GHC.Base.hs_string__ "Word32"))
  word32TyConKey.

Definition word64TyConName : Name.Name :=
  tcQual gHC_WORD (FastString.fsLit (GHC.Base.hs_string__ "Word64"))
  word64TyConKey.

Definition gHC_TYPES : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Types")).

Definition ioTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "IO")) ioTyConKey.

Definition kindRepTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRep"))
  kindRepTyConKey.

Definition orderingTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "Ordering"))
  orderingTyConKey.

Definition specTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "SPEC")) specTyConKey.

Definition starArrStarArrStarKindRepName : Name.Name :=
  varQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "krep$*->*->*"))
  starArrStarArrStarKindRepKey.

Definition starArrStarKindRepName : Name.Name :=
  varQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "krep$*Arr*"))
  starArrStarKindRepKey.

Definition starKindRepName : Name.Name :=
  varQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "krep$*"))
  starKindRepKey.

Definition trGhcPrimModuleName : Name.Name :=
  varQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "tr$ModuleGHCPrim"))
  trGhcPrimModuleKey.

Definition trModuleTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "Module"))
  trModuleTyConKey.

Definition trNameTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TrName"))
  trNameTyConKey.

Definition trTyConTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TyCon"))
  trTyConTyConKey.

Definition typeLitSortTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TypeLitSort"))
  typeLitSortTyConKey.

Definition gHC_TYPENATS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.TypeNats")).

Definition gHC_TYPELITS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.TypeLits")).

Definition gHC_TUPLE : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Tuple")).

Definition gHC_TOP_HANDLER : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.TopHandler")).

Definition runMainIOName : Name.Name :=
  varQual gHC_TOP_HANDLER (FastString.fsLit (GHC.Base.hs_string__ "runMainIO"))
  runMainKey.

Definition gHC_STATICPTR_INTERNAL : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.StaticPtr.Internal")).

Definition makeStaticName : Name.Name :=
  varQual gHC_STATICPTR_INTERNAL (FastString.fsLit (GHC.Base.hs_string__
                                                    "makeStatic")) makeStaticKey.

Definition gHC_STATICPTR : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.StaticPtr")).

Definition staticPtrInfoTyConName : Name.Name :=
  tcQual gHC_STATICPTR (FastString.fsLit (GHC.Base.hs_string__ "StaticPtrInfo"))
  staticPtrInfoTyConKey.

Definition staticPtrTyConName : Name.Name :=
  tcQual gHC_STATICPTR (FastString.fsLit (GHC.Base.hs_string__ "StaticPtr"))
  staticPtrTyConKey.

Definition gHC_STACK_TYPES : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Stack.Types")).

Definition pushCallStackName : Name.Name :=
  varQual gHC_STACK_TYPES (FastString.fsLit (GHC.Base.hs_string__
                                             "pushCallStack")) pushCallStackKey.

Definition gHC_STACK : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Stack")).

Definition gHC_STABLE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Stable")).

Definition newStablePtrName : Name.Name :=
  varQual gHC_STABLE (FastString.fsLit (GHC.Base.hs_string__ "newStablePtr"))
  newStablePtrIdKey.

Axiom nameRdrName : Name.Name -> RdrName.

Definition newStablePtr_RDR : RdrName :=
  nameRdrName newStablePtrName.

Definition stablePtrTyConName : Name.Name :=
  tcQual gHC_STABLE (FastString.fsLit (GHC.Base.hs_string__ "StablePtr"))
  stablePtrTyConKey.

Definition gHC_ST : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.ST")).

Definition gHC_SRCLOC : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.SrcLoc")).

Definition gHC_SHOW : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Show")).

Definition showCommaSpace_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "showCommaSpace")).

Definition showParen_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "showParen")).

Definition showSpace_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "showSpace")).

Definition showString_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "showString")).

Definition showsPrec_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "showsPrec")).

Definition shows_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "shows")).

Definition gHC_RECORDS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Records")).

Definition gHC_REAL : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Real")).

Definition ratioTyConName : Name.Name :=
  tcQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "Ratio")) ratioTyConKey.

Definition rationalTyConName : Name.Name :=
  tcQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "Rational"))
  rationalTyConKey.

Definition realToFracName : Name.Name :=
  varQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "realToFrac"))
  realToFracIdKey.

Definition toIntegerName : Name.Name :=
  varQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "toInteger"))
  toIntegerClassOpKey.

Definition toInteger_RDR : RdrName :=
  nameRdrName toIntegerName.

Definition toRationalName : Name.Name :=
  varQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "toRational"))
  toRationalClassOpKey.

Definition toRational_RDR : RdrName :=
  nameRdrName toRationalName.

Definition gHC_READ : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Read")).

Definition lexP_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "lexP")).

Definition parens_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "parens")).

Definition readFieldHash_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readFieldHash")).

Definition readField_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readField")).

Definition readListDefault_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__
                                          "readListDefault")).

Definition readListPrecDefault_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__
                                          "readListPrecDefault")).

Definition readListPrec_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readListPrec")).

Definition readList_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readList")).

Definition readPrec_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readPrec")).

Definition readSymField_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readSymField")).

Definition gHC_PTR : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Ptr")).

Definition ptrTyConName : Name.Name :=
  tcQual gHC_PTR (FastString.fsLit (GHC.Base.hs_string__ "Ptr")) ptrTyConKey.

Definition gHC_PRIM : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Prim")).

Definition gHC_PARR' : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.PArr")).

Definition gHC_OVER_LABELS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.OverloadedLabels")).

Definition gHC_NUM : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Num")).

Definition minusName : Name.Name :=
  varQual gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "-")) minusClassOpKey.

Definition minus_RDR : RdrName :=
  nameRdrName minusName.

Definition negateName : Name.Name :=
  varQual gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "negate"))
  negateClassOpKey.

Definition plus_RDR : RdrName :=
  varQual_RDR gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "+")).

Definition times_RDR : RdrName :=
  varQual_RDR gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "*")).

Definition gHC_NATURAL : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Natural")).

Definition naturalFromIntegerName : Name.Name :=
  varQual gHC_NATURAL (FastString.fsLit (GHC.Base.hs_string__
                                         "naturalFromInteger")) naturalFromIntegerIdKey.

Definition naturalTyConName : Name.Name :=
  tcQual gHC_NATURAL (FastString.fsLit (GHC.Base.hs_string__ "Natural"))
  naturalTyConKey.

Definition gHC_MAGIC : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Magic")).

Definition inlineIdName : Name.Name :=
  varQual gHC_MAGIC (FastString.fsLit (GHC.Base.hs_string__ "inline"))
  inlineIdKey.

Definition gHC_LIST : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.List")).

Definition zipName : Name.Name :=
  varQual gHC_LIST (FastString.fsLit (GHC.Base.hs_string__ "zip")) zipIdKey.

Definition gHC_IO_Exception : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.IO.Exception")).

Definition gHC_IO : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.IO")).

Definition gHC_INTEGER_TYPE : Module.Module :=
  mkIntegerModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Integer.Type")).

Definition gcdIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "gcdInteger"))
  gcdIntegerIdKey.

Definition geIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "geInteger#"))
  geIntegerPrimIdKey.

Definition gtIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "gtInteger#"))
  gtIntegerPrimIdKey.

Definition int64ToIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "int64ToInteger")) int64ToIntegerIdKey.

Definition integerToInt64Name : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "integerToInt64")) integerToInt64IdKey.

Definition integerToIntName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "integerToInt")) integerToIntIdKey.

Definition integerToWord64Name : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "integerToWord64")) integerToWord64IdKey.

Definition integerToWordName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "integerToWord")) integerToWordIdKey.

Definition integerTyConName : Name.Name :=
  tcQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "Integer"))
  integerTyConKey.

Definition lcmIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "lcmInteger"))
  lcmIntegerIdKey.

Definition leIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "leInteger#"))
  leIntegerPrimIdKey.

Definition ltIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "ltInteger#"))
  ltIntegerPrimIdKey.

Definition minusIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "minusInteger")) minusIntegerIdKey.

Definition mkIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "mkInteger"))
  mkIntegerIdKey.

Definition modIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "modInteger"))
  modIntegerIdKey.

Definition negateIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "negateInteger")) negateIntegerIdKey.

Definition neqIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "neqInteger#"))
  neqIntegerPrimIdKey.

Definition orIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "orInteger"))
  orIntegerIdKey.

Definition plusIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "plusInteger"))
  plusIntegerIdKey.

Definition plusInteger_RDR : RdrName :=
  nameRdrName plusIntegerName.

Definition quotIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "quotInteger"))
  quotIntegerIdKey.

Definition quotRemIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "quotRemInteger")) quotRemIntegerIdKey.

Definition remIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "remInteger"))
  remIntegerIdKey.

Definition shiftLIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "shiftLInteger")) shiftLIntegerIdKey.

Definition shiftRIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "shiftRInteger")) shiftRIntegerIdKey.

Definition signumIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "signumInteger")) signumIntegerIdKey.

Definition smallIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "smallInteger")) smallIntegerIdKey.

Definition timesIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "timesInteger")) timesIntegerIdKey.

Definition timesInteger_RDR : RdrName :=
  nameRdrName timesIntegerName.

Definition word64ToIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "word64ToInteger")) word64ToIntegerIdKey.

Definition wordToIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "wordToInteger")) wordToIntegerIdKey.

Definition xorIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "xorInteger"))
  xorIntegerIdKey.

Definition gHC_INT : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Int")).

Definition int16TyConName : Name.Name :=
  tcQual gHC_INT (FastString.fsLit (GHC.Base.hs_string__ "Int16")) int16TyConKey.

Definition int32TyConName : Name.Name :=
  tcQual gHC_INT (FastString.fsLit (GHC.Base.hs_string__ "Int32")) int32TyConKey.

Definition int64TyConName : Name.Name :=
  tcQual gHC_INT (FastString.fsLit (GHC.Base.hs_string__ "Int64")) int64TyConKey.

Definition int8TyConName : Name.Name :=
  tcQual gHC_INT (FastString.fsLit (GHC.Base.hs_string__ "Int8")) int8TyConKey.

Definition gHC_GHCI : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.GHCi")).

Definition ghciStepIoMName : Name.Name :=
  varQual gHC_GHCI (FastString.fsLit (GHC.Base.hs_string__ "ghciStepIO"))
  ghciStepIoMClassOpKey.

Definition gHC_GENERICS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Generics")).

Definition isNewtypeName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "isNewtype")).

Definition k1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "K1")) k1TyConKey.

Definition m1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "M1")) m1TyConKey.

Definition moduleName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "moduleName")).

Definition noSelTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "NoSelector"))
  noSelTyConKey.

Definition packageName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                              "packageName")).

Definition par1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Par1"))
  par1TyConKey.

Definition prodTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ ":*:"))
  prodTyConKey.

Definition rTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "R")) rTyConKey.

Definition rec0TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Rec0"))
  rec0TyConKey.

Definition rec1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Rec1"))
  rec1TyConKey.

Definition rep1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Rep1"))
  rep1TyConKey.

Definition repTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Rep")) repTyConKey.

Definition s1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "S1")) s1TyConKey.

Definition sTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "S")) sTyConKey.

Definition selName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "selName")).

Definition sumTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ ":+:")) sumTyConKey.

Definition to1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "to1")).

Definition to_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "to")).

Definition u1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "U1")) u1TyConKey.

Definition uAddrHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uAddr#")).

Definition uAddrTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UAddr"))
  uAddrTyConKey.

Definition uCharHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uChar#")).

Definition uCharTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UChar"))
  uCharTyConKey.

Definition uDoubleHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uDouble#")).

Definition uDoubleTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UDouble"))
  uDoubleTyConKey.

Definition uFloatHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uFloat#")).

Definition uFloatTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UFloat"))
  uFloatTyConKey.

Definition uIntHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uInt#")).

Definition uIntTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UInt"))
  uIntTyConKey.

Definition uRecTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "URec"))
  uRecTyConKey.

Definition uWordHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uWord#")).

Definition uWordTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UWord"))
  uWordTyConKey.

Definition unComp1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "unComp1")).

Definition unK1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "unK1")).

Definition unPar1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "unPar1")).

Definition unRec1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "unRec1")).

Definition v1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "V1")) v1TyConKey.

Definition gHC_FLOAT : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Float")).

Definition rationalToDoubleName : Name.Name :=
  varQual gHC_FLOAT (FastString.fsLit (GHC.Base.hs_string__ "rationalToDouble"))
  rationalToDoubleIdKey.

Definition rationalToFloatName : Name.Name :=
  varQual gHC_FLOAT (FastString.fsLit (GHC.Base.hs_string__ "rationalToFloat"))
  rationalToFloatIdKey.

Definition gHC_FINGERPRINT_TYPE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Fingerprint.Type")).

Definition gHC_EXTS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Exts")).

Definition groupWithName : Name.Name :=
  varQual gHC_EXTS (FastString.fsLit (GHC.Base.hs_string__ "groupWith"))
  groupWithIdKey.

Definition toListName : Name.Name :=
  varQual gHC_EXTS (FastString.fsLit (GHC.Base.hs_string__ "toList"))
  toListClassOpKey.

Definition toList_RDR : RdrName :=
  nameRdrName toListName.

Definition gHC_ERR : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Err")).

Definition undefined_RDR : RdrName :=
  varQual_RDR gHC_ERR (FastString.fsLit (GHC.Base.hs_string__ "undefined")).

Definition gHC_ENUM : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Enum")).

Definition maxBound_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "maxBound")).

Definition minBound_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "minBound")).

Definition pred_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "pred")).

Definition succ_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "succ")).

Definition toEnum_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "toEnum")).

Definition gHC_DESUGAR : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Desugar")).

Definition toAnnotationWrapperName : Name.Name :=
  varQual gHC_DESUGAR (FastString.fsLit (GHC.Base.hs_string__
                                         "toAnnotationWrapper")) toAnnotationWrapperIdKey.

Definition gHC_CSTRING : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.CString")).

Definition unpackCStringFoldrName : Name.Name :=
  varQual gHC_CSTRING (FastString.fsLit (GHC.Base.hs_string__
                                         "unpackFoldrCString#")) unpackCStringFoldrIdKey.

Definition unpackCStringFoldr_RDR : RdrName :=
  nameRdrName unpackCStringFoldrName.

Definition unpackCStringName : Name.Name :=
  varQual gHC_CSTRING (FastString.fsLit (GHC.Base.hs_string__ "unpackCString#"))
  unpackCStringIdKey.

Definition unpackCString_RDR : RdrName :=
  nameRdrName unpackCStringName.

Definition unpackCStringUtf8Name : Name.Name :=
  varQual gHC_CSTRING (FastString.fsLit (GHC.Base.hs_string__
                                         "unpackCStringUtf8#")) unpackCStringUtf8IdKey.

Definition unpackCStringUtf8_RDR : RdrName :=
  nameRdrName unpackCStringUtf8Name.

Definition gHC_CONC : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Conc")).

Definition gHC_CLASSES : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Classes")).

Definition geName : Name.Name :=
  varQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ ">=")) geClassOpKey.

Definition ge_RDR : RdrName :=
  nameRdrName geName.

Definition gt_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ ">")).

Definition le_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "<=")).

Definition lt_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "<")).

Definition modIntName : Name.Name :=
  varQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "modInt#"))
  modIntIdKey.

Definition not_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "not")).

Definition gHC_BASE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Base")).

Definition getTag_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "getTag")).

Definition joinMName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "join")) joinMIdKey.

Definition liftA2_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "liftA2")).

Definition mapName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "map")) mapIdKey.

Definition map_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "map")).

Definition mappendName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "mappend"))
  mappendClassOpKey.

Definition mappend_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "mappend")).

Definition mconcatName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "mconcat"))
  mconcatClassOpKey.

Definition memptyName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "mempty"))
  memptyClassOpKey.

Definition mempty_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "mempty")).

Definition opaqueTyConName : Name.Name :=
  tcQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Opaque"))
  opaqueTyConKey.

Definition otherwiseIdName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "otherwise"))
  otherwiseIdKey.

Definition pureAName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "pure"))
  pureAClassOpKey.

Definition pure_RDR : RdrName :=
  nameRdrName pureAName.

Definition replace_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "<$")).

Definition returnIOName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "returnIO"))
  returnIOIdKey.

Definition returnIO_RDR : RdrName :=
  nameRdrName returnIOName.

Definition returnMName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "return"))
  returnMClassOpKey.

Definition returnM_RDR : RdrName :=
  nameRdrName returnMName.

Definition sappendName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "<>"))
  sappendClassOpKey.

Definition stringTy_RDR : RdrName :=
  tcQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "String")).

Definition thenAName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "*>")) thenAClassOpKey.

Definition thenIOName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "thenIO")) thenIOIdKey.

Definition thenMName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ ">>")) thenMClassOpKey.

Definition gHC_ARR : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Arr")).

Definition inRange_RDR : RdrName :=
  varQual_RDR gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "inRange")).

Definition index_RDR : RdrName :=
  varQual_RDR gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "index")).

Definition range_RDR : RdrName :=
  varQual_RDR gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "range")).

Definition unsafeIndex_RDR : RdrName :=
  varQual_RDR gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "unsafeIndex")).

Definition unsafeRangeSize_RDR : RdrName :=
  varQual_RDR gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "unsafeRangeSize")).

Definition gENERICS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Data")).

Definition functorClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #10.

Definition funTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #13.

Definition funPtrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #76.

Definition funPtrTyConName : Name.Name :=
  tcQual gHC_PTR (FastString.fsLit (GHC.Base.hs_string__ "FunPtr"))
  funPtrTyConKey.

Definition fstIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #41.

Definition frontendPluginTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #103.

Definition frontendPluginTyConName : Name.Name :=
  tcQual pLUGINS (FastString.fsLit (GHC.Base.hs_string__ "FrontendPlugin"))
  frontendPluginTyConKey.

Definition from_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "from")).

Definition fromStringClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #186.

Definition fromStaticPtrClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #560.

Definition fromStaticPtrName : Name.Name :=
  varQual gHC_STATICPTR (FastString.fsLit (GHC.Base.hs_string__ "fromStaticPtr"))
  fromStaticPtrClassOpKey.

Definition fromRationalClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #162.

Definition fromRationalName : Name.Name :=
  varQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "fromRational"))
  fromRationalClassOpKey.

Definition fromRational_RDR : RdrName :=
  nameRdrName fromRationalName.

Definition fromListNClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #500.

Definition fromListNName : Name.Name :=
  varQual gHC_EXTS (FastString.fsLit (GHC.Base.hs_string__ "fromListN"))
  fromListNClassOpKey.

Definition fromListN_RDR : RdrName :=
  nameRdrName fromListNName.

Definition fromListClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #199.

Definition fromListName : Name.Name :=
  varQual gHC_EXTS (FastString.fsLit (GHC.Base.hs_string__ "fromList"))
  fromListClassOpKey.

Definition fromList_RDR : RdrName :=
  nameRdrName fromListName.

Definition fromIntegralIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #190.

Definition fromIntegralName : Name.Name :=
  varQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "fromIntegral"))
  fromIntegralIdKey.

Definition fromIntegral_RDR : RdrName :=
  nameRdrName fromIntegralName.

Definition fromIntegerClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #160.

Definition fromIntegerName : Name.Name :=
  varQual gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "fromInteger"))
  fromIntegerClassOpKey.

Definition fromInteger_RDR : RdrName :=
  nameRdrName fromIntegerName.

Definition fromEnum_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "fromEnum")).

Definition from1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "from1")).

Definition fractionalClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #6.

Definition foreignObjPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #25.

Axiom forall_tv_RDR : RdrName.

Definition foldrIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #6.

Definition foldrName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "foldr")) foldrIdKey.

Definition foldr_RDR : RdrName :=
  nameRdrName foldrName.

Definition foldableClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #35.

Definition fmap_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "fmap")).

Definition fmapClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #173.

Definition fmapName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "fmap"))
  fmapClassOpKey.

Definition floatingClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #5.

Definition fractionalClassKeys : list Unique.Unique :=
  cons fractionalClassKey (cons floatingClassKey (cons realFracClassKey (cons
                                                        realFloatClassKey nil))).

Definition numericClassKeys : list Unique.Unique :=
  Coq.Init.Datatypes.app (cons numClassKey (cons realClassKey (cons
                                                  integralClassKey nil))) fractionalClassKeys.

Definition floatX8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #326.

Definition floatX4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #324.

Definition floatX16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #328.

Definition floatTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #12.

Definition floatPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #11.

Definition floatFromIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #85.

Definition floatFromIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "floatFromInteger")) floatFromIntegerIdKey.

Definition floatDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #5.

Definition firstAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #182.

Definition fingerprintDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #35.

Definition filterIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #32.

Definition filterName : Name.Name :=
  varQual gHC_LIST (FastString.fsLit (GHC.Base.hs_string__ "filter")) filterIdKey.

Definition falseDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #4.

Definition failMClassOpKey_preMFP : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #170.

Definition failMName_preMFP : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "fail"))
  failMClassOpKey_preMFP.

Definition failM_RDR_preMFP : RdrName :=
  nameRdrName failMName_preMFP.

Definition failMClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #176.

Definition failMName : Name.Name :=
  varQual mONAD_FAIL (FastString.fsLit (GHC.Base.hs_string__ "fail"))
  failMClassOpKey.

Definition failM_RDR : RdrName :=
  nameRdrName failMName.

Definition failIOIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #38.

Definition failIOName : Name.Name :=
  varQual gHC_IO (FastString.fsLit (GHC.Base.hs_string__ "failIO")) failIOIdKey.

Definition expectP_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "expectP")).

Definition error_RDR : RdrName :=
  varQual_RDR gHC_ERR (FastString.fsLit (GHC.Base.hs_string__ "error")).

Definition errorMessageTypeErrorFamKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #176.

Definition errorMessageTypeErrorFamName : Name.Name :=
  tcQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ "TypeError"))
  errorMessageTypeErrorFamKey.

Definition errorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #5.

Definition eqTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #38.

Definition eqStringIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #10.

Definition eqStringName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "eqString"))
  eqStringIdKey.

Definition eqString_RDR : RdrName :=
  nameRdrName eqStringName.

Definition eqReprPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #54.

Definition eqPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #53.

Definition eqPhantPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #55.

Definition eqIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #70.

Definition eqIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "eqInteger#"))
  eqIntegerPrimIdKey.

Definition eqDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #28.

Definition eqClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #167.

Definition eqName : Name.Name :=
  varQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "==")) eqClassOpKey.

Definition eq_RDR : RdrName :=
  nameRdrName eqName.

Definition eqClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #3.

Definition enumFromToClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #165.

Definition enumFromToName : Name.Name :=
  varQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "enumFromTo"))
  enumFromToClassOpKey.

Definition enumFromTo_RDR : RdrName :=
  nameRdrName enumFromToName.

Definition enumFromThenToClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #166.

Definition enumFromThenToName : Name.Name :=
  varQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "enumFromThenTo"))
  enumFromThenToClassOpKey.

Definition enumFromThenTo_RDR : RdrName :=
  nameRdrName enumFromThenToName.

Definition enumFromThenClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #164.

Definition enumFromThenName : Name.Name :=
  varQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "enumFromThen"))
  enumFromThenClassOpKey.

Definition enumFromThen_RDR : RdrName :=
  nameRdrName enumFromThenName.

Definition enumFromClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #163.

Definition enumFromName : Name.Name :=
  varQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "enumFrom"))
  enumFromClassOpKey.

Definition enumFrom_RDR : RdrName :=
  nameRdrName enumFromName.

Definition enumClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #2.

Definition encodeFloatIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #87.

Definition encodeFloatIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "encodeFloatInteger")) encodeFloatIntegerIdKey.

Definition encodeDoubleIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #88.

Definition encodeDoubleIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "encodeDoubleInteger")) encodeDoubleIntegerIdKey.

Definition emptyCallStackKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #558.

Definition emptyCallStackName : Name.Name :=
  varQual gHC_STACK_TYPES (FastString.fsLit (GHC.Base.hs_string__
                                             "emptyCallStack")) emptyCallStackKey.

Definition eitherTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #84.

Definition doubleX8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #329.

Definition doubleX4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #327.

Definition doubleX2PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #325.

Definition doubleTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #10.

Definition doublePrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #9.

Definition doubleFromIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #86.

Definition doubleFromIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "doubleFromInteger")) doubleFromIntegerIdKey.

Definition doubleDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #3.

Axiom dot_tv_RDR : RdrName.

Definition dollarIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #123.

Definition divModIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #83.

Definition divModIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "divModInteger")) divModIntegerIdKey.

Definition divIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #81.

Definition divIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "divInteger"))
  divIntegerIdKey.

Definition divIntIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #23.

Definition divIntName : Name.Name :=
  varQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "divInt#"))
  divIntIdKey.

Definition decodeDoubleIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #100.

Definition decodeDoubleIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "decodeDoubleInteger")) decodeDoubleIntegerIdKey.

Definition decidedUnpackDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #67.

Definition decidedStrictDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #66.

Definition decidedLazyDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #65.

Definition dcQual
   : Module.Module -> FastString.FastString -> Unique.Unique -> Name.Name :=
  mk_known_key_name OccName.dataName.

Definition decidedLazyDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "DecidedLazy"))
  decidedLazyDataConKey.

Definition decidedStrictDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "DecidedStrict"))
  decidedStrictDataConKey.

Definition decidedUnpackDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "DecidedUnpack"))
  decidedUnpackDataConKey.

Definition eqDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "EQ")) eqDataConKey.

Definition fingerprintDataConName : Name.Name :=
  dcQual gHC_FINGERPRINT_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                                 "Fingerprint")) fingerprintDataConKey.

Definition gtDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "GT")) gtDataConKey.

Definition infixIDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "InfixI"))
  infixIDataConKey.

Definition ioDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "IO")) ioDataConKey.

Definition ioDataCon_RDR : RdrName :=
  nameRdrName ioDataConName.

Definition kindRepAppDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepApp"))
  kindRepAppDataConKey.

Definition kindRepFunDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepFun"))
  kindRepFunDataConKey.

Definition kindRepTYPEDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepTYPE"))
  kindRepTYPEDataConKey.

Definition kindRepTyConAppDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepTyConApp"))
  kindRepTyConAppDataConKey.

Definition kindRepTypeLitDDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepTypeLitD"))
  kindRepTypeLitDDataConKey.

Definition kindRepTypeLitSDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepTypeLitS"))
  kindRepTypeLitSDataConKey.

Definition kindRepVarDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepVar"))
  kindRepVarDataConKey.

Definition leftAssociativeDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "LeftAssociative"))
  leftAssociativeDataConKey.

Definition ltDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "LT")) ltDataConKey.

Definition metaConsDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "MetaCons"))
  metaConsDataConKey.

Definition metaDataDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "MetaData"))
  metaDataDataConKey.

Definition metaSelDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "MetaSel"))
  metaSelDataConKey.

Definition noSourceStrictnessDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                         "NoSourceStrictness")) noSourceStrictnessDataConKey.

Definition noSourceUnpackednessDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                         "NoSourceUnpackedness")) noSourceUnpackednessDataConKey.

Definition notAssociativeDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "NotAssociative"))
  notAssociativeDataConKey.

Definition prefixIDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "PrefixI"))
  prefixIDataConKey.

Definition ratioDataConName : Name.Name :=
  dcQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ ":%")) ratioDataConKey.

Definition ratioDataCon_RDR : RdrName :=
  nameRdrName ratioDataConName.

Definition rightAssociativeDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "RightAssociative"))
  rightAssociativeDataConKey.

Definition someTypeRepDataConName : Name.Name :=
  dcQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "SomeTypeRep"))
  someTypeRepDataConKey.

Definition sourceLazyDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "SourceLazy"))
  sourceLazyDataConKey.

Definition sourceNoUnpackDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "SourceNoUnpack"))
  sourceNoUnpackDataConKey.

Definition sourceStrictDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "SourceStrict"))
  sourceStrictDataConKey.

Definition sourceUnpackDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "SourceUnpack"))
  sourceUnpackDataConKey.

Definition srcLocDataConName : Name.Name :=
  dcQual gHC_STACK_TYPES (FastString.fsLit (GHC.Base.hs_string__ "SrcLoc"))
  srcLocDataConKey.

Definition staticPtrDataConName : Name.Name :=
  dcQual gHC_STATICPTR (FastString.fsLit (GHC.Base.hs_string__ "StaticPtr"))
  staticPtrDataConKey.

Definition staticPtrInfoDataConName : Name.Name :=
  dcQual gHC_STATICPTR (FastString.fsLit (GHC.Base.hs_string__ "StaticPtrInfo"))
  staticPtrInfoDataConKey.

Definition trModuleDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "Module"))
  trModuleDataConKey.

Definition trNameDDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TrNameD"))
  trNameDDataConKey.

Definition trNameSDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TrNameS"))
  trNameSDataConKey.

Definition trTyConDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TyCon"))
  trTyConDataConKey.

Definition typeErrorAppendDataConName : Name.Name :=
  dcQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ ":<>:"))
  typeErrorAppendDataConKey.

Definition typeErrorShowTypeDataConName : Name.Name :=
  dcQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ "ShowType"))
  typeErrorShowTypeDataConKey.

Definition typeErrorTextDataConName : Name.Name :=
  dcQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ "Text"))
  typeErrorTextDataConKey.

Definition typeErrorVAppendDataConName : Name.Name :=
  dcQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ ":$$:"))
  typeErrorVAppendDataConKey.

Definition typeLitNatDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TypeLitNat"))
  typeLitNatDataConKey.

Definition typeLitSymbolDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TypeLitSymbol"))
  typeLitSymbolDataConKey.

Definition datatypeName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                              "datatypeName")).

Definition datatypeClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #39.

Axiom dataQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Definition eqTag_RDR : RdrName :=
  dataQual_RDR gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "EQ")).

Definition gtTag_RDR : RdrName :=
  dataQual_RDR gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "GT")).

Definition ident_RDR : RdrName :=
  dataQual_RDR lEX (FastString.fsLit (GHC.Base.hs_string__ "Ident")).

Definition infixDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Infix")).

Definition k1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "K1")).

Definition l1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "L1")).

Definition leftAssocDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                               "LeftAssociative")).

Definition ltTag_RDR : RdrName :=
  dataQual_RDR gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "LT")).

Definition m1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "M1")).

Definition notAssocDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                               "NotAssociative")).

Definition par1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Par1")).

Definition prefixDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Prefix")).

Definition prodDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ ":*:")).

Definition punc_RDR : RdrName :=
  dataQual_RDR lEX (FastString.fsLit (GHC.Base.hs_string__ "Punc")).

Definition r1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "R1")).

Definition rec1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Rec1")).

Definition rightAssocDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                               "RightAssociative")).

Definition symbol_RDR : RdrName :=
  dataQual_RDR lEX (FastString.fsLit (GHC.Base.hs_string__ "Symbol")).

Definition u1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "U1")).

Definition uAddrDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UAddr")).

Definition uCharDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UChar")).

Definition uDoubleDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UDouble")).

Definition uFloatDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UFloat")).

Definition uIntDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UInt")).

Definition uWordDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UWord")).

Definition dataClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #9.

Definition dYNAMIC : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Dynamic")).

Definition toDynName : Name.Name :=
  varQual dYNAMIC (FastString.fsLit (GHC.Base.hs_string__ "toDyn")) toDynIdKey.

Definition dTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #146.

Definition dTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "D")) dTyConKey.

Definition dEBUG_TRACE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Debug.Trace")).

Definition traceName : Name.Name :=
  varQual dEBUG_TRACE (FastString.fsLit (GHC.Base.hs_string__ "trace")) traceKey.

Definition dATA_TYPE_EQUALITY : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Type.Equality")).

Definition eqTyConName : Name.Name :=
  tcQual dATA_TYPE_EQUALITY (FastString.fsLit (GHC.Base.hs_string__ "~"))
  eqTyConKey.

Definition eqTyCon_RDR : RdrName :=
  tcQual_RDR dATA_TYPE_EQUALITY (FastString.fsLit (GHC.Base.hs_string__ "~")).

Definition dATA_TUPLE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Tuple")).

Definition fstName : Name.Name :=
  varQual dATA_TUPLE (FastString.fsLit (GHC.Base.hs_string__ "fst")) fstIdKey.

Definition sndName : Name.Name :=
  varQual dATA_TUPLE (FastString.fsLit (GHC.Base.hs_string__ "snd")) sndIdKey.

Definition dATA_TRAVERSABLE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Traversable")).

Definition traverse_RDR : RdrName :=
  varQual_RDR dATA_TRAVERSABLE (FastString.fsLit (GHC.Base.hs_string__
                                                  "traverse")).

Definition dATA_STRING : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.String")).

Definition fromStringName : Name.Name :=
  varQual dATA_STRING (FastString.fsLit (GHC.Base.hs_string__ "fromString"))
  fromStringClassOpKey.

Definition fromString_RDR : RdrName :=
  nameRdrName fromStringName.

Definition dATA_FOLDABLE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Foldable")).

Definition foldMap_RDR : RdrName :=
  varQual_RDR dATA_FOLDABLE (FastString.fsLit (GHC.Base.hs_string__ "foldMap")).

Definition foldable_foldr_RDR : RdrName :=
  varQual_RDR dATA_FOLDABLE (FastString.fsLit (GHC.Base.hs_string__ "foldr")).

Definition null_RDR : RdrName :=
  varQual_RDR dATA_FOLDABLE (FastString.fsLit (GHC.Base.hs_string__ "null")).

Definition dATA_EITHER : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Either")).

Definition eitherTyConName : Name.Name :=
  tcQual dATA_EITHER (FastString.fsLit (GHC.Base.hs_string__ "Either"))
  eitherTyConKey.

Definition leftDataConName : Name.Name :=
  dcQual dATA_EITHER (FastString.fsLit (GHC.Base.hs_string__ "Left"))
  leftDataConKey.

Definition left_RDR : RdrName :=
  nameRdrName leftDataConName.

Definition rightDataConName : Name.Name :=
  dcQual dATA_EITHER (FastString.fsLit (GHC.Base.hs_string__ "Right"))
  rightDataConKey.

Definition right_RDR : RdrName :=
  nameRdrName rightDataConName.

Definition dATA_COERCE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Coerce")).

Definition dATA_ARRAY_PARALLEL_PRIM_NAME : Module.ModuleName :=
  Module.mkModuleNameFS (FastString.fsLit (GHC.Base.hs_string__
                                           "Data.Array.Parallel.Prim")).

Definition dATA_ARRAY_PARALLEL_NAME : Module.ModuleName :=
  Module.mkModuleNameFS (FastString.fsLit (GHC.Base.hs_string__
                                           "Data.Array.Parallel")).

Definition d1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #151.

Definition d1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "D1")) d1TyConKey.

Definition crossDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #20.

Definition constructorClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #40.

Definition constraintKindTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #92.

Definition consDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #2.

Definition concatIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #31.

Definition concatName : Name.Name :=
  varQual gHC_LIST (FastString.fsLit (GHC.Base.hs_string__ "concat")) concatIdKey.

Definition conName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "conName")).

Definition conIsRecord_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                              "conIsRecord")).

Definition conFixity_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "conFixity")).

Definition compose_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ ".")).

Definition composeAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #181.

Definition composeAName : Name.Name :=
  varQual gHC_DESUGAR (FastString.fsLit (GHC.Base.hs_string__ ">>>"))
  composeAIdKey.

Definition complementIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #94.

Definition complementIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "complementInteger")) complementIntegerIdKey.

Definition compare_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "compare")).

Definition compareIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #78.

Definition compareIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "compareInteger")) compareIntegerIdKey.

Definition compactPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #78.

Definition compTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #143.

Definition compTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ ":.:"))
  compTyConKey.

Definition comp1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Comp1")).

Definition coercionTokenIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #124.

Definition coercibleTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #178.

Definition coercibleSCSelIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #553.

Definition coercibleDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #32.

Definition coerceKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #157.

Axiom clsQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Definition clsQual
   : Module.Module -> FastString.FastString -> Unique.Unique -> Name.Name :=
  mk_known_key_name OccName.clsName.

Definition constructorClassName : Name.Name :=
  clsQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Constructor"))
  constructorClassKey.

Definition dataClassName : Name.Name :=
  clsQual gENERICS (FastString.fsLit (GHC.Base.hs_string__ "Data")) dataClassKey.

Definition datatypeClassName : Name.Name :=
  clsQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Datatype"))
  datatypeClassKey.

Definition enumClassName : Name.Name :=
  clsQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "Enum")) enumClassKey.

Definition enumClass_RDR : RdrName :=
  nameRdrName enumClassName.

Definition eqClassName : Name.Name :=
  clsQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "Eq")) eqClassKey.

Definition eqClass_RDR : RdrName :=
  nameRdrName eqClassName.

Definition floatingClassName : Name.Name :=
  clsQual gHC_FLOAT (FastString.fsLit (GHC.Base.hs_string__ "Floating"))
  floatingClassKey.

Definition foldableClassName : Name.Name :=
  clsQual dATA_FOLDABLE (FastString.fsLit (GHC.Base.hs_string__ "Foldable"))
  foldableClassKey.

Definition fractionalClassName : Name.Name :=
  clsQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "Fractional"))
  fractionalClassKey.

Definition functorClassName : Name.Name :=
  clsQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Functor"))
  functorClassKey.

Definition gen1ClassName : Name.Name :=
  clsQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Generic1"))
  gen1ClassKey.

Definition genClassName : Name.Name :=
  clsQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Generic"))
  genClassKey.

Definition genericClassNames : list Name.Name :=
  cons genClassName (cons gen1ClassName nil).

Definition ghciIoClassName : Name.Name :=
  clsQual gHC_GHCI (FastString.fsLit (GHC.Base.hs_string__ "GHCiSandboxIO"))
  ghciIoClassKey.

Definition hasFieldClassName : Name.Name :=
  clsQual gHC_RECORDS (FastString.fsLit (GHC.Base.hs_string__ "HasField"))
  hasFieldClassNameKey.

Definition integralClassName : Name.Name :=
  clsQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "Integral"))
  integralClassKey.

Definition ipClassName : Name.Name :=
  clsQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "IP")) ipClassKey.

Definition isLabelClassName : Name.Name :=
  clsQual gHC_OVER_LABELS (FastString.fsLit (GHC.Base.hs_string__ "IsLabel"))
  isLabelClassNameKey.

Definition isListClassName : Name.Name :=
  clsQual gHC_EXTS (FastString.fsLit (GHC.Base.hs_string__ "IsList"))
  isListClassKey.

Definition isStringClassName : Name.Name :=
  clsQual dATA_STRING (FastString.fsLit (GHC.Base.hs_string__ "IsString"))
  isStringClassKey.

Definition ixClassName : Name.Name :=
  clsQual gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "Ix")) ixClassKey.

Definition knownNatClassName : Name.Name :=
  clsQual gHC_TYPENATS (FastString.fsLit (GHC.Base.hs_string__ "KnownNat"))
  knownNatClassNameKey.

Definition knownSymbolClassName : Name.Name :=
  clsQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ "KnownSymbol"))
  knownSymbolClassNameKey.

Definition monadClassName : Name.Name :=
  clsQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Monad"))
  monadClassKey.

Definition monadClass_RDR : RdrName :=
  nameRdrName monadClassName.

Definition monadFailClassName : Name.Name :=
  clsQual mONAD_FAIL (FastString.fsLit (GHC.Base.hs_string__ "MonadFail"))
  monadFailClassKey.

Definition monadFixClassName : Name.Name :=
  clsQual mONAD_FIX (FastString.fsLit (GHC.Base.hs_string__ "MonadFix"))
  monadFixClassKey.

Definition monadPlusClassName : Name.Name :=
  clsQual mONAD (FastString.fsLit (GHC.Base.hs_string__ "MonadPlus"))
  monadPlusClassKey.

Definition monoidClassName : Name.Name :=
  clsQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Monoid"))
  monoidClassKey.

Definition numClassName : Name.Name :=
  clsQual gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "Num")) numClassKey.

Definition numClass_RDR : RdrName :=
  nameRdrName numClassName.

Definition ordClassName : Name.Name :=
  clsQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "Ord")) ordClassKey.

Definition ordClass_RDR : RdrName :=
  nameRdrName ordClassName.

Definition randomClassName : Name.Name :=
  clsQual rANDOM (FastString.fsLit (GHC.Base.hs_string__ "Random"))
  randomClassKey.

Definition randomGenClassName : Name.Name :=
  clsQual rANDOM (FastString.fsLit (GHC.Base.hs_string__ "RandomGen"))
  randomGenClassKey.

Definition readClassName : Name.Name :=
  clsQual gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "Read")) readClassKey.

Definition realClassName : Name.Name :=
  clsQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "Real")) realClassKey.

Definition realFloatClassName : Name.Name :=
  clsQual gHC_FLOAT (FastString.fsLit (GHC.Base.hs_string__ "RealFloat"))
  realFloatClassKey.

Definition realFracClassName : Name.Name :=
  clsQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "RealFrac"))
  realFracClassKey.

Definition selectorClassName : Name.Name :=
  clsQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Selector"))
  selectorClassKey.

Definition semigroupClassName : Name.Name :=
  clsQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Semigroup"))
  semigroupClassKey.

Definition showClassName : Name.Name :=
  clsQual gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "Show")) showClassKey.

Definition traversableClassName : Name.Name :=
  clsQual dATA_TRAVERSABLE (FastString.fsLit (GHC.Base.hs_string__ "Traversable"))
  traversableClassKey.

Definition interactiveClassNames : list Name.Name :=
  cons showClassName (cons eqClassName (cons ordClassName (cons foldableClassName
                                                                (cons traversableClassName nil)))).

Definition interactiveClassKeys : list Unique.Unique :=
  GHC.Base.map Unique.getUnique interactiveClassNames.

Definition typeableClassName : Name.Name :=
  clsQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "Typeable"))
  typeableClassKey.

Definition choose_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "choose")).

Definition choiceAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #184.

Definition checkDotnetResNameIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #154.

Definition charTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #8.

Definition charPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #7.

Definition charDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #1.

Definition callStackTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #186.

Definition callStackTyConName : Name.Name :=
  tcQual gHC_STACK_TYPES (FastString.fsLit (GHC.Base.hs_string__ "CallStack"))
  callStackTyConKey.

Definition cTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #147.

Definition cTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "C")) cTyConKey.

Definition cONTROL_EXCEPTION_BASE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Exception.Base")).

Definition cONTROL_APPLICATIVE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Applicative")).

Definition c1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #152.

Definition c1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "C1")) c1TyConKey.

Definition byteArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #5.

Definition buildIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #4.

Definition buildName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "build")) buildIdKey.

Definition build_RDR : RdrName :=
  nameRdrName buildName.

Definition breakpointJumpIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #113.

Definition breakpointJumpName : Name.Name :=
  Name.mkInternalName breakpointJumpIdKey (OccName.mkOccNameFS OccName.varName
                                           (FastString.fsLit (GHC.Base.hs_string__ "breakpointJump"))) SrcLoc.noSrcSpan.

Definition breakpointIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #110.

Definition breakpointName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "breakpoint"))
  breakpointIdKey.

Definition breakpointCondJumpIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #114.

Definition breakpointCondJumpName : Name.Name :=
  Name.mkInternalName breakpointCondJumpIdKey (OccName.mkOccNameFS OccName.varName
                                               (FastString.fsLit (GHC.Base.hs_string__ "breakpointCondJump")))
  SrcLoc.noSrcSpan.

Definition breakpointCondIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #111.

Definition breakpointCondName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "breakpointCond"))
  breakpointCondIdKey.

Definition breakpointAutoJumpIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #115.

Definition breakpointAutoJumpName : Name.Name :=
  Name.mkInternalName breakpointAutoJumpIdKey (OccName.mkOccNameFS OccName.varName
                                               (FastString.fsLit (GHC.Base.hs_string__ "breakpointAutoJump")))
  SrcLoc.noSrcSpan.

Definition breakpointAutoIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #112.

Definition breakpointAutoName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "breakpointAuto"))
  breakpointAutoIdKey.

Definition boxityConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #71.

Definition boundedClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #1.

Definition boundedClassName : Name.Name :=
  clsQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "Bounded"))
  boundedClassKey.

Definition derivableClassKeys : list Unique.Unique :=
  cons eqClassKey (cons ordClassKey (cons enumClassKey (cons ixClassKey (cons
                                                              boundedClassKey (cons showClassKey (cons readClassKey
                                                                                                       nil)))))).

Definition boolTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #4.

Definition bitIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #551.

Definition bitIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "bitInteger"))
  bitIntegerIdKey.

Definition bindMClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #171.

Definition bindMName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ ">>="))
  bindMClassOpKey.

Definition bindM_RDR : RdrName :=
  nameRdrName bindMName.

Definition bindIOIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #34.

Definition bindIOName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "bindIO")) bindIOIdKey.

Definition bindIO_RDR : RdrName :=
  nameRdrName bindIOName.

Definition bcoPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #74.

Axiom basicKnownKeyNames : list Name.Name.

Definition augmentIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #2.

Definition augmentName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "augment"))
  augmentIdKey.

Definition assertIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #44.

Definition assertName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "assert")) assertIdKey.

Definition assertErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #105.

Definition assertErrorName : Name.Name :=
  varQual gHC_IO_Exception (FastString.fsLit (GHC.Base.hs_string__ "assertError"))
  assertErrorIdKey.

Definition arrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #3.

Definition arrayArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #40.

Definition arrAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #180.

Definition applicativeClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #34.

Definition applicativeClassName : Name.Name :=
  clsQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Applicative"))
  applicativeClassKey.

Definition append_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "++")).

Definition appendIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #3.

Definition appendName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "++")) appendIdKey.

Definition appAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #183.

Definition apAClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #751.

Definition apAName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "<*>")) apAClassOpKey.

Definition ap_RDR : RdrName :=
  nameRdrName apAName.

Definition anyTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #181.

Definition anyBoxConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #69.

Definition and_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "&&")).

Definition andIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #91.

Definition andIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "andInteger"))
  andIntegerIdKey.

Definition alternativeClassKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #754.

Definition alternativeClassName : Name.Name :=
  clsQual mONAD (FastString.fsLit (GHC.Base.hs_string__ "Alternative"))
  alternativeClassKey.

Definition standardClassKeys : list Unique.Unique :=
  Coq.Init.Datatypes.app derivableClassKeys (Coq.Init.Datatypes.app
                          numericClassKeys (cons randomClassKey (cons randomGenClassKey (cons
                                                                       functorClassKey (cons monadClassKey (cons
                                                                                              monadPlusClassKey (cons
                                                                                               monadFailClassKey (cons
                                                                                                semigroupClassKey (cons
                                                                                                 monoidClassKey (cons
                                                                                                  isStringClassKey (cons
                                                                                                   applicativeClassKey
                                                                                                   (cons
                                                                                                    foldableClassKey
                                                                                                    (cons
                                                                                                     traversableClassKey
                                                                                                     (cons
                                                                                                      alternativeClassKey
                                                                                                      nil)))))))))))))).

Definition alt_RDR : RdrName :=
  varQual_RDR rEAD_PREC (FastString.fsLit (GHC.Base.hs_string__ "+++")).

Definition all_RDR : RdrName :=
  varQual_RDR dATA_FOLDABLE (FastString.fsLit (GHC.Base.hs_string__ "all")).

Axiom allNameStrings : list GHC.Base.String.

Definition addrPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #1.

Definition absentSumFieldErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #25.

Definition absentErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #1.

Definition absIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #72.

Definition absIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "absInteger"))
  absIntegerIdKey.

Definition aRROW : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Arrow")).

Definition appAName : Name.Name :=
  varQual aRROW (FastString.fsLit (GHC.Base.hs_string__ "app")) appAIdKey.

Definition arrAName : Name.Name :=
  varQual aRROW (FastString.fsLit (GHC.Base.hs_string__ "arr")) arrAIdKey.

Definition choiceAName : Name.Name :=
  varQual aRROW (FastString.fsLit (GHC.Base.hs_string__ "|||")) choiceAIdKey.

Definition firstAName : Name.Name :=
  varQual aRROW (FastString.fsLit (GHC.Base.hs_string__ "first")) firstAIdKey.

Definition loopAName : Name.Name :=
  varQual aRROW (FastString.fsLit (GHC.Base.hs_string__ "loop")) loopAIdKey.

(* External variables:
     Type bool cons list nat nil Coq.Init.Datatypes.app FastString.FastString
     FastString.fsLit GHC.Base.String GHC.Base.map GHC.Enum.enumFromTo
     GHC.Num.fromInteger Module.Module Module.ModuleName Module.baseUnitId
     Module.mainUnitId Module.mkModule Module.mkModuleNameFS Module.primUnitId
     Module.thisGhcUnitId Name.Name Name.mkExternalName Name.mkInternalName
     Name.mkSystemVarName OccName.NameSpace OccName.OccName OccName.clsName
     OccName.dataName OccName.mkOccNameFS OccName.tcName OccName.varName
     SrcLoc.SrcSpan SrcLoc.noSrcSpan Unique.Unique Unique.getUnique Unique.hasKey
     Unique.mkPreludeClassUnique Unique.mkPreludeDataConUnique
     Unique.mkPreludeMiscIdUnique Unique.mkPreludeTyConUnique
*)
