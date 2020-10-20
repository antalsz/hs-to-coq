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

Definition int8X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #300.

Definition int16X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #301.

Definition int32X4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #302.

Definition int64X2PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #303.

Definition int8X32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #304.

Definition int16X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #305.

Definition int32X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #306.

Definition int64X4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #307.

Definition int8X64PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #308.

Definition int16X32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #309.

Definition int32X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #310.

Definition int64X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #311.

Definition word8X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #312.

Definition word16X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #313.

Definition word32X4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #314.

Definition word64X2PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #315.

Definition word8X32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #316.

Definition word16X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #317.

Definition word32X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #318.

Definition word64X4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #319.

Definition word8X64PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #320.

Definition word16X32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #321.

Definition word32X16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #322.

Definition word64X8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #323.

Definition floatX4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #324.

Definition doubleX2PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #325.

Definition floatX8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #326.

Definition doubleX4PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #327.

Definition floatX16PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #328.

Definition doubleX8PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #329.

Axiom allNameStrings : list GHC.Base.String.

Definition itName : Unique.Unique -> SrcLoc.SrcSpan -> Name.Name :=
  fun uniq loc =>
    Name.mkInternalName uniq (OccName.mkOccNameFS OccName.varName (FastString.fsLit
                                                                   (GHC.Base.hs_string__ "it"))) loc.

Definition unboundKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #158.

Definition mkUnboundName : OccName.OccName -> Name.Name :=
  fun occ => Name.mkInternalName unboundKey occ SrcLoc.noSrcSpan.

Definition isUnboundName : Name.Name -> bool :=
  fun name => Unique.hasKey name unboundKey.

Axiom basicKnownKeyNames : list Name.Name.

Axiom genericTyConNames : list Name.Name.

Definition mkBaseModule_ : Module.ModuleName -> Module.Module :=
  fun m => Module.mkModule Module.baseUnitId m.

Definition pRELUDE_NAME : Module.ModuleName :=
  Module.mkModuleNameFS (FastString.fsLit (GHC.Base.hs_string__ "Prelude")).

Definition pRELUDE : Module.Module :=
  mkBaseModule_ pRELUDE_NAME.

Definition mkPrimModule : FastString.FastString -> Module.Module :=
  fun m => Module.mkModule Module.primUnitId (Module.mkModuleNameFS m).

Definition gHC_PRIM : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Prim")).

Definition gHC_TYPES : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Types")).

Definition gHC_MAGIC : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Magic")).

Definition gHC_CSTRING : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.CString")).

Definition gHC_CLASSES : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Classes")).

Definition mkBaseModule : FastString.FastString -> Module.Module :=
  fun m => Module.mkModule Module.baseUnitId (Module.mkModuleNameFS m).

Definition gHC_BASE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Base")).

Definition gHC_ENUM : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Enum")).

Definition gHC_GHCI : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.GHCi")).

Definition gHC_SHOW : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Show")).

Definition gHC_READ : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Read")).

Definition gHC_NUM : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Num")).

Axiom mkIntegerModule : FastString.FastString -> Module.Module.

Definition gHC_INTEGER_TYPE : Module.Module :=
  mkIntegerModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Integer.Type")).

Definition gHC_NATURAL : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Natural")).

Definition gHC_LIST : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.List")).

Definition gHC_TUPLE : Module.Module :=
  mkPrimModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Tuple")).

Definition dATA_TUPLE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Tuple")).

Definition dATA_EITHER : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Either")).

Definition dATA_STRING : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.String")).

Definition dATA_FOLDABLE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Foldable")).

Definition dATA_TRAVERSABLE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Traversable")).

Definition gHC_CONC : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Conc")).

Definition gHC_IO : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.IO")).

Definition gHC_IO_Exception : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.IO.Exception")).

Definition gHC_ST : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.ST")).

Definition gHC_ARR : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Arr")).

Definition gHC_STABLE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Stable")).

Definition gHC_PTR : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Ptr")).

Definition gHC_ERR : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Err")).

Definition gHC_REAL : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Real")).

Definition gHC_FLOAT : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Float")).

Definition gHC_TOP_HANDLER : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.TopHandler")).

Definition sYSTEM_IO : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "System.IO")).

Definition dYNAMIC : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Dynamic")).

Definition tYPEABLE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Typeable")).

Definition tYPEABLE_INTERNAL : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Typeable.Internal")).

Definition gENERICS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Data")).

Definition rEAD_PREC : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__
                                  "Text.ParserCombinators.ReadPrec")).

Definition lEX : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Text.Read.Lex")).

Definition gHC_INT : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Int")).

Definition gHC_WORD : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Word")).

Definition mONAD : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Monad")).

Definition mONAD_FIX : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Monad.Fix")).

Definition mONAD_ZIP : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Monad.Zip")).

Definition mONAD_FAIL : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Monad.Fail")).

Definition aRROW : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Arrow")).

Definition cONTROL_APPLICATIVE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Applicative")).

Definition gHC_DESUGAR : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Desugar")).

Definition rANDOM : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "System.Random")).

Definition gHC_EXTS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Exts")).

Definition cONTROL_EXCEPTION_BASE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Control.Exception.Base")).

Definition gHC_GENERICS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Generics")).

Definition gHC_TYPELITS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.TypeLits")).

Definition gHC_TYPENATS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.TypeNats")).

Definition dATA_TYPE_EQUALITY : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Type.Equality")).

Definition dATA_COERCE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Data.Coerce")).

Definition dEBUG_TRACE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "Debug.Trace")).

Definition gHC_PARR' : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.PArr")).

Definition gHC_SRCLOC : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.SrcLoc")).

Definition gHC_STACK : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Stack")).

Definition gHC_STACK_TYPES : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Stack.Types")).

Definition gHC_STATICPTR : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.StaticPtr")).

Definition gHC_STATICPTR_INTERNAL : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.StaticPtr.Internal")).

Definition gHC_FINGERPRINT_TYPE : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Fingerprint.Type")).

Definition gHC_OVER_LABELS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.OverloadedLabels")).

Definition gHC_RECORDS : Module.Module :=
  mkBaseModule (FastString.fsLit (GHC.Base.hs_string__ "GHC.Records")).

Definition mAIN_NAME : Module.ModuleName :=
  Module.mkModuleNameFS (FastString.fsLit (GHC.Base.hs_string__ "Main")).

Definition mkMainModule_ : Module.ModuleName -> Module.Module :=
  fun m => Module.mkModule Module.mainUnitId m.

Definition mAIN : Module.Module :=
  mkMainModule_ mAIN_NAME.

Definition mkMainModule : FastString.FastString -> Module.Module :=
  fun m => Module.mkModule Module.mainUnitId (Module.mkModuleNameFS m).

Definition rOOT_MAIN : Module.Module :=
  mkMainModule (FastString.fsLit (GHC.Base.hs_string__ ":Main")).

Axiom mkInteractiveModule : nat -> Module.Module.

Definition dATA_ARRAY_PARALLEL_NAME : Module.ModuleName :=
  Module.mkModuleNameFS (FastString.fsLit (GHC.Base.hs_string__
                                           "Data.Array.Parallel")).

Definition dATA_ARRAY_PARALLEL_PRIM_NAME : Module.ModuleName :=
  Module.mkModuleNameFS (FastString.fsLit (GHC.Base.hs_string__
                                           "Data.Array.Parallel.Prim")).

Definition mkThisGhcModule : FastString.FastString -> Module.Module :=
  fun m => Module.mkModule Module.thisGhcUnitId (Module.mkModuleNameFS m).

Definition mkThisGhcModule_ : Module.ModuleName -> Module.Module :=
  fun m => Module.mkModule Module.thisGhcUnitId m.

Axiom RdrName : Type.

Axiom main_RDR_Unqual : RdrName.

Axiom forall_tv_RDR : RdrName.

Axiom dot_tv_RDR : RdrName.

Definition eqClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #167.

Definition mk_known_key_name
   : OccName.NameSpace ->
     Module.Module -> FastString.FastString -> Unique.Unique -> Name.Name :=
  fun space modu str unique =>
    Name.mkExternalName unique modu (OccName.mkOccNameFS space str)
    SrcLoc.noSrcSpan.

Definition varQual
   : Module.Module -> FastString.FastString -> Unique.Unique -> Name.Name :=
  mk_known_key_name OccName.varName.

Definition eqName : Name.Name :=
  varQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "==")) eqClassOpKey.

Axiom nameRdrName : Name.Name -> RdrName.

Definition eq_RDR : RdrName :=
  nameRdrName eqName.

Definition geClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #168.

Definition geName : Name.Name :=
  varQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ ">=")) geClassOpKey.

Definition ge_RDR : RdrName :=
  nameRdrName geName.

Axiom varQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Definition le_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "<=")).

Definition lt_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "<")).

Definition gt_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ ">")).

Definition compare_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "compare")).

Axiom dataQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Definition ltTag_RDR : RdrName :=
  dataQual_RDR gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "LT")).

Definition eqTag_RDR : RdrName :=
  dataQual_RDR gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "EQ")).

Definition gtTag_RDR : RdrName :=
  dataQual_RDR gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "GT")).

Definition clsQual
   : Module.Module -> FastString.FastString -> Unique.Unique -> Name.Name :=
  mk_known_key_name OccName.clsName.

Definition eqClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #3.

Definition eqClassName : Name.Name :=
  clsQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "Eq")) eqClassKey.

Definition eqClass_RDR : RdrName :=
  nameRdrName eqClassName.

Definition numClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #11.

Definition numClassName : Name.Name :=
  clsQual gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "Num")) numClassKey.

Definition numClass_RDR : RdrName :=
  nameRdrName numClassName.

Definition ordClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #12.

Definition ordClassName : Name.Name :=
  clsQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "Ord")) ordClassKey.

Definition ordClass_RDR : RdrName :=
  nameRdrName ordClassName.

Definition enumClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #2.

Definition enumClassName : Name.Name :=
  clsQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "Enum")) enumClassKey.

Definition enumClass_RDR : RdrName :=
  nameRdrName enumClassName.

Definition monadClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #8.

Definition monadClassName : Name.Name :=
  clsQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Monad"))
  monadClassKey.

Definition monadClass_RDR : RdrName :=
  nameRdrName monadClassName.

Definition map_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "map")).

Definition append_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "++")).

Definition foldrIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #6.

Definition foldrName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "foldr")) foldrIdKey.

Definition foldr_RDR : RdrName :=
  nameRdrName foldrName.

Definition buildIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #4.

Definition buildName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "build")) buildIdKey.

Definition build_RDR : RdrName :=
  nameRdrName buildName.

Definition returnMClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #174.

Definition returnMName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "return"))
  returnMClassOpKey.

Definition returnM_RDR : RdrName :=
  nameRdrName returnMName.

Definition bindMClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #171.

Definition bindMName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ ">>="))
  bindMClassOpKey.

Definition bindM_RDR : RdrName :=
  nameRdrName bindMName.

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

Definition dcQual
   : Module.Module -> FastString.FastString -> Unique.Unique -> Name.Name :=
  mk_known_key_name OccName.dataName.

Definition leftDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #25.

Definition leftDataConName : Name.Name :=
  dcQual dATA_EITHER (FastString.fsLit (GHC.Base.hs_string__ "Left"))
  leftDataConKey.

Definition left_RDR : RdrName :=
  nameRdrName leftDataConName.

Definition rightDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #26.

Definition rightDataConName : Name.Name :=
  dcQual dATA_EITHER (FastString.fsLit (GHC.Base.hs_string__ "Right"))
  rightDataConKey.

Definition right_RDR : RdrName :=
  nameRdrName rightDataConName.

Definition fromEnum_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "fromEnum")).

Definition toEnum_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "toEnum")).

Definition enumFromClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #163.

Definition enumFromName : Name.Name :=
  varQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "enumFrom"))
  enumFromClassOpKey.

Definition enumFrom_RDR : RdrName :=
  nameRdrName enumFromName.

Definition enumFromToClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #165.

Definition enumFromToName : Name.Name :=
  varQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "enumFromTo"))
  enumFromToClassOpKey.

Definition enumFromTo_RDR : RdrName :=
  nameRdrName enumFromToName.

Definition enumFromThenClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #164.

Definition enumFromThenName : Name.Name :=
  varQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "enumFromThen"))
  enumFromThenClassOpKey.

Definition enumFromThen_RDR : RdrName :=
  nameRdrName enumFromThenName.

Definition enumFromThenToClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #166.

Definition enumFromThenToName : Name.Name :=
  varQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "enumFromThenTo"))
  enumFromThenToClassOpKey.

Definition enumFromThenTo_RDR : RdrName :=
  nameRdrName enumFromThenToName.

Definition ratioDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #12.

Definition ratioDataConName : Name.Name :=
  dcQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ ":%")) ratioDataConKey.

Definition ratioDataCon_RDR : RdrName :=
  nameRdrName ratioDataConName.

Definition plusIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #66.

Definition plusIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "plusInteger"))
  plusIntegerIdKey.

Definition plusInteger_RDR : RdrName :=
  nameRdrName plusIntegerName.

Definition timesIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #67.

Definition timesIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "timesInteger")) timesIntegerIdKey.

Definition timesInteger_RDR : RdrName :=
  nameRdrName timesIntegerName.

Definition ioDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #17.

Definition ioDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "IO")) ioDataConKey.

Definition ioDataCon_RDR : RdrName :=
  nameRdrName ioDataConName.

Definition eqStringIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #10.

Definition eqStringName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "eqString"))
  eqStringIdKey.

Definition eqString_RDR : RdrName :=
  nameRdrName eqStringName.

Definition unpackCStringIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #20.

Definition unpackCStringName : Name.Name :=
  varQual gHC_CSTRING (FastString.fsLit (GHC.Base.hs_string__ "unpackCString#"))
  unpackCStringIdKey.

Definition unpackCString_RDR : RdrName :=
  nameRdrName unpackCStringName.

Definition unpackCStringFoldrIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #19.

Definition unpackCStringFoldrName : Name.Name :=
  varQual gHC_CSTRING (FastString.fsLit (GHC.Base.hs_string__
                                         "unpackFoldrCString#")) unpackCStringFoldrIdKey.

Definition unpackCStringFoldr_RDR : RdrName :=
  nameRdrName unpackCStringFoldrName.

Definition unpackCStringUtf8IdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #17.

Definition unpackCStringUtf8Name : Name.Name :=
  varQual gHC_CSTRING (FastString.fsLit (GHC.Base.hs_string__
                                         "unpackCStringUtf8#")) unpackCStringUtf8IdKey.

Definition unpackCStringUtf8_RDR : RdrName :=
  nameRdrName unpackCStringUtf8Name.

Definition newStablePtrIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #36.

Definition newStablePtrName : Name.Name :=
  varQual gHC_STABLE (FastString.fsLit (GHC.Base.hs_string__ "newStablePtr"))
  newStablePtrIdKey.

Definition newStablePtr_RDR : RdrName :=
  nameRdrName newStablePtrName.

Definition bindIOIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #34.

Definition bindIOName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "bindIO")) bindIOIdKey.

Definition bindIO_RDR : RdrName :=
  nameRdrName bindIOName.

Definition returnIOIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #35.

Definition returnIOName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "returnIO"))
  returnIOIdKey.

Definition returnIO_RDR : RdrName :=
  nameRdrName returnIOName.

Definition fromIntegerClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #160.

Definition fromIntegerName : Name.Name :=
  varQual gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "fromInteger"))
  fromIntegerClassOpKey.

Definition fromInteger_RDR : RdrName :=
  nameRdrName fromIntegerName.

Definition fromRationalClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #162.

Definition fromRationalName : Name.Name :=
  varQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "fromRational"))
  fromRationalClassOpKey.

Definition fromRational_RDR : RdrName :=
  nameRdrName fromRationalName.

Definition minusClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #161.

Definition minusName : Name.Name :=
  varQual gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "-")) minusClassOpKey.

Definition minus_RDR : RdrName :=
  nameRdrName minusName.

Definition times_RDR : RdrName :=
  varQual_RDR gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "*")).

Definition plus_RDR : RdrName :=
  varQual_RDR gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "+")).

Definition toIntegerClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #192.

Definition toIntegerName : Name.Name :=
  varQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "toInteger"))
  toIntegerClassOpKey.

Definition toInteger_RDR : RdrName :=
  nameRdrName toIntegerName.

Definition toRationalClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #193.

Definition toRationalName : Name.Name :=
  varQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "toRational"))
  toRationalClassOpKey.

Definition toRational_RDR : RdrName :=
  nameRdrName toRationalName.

Definition fromIntegralIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #190.

Definition fromIntegralName : Name.Name :=
  varQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "fromIntegral"))
  fromIntegralIdKey.

Definition fromIntegral_RDR : RdrName :=
  nameRdrName fromIntegralName.

Axiom tcQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Definition stringTy_RDR : RdrName :=
  tcQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "String")).

Definition fromStringClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #186.

Definition fromStringName : Name.Name :=
  varQual dATA_STRING (FastString.fsLit (GHC.Base.hs_string__ "fromString"))
  fromStringClassOpKey.

Definition fromString_RDR : RdrName :=
  nameRdrName fromStringName.

Definition fromListClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #199.

Definition fromListName : Name.Name :=
  varQual gHC_EXTS (FastString.fsLit (GHC.Base.hs_string__ "fromList"))
  fromListClassOpKey.

Definition fromList_RDR : RdrName :=
  nameRdrName fromListName.

Definition fromListNClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #500.

Definition fromListNName : Name.Name :=
  varQual gHC_EXTS (FastString.fsLit (GHC.Base.hs_string__ "fromListN"))
  fromListNClassOpKey.

Definition fromListN_RDR : RdrName :=
  nameRdrName fromListNName.

Definition toListClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #501.

Definition toListName : Name.Name :=
  varQual gHC_EXTS (FastString.fsLit (GHC.Base.hs_string__ "toList"))
  toListClassOpKey.

Definition toList_RDR : RdrName :=
  nameRdrName toListName.

Definition compose_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ ".")).

Definition and_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "&&")).

Definition not_RDR : RdrName :=
  varQual_RDR gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "not")).

Definition getTag_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "getTag")).

Definition succ_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "succ")).

Definition pred_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "pred")).

Definition minBound_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "minBound")).

Definition maxBound_RDR : RdrName :=
  varQual_RDR gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "maxBound")).

Definition range_RDR : RdrName :=
  varQual_RDR gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "range")).

Definition inRange_RDR : RdrName :=
  varQual_RDR gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "inRange")).

Definition index_RDR : RdrName :=
  varQual_RDR gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "index")).

Definition unsafeIndex_RDR : RdrName :=
  varQual_RDR gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "unsafeIndex")).

Definition unsafeRangeSize_RDR : RdrName :=
  varQual_RDR gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "unsafeRangeSize")).

Definition readList_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readList")).

Definition readListDefault_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__
                                          "readListDefault")).

Definition readListPrec_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readListPrec")).

Definition readListPrecDefault_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__
                                          "readListPrecDefault")).

Definition readPrec_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readPrec")).

Definition parens_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "parens")).

Definition choose_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "choose")).

Definition lexP_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "lexP")).

Definition expectP_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "expectP")).

Definition readField_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readField")).

Definition readFieldHash_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readFieldHash")).

Definition readSymField_RDR : RdrName :=
  varQual_RDR gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "readSymField")).

Definition punc_RDR : RdrName :=
  dataQual_RDR lEX (FastString.fsLit (GHC.Base.hs_string__ "Punc")).

Definition ident_RDR : RdrName :=
  dataQual_RDR lEX (FastString.fsLit (GHC.Base.hs_string__ "Ident")).

Definition symbol_RDR : RdrName :=
  dataQual_RDR lEX (FastString.fsLit (GHC.Base.hs_string__ "Symbol")).

Definition step_RDR : RdrName :=
  varQual_RDR rEAD_PREC (FastString.fsLit (GHC.Base.hs_string__ "step")).

Definition alt_RDR : RdrName :=
  varQual_RDR rEAD_PREC (FastString.fsLit (GHC.Base.hs_string__ "+++")).

Definition reset_RDR : RdrName :=
  varQual_RDR rEAD_PREC (FastString.fsLit (GHC.Base.hs_string__ "reset")).

Definition prec_RDR : RdrName :=
  varQual_RDR rEAD_PREC (FastString.fsLit (GHC.Base.hs_string__ "prec")).

Definition pfail_RDR : RdrName :=
  varQual_RDR rEAD_PREC (FastString.fsLit (GHC.Base.hs_string__ "pfail")).

Definition showsPrec_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "showsPrec")).

Definition shows_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "shows")).

Definition showString_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "showString")).

Definition showSpace_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "showSpace")).

Definition showCommaSpace_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "showCommaSpace")).

Definition showParen_RDR : RdrName :=
  varQual_RDR gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "showParen")).

Definition undefined_RDR : RdrName :=
  varQual_RDR gHC_ERR (FastString.fsLit (GHC.Base.hs_string__ "undefined")).

Definition error_RDR : RdrName :=
  varQual_RDR gHC_ERR (FastString.fsLit (GHC.Base.hs_string__ "error")).

Definition u1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "U1")).

Definition par1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Par1")).

Definition rec1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Rec1")).

Definition k1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "K1")).

Definition m1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "M1")).

Definition l1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "L1")).

Definition r1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "R1")).

Definition prodDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ ":*:")).

Definition comp1DataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Comp1")).

Definition unPar1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "unPar1")).

Definition unRec1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "unRec1")).

Definition unK1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "unK1")).

Definition unComp1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "unComp1")).

Definition from_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "from")).

Definition from1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "from1")).

Definition to_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "to")).

Definition to1_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "to1")).

Definition datatypeName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                              "datatypeName")).

Definition moduleName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "moduleName")).

Definition packageName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                              "packageName")).

Definition isNewtypeName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "isNewtype")).

Definition selName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "selName")).

Definition conName_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "conName")).

Definition conFixity_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "conFixity")).

Definition conIsRecord_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                              "conIsRecord")).

Definition prefixDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Prefix")).

Definition infixDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Infix")).

Definition leftAssocDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                               "LeftAssociative")).

Definition rightAssocDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                               "RightAssociative")).

Definition notAssocDataCon_RDR : RdrName :=
  dataQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                               "NotAssociative")).

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

Definition uAddrHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uAddr#")).

Definition uCharHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uChar#")).

Definition uDoubleHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uDouble#")).

Definition uFloatHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uFloat#")).

Definition uIntHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uInt#")).

Definition uWordHash_RDR : RdrName :=
  varQual_RDR gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "uWord#")).

Definition fmap_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "fmap")).

Definition replace_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "<$")).

Definition pureAClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #752.

Definition pureAName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "pure"))
  pureAClassOpKey.

Definition pure_RDR : RdrName :=
  nameRdrName pureAName.

Definition apAClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #751.

Definition apAName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "<*>")) apAClassOpKey.

Definition ap_RDR : RdrName :=
  nameRdrName apAName.

Definition liftA2_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "liftA2")).

Definition foldable_foldr_RDR : RdrName :=
  varQual_RDR dATA_FOLDABLE (FastString.fsLit (GHC.Base.hs_string__ "foldr")).

Definition foldMap_RDR : RdrName :=
  varQual_RDR dATA_FOLDABLE (FastString.fsLit (GHC.Base.hs_string__ "foldMap")).

Definition null_RDR : RdrName :=
  varQual_RDR dATA_FOLDABLE (FastString.fsLit (GHC.Base.hs_string__ "null")).

Definition all_RDR : RdrName :=
  varQual_RDR dATA_FOLDABLE (FastString.fsLit (GHC.Base.hs_string__ "all")).

Definition traverse_RDR : RdrName :=
  varQual_RDR dATA_TRAVERSABLE (FastString.fsLit (GHC.Base.hs_string__
                                                  "traverse")).

Definition mempty_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "mempty")).

Definition mappend_RDR : RdrName :=
  varQual_RDR gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "mappend")).

Definition eqTyCon_RDR : RdrName :=
  tcQual_RDR dATA_TYPE_EQUALITY (FastString.fsLit (GHC.Base.hs_string__ "~")).

Axiom clsQual_RDR : Module.Module -> FastString.FastString -> RdrName.

Definition wildCardKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #0.

Definition wildCardName : Name.Name :=
  Name.mkSystemVarName wildCardKey (FastString.fsLit (GHC.Base.hs_string__
                                                      "wild")).

Definition runMainKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #102.

Definition runMainIOName : Name.Name :=
  varQual gHC_TOP_HANDLER (FastString.fsLit (GHC.Base.hs_string__ "runMainIO"))
  runMainKey.

Definition orderingTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #30.

Definition tcQual
   : Module.Module -> FastString.FastString -> Unique.Unique -> Name.Name :=
  mk_known_key_name OccName.tcName.

Definition orderingTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "Ordering"))
  orderingTyConKey.

Definition ltDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #27.

Definition ltDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "LT")) ltDataConKey.

Definition eqDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #28.

Definition eqDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "EQ")) eqDataConKey.

Definition gtDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #29.

Definition gtDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "GT")) gtDataConKey.

Definition specTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #180.

Definition specTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "SPEC")) specTyConKey.

Definition eitherTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #84.

Definition eitherTyConName : Name.Name :=
  tcQual dATA_EITHER (FastString.fsLit (GHC.Base.hs_string__ "Either"))
  eitherTyConKey.

Definition v1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #135.

Definition v1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "V1")) v1TyConKey.

Definition u1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #136.

Definition u1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "U1")) u1TyConKey.

Definition par1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #137.

Definition par1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Par1"))
  par1TyConKey.

Definition rec1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #138.

Definition rec1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Rec1"))
  rec1TyConKey.

Definition k1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #139.

Definition k1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "K1")) k1TyConKey.

Definition m1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #140.

Definition m1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "M1")) m1TyConKey.

Definition sumTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #141.

Definition sumTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ ":+:")) sumTyConKey.

Definition prodTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #142.

Definition prodTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ ":*:"))
  prodTyConKey.

Definition compTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #143.

Definition compTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ ":.:"))
  compTyConKey.

Definition rTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #144.

Definition rTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "R")) rTyConKey.

Definition dTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #146.

Definition dTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "D")) dTyConKey.

Definition cTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #147.

Definition cTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "C")) cTyConKey.

Definition sTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #148.

Definition sTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "S")) sTyConKey.

Definition rec0TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #149.

Definition rec0TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Rec0"))
  rec0TyConKey.

Definition d1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #151.

Definition d1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "D1")) d1TyConKey.

Definition c1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #152.

Definition c1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "C1")) c1TyConKey.

Definition s1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #153.

Definition s1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "S1")) s1TyConKey.

Definition noSelTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #154.

Definition noSelTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "NoSelector"))
  noSelTyConKey.

Definition repTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #155.

Definition repTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Rep")) repTyConKey.

Definition rep1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #156.

Definition rep1TyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Rep1"))
  rep1TyConKey.

Definition uRecTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #157.

Definition uRecTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "URec"))
  uRecTyConKey.

Definition uAddrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #158.

Definition uAddrTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UAddr"))
  uAddrTyConKey.

Definition uCharTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #159.

Definition uCharTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UChar"))
  uCharTyConKey.

Definition uDoubleTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #160.

Definition uDoubleTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UDouble"))
  uDoubleTyConKey.

Definition uFloatTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #161.

Definition uFloatTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UFloat"))
  uFloatTyConKey.

Definition uIntTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #162.

Definition uIntTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UInt"))
  uIntTyConKey.

Definition uWordTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #163.

Definition uWordTyConName : Name.Name :=
  tcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "UWord"))
  uWordTyConKey.

Definition prefixIDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #54.

Definition prefixIDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "PrefixI"))
  prefixIDataConKey.

Definition infixIDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #55.

Definition infixIDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "InfixI"))
  infixIDataConKey.

Definition leftAssociativeDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #56.

Definition leftAssociativeDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "LeftAssociative"))
  leftAssociativeDataConKey.

Definition rightAssociativeDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #57.

Definition rightAssociativeDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "RightAssociative"))
  rightAssociativeDataConKey.

Definition notAssociativeDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #58.

Definition notAssociativeDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "NotAssociative"))
  notAssociativeDataConKey.

Definition sourceUnpackDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #59.

Definition sourceUnpackDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "SourceUnpack"))
  sourceUnpackDataConKey.

Definition sourceNoUnpackDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #60.

Definition sourceNoUnpackDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "SourceNoUnpack"))
  sourceNoUnpackDataConKey.

Definition noSourceUnpackednessDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #61.

Definition noSourceUnpackednessDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                         "NoSourceUnpackedness")) noSourceUnpackednessDataConKey.

Definition sourceLazyDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #62.

Definition sourceLazyDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "SourceLazy"))
  sourceLazyDataConKey.

Definition sourceStrictDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #63.

Definition sourceStrictDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "SourceStrict"))
  sourceStrictDataConKey.

Definition noSourceStrictnessDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #64.

Definition noSourceStrictnessDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__
                                         "NoSourceStrictness")) noSourceStrictnessDataConKey.

Definition decidedLazyDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #65.

Definition decidedLazyDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "DecidedLazy"))
  decidedLazyDataConKey.

Definition decidedStrictDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #66.

Definition decidedStrictDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "DecidedStrict"))
  decidedStrictDataConKey.

Definition decidedUnpackDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #67.

Definition decidedUnpackDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "DecidedUnpack"))
  decidedUnpackDataConKey.

Definition metaDataDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #68.

Definition metaDataDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "MetaData"))
  metaDataDataConKey.

Definition metaConsDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #69.

Definition metaConsDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "MetaCons"))
  metaConsDataConKey.

Definition metaSelDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #70.

Definition metaSelDataConName : Name.Name :=
  dcQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "MetaSel"))
  metaSelDataConKey.

Definition divIntIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #23.

Definition divIntName : Name.Name :=
  varQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "divInt#"))
  divIntIdKey.

Definition modIntIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #24.

Definition modIntName : Name.Name :=
  varQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "modInt#"))
  modIntIdKey.

Definition inlineIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #120.

Definition inlineIdName : Name.Name :=
  varQual gHC_MAGIC (FastString.fsLit (GHC.Base.hs_string__ "inline"))
  inlineIdKey.

Definition functorClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #10.

Definition functorClassName : Name.Name :=
  clsQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Functor"))
  functorClassKey.

Definition fmapClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #173.

Definition fmapName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "fmap"))
  fmapClassOpKey.

Definition thenMClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #172.

Definition thenMName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ ">>")) thenMClassOpKey.

Definition monadFailClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #29.

Definition monadFailClassName : Name.Name :=
  clsQual mONAD_FAIL (FastString.fsLit (GHC.Base.hs_string__ "MonadFail"))
  monadFailClassKey.

Definition applicativeClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #34.

Definition applicativeClassName : Name.Name :=
  clsQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Applicative"))
  applicativeClassKey.

Definition thenAClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #753.

Definition thenAName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "*>")) thenAClassOpKey.

Definition foldableClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #35.

Definition foldableClassName : Name.Name :=
  clsQual dATA_FOLDABLE (FastString.fsLit (GHC.Base.hs_string__ "Foldable"))
  foldableClassKey.

Definition traversableClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #36.

Definition traversableClassName : Name.Name :=
  clsQual dATA_TRAVERSABLE (FastString.fsLit (GHC.Base.hs_string__ "Traversable"))
  traversableClassKey.

Definition semigroupClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #46.

Definition semigroupClassName : Name.Name :=
  clsQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Semigroup"))
  semigroupClassKey.

Definition sappendClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #554.

Definition sappendName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "<>"))
  sappendClassOpKey.

Definition monoidClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #47.

Definition monoidClassName : Name.Name :=
  clsQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Monoid"))
  monoidClassKey.

Definition memptyClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #555.

Definition memptyName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "mempty"))
  memptyClassOpKey.

Definition mappendClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #556.

Definition mappendName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "mappend"))
  mappendClassOpKey.

Definition mconcatClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #557.

Definition mconcatName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "mconcat"))
  mconcatClassOpKey.

Definition joinMIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #750.

Definition joinMName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "join")) joinMIdKey.

Definition alternativeClassKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #754.

Definition alternativeClassName : Name.Name :=
  clsQual mONAD (FastString.fsLit (GHC.Base.hs_string__ "Alternative"))
  alternativeClassKey.

Definition groupWithIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #122.

Definition groupWithName : Name.Name :=
  varQual gHC_EXTS (FastString.fsLit (GHC.Base.hs_string__ "groupWith"))
  groupWithIdKey.

Definition otherwiseIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #43.

Definition otherwiseIdName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "otherwise"))
  otherwiseIdKey.

Definition augmentIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #2.

Definition augmentName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "augment"))
  augmentIdKey.

Definition mapIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #121.

Definition mapName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "map")) mapIdKey.

Definition appendIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #3.

Definition appendName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "++")) appendIdKey.

Definition assertIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #44.

Definition assertName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "assert")) assertIdKey.

Definition breakpointIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #110.

Definition breakpointName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "breakpoint"))
  breakpointIdKey.

Definition breakpointCondIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #111.

Definition breakpointCondName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "breakpointCond"))
  breakpointCondIdKey.

Definition breakpointAutoIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #112.

Definition breakpointAutoName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "breakpointAuto"))
  breakpointAutoIdKey.

Definition opaqueTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #133.

Definition opaqueTyConName : Name.Name :=
  tcQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "Opaque"))
  opaqueTyConKey.

Definition breakpointJumpIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #113.

Definition breakpointJumpName : Name.Name :=
  Name.mkInternalName breakpointJumpIdKey (OccName.mkOccNameFS OccName.varName
                                           (FastString.fsLit (GHC.Base.hs_string__ "breakpointJump"))) SrcLoc.noSrcSpan.

Definition breakpointCondJumpIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #114.

Definition breakpointCondJumpName : Name.Name :=
  Name.mkInternalName breakpointCondJumpIdKey (OccName.mkOccNameFS OccName.varName
                                               (FastString.fsLit (GHC.Base.hs_string__ "breakpointCondJump")))
  SrcLoc.noSrcSpan.

Definition breakpointAutoJumpIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #115.

Definition breakpointAutoJumpName : Name.Name :=
  Name.mkInternalName breakpointAutoJumpIdKey (OccName.mkOccNameFS OccName.varName
                                               (FastString.fsLit (GHC.Base.hs_string__ "breakpointAutoJump")))
  SrcLoc.noSrcSpan.

Definition fstIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #41.

Definition fstName : Name.Name :=
  varQual dATA_TUPLE (FastString.fsLit (GHC.Base.hs_string__ "fst")) fstIdKey.

Definition sndIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #42.

Definition sndName : Name.Name :=
  varQual dATA_TUPLE (FastString.fsLit (GHC.Base.hs_string__ "snd")) sndIdKey.

Definition negateClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #169.

Definition negateName : Name.Name :=
  varQual gHC_NUM (FastString.fsLit (GHC.Base.hs_string__ "negate"))
  negateClassOpKey.

Definition integerTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #22.

Definition integerTyConName : Name.Name :=
  tcQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "Integer"))
  integerTyConKey.

Axiom integerSDataConName : Name.Name.

Definition mkIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #60.

Definition mkIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "mkInteger"))
  mkIntegerIdKey.

Definition integerToWord64IdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #64.

Definition integerToWord64Name : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "integerToWord64")) integerToWord64IdKey.

Definition integerToInt64IdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #65.

Definition integerToInt64Name : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "integerToInt64")) integerToInt64IdKey.

Definition word64ToIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #98.

Definition word64ToIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "word64ToInteger")) word64ToIntegerIdKey.

Definition int64ToIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #99.

Definition int64ToIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "int64ToInteger")) int64ToIntegerIdKey.

Definition smallIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #61.

Definition smallIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "smallInteger")) smallIntegerIdKey.

Definition wordToIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #97.

Definition wordToIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "wordToInteger")) wordToIntegerIdKey.

Definition integerToWordIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #62.

Definition integerToWordName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "integerToWord")) integerToWordIdKey.

Definition integerToIntIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #63.

Definition integerToIntName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "integerToInt")) integerToIntIdKey.

Definition minusIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #68.

Definition minusIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "minusInteger")) minusIntegerIdKey.

Definition negateIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #69.

Definition negateIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "negateInteger")) negateIntegerIdKey.

Definition eqIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #70.

Definition eqIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "eqInteger#"))
  eqIntegerPrimIdKey.

Definition neqIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #71.

Definition neqIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "neqInteger#"))
  neqIntegerPrimIdKey.

Definition absIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #72.

Definition absIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "absInteger"))
  absIntegerIdKey.

Definition signumIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #73.

Definition signumIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "signumInteger")) signumIntegerIdKey.

Definition leIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #74.

Definition leIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "leInteger#"))
  leIntegerPrimIdKey.

Definition gtIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #75.

Definition gtIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "gtInteger#"))
  gtIntegerPrimIdKey.

Definition ltIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #76.

Definition ltIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "ltInteger#"))
  ltIntegerPrimIdKey.

Definition geIntegerPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #77.

Definition geIntegerPrimName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "geInteger#"))
  geIntegerPrimIdKey.

Definition compareIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #78.

Definition compareIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "compareInteger")) compareIntegerIdKey.

Definition quotRemIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #84.

Definition quotRemIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "quotRemInteger")) quotRemIntegerIdKey.

Definition divModIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #83.

Definition divModIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "divModInteger")) divModIntegerIdKey.

Definition quotIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #79.

Definition quotIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "quotInteger"))
  quotIntegerIdKey.

Definition remIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #80.

Definition remIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "remInteger"))
  remIntegerIdKey.

Definition divIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #81.

Definition divIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "divInteger"))
  divIntegerIdKey.

Definition modIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #82.

Definition modIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "modInteger"))
  modIntegerIdKey.

Definition floatFromIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #85.

Definition floatFromIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "floatFromInteger")) floatFromIntegerIdKey.

Definition doubleFromIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #86.

Definition doubleFromIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "doubleFromInteger")) doubleFromIntegerIdKey.

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

Definition decodeDoubleIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #100.

Definition decodeDoubleIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "decodeDoubleInteger")) decodeDoubleIntegerIdKey.

Definition gcdIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #89.

Definition gcdIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "gcdInteger"))
  gcdIntegerIdKey.

Definition lcmIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #90.

Definition lcmIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "lcmInteger"))
  lcmIntegerIdKey.

Definition andIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #91.

Definition andIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "andInteger"))
  andIntegerIdKey.

Definition orIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #92.

Definition orIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "orInteger"))
  orIntegerIdKey.

Definition xorIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #93.

Definition xorIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "xorInteger"))
  xorIntegerIdKey.

Definition complementIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #94.

Definition complementIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "complementInteger")) complementIntegerIdKey.

Definition shiftLIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #95.

Definition shiftLIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "shiftLInteger")) shiftLIntegerIdKey.

Definition shiftRIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #96.

Definition shiftRIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                              "shiftRInteger")) shiftRIntegerIdKey.

Definition bitIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #551.

Definition bitIntegerName : Name.Name :=
  varQual gHC_INTEGER_TYPE (FastString.fsLit (GHC.Base.hs_string__ "bitInteger"))
  bitIntegerIdKey.

Definition naturalTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #23.

Definition naturalTyConName : Name.Name :=
  tcQual gHC_NATURAL (FastString.fsLit (GHC.Base.hs_string__ "Natural"))
  naturalTyConKey.

Definition naturalFromIntegerIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #562.

Definition naturalFromIntegerName : Name.Name :=
  varQual gHC_NATURAL (FastString.fsLit (GHC.Base.hs_string__
                                         "naturalFromInteger")) naturalFromIntegerIdKey.

Definition rationalTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #33.

Definition rationalTyConName : Name.Name :=
  tcQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "Rational"))
  rationalTyConKey.

Definition ratioTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #32.

Definition ratioTyConName : Name.Name :=
  tcQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "Ratio")) ratioTyConKey.

Definition realClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #14.

Definition realClassName : Name.Name :=
  clsQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "Real")) realClassKey.

Definition integralClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #7.

Definition integralClassName : Name.Name :=
  clsQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "Integral"))
  integralClassKey.

Definition realFracClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #16.

Definition realFracClassName : Name.Name :=
  clsQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "RealFrac"))
  realFracClassKey.

Definition fractionalClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #6.

Definition fractionalClassName : Name.Name :=
  clsQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "Fractional"))
  fractionalClassKey.

Definition realToFracIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #191.

Definition realToFracName : Name.Name :=
  varQual gHC_REAL (FastString.fsLit (GHC.Base.hs_string__ "realToFrac"))
  realToFracIdKey.

Definition floatingClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #5.

Definition floatingClassName : Name.Name :=
  clsQual gHC_FLOAT (FastString.fsLit (GHC.Base.hs_string__ "Floating"))
  floatingClassKey.

Definition realFloatClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #15.

Definition realFloatClassName : Name.Name :=
  clsQual gHC_FLOAT (FastString.fsLit (GHC.Base.hs_string__ "RealFloat"))
  realFloatClassKey.

Definition rationalToFloatIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #130.

Definition rationalToFloatName : Name.Name :=
  varQual gHC_FLOAT (FastString.fsLit (GHC.Base.hs_string__ "rationalToFloat"))
  rationalToFloatIdKey.

Definition rationalToDoubleIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #131.

Definition rationalToDoubleName : Name.Name :=
  varQual gHC_FLOAT (FastString.fsLit (GHC.Base.hs_string__ "rationalToDouble"))
  rationalToDoubleIdKey.

Definition ixClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #18.

Definition ixClassName : Name.Name :=
  clsQual gHC_ARR (FastString.fsLit (GHC.Base.hs_string__ "Ix")) ixClassKey.

Definition trModuleTyConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #42.

Definition trModuleTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "Module"))
  trModuleTyConKey.

Definition trModuleDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #43.

Definition trModuleDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "Module"))
  trModuleDataConKey.

Definition trNameTyConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #44.

Definition trNameTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TrName"))
  trNameTyConKey.

Definition trNameSDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #45.

Definition trNameSDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TrNameS"))
  trNameSDataConKey.

Definition trNameDDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #46.

Definition trNameDDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TrNameD"))
  trNameDDataConKey.

Definition trTyConTyConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #40.

Definition trTyConTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TyCon"))
  trTyConTyConKey.

Definition trTyConDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #41.

Definition trTyConDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TyCon"))
  trTyConDataConKey.

Definition kindRepTyConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #48.

Definition kindRepTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRep"))
  kindRepTyConKey.

Definition kindRepTyConAppDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #100.

Definition kindRepTyConAppDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepTyConApp"))
  kindRepTyConAppDataConKey.

Definition kindRepVarDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #101.

Definition kindRepVarDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepVar"))
  kindRepVarDataConKey.

Definition kindRepAppDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #102.

Definition kindRepAppDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepApp"))
  kindRepAppDataConKey.

Definition kindRepFunDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #103.

Definition kindRepFunDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepFun"))
  kindRepFunDataConKey.

Definition kindRepTYPEDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #104.

Definition kindRepTYPEDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepTYPE"))
  kindRepTYPEDataConKey.

Definition kindRepTypeLitSDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #105.

Definition kindRepTypeLitSDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepTypeLitS"))
  kindRepTypeLitSDataConKey.

Definition kindRepTypeLitDDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #106.

Definition kindRepTypeLitDDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "KindRepTypeLitD"))
  kindRepTypeLitDDataConKey.

Definition typeLitSortTyConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #49.

Definition typeLitSortTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TypeLitSort"))
  typeLitSortTyConKey.

Definition typeLitSymbolDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #107.

Definition typeLitSymbolDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TypeLitSymbol"))
  typeLitSymbolDataConKey.

Definition typeLitNatDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #108.

Definition typeLitNatDataConName : Name.Name :=
  dcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "TypeLitNat"))
  typeLitNatDataConKey.

Definition typeableClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #20.

Definition typeableClassName : Name.Name :=
  clsQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "Typeable"))
  typeableClassKey.

Definition typeRepTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #187.

Definition typeRepTyConName : Name.Name :=
  tcQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "TypeRep"))
  typeRepTyConKey.

Definition someTypeRepTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #188.

Definition someTypeRepTyConName : Name.Name :=
  tcQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "SomeTypeRep"))
  someTypeRepTyConKey.

Definition someTypeRepDataConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #189.

Definition someTypeRepDataConName : Name.Name :=
  dcQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "SomeTypeRep"))
  someTypeRepDataConKey.

Definition typeRepIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #509.

Definition typeRepIdName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "typeRep#"))
  typeRepIdKey.

Definition mkTrTypeKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #504.

Definition mkTrTypeName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "mkTrType"))
  mkTrTypeKey.

Definition mkTrConKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #505.

Definition mkTrConName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "mkTrCon"))
  mkTrConKey.

Definition mkTrAppKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #506.

Definition mkTrAppName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "mkTrApp"))
  mkTrAppKey.

Definition mkTrFunKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #510.

Definition mkTrFunName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__ "mkTrFun"))
  mkTrFunKey.

Definition typeNatTypeRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #507.

Definition typeNatTypeRepName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__
                                               "typeNatTypeRep")) typeNatTypeRepKey.

Definition typeSymbolTypeRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #508.

Definition typeSymbolTypeRepName : Name.Name :=
  varQual tYPEABLE_INTERNAL (FastString.fsLit (GHC.Base.hs_string__
                                               "typeSymbolTypeRep")) typeSymbolTypeRepKey.

Definition trGhcPrimModuleKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #47.

Definition trGhcPrimModuleName : Name.Name :=
  varQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "tr$ModuleGHCPrim"))
  trGhcPrimModuleKey.

Definition starKindRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #520.

Definition starKindRepName : Name.Name :=
  varQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "krep$*"))
  starKindRepKey.

Definition starArrStarKindRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #521.

Definition starArrStarKindRepName : Name.Name :=
  varQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "krep$*Arr*"))
  starArrStarKindRepKey.

Definition starArrStarArrStarKindRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #522.

Definition starArrStarArrStarKindRepName : Name.Name :=
  varQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "krep$*->*->*"))
  starArrStarArrStarKindRepKey.

Definition errorMessageTypeErrorFamKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #176.

Definition errorMessageTypeErrorFamName : Name.Name :=
  tcQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ "TypeError"))
  errorMessageTypeErrorFamKey.

Definition typeErrorTextDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #50.

Definition typeErrorTextDataConName : Name.Name :=
  dcQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ "Text"))
  typeErrorTextDataConKey.

Definition typeErrorAppendDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #51.

Definition typeErrorAppendDataConName : Name.Name :=
  dcQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ ":<>:"))
  typeErrorAppendDataConKey.

Definition typeErrorVAppendDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #52.

Definition typeErrorVAppendDataConName : Name.Name :=
  dcQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ ":$$:"))
  typeErrorVAppendDataConKey.

Definition typeErrorShowTypeDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #53.

Definition typeErrorShowTypeDataConName : Name.Name :=
  dcQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ "ShowType"))
  typeErrorShowTypeDataConKey.

Definition toDynIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #550.

Definition toDynName : Name.Name :=
  varQual dYNAMIC (FastString.fsLit (GHC.Base.hs_string__ "toDyn")) toDynIdKey.

Definition dataClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #9.

Definition dataClassName : Name.Name :=
  clsQual gENERICS (FastString.fsLit (GHC.Base.hs_string__ "Data")) dataClassKey.

Definition assertErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #105.

Definition assertErrorName : Name.Name :=
  varQual gHC_IO_Exception (FastString.fsLit (GHC.Base.hs_string__ "assertError"))
  assertErrorIdKey.

Definition traceKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #108.

Definition traceName : Name.Name :=
  varQual dEBUG_TRACE (FastString.fsLit (GHC.Base.hs_string__ "trace")) traceKey.

Definition boundedClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #1.

Definition boundedClassName : Name.Name :=
  clsQual gHC_ENUM (FastString.fsLit (GHC.Base.hs_string__ "Bounded"))
  boundedClassKey.

Definition concatIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #31.

Definition concatName : Name.Name :=
  varQual gHC_LIST (FastString.fsLit (GHC.Base.hs_string__ "concat")) concatIdKey.

Definition filterIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #32.

Definition filterName : Name.Name :=
  varQual gHC_LIST (FastString.fsLit (GHC.Base.hs_string__ "filter")) filterIdKey.

Definition zipIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #33.

Definition zipName : Name.Name :=
  varQual gHC_LIST (FastString.fsLit (GHC.Base.hs_string__ "zip")) zipIdKey.

Definition isListClassKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #198.

Definition isListClassName : Name.Name :=
  clsQual gHC_EXTS (FastString.fsLit (GHC.Base.hs_string__ "IsList"))
  isListClassKey.

Definition showClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #17.

Definition showClassName : Name.Name :=
  clsQual gHC_SHOW (FastString.fsLit (GHC.Base.hs_string__ "Show")) showClassKey.

Definition readClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #13.

Definition readClassName : Name.Name :=
  clsQual gHC_READ (FastString.fsLit (GHC.Base.hs_string__ "Read")) readClassKey.

Definition genClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #37.

Definition genClassName : Name.Name :=
  clsQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Generic"))
  genClassKey.

Definition gen1ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #38.

Definition gen1ClassName : Name.Name :=
  clsQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Generic1"))
  gen1ClassKey.

Definition datatypeClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #39.

Definition datatypeClassName : Name.Name :=
  clsQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Datatype"))
  datatypeClassKey.

Definition constructorClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #40.

Definition constructorClassName : Name.Name :=
  clsQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Constructor"))
  constructorClassKey.

Definition selectorClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #41.

Definition selectorClassName : Name.Name :=
  clsQual gHC_GENERICS (FastString.fsLit (GHC.Base.hs_string__ "Selector"))
  selectorClassKey.

Definition genericClassNames : list Name.Name :=
  cons genClassName (cons gen1ClassName nil).

Definition ghciIoClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #44.

Definition ghciIoClassName : Name.Name :=
  clsQual gHC_GHCI (FastString.fsLit (GHC.Base.hs_string__ "GHCiSandboxIO"))
  ghciIoClassKey.

Definition ghciStepIoMClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #197.

Definition ghciStepIoMName : Name.Name :=
  varQual gHC_GHCI (FastString.fsLit (GHC.Base.hs_string__ "ghciStepIO"))
  ghciStepIoMClassOpKey.

Definition ioTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #57.

Definition ioTyConName : Name.Name :=
  tcQual gHC_TYPES (FastString.fsLit (GHC.Base.hs_string__ "IO")) ioTyConKey.

Definition thenIOIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #103.

Definition thenIOName : Name.Name :=
  varQual gHC_BASE (FastString.fsLit (GHC.Base.hs_string__ "thenIO")) thenIOIdKey.

Definition failIOIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #38.

Definition failIOName : Name.Name :=
  varQual gHC_IO (FastString.fsLit (GHC.Base.hs_string__ "failIO")) failIOIdKey.

Definition printIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #37.

Definition printName : Name.Name :=
  varQual sYSTEM_IO (FastString.fsLit (GHC.Base.hs_string__ "print")) printIdKey.

Definition int8TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #16.

Definition int8TyConName : Name.Name :=
  tcQual gHC_INT (FastString.fsLit (GHC.Base.hs_string__ "Int8")) int8TyConKey.

Definition int16TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #17.

Definition int16TyConName : Name.Name :=
  tcQual gHC_INT (FastString.fsLit (GHC.Base.hs_string__ "Int16")) int16TyConKey.

Definition int32TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #19.

Definition int32TyConName : Name.Name :=
  tcQual gHC_INT (FastString.fsLit (GHC.Base.hs_string__ "Int32")) int32TyConKey.

Definition int64TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #21.

Definition int64TyConName : Name.Name :=
  tcQual gHC_INT (FastString.fsLit (GHC.Base.hs_string__ "Int64")) int64TyConKey.

Definition word16TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #62.

Definition word16TyConName : Name.Name :=
  tcQual gHC_WORD (FastString.fsLit (GHC.Base.hs_string__ "Word16"))
  word16TyConKey.

Definition word32TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #64.

Definition word32TyConName : Name.Name :=
  tcQual gHC_WORD (FastString.fsLit (GHC.Base.hs_string__ "Word32"))
  word32TyConKey.

Definition word64TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #66.

Definition word64TyConName : Name.Name :=
  tcQual gHC_WORD (FastString.fsLit (GHC.Base.hs_string__ "Word64"))
  word64TyConKey.

Definition ptrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #75.

Definition ptrTyConName : Name.Name :=
  tcQual gHC_PTR (FastString.fsLit (GHC.Base.hs_string__ "Ptr")) ptrTyConKey.

Definition funPtrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #76.

Definition funPtrTyConName : Name.Name :=
  tcQual gHC_PTR (FastString.fsLit (GHC.Base.hs_string__ "FunPtr"))
  funPtrTyConKey.

Definition stablePtrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #36.

Definition stablePtrTyConName : Name.Name :=
  tcQual gHC_STABLE (FastString.fsLit (GHC.Base.hs_string__ "StablePtr"))
  stablePtrTyConKey.

Definition monadFixClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #28.

Definition monadFixClassName : Name.Name :=
  clsQual mONAD_FIX (FastString.fsLit (GHC.Base.hs_string__ "MonadFix"))
  monadFixClassKey.

Definition mfixIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #175.

Definition mfixName : Name.Name :=
  varQual mONAD_FIX (FastString.fsLit (GHC.Base.hs_string__ "mfix")) mfixIdKey.

Definition arrAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #180.

Definition arrAName : Name.Name :=
  varQual aRROW (FastString.fsLit (GHC.Base.hs_string__ "arr")) arrAIdKey.

Definition composeAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #181.

Definition composeAName : Name.Name :=
  varQual gHC_DESUGAR (FastString.fsLit (GHC.Base.hs_string__ ">>>"))
  composeAIdKey.

Definition firstAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #182.

Definition firstAName : Name.Name :=
  varQual aRROW (FastString.fsLit (GHC.Base.hs_string__ "first")) firstAIdKey.

Definition appAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #183.

Definition appAName : Name.Name :=
  varQual aRROW (FastString.fsLit (GHC.Base.hs_string__ "app")) appAIdKey.

Definition choiceAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #184.

Definition choiceAName : Name.Name :=
  varQual aRROW (FastString.fsLit (GHC.Base.hs_string__ "|||")) choiceAIdKey.

Definition loopAIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #185.

Definition loopAName : Name.Name :=
  varQual aRROW (FastString.fsLit (GHC.Base.hs_string__ "loop")) loopAIdKey.

Definition guardMIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #194.

Definition guardMName : Name.Name :=
  varQual mONAD (FastString.fsLit (GHC.Base.hs_string__ "guard")) guardMIdKey.

Definition liftMIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #195.

Definition liftMName : Name.Name :=
  varQual mONAD (FastString.fsLit (GHC.Base.hs_string__ "liftM")) liftMIdKey.

Definition mzipIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #196.

Definition mzipName : Name.Name :=
  varQual mONAD_ZIP (FastString.fsLit (GHC.Base.hs_string__ "mzip")) mzipIdKey.

Definition toAnnotationWrapperIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #187.

Definition toAnnotationWrapperName : Name.Name :=
  varQual gHC_DESUGAR (FastString.fsLit (GHC.Base.hs_string__
                                         "toAnnotationWrapper")) toAnnotationWrapperIdKey.

Definition monadPlusClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #30.

Definition monadPlusClassName : Name.Name :=
  clsQual mONAD (FastString.fsLit (GHC.Base.hs_string__ "MonadPlus"))
  monadPlusClassKey.

Definition randomClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #31.

Definition randomClassName : Name.Name :=
  clsQual rANDOM (FastString.fsLit (GHC.Base.hs_string__ "Random"))
  randomClassKey.

Definition randomGenClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #32.

Definition randomGenClassName : Name.Name :=
  clsQual rANDOM (FastString.fsLit (GHC.Base.hs_string__ "RandomGen"))
  randomGenClassKey.

Definition isStringClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #33.

Definition isStringClassName : Name.Name :=
  clsQual dATA_STRING (FastString.fsLit (GHC.Base.hs_string__ "IsString"))
  isStringClassKey.

Definition knownNatClassNameKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #42.

Definition knownNatClassName : Name.Name :=
  clsQual gHC_TYPENATS (FastString.fsLit (GHC.Base.hs_string__ "KnownNat"))
  knownNatClassNameKey.

Definition knownSymbolClassNameKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #43.

Definition knownSymbolClassName : Name.Name :=
  clsQual gHC_TYPELITS (FastString.fsLit (GHC.Base.hs_string__ "KnownSymbol"))
  knownSymbolClassNameKey.

Definition isLabelClassNameKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #45.

Definition isLabelClassName : Name.Name :=
  clsQual gHC_OVER_LABELS (FastString.fsLit (GHC.Base.hs_string__ "IsLabel"))
  isLabelClassNameKey.

Definition ipClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #48.

Definition ipClassName : Name.Name :=
  clsQual gHC_CLASSES (FastString.fsLit (GHC.Base.hs_string__ "IP")) ipClassKey.

Definition hasFieldClassNameKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #49.

Definition hasFieldClassName : Name.Name :=
  clsQual gHC_RECORDS (FastString.fsLit (GHC.Base.hs_string__ "HasField"))
  hasFieldClassNameKey.

Definition callStackTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #186.

Definition callStackTyConName : Name.Name :=
  tcQual gHC_STACK_TYPES (FastString.fsLit (GHC.Base.hs_string__ "CallStack"))
  callStackTyConKey.

Definition emptyCallStackKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #558.

Definition emptyCallStackName : Name.Name :=
  varQual gHC_STACK_TYPES (FastString.fsLit (GHC.Base.hs_string__
                                             "emptyCallStack")) emptyCallStackKey.

Definition pushCallStackKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #559.

Definition pushCallStackName : Name.Name :=
  varQual gHC_STACK_TYPES (FastString.fsLit (GHC.Base.hs_string__
                                             "pushCallStack")) pushCallStackKey.

Definition srcLocDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #37.

Definition srcLocDataConName : Name.Name :=
  dcQual gHC_STACK_TYPES (FastString.fsLit (GHC.Base.hs_string__ "SrcLoc"))
  srcLocDataConKey.

Definition pLUGINS : Module.Module :=
  mkThisGhcModule (FastString.fsLit (GHC.Base.hs_string__ "Plugins")).

Definition pluginTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #102.

Definition pluginTyConName : Name.Name :=
  tcQual pLUGINS (FastString.fsLit (GHC.Base.hs_string__ "Plugin"))
  pluginTyConKey.

Definition frontendPluginTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #103.

Definition frontendPluginTyConName : Name.Name :=
  tcQual pLUGINS (FastString.fsLit (GHC.Base.hs_string__ "FrontendPlugin"))
  frontendPluginTyConKey.

Definition makeStaticKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #561.

Definition makeStaticName : Name.Name :=
  varQual gHC_STATICPTR_INTERNAL (FastString.fsLit (GHC.Base.hs_string__
                                                    "makeStatic")) makeStaticKey.

Definition staticPtrInfoTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #185.

Definition staticPtrInfoTyConName : Name.Name :=
  tcQual gHC_STATICPTR (FastString.fsLit (GHC.Base.hs_string__ "StaticPtrInfo"))
  staticPtrInfoTyConKey.

Definition staticPtrInfoDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #34.

Definition staticPtrInfoDataConName : Name.Name :=
  dcQual gHC_STATICPTR (FastString.fsLit (GHC.Base.hs_string__ "StaticPtrInfo"))
  staticPtrInfoDataConKey.

Definition staticPtrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #184.

Definition staticPtrTyConName : Name.Name :=
  tcQual gHC_STATICPTR (FastString.fsLit (GHC.Base.hs_string__ "StaticPtr"))
  staticPtrTyConKey.

Definition staticPtrDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #33.

Definition staticPtrDataConName : Name.Name :=
  dcQual gHC_STATICPTR (FastString.fsLit (GHC.Base.hs_string__ "StaticPtr"))
  staticPtrDataConKey.

Definition fromStaticPtrClassOpKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #560.

Definition fromStaticPtrName : Name.Name :=
  varQual gHC_STATICPTR (FastString.fsLit (GHC.Base.hs_string__ "fromStaticPtr"))
  fromStaticPtrClassOpKey.

Definition fingerprintDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #35.

Definition fingerprintDataConName : Name.Name :=
  dcQual gHC_FINGERPRINT_TYPE (FastString.fsLit (GHC.Base.hs_string__
                                                 "Fingerprint")) fingerprintDataConKey.

Definition eqTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #38.

Definition eqTyConName : Name.Name :=
  tcQual dATA_TYPE_EQUALITY (FastString.fsLit (GHC.Base.hs_string__ "~"))
  eqTyConKey.

Definition typeable1ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #21.

Definition typeable2ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #22.

Definition typeable3ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #23.

Definition typeable4ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #24.

Definition typeable5ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #25.

Definition typeable6ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #26.

Definition typeable7ClassKey : Unique.Unique :=
  Unique.mkPreludeClassUnique #27.

Definition addrPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #1.

Definition arrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #3.

Definition boolTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #4.

Definition byteArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #5.

Definition charPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #7.

Definition charTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #8.

Definition doublePrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #9.

Definition doubleTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #10.

Definition floatPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #11.

Definition floatTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #12.

Definition funTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #13.

Definition intPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #14.

Definition intTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #15.

Definition int32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #18.

Definition int64PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #20.

Definition listTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #24.

Definition foreignObjPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #25.

Definition maybeTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #26.

Definition weakPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #27.

Definition mutableArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #28.

Definition mutableByteArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #29.

Definition mVarPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #31.

Definition realWorldTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #34.

Definition stablePtrPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #35.

Definition heqTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #39.

Definition arrayArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #40.

Definition mutableArrayArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #41.

Definition statePrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #50.

Definition stableNamePrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #51.

Definition stableNameTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #52.

Definition eqPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #53.

Definition eqReprPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #54.

Definition eqPhantPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #55.

Definition mutVarPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #56.

Definition voidPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #58.

Definition wordPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #59.

Definition wordTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #60.

Definition word8TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #61.

Definition word32PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #63.

Definition word64PrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #65.

Definition liftedConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #67.

Definition unliftedConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #68.

Definition anyBoxConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #69.

Definition kindConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #70.

Definition boxityConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #71.

Definition typeConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #72.

Definition threadIdPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #73.

Definition bcoPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #74.

Definition tVarPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #77.

Definition compactPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #78.

Definition parrTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #82.

Definition objectTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #83.

Definition liftedTypeKindTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #87.

Definition tYPETyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #88.

Definition constraintKindTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #92.

Definition starKindTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #93.

Definition unicodeStarKindTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #94.

Definition runtimeRepTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #95.

Definition vecCountTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #96.

Definition vecElemTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #97.

Definition unknownTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #129.

Definition unknown1TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #130.

Definition unknown2TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #131.

Definition unknown3TyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #132.

Definition typeNatKindConNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #164.

Definition typeSymbolKindConNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #165.

Definition typeNatAddTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #166.

Definition typeNatMulTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #167.

Definition typeNatExpTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #168.

Definition typeNatLeqTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #169.

Definition typeNatSubTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #170.

Definition typeSymbolCmpTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #171.

Definition typeNatCmpTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #172.

Definition typeNatDivTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #173.

Definition typeNatModTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #174.

Definition typeNatLogTyFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #175.

Definition ntTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #177.

Definition coercibleTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #178.

Definition proxyPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #179.

Definition anyTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #181.

Definition smallArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #182.

Definition smallMutableArrayPrimTyConKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #183.

Definition typeSymbolAppendFamNameKey : Unique.Unique :=
  Unique.mkPreludeTyConUnique #190.

Definition charDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #1.

Definition consDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #2.

Definition doubleDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #3.

Definition falseDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #4.

Definition floatDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #5.

Definition intDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #6.

Definition integerSDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #7.

Definition nothingDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #8.

Definition justDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #9.

Definition nilDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #11.

Definition word8DataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #13.

Definition stableNameDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #14.

Definition trueDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #15.

Definition wordDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #16.

Definition integerDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #18.

Definition heqDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #19.

Definition crossDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #20.

Definition inlDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #21.

Definition inrDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #22.

Definition genUnitDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #23.

Definition parrDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #24.

Definition coercibleDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #32.

Definition vecRepDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #71.

Definition tupleRepDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #72.

Definition sumRepDataConKey : Unique.Unique :=
  Unique.mkPreludeDataConUnique #73.

Definition vecCountDataConKeys : list Unique.Unique :=
  GHC.Base.map Unique.mkPreludeDataConUnique (GHC.Enum.enumFromTo #83 #88).

Definition vecElemDataConKeys : list Unique.Unique :=
  GHC.Base.map Unique.mkPreludeDataConUnique (GHC.Enum.enumFromTo #89 #98).

Definition absentErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #1.

Definition errorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #5.

Definition recSelErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #7.

Definition seqIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #8.

Definition irrefutPatErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #9.

Definition noMethodBindingErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #11.

Definition nonExhaustiveGuardsErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #12.

Definition runtimeErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #13.

Definition patErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #14.

Definition realWorldPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #15.

Definition recConErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #16.

Definition unpackCStringAppendIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #18.

Definition voidPrimIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #21.

Definition typeErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #22.

Definition absentSumFieldErrorIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #25.

Definition unsafeCoerceIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #30.

Definition nullAddrIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #39.

Definition voidArgIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #40.

Definition rootMainKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #101.

Definition lazyIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #104.

Definition oneShotKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #106.

Definition runRWKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #107.

Definition dollarIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #123.

Definition coercionTokenIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #124.

Definition noinlineIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #125.

Definition unmarshalObjectIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #150.

Definition marshalObjectIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #151.

Definition marshalStringIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #152.

Definition unmarshalStringIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #153.

Definition checkDotnetResNameIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #154.

Definition undefinedKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #155.

Definition magicDictKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #156.

Definition coerceKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #157.

Definition proxyHashKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #502.

Definition mkTyConKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #503.

Definition trTYPEKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #511.

Definition trTYPE'PtrRepLiftedKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #512.

Definition trRuntimeRepKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #513.

Definition tr'PtrRepLiftedKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #514.

Definition heqSCSelIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #552.

Definition coercibleSCSelIdKey : Unique.Unique :=
  Unique.mkPreludeMiscIdUnique #553.

Definition fractionalClassKeys : list Unique.Unique :=
  cons fractionalClassKey (cons floatingClassKey (cons realFracClassKey (cons
                                                        realFloatClassKey nil))).

Definition numericClassKeys : list Unique.Unique :=
  Coq.Init.Datatypes.app (cons numClassKey (cons realClassKey (cons
                                                  integralClassKey nil))) fractionalClassKeys.

Definition derivableClassKeys : list Unique.Unique :=
  cons eqClassKey (cons ordClassKey (cons enumClassKey (cons ixClassKey (cons
                                                              boundedClassKey (cons showClassKey (cons readClassKey
                                                                                                       nil)))))).

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

Definition interactiveClassNames : list Name.Name :=
  cons showClassName (cons eqClassName (cons ordClassName (cons foldableClassName
                                                                (cons traversableClassName nil)))).

Definition interactiveClassKeys : list Unique.Unique :=
  GHC.Base.map Unique.getUnique interactiveClassNames.

Axiom pretendNameIsInScope : Name.Name -> bool.

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
