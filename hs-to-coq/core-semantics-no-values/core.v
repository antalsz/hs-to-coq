(* Preamble *)
Definition Synonym {A : Type} (_uniq : Type) (x : A) : A := x.
Arguments Synonym {A}%type _uniq%type x%type.

Require Import ZArith.

Axiom Char     : Type.
Axiom Int      : Type.
Axiom Rational : Type.

Definition String     := list Char.
Definition FilePath   := String.
Definition FastString := String.

(* Temporary *)
Record Array  k v := ListToArray  { arrayToList  : list (k * v) }.
Record Map    k v := ListToMap    { mapToList    : list (k * v) }.
Record IntMap   v := ListToIntMap { intMapToList : list (Int * v) }.

Axiom error : forall {A : Type}, String -> A.

(* I've been assured that this is OK *)
Inductive IORef (a : Type) : Type :=.

(* List notation *)
Require Import Coq.Lists.List.

(* Temporary – but will probably need to be handled specially *)
Axiom DynFlags : Type.

(* Temporary – this probably needs to map directly to a Coq type *)
Axiom ByteString : Type.

Generalizable All Variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(********************************************************************************)

(* Haskell Prelude stuff *)

Class Functor (f : Type -> Type) := {
  fmap : forall {a b}, (a -> b) -> f a -> f b;
  __op_zlzd__ : forall {a b}, a -> f b -> f a
}.

Infix "<$"        := __op_zlzd__ (at level 99).
Notation "'_<$_'" := __op_zlzd__.

Class Applicative (f : Type -> Type) `{Functor f} := {
  pure          : forall {a},   a -> f a;
  __op_zlztzg__ : forall {a b}, f (a -> b) -> f a -> f b;
  __op_ztzg__   : forall {a b}, f a -> f b -> f b;
  __op_zlzt__   : forall {a b}, f a -> f b -> f a
}.

Infix "<*>" := __op_zlztzg__ (at level 99).
Infix "*>"  := __op_ztzg__   (at level 99).
Infix "<*"  := __op_zlzt__   (at level 99).

Notation "'_<*>_'" := __op_zlztzg__.
Notation "'_*>_'"  := __op_ztzg__.
Notation "'_<*_'"  := __op_zlzt__.

Class Monad (m : Type -> Type) `{Applicative m} := {
  __op_zgzgze__ : forall {a b}, m a -> (a -> m b) -> m b;
  __op_zgzg__   : forall {a b}, m a -> m b -> m b;
  return_       : forall {a},   a -> m a;
  fail          : forall {a},   String -> m a
}.

Infix ">>=" := __op_zgzgze__ (at level 99).
Infix ">>"  := __op_zgzg__   (at level 99).

Notation "'_>>=_'" := __op_zgzgze__.
Notation "'_>>_'"  := __op_zgzg__.

Class Num a := {
  __op_zp__   : a -> a -> a ;
  __op_zm__   : a -> a -> a ;
  __op_zt__   : a -> a -> a ;
  abs         : a -> a ;
  fromInteger : Z -> a ;
  negate      : a -> a ;
  signum      : a -> a
}.

Infix    "+"     := __op_zp__ (at level 50, left associativity).
Notation "'_+_'" := __op_zp__.

Infix    "-"     := __op_zm__ (at level 50, left associativity).
Notation "'_-_'" := __op_zm__.

Infix    "*"     := __op_zt__ (at level 40, left associativity).
Notation "'_*_'" := __op_zt__.

(* Fancy notation *)

Notation "'#' n" := (fromInteger n) (at level 1, format "'#' n").

Require Coq.Strings.String.
Require Coq.Strings.Ascii.

Bind Scope string_scope with String.string.
Bind Scope char_scope   with Ascii.ascii.

Axiom __hs_char__ : Ascii.ascii -> Char.
Notation "'&#' c" := (__hs_char__ c) (at level 1, format "'&#' c").

Fixpoint __hs_string__ (s : String.string) : String :=
  match s with
  | String.EmptyString => nil
  | String.String c s  => &#c :: __hs_string__ s
  end.
Notation "'&' s" := (__hs_string__ s) (at level 1, format "'&' s").

(* Converted data type declarations: *)
Inductive Width : Type := Mk_W8 : Width
                       |  Mk_W16 : Width
                       |  Mk_W32 : Width
                       |  Mk_W64 : Width
                       |  Mk_W80 : Width
                       |  Mk_W128 : Width
                       |  Mk_W256 : Width
                       |  Mk_W512 : Width.

Inductive VisibilityFlag : Type := Mk_Visible : VisibilityFlag
                                |  Mk_Specified : VisibilityFlag
                                |  Mk_Invisible : VisibilityFlag.

Definition Version := (Int%type).

Inductive UnitId : Type := Mk_PId : (FastString -> UnitId).

Inductive Unique : Type := Mk_MkUnique : (Int -> Unique).

Class Uniquable a := {
  getUnique : (a -> Unique) }.

Inductive UniqSupply : Type := Mk_MkSplitUniqSupply
                              : (Int -> (UniqSupply -> (UniqSupply -> UniqSupply))).

Inductive UniqSM result : Type := Mk_USM : ((UniqSupply -> (result *
                                           UniqSupply)) -> (UniqSM result)).

Inductive UniqFM ele : Type := Mk_UFM : (((IntMap ele)) -> (UniqFM ele)).

Definition UniqSet a := ((UniqFM a)%type).

Definition VarEnv elt := ((UniqFM elt)%type).

Inductive UnfoldingSource : Type := Mk_InlineRhs : UnfoldingSource
                                 |  Mk_InlineStable : UnfoldingSource
                                 |  Mk_InlineCompulsory : UnfoldingSource.

Inductive TypeShape : Type := Mk_TsFun : (TypeShape -> TypeShape)
                           |  Mk_TsProd : ((list TypeShape) -> TypeShape)
                           |  Mk_TsUnk : TypeShape.

Definition TyVarEnv elt := ((VarEnv elt)%type).

Inductive TyPrec : Type := Mk_TopPrec : TyPrec
                        |  Mk_FunPrec : TyPrec
                        |  Mk_TyOpPrec : TyPrec
                        |  Mk_TyConPrec : TyPrec.

Inductive TyLit : Type := Mk_NumTyLit : (Z -> TyLit)
                       |  Mk_StrTyLit : (FastString -> TyLit).

Definition TyCoVarEnv elt := ((VarEnv elt)%type).

Inductive TupleSort : Type := Mk_BoxedTuple : TupleSort
                           |  Mk_UnboxedTuple : TupleSort
                           |  Mk_ConstraintTuple : TupleSort.

Inductive TopLevelFlag : Type := Mk_TopLevel : TopLevelFlag
                              |  Mk_NotTopLevel : TopLevelFlag.

Definition TidyOccEnv := ((UniqFM Int)%type).

Inductive TickishScoping : Type := Mk_NoScope : TickishScoping
                                |  Mk_SoftScope : TickishScoping
                                |  Mk_CostCentreScope : TickishScoping.

Inductive TickishPlacement : Type := Mk_PlaceRuntime : TickishPlacement
                                  |  Mk_PlaceNonLam : TickishPlacement
                                  |  Mk_PlaceCostCentre : TickishPlacement.

Definition TickBoxId := (Int%type).

Inductive Termination r : Type := Mk_Diverges : (Termination r)
                               |  Mk_ThrowsExn : (Termination r)
                               |  Mk_Dunno : (r -> (Termination r)).

Inductive TcLevel : Type := Mk_TcLevel : (Int -> TcLevel).

Inductive TauTvFlavour : Type := Mk_VanillaTau : TauTvFlavour
                              |  Mk_WildcardTau : TauTvFlavour.

Inductive TaggedVal val : Type := Mk_TaggedVal : (val -> (Int -> (TaggedVal
                                                 val))).

Inductive UniqDFM ele : Type := Mk_UDFM : (((IntMap ((TaggedVal
                                                    ele)))) -> (Int -> (UniqDFM ele))).

Definition UniqDSet a := ((UniqDFM a)%type).

Inductive SwapFlag : Type := Mk_NotSwapped : SwapFlag
                          |  Mk_IsSwapped : SwapFlag.

Inductive SuccessFlag : Type := Mk_Succeeded : SuccessFlag
                             |  Mk_Failed : SuccessFlag.

Inductive StrictnessMark : Type := Mk_MarkedStrict : StrictnessMark
                                |  Mk_NotMarkedStrict : StrictnessMark.

Inductive SrcUnpackedness : Type := Mk_SrcUnpack : SrcUnpackedness
                                 |  Mk_SrcNoUnpack : SrcUnpackedness
                                 |  Mk_NoSrcUnpack : SrcUnpackedness.

Inductive SrcStrictness : Type := Mk_SrcLazy : SrcStrictness
                               |  Mk_SrcStrict : SrcStrictness
                               |  Mk_NoSrcStrict : SrcStrictness.

Definition SourceText := (String%type).

Inductive StringLiteral : Type := Mk_StringLiteral
                                 : (SourceText -> (FastString -> StringLiteral)).

Inductive Safety : Type := Mk_PlaySafe : Safety
                        |  Mk_PlayInterruptible : Safety
                        |  Mk_PlayRisky : Safety.

Definition RulesOnly := (bool%type).

Definition RuleName := (FastString%type).

Inductive RuleMatchInfo : Type := Mk_ConLike : RuleMatchInfo
                               |  Mk_FunLike : RuleMatchInfo.

Inductive Role : Type := Mk_Nominal : Role
                      |  Mk_Representational : Role
                      |  Mk_Phantom : Role.

Definition RepArity := (Int%type).

Inductive RecFlag : Type := Mk_Recursive : RecFlag
                         |  Mk_NonRecursive : RecFlag.

Inductive RealSrcSpan : Type := Mk_RealSrcSpan'
                               : (FastString -> (Int -> (Int -> (Int -> (Int -> RealSrcSpan))))).

Inductive SrcSpan : Type := Mk_RealSrcSpan : (RealSrcSpan -> SrcSpan)
                         |  Mk_UnhelpfulSpan : (FastString -> SrcSpan).

Inductive RealSrcLoc : Type := Mk_SrcLoc
                              : (FastString -> (Int -> (Int -> RealSrcLoc))).

Inductive SrcLoc : Type := Mk_RealSrcLoc : (RealSrcLoc -> SrcLoc)
                        |  Mk_UnhelpfulLoc : (FastString -> SrcLoc).

Inductive PrimOpVecCat : Type := Mk_IntVec : PrimOpVecCat
                              |  Mk_WordVec : PrimOpVecCat
                              |  Mk_FloatVec : PrimOpVecCat.

Inductive PrimElemRep : Type := Mk_Int8ElemRep : PrimElemRep
                             |  Mk_Int16ElemRep : PrimElemRep
                             |  Mk_Int32ElemRep : PrimElemRep
                             |  Mk_Int64ElemRep : PrimElemRep
                             |  Mk_Word8ElemRep : PrimElemRep
                             |  Mk_Word16ElemRep : PrimElemRep
                             |  Mk_Word32ElemRep : PrimElemRep
                             |  Mk_Word64ElemRep : PrimElemRep
                             |  Mk_FloatElemRep : PrimElemRep
                             |  Mk_DoubleElemRep : PrimElemRep.

Inductive PrimRep : Type := Mk_VoidRep : PrimRep
                         |  Mk_PtrRep : PrimRep
                         |  Mk_IntRep : PrimRep
                         |  Mk_WordRep : PrimRep
                         |  Mk_Int64Rep : PrimRep
                         |  Mk_Word64Rep : PrimRep
                         |  Mk_AddrRep : PrimRep
                         |  Mk_FloatRep : PrimRep
                         |  Mk_DoubleRep : PrimRep
                         |  Mk_VecRep : (Int -> (PrimElemRep -> PrimRep)).

Definition PhaseNum := (Int%type).

Inductive Pair a : Type := Mk_Pair : (a -> (a -> (Pair a))).

Inductive OverlapMode : Type := Mk_NoOverlap : (SourceText -> OverlapMode)
                             |  Mk_Overlappable : (SourceText -> OverlapMode)
                             |  Mk_Overlapping : (SourceText -> OverlapMode)
                             |  Mk_Overlaps : (SourceText -> OverlapMode)
                             |  Mk_Incoherent : (SourceText -> OverlapMode).

Inductive OverlapFlag : Type := Mk_OverlapFlag
                               : (OverlapMode -> (bool -> OverlapFlag)).

Inductive Origin : Type := Mk_FromSource : Origin
                        |  Mk_Generated : Origin.

Inductive OneShotInfo : Type := Mk_NoOneShotInfo : OneShotInfo
                             |  Mk_ProbOneShot : OneShotInfo
                             |  Mk_OneShotLam : OneShotInfo.

Definition OneBranch := (bool%type).

Inductive OccEnv a : Type := Mk_A : (((UniqFM a)) -> (OccEnv a)).

Inductive OccCheckResult a : Type := Mk_OC_OK : (a -> (OccCheckResult a))
                                  |  Mk_OC_Forall : (OccCheckResult a)
                                  |  Mk_OC_NonTyVar : (OccCheckResult a)
                                  |  Mk_OC_Occurs : (OccCheckResult a).

Inductive NameSpace : Type := Mk_VarName : NameSpace
                           |  Mk_DataName : NameSpace
                           |  Mk_TvName : NameSpace
                           |  Mk_TcClsName : NameSpace.

Inductive OccName : Type := Mk_OccName : (NameSpace -> (FastString -> OccName)).

Definition OccSet := ((UniqSet OccName)%type).

Definition NameEnv a := ((UniqFM a)%type).

Inductive RecTcChecker : Type := Mk_RC : (Int -> (((NameEnv
                                         Int)) -> RecTcChecker)).

Class MonadUnique m `{(Monad m)} := {
  getUniqueM : (m Unique) ;
  getUniqueSupplyM : (m UniqSupply) ;
  getUniquesM : (m (list Unique)) }.

Definition ModuleNameEnv elt := ((UniqFM elt)%type).

Inductive ModuleName : Type := Mk_ModuleName : (FastString -> ModuleName).

Inductive Module : Type := Mk_Module : (UnitId -> (ModuleName -> Module)).

Inductive ModuleEnv elt : Type := Mk_ModuleEnv : ((((Map Module)
                                                 elt)) -> (ModuleEnv elt)).

Definition ModuleSet := (((Map Module) unit)%type).

Inductive TickBoxOp : Type := Mk_TickBox : (Module -> (TickBoxId -> TickBoxOp)).

Inductive ModLocation : Type := Mk_ModLocation : ((option
                                                 FilePath) -> (FilePath -> (FilePath -> ModLocation))).

Inductive MetaInfo : Type := Mk_TauTv : MetaInfo
                          |  Mk_SigTv : MetaInfo
                          |  Mk_FlatMetaTv : MetaInfo.

Definition Length := (Int%type).

Inductive PrimOp : Type := Mk_CharGtOp : PrimOp
                        |  Mk_CharGeOp : PrimOp
                        |  Mk_CharEqOp : PrimOp
                        |  Mk_CharNeOp : PrimOp
                        |  Mk_CharLtOp : PrimOp
                        |  Mk_CharLeOp : PrimOp
                        |  Mk_OrdOp : PrimOp
                        |  Mk_IntAddOp : PrimOp
                        |  Mk_IntSubOp : PrimOp
                        |  Mk_IntMulOp : PrimOp
                        |  Mk_IntMulMayOfloOp : PrimOp
                        |  Mk_IntQuotOp : PrimOp
                        |  Mk_IntRemOp : PrimOp
                        |  Mk_IntQuotRemOp : PrimOp
                        |  Mk_AndIOp : PrimOp
                        |  Mk_OrIOp : PrimOp
                        |  Mk_XorIOp : PrimOp
                        |  Mk_NotIOp : PrimOp
                        |  Mk_IntNegOp : PrimOp
                        |  Mk_IntAddCOp : PrimOp
                        |  Mk_IntSubCOp : PrimOp
                        |  Mk_IntGtOp : PrimOp
                        |  Mk_IntGeOp : PrimOp
                        |  Mk_IntEqOp : PrimOp
                        |  Mk_IntNeOp : PrimOp
                        |  Mk_IntLtOp : PrimOp
                        |  Mk_IntLeOp : PrimOp
                        |  Mk_ChrOp : PrimOp
                        |  Mk_Int2WordOp : PrimOp
                        |  Mk_Int2FloatOp : PrimOp
                        |  Mk_Int2DoubleOp : PrimOp
                        |  Mk_Word2FloatOp : PrimOp
                        |  Mk_Word2DoubleOp : PrimOp
                        |  Mk_ISllOp : PrimOp
                        |  Mk_ISraOp : PrimOp
                        |  Mk_ISrlOp : PrimOp
                        |  Mk_WordAddOp : PrimOp
                        |  Mk_WordSubCOp : PrimOp
                        |  Mk_WordAdd2Op : PrimOp
                        |  Mk_WordSubOp : PrimOp
                        |  Mk_WordMulOp : PrimOp
                        |  Mk_WordMul2Op : PrimOp
                        |  Mk_WordQuotOp : PrimOp
                        |  Mk_WordRemOp : PrimOp
                        |  Mk_WordQuotRemOp : PrimOp
                        |  Mk_WordQuotRem2Op : PrimOp
                        |  Mk_AndOp : PrimOp
                        |  Mk_OrOp : PrimOp
                        |  Mk_XorOp : PrimOp
                        |  Mk_NotOp : PrimOp
                        |  Mk_SllOp : PrimOp
                        |  Mk_SrlOp : PrimOp
                        |  Mk_Word2IntOp : PrimOp
                        |  Mk_WordGtOp : PrimOp
                        |  Mk_WordGeOp : PrimOp
                        |  Mk_WordEqOp : PrimOp
                        |  Mk_WordNeOp : PrimOp
                        |  Mk_WordLtOp : PrimOp
                        |  Mk_WordLeOp : PrimOp
                        |  Mk_PopCnt8Op : PrimOp
                        |  Mk_PopCnt16Op : PrimOp
                        |  Mk_PopCnt32Op : PrimOp
                        |  Mk_PopCnt64Op : PrimOp
                        |  Mk_PopCntOp : PrimOp
                        |  Mk_Clz8Op : PrimOp
                        |  Mk_Clz16Op : PrimOp
                        |  Mk_Clz32Op : PrimOp
                        |  Mk_Clz64Op : PrimOp
                        |  Mk_ClzOp : PrimOp
                        |  Mk_Ctz8Op : PrimOp
                        |  Mk_Ctz16Op : PrimOp
                        |  Mk_Ctz32Op : PrimOp
                        |  Mk_Ctz64Op : PrimOp
                        |  Mk_CtzOp : PrimOp
                        |  Mk_BSwap16Op : PrimOp
                        |  Mk_BSwap32Op : PrimOp
                        |  Mk_BSwap64Op : PrimOp
                        |  Mk_BSwapOp : PrimOp
                        |  Mk_Narrow8IntOp : PrimOp
                        |  Mk_Narrow16IntOp : PrimOp
                        |  Mk_Narrow32IntOp : PrimOp
                        |  Mk_Narrow8WordOp : PrimOp
                        |  Mk_Narrow16WordOp : PrimOp
                        |  Mk_Narrow32WordOp : PrimOp
                        |  Mk_DoubleGtOp : PrimOp
                        |  Mk_DoubleGeOp : PrimOp
                        |  Mk_DoubleEqOp : PrimOp
                        |  Mk_DoubleNeOp : PrimOp
                        |  Mk_DoubleLtOp : PrimOp
                        |  Mk_DoubleLeOp : PrimOp
                        |  Mk_DoubleAddOp : PrimOp
                        |  Mk_DoubleSubOp : PrimOp
                        |  Mk_DoubleMulOp : PrimOp
                        |  Mk_DoubleDivOp : PrimOp
                        |  Mk_DoubleNegOp : PrimOp
                        |  Mk_Double2IntOp : PrimOp
                        |  Mk_Double2FloatOp : PrimOp
                        |  Mk_DoubleExpOp : PrimOp
                        |  Mk_DoubleLogOp : PrimOp
                        |  Mk_DoubleSqrtOp : PrimOp
                        |  Mk_DoubleSinOp : PrimOp
                        |  Mk_DoubleCosOp : PrimOp
                        |  Mk_DoubleTanOp : PrimOp
                        |  Mk_DoubleAsinOp : PrimOp
                        |  Mk_DoubleAcosOp : PrimOp
                        |  Mk_DoubleAtanOp : PrimOp
                        |  Mk_DoubleSinhOp : PrimOp
                        |  Mk_DoubleCoshOp : PrimOp
                        |  Mk_DoubleTanhOp : PrimOp
                        |  Mk_DoublePowerOp : PrimOp
                        |  Mk_DoubleDecode_2IntOp : PrimOp
                        |  Mk_DoubleDecode_Int64Op : PrimOp
                        |  Mk_FloatGtOp : PrimOp
                        |  Mk_FloatGeOp : PrimOp
                        |  Mk_FloatEqOp : PrimOp
                        |  Mk_FloatNeOp : PrimOp
                        |  Mk_FloatLtOp : PrimOp
                        |  Mk_FloatLeOp : PrimOp
                        |  Mk_FloatAddOp : PrimOp
                        |  Mk_FloatSubOp : PrimOp
                        |  Mk_FloatMulOp : PrimOp
                        |  Mk_FloatDivOp : PrimOp
                        |  Mk_FloatNegOp : PrimOp
                        |  Mk_Float2IntOp : PrimOp
                        |  Mk_FloatExpOp : PrimOp
                        |  Mk_FloatLogOp : PrimOp
                        |  Mk_FloatSqrtOp : PrimOp
                        |  Mk_FloatSinOp : PrimOp
                        |  Mk_FloatCosOp : PrimOp
                        |  Mk_FloatTanOp : PrimOp
                        |  Mk_FloatAsinOp : PrimOp
                        |  Mk_FloatAcosOp : PrimOp
                        |  Mk_FloatAtanOp : PrimOp
                        |  Mk_FloatSinhOp : PrimOp
                        |  Mk_FloatCoshOp : PrimOp
                        |  Mk_FloatTanhOp : PrimOp
                        |  Mk_FloatPowerOp : PrimOp
                        |  Mk_Float2DoubleOp : PrimOp
                        |  Mk_FloatDecode_IntOp : PrimOp
                        |  Mk_NewArrayOp : PrimOp
                        |  Mk_SameMutableArrayOp : PrimOp
                        |  Mk_ReadArrayOp : PrimOp
                        |  Mk_WriteArrayOp : PrimOp
                        |  Mk_SizeofArrayOp : PrimOp
                        |  Mk_SizeofMutableArrayOp : PrimOp
                        |  Mk_IndexArrayOp : PrimOp
                        |  Mk_UnsafeFreezeArrayOp : PrimOp
                        |  Mk_UnsafeThawArrayOp : PrimOp
                        |  Mk_CopyArrayOp : PrimOp
                        |  Mk_CopyMutableArrayOp : PrimOp
                        |  Mk_CloneArrayOp : PrimOp
                        |  Mk_CloneMutableArrayOp : PrimOp
                        |  Mk_FreezeArrayOp : PrimOp
                        |  Mk_ThawArrayOp : PrimOp
                        |  Mk_CasArrayOp : PrimOp
                        |  Mk_NewSmallArrayOp : PrimOp
                        |  Mk_SameSmallMutableArrayOp : PrimOp
                        |  Mk_ReadSmallArrayOp : PrimOp
                        |  Mk_WriteSmallArrayOp : PrimOp
                        |  Mk_SizeofSmallArrayOp : PrimOp
                        |  Mk_SizeofSmallMutableArrayOp : PrimOp
                        |  Mk_IndexSmallArrayOp : PrimOp
                        |  Mk_UnsafeFreezeSmallArrayOp : PrimOp
                        |  Mk_UnsafeThawSmallArrayOp : PrimOp
                        |  Mk_CopySmallArrayOp : PrimOp
                        |  Mk_CopySmallMutableArrayOp : PrimOp
                        |  Mk_CloneSmallArrayOp : PrimOp
                        |  Mk_CloneSmallMutableArrayOp : PrimOp
                        |  Mk_FreezeSmallArrayOp : PrimOp
                        |  Mk_ThawSmallArrayOp : PrimOp
                        |  Mk_CasSmallArrayOp : PrimOp
                        |  Mk_NewByteArrayOp_Char : PrimOp
                        |  Mk_NewPinnedByteArrayOp_Char : PrimOp
                        |  Mk_NewAlignedPinnedByteArrayOp_Char : PrimOp
                        |  Mk_ByteArrayContents_Char : PrimOp
                        |  Mk_SameMutableByteArrayOp : PrimOp
                        |  Mk_ShrinkMutableByteArrayOp_Char : PrimOp
                        |  Mk_ResizeMutableByteArrayOp_Char : PrimOp
                        |  Mk_UnsafeFreezeByteArrayOp : PrimOp
                        |  Mk_SizeofByteArrayOp : PrimOp
                        |  Mk_SizeofMutableByteArrayOp : PrimOp
                        |  Mk_GetSizeofMutableByteArrayOp : PrimOp
                        |  Mk_IndexByteArrayOp_Char : PrimOp
                        |  Mk_IndexByteArrayOp_WideChar : PrimOp
                        |  Mk_IndexByteArrayOp_Int : PrimOp
                        |  Mk_IndexByteArrayOp_Word : PrimOp
                        |  Mk_IndexByteArrayOp_Addr : PrimOp
                        |  Mk_IndexByteArrayOp_Float : PrimOp
                        |  Mk_IndexByteArrayOp_Double : PrimOp
                        |  Mk_IndexByteArrayOp_StablePtr : PrimOp
                        |  Mk_IndexByteArrayOp_Int8 : PrimOp
                        |  Mk_IndexByteArrayOp_Int16 : PrimOp
                        |  Mk_IndexByteArrayOp_Int32 : PrimOp
                        |  Mk_IndexByteArrayOp_Int64 : PrimOp
                        |  Mk_IndexByteArrayOp_Word8 : PrimOp
                        |  Mk_IndexByteArrayOp_Word16 : PrimOp
                        |  Mk_IndexByteArrayOp_Word32 : PrimOp
                        |  Mk_IndexByteArrayOp_Word64 : PrimOp
                        |  Mk_ReadByteArrayOp_Char : PrimOp
                        |  Mk_ReadByteArrayOp_WideChar : PrimOp
                        |  Mk_ReadByteArrayOp_Int : PrimOp
                        |  Mk_ReadByteArrayOp_Word : PrimOp
                        |  Mk_ReadByteArrayOp_Addr : PrimOp
                        |  Mk_ReadByteArrayOp_Float : PrimOp
                        |  Mk_ReadByteArrayOp_Double : PrimOp
                        |  Mk_ReadByteArrayOp_StablePtr : PrimOp
                        |  Mk_ReadByteArrayOp_Int8 : PrimOp
                        |  Mk_ReadByteArrayOp_Int16 : PrimOp
                        |  Mk_ReadByteArrayOp_Int32 : PrimOp
                        |  Mk_ReadByteArrayOp_Int64 : PrimOp
                        |  Mk_ReadByteArrayOp_Word8 : PrimOp
                        |  Mk_ReadByteArrayOp_Word16 : PrimOp
                        |  Mk_ReadByteArrayOp_Word32 : PrimOp
                        |  Mk_ReadByteArrayOp_Word64 : PrimOp
                        |  Mk_WriteByteArrayOp_Char : PrimOp
                        |  Mk_WriteByteArrayOp_WideChar : PrimOp
                        |  Mk_WriteByteArrayOp_Int : PrimOp
                        |  Mk_WriteByteArrayOp_Word : PrimOp
                        |  Mk_WriteByteArrayOp_Addr : PrimOp
                        |  Mk_WriteByteArrayOp_Float : PrimOp
                        |  Mk_WriteByteArrayOp_Double : PrimOp
                        |  Mk_WriteByteArrayOp_StablePtr : PrimOp
                        |  Mk_WriteByteArrayOp_Int8 : PrimOp
                        |  Mk_WriteByteArrayOp_Int16 : PrimOp
                        |  Mk_WriteByteArrayOp_Int32 : PrimOp
                        |  Mk_WriteByteArrayOp_Int64 : PrimOp
                        |  Mk_WriteByteArrayOp_Word8 : PrimOp
                        |  Mk_WriteByteArrayOp_Word16 : PrimOp
                        |  Mk_WriteByteArrayOp_Word32 : PrimOp
                        |  Mk_WriteByteArrayOp_Word64 : PrimOp
                        |  Mk_CopyByteArrayOp : PrimOp
                        |  Mk_CopyMutableByteArrayOp : PrimOp
                        |  Mk_CopyByteArrayToAddrOp : PrimOp
                        |  Mk_CopyMutableByteArrayToAddrOp : PrimOp
                        |  Mk_CopyAddrToByteArrayOp : PrimOp
                        |  Mk_SetByteArrayOp : PrimOp
                        |  Mk_AtomicReadByteArrayOp_Int : PrimOp
                        |  Mk_AtomicWriteByteArrayOp_Int : PrimOp
                        |  Mk_CasByteArrayOp_Int : PrimOp
                        |  Mk_FetchAddByteArrayOp_Int : PrimOp
                        |  Mk_FetchSubByteArrayOp_Int : PrimOp
                        |  Mk_FetchAndByteArrayOp_Int : PrimOp
                        |  Mk_FetchNandByteArrayOp_Int : PrimOp
                        |  Mk_FetchOrByteArrayOp_Int : PrimOp
                        |  Mk_FetchXorByteArrayOp_Int : PrimOp
                        |  Mk_NewArrayArrayOp : PrimOp
                        |  Mk_SameMutableArrayArrayOp : PrimOp
                        |  Mk_UnsafeFreezeArrayArrayOp : PrimOp
                        |  Mk_SizeofArrayArrayOp : PrimOp
                        |  Mk_SizeofMutableArrayArrayOp : PrimOp
                        |  Mk_IndexArrayArrayOp_ByteArray : PrimOp
                        |  Mk_IndexArrayArrayOp_ArrayArray : PrimOp
                        |  Mk_ReadArrayArrayOp_ByteArray : PrimOp
                        |  Mk_ReadArrayArrayOp_MutableByteArray : PrimOp
                        |  Mk_ReadArrayArrayOp_ArrayArray : PrimOp
                        |  Mk_ReadArrayArrayOp_MutableArrayArray : PrimOp
                        |  Mk_WriteArrayArrayOp_ByteArray : PrimOp
                        |  Mk_WriteArrayArrayOp_MutableByteArray : PrimOp
                        |  Mk_WriteArrayArrayOp_ArrayArray : PrimOp
                        |  Mk_WriteArrayArrayOp_MutableArrayArray : PrimOp
                        |  Mk_CopyArrayArrayOp : PrimOp
                        |  Mk_CopyMutableArrayArrayOp : PrimOp
                        |  Mk_AddrAddOp : PrimOp
                        |  Mk_AddrSubOp : PrimOp
                        |  Mk_AddrRemOp : PrimOp
                        |  Mk_Addr2IntOp : PrimOp
                        |  Mk_Int2AddrOp : PrimOp
                        |  Mk_AddrGtOp : PrimOp
                        |  Mk_AddrGeOp : PrimOp
                        |  Mk_AddrEqOp : PrimOp
                        |  Mk_AddrNeOp : PrimOp
                        |  Mk_AddrLtOp : PrimOp
                        |  Mk_AddrLeOp : PrimOp
                        |  Mk_IndexOffAddrOp_Char : PrimOp
                        |  Mk_IndexOffAddrOp_WideChar : PrimOp
                        |  Mk_IndexOffAddrOp_Int : PrimOp
                        |  Mk_IndexOffAddrOp_Word : PrimOp
                        |  Mk_IndexOffAddrOp_Addr : PrimOp
                        |  Mk_IndexOffAddrOp_Float : PrimOp
                        |  Mk_IndexOffAddrOp_Double : PrimOp
                        |  Mk_IndexOffAddrOp_StablePtr : PrimOp
                        |  Mk_IndexOffAddrOp_Int8 : PrimOp
                        |  Mk_IndexOffAddrOp_Int16 : PrimOp
                        |  Mk_IndexOffAddrOp_Int32 : PrimOp
                        |  Mk_IndexOffAddrOp_Int64 : PrimOp
                        |  Mk_IndexOffAddrOp_Word8 : PrimOp
                        |  Mk_IndexOffAddrOp_Word16 : PrimOp
                        |  Mk_IndexOffAddrOp_Word32 : PrimOp
                        |  Mk_IndexOffAddrOp_Word64 : PrimOp
                        |  Mk_ReadOffAddrOp_Char : PrimOp
                        |  Mk_ReadOffAddrOp_WideChar : PrimOp
                        |  Mk_ReadOffAddrOp_Int : PrimOp
                        |  Mk_ReadOffAddrOp_Word : PrimOp
                        |  Mk_ReadOffAddrOp_Addr : PrimOp
                        |  Mk_ReadOffAddrOp_Float : PrimOp
                        |  Mk_ReadOffAddrOp_Double : PrimOp
                        |  Mk_ReadOffAddrOp_StablePtr : PrimOp
                        |  Mk_ReadOffAddrOp_Int8 : PrimOp
                        |  Mk_ReadOffAddrOp_Int16 : PrimOp
                        |  Mk_ReadOffAddrOp_Int32 : PrimOp
                        |  Mk_ReadOffAddrOp_Int64 : PrimOp
                        |  Mk_ReadOffAddrOp_Word8 : PrimOp
                        |  Mk_ReadOffAddrOp_Word16 : PrimOp
                        |  Mk_ReadOffAddrOp_Word32 : PrimOp
                        |  Mk_ReadOffAddrOp_Word64 : PrimOp
                        |  Mk_WriteOffAddrOp_Char : PrimOp
                        |  Mk_WriteOffAddrOp_WideChar : PrimOp
                        |  Mk_WriteOffAddrOp_Int : PrimOp
                        |  Mk_WriteOffAddrOp_Word : PrimOp
                        |  Mk_WriteOffAddrOp_Addr : PrimOp
                        |  Mk_WriteOffAddrOp_Float : PrimOp
                        |  Mk_WriteOffAddrOp_Double : PrimOp
                        |  Mk_WriteOffAddrOp_StablePtr : PrimOp
                        |  Mk_WriteOffAddrOp_Int8 : PrimOp
                        |  Mk_WriteOffAddrOp_Int16 : PrimOp
                        |  Mk_WriteOffAddrOp_Int32 : PrimOp
                        |  Mk_WriteOffAddrOp_Int64 : PrimOp
                        |  Mk_WriteOffAddrOp_Word8 : PrimOp
                        |  Mk_WriteOffAddrOp_Word16 : PrimOp
                        |  Mk_WriteOffAddrOp_Word32 : PrimOp
                        |  Mk_WriteOffAddrOp_Word64 : PrimOp
                        |  Mk_NewMutVarOp : PrimOp
                        |  Mk_ReadMutVarOp : PrimOp
                        |  Mk_WriteMutVarOp : PrimOp
                        |  Mk_SameMutVarOp : PrimOp
                        |  Mk_AtomicModifyMutVarOp : PrimOp
                        |  Mk_CasMutVarOp : PrimOp
                        |  Mk_CatchOp : PrimOp
                        |  Mk_RaiseOp : PrimOp
                        |  Mk_RaiseIOOp : PrimOp
                        |  Mk_MaskAsyncExceptionsOp : PrimOp
                        |  Mk_MaskUninterruptibleOp : PrimOp
                        |  Mk_UnmaskAsyncExceptionsOp : PrimOp
                        |  Mk_MaskStatus : PrimOp
                        |  Mk_AtomicallyOp : PrimOp
                        |  Mk_RetryOp : PrimOp
                        |  Mk_CatchRetryOp : PrimOp
                        |  Mk_CatchSTMOp : PrimOp
                        |  Mk_CheckOp : PrimOp
                        |  Mk_NewTVarOp : PrimOp
                        |  Mk_ReadTVarOp : PrimOp
                        |  Mk_ReadTVarIOOp : PrimOp
                        |  Mk_WriteTVarOp : PrimOp
                        |  Mk_SameTVarOp : PrimOp
                        |  Mk_NewMVarOp : PrimOp
                        |  Mk_TakeMVarOp : PrimOp
                        |  Mk_TryTakeMVarOp : PrimOp
                        |  Mk_PutMVarOp : PrimOp
                        |  Mk_TryPutMVarOp : PrimOp
                        |  Mk_ReadMVarOp : PrimOp
                        |  Mk_TryReadMVarOp : PrimOp
                        |  Mk_SameMVarOp : PrimOp
                        |  Mk_IsEmptyMVarOp : PrimOp
                        |  Mk_DelayOp : PrimOp
                        |  Mk_WaitReadOp : PrimOp
                        |  Mk_WaitWriteOp : PrimOp
                        |  Mk_ForkOp : PrimOp
                        |  Mk_ForkOnOp : PrimOp
                        |  Mk_KillThreadOp : PrimOp
                        |  Mk_YieldOp : PrimOp
                        |  Mk_MyThreadIdOp : PrimOp
                        |  Mk_LabelThreadOp : PrimOp
                        |  Mk_IsCurrentThreadBoundOp : PrimOp
                        |  Mk_NoDuplicateOp : PrimOp
                        |  Mk_ThreadStatusOp : PrimOp
                        |  Mk_MkWeakOp : PrimOp
                        |  Mk_MkWeakNoFinalizerOp : PrimOp
                        |  Mk_AddCFinalizerToWeakOp : PrimOp
                        |  Mk_DeRefWeakOp : PrimOp
                        |  Mk_FinalizeWeakOp : PrimOp
                        |  Mk_TouchOp : PrimOp
                        |  Mk_MakeStablePtrOp : PrimOp
                        |  Mk_DeRefStablePtrOp : PrimOp
                        |  Mk_EqStablePtrOp : PrimOp
                        |  Mk_MakeStableNameOp : PrimOp
                        |  Mk_EqStableNameOp : PrimOp
                        |  Mk_StableNameToIntOp : PrimOp
                        |  Mk_ReallyUnsafePtrEqualityOp : PrimOp
                        |  Mk_ParOp : PrimOp
                        |  Mk_SparkOp : PrimOp
                        |  Mk_SeqOp : PrimOp
                        |  Mk_GetSparkOp : PrimOp
                        |  Mk_NumSparks : PrimOp
                        |  Mk_DataToTagOp : PrimOp
                        |  Mk_TagToEnumOp : PrimOp
                        |  Mk_AddrToAnyOp : PrimOp
                        |  Mk_MkApUpd0_Op : PrimOp
                        |  Mk_NewBCOOp : PrimOp
                        |  Mk_UnpackClosureOp : PrimOp
                        |  Mk_GetApStackValOp : PrimOp
                        |  Mk_GetCCSOfOp : PrimOp
                        |  Mk_GetCurrentCCSOp : PrimOp
                        |  Mk_TraceEventOp : PrimOp
                        |  Mk_TraceMarkerOp : PrimOp
                        |  Mk_VecBroadcastOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecPackOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecUnpackOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecInsertOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecAddOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecSubOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecMulOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecDivOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecQuotOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecRemOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecNegOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecIndexByteArrayOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecReadByteArrayOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecWriteByteArrayOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecIndexOffAddrOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecReadOffAddrOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecWriteOffAddrOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecIndexScalarByteArrayOp
                          : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecReadScalarByteArrayOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecWriteScalarByteArrayOp
                          : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecIndexScalarOffAddrOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecReadScalarOffAddrOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_VecWriteScalarOffAddrOp : (PrimOpVecCat -> (Length -> (Width -> PrimOp)))
                        |  Mk_PrefetchByteArrayOp3 : PrimOp
                        |  Mk_PrefetchMutableByteArrayOp3 : PrimOp
                        |  Mk_PrefetchAddrOp3 : PrimOp
                        |  Mk_PrefetchValueOp3 : PrimOp
                        |  Mk_PrefetchByteArrayOp2 : PrimOp
                        |  Mk_PrefetchMutableByteArrayOp2 : PrimOp
                        |  Mk_PrefetchAddrOp2 : PrimOp
                        |  Mk_PrefetchValueOp2 : PrimOp
                        |  Mk_PrefetchByteArrayOp1 : PrimOp
                        |  Mk_PrefetchMutableByteArrayOp1 : PrimOp
                        |  Mk_PrefetchAddrOp1 : PrimOp
                        |  Mk_PrefetchValueOp1 : PrimOp
                        |  Mk_PrefetchByteArrayOp0 : PrimOp
                        |  Mk_PrefetchMutableByteArrayOp0 : PrimOp
                        |  Mk_PrefetchAddrOp0 : PrimOp
                        |  Mk_PrefetchValueOp0 : PrimOp.

Inductive LeftOrRight : Type := Mk_CLeft : LeftOrRight
                             |  Mk_CRight : LeftOrRight.

Definition KillFlags := ((bool * bool)%type).

Inductive JointDmd s u : Type := Mk_JD : (s -> (u -> (JointDmd s u))).

Inductive IsOrphan : Type := Mk_IsOrphan : IsOrphan
                          |  Mk_NotOrphan : (OccName -> IsOrphan).

Inductive IsCafCC : Type := Mk_NotCafCC : IsCafCC
                         |  Mk_CafCC : IsCafCC.

Definition InterestingCxt := (bool%type).

Inductive IntWithInf : Type := Mk_Int : (Int -> IntWithInf)
                            |  Mk_Infinity : IntWithInf.

Definition TypeSize := (IntWithInf%type).

Definition InsideLam := (bool%type).

Inductive OccInfo : Type := Mk_NoOccInfo : OccInfo
                         |  Mk_IAmDead : OccInfo
                         |  Mk_OneOcc : (InsideLam -> (OneBranch -> (InterestingCxt -> OccInfo)))
                         |  Mk_IAmALoopBreaker : (RulesOnly -> OccInfo).

Inductive InlineSpec : Type := Mk_Inline : InlineSpec
                            |  Mk_Inlinable : InlineSpec
                            |  Mk_NoInline : InlineSpec
                            |  Mk_EmptyInlineSpec : InlineSpec.

Inductive Injectivity : Type := Mk_NotInjective : Injectivity
                             |  Mk_Injective : ((list bool) -> Injectivity).

Inductive IdInfo : Type :=.

Definition IdEnv elt := ((VarEnv elt)%type).

Inductive HsSrcBang : Type := Mk_HsSrcBang : (((option
                                             SourceText)) -> (SrcUnpackedness -> (SrcStrictness -> HsSrcBang))).

Inductive Header : Type := Mk_Header : (SourceText -> (FastString -> Header)).

Class HasOccName name := {
  occName : (name -> OccName) }.

Class HasModule m := {
  getModule : (m Module) }.

Inductive GenLocated l e : Type := Mk_L : (l -> (e -> (GenLocated l e))).

Definition Located e := (((GenLocated SrcSpan) e)%type).

Inductive WarningTxt : Type := Mk_WarningTxt : (((Located SourceText)) -> ((list
                                               (Located StringLiteral)) -> WarningTxt))
                            |  Mk_DeprecatedTxt : (((Located SourceText)) -> ((list (Located
                                                                                    StringLiteral)) -> WarningTxt)).

Definition RealLocated e := (((GenLocated RealSrcSpan) e)%type).

Inductive FunctionOrData : Type := Mk_IsFunction : FunctionOrData
                                |  Mk_IsData : FunctionOrData.

Definition FunDep a : Type := (((list a) * (list a))%type).

Inductive FractionalLit : Type := Mk_FL
                                 : (String -> (Rational -> FractionalLit)).

Inductive ForeignHint : Type := Mk_NoHint : ForeignHint
                             |  Mk_AddrHint : ForeignHint
                             |  Mk_SignedHint : ForeignHint.

Inductive FixityDirection : Type := Mk_InfixL : FixityDirection
                                 |  Mk_InfixR : FixityDirection
                                 |  Mk_InfixN : FixityDirection.

Inductive Fixity : Type := Mk_Fixity
                          : (SourceText -> (Int -> (FixityDirection -> Fixity))).

Definition FieldLabelString := (FastString%type).

Inductive FieldLbl a : Type := Mk_FieldLabel
                              : (FieldLabelString -> (bool -> (a -> (FieldLbl a)))).

Definition FastStringEnv a := ((UniqFM a)%type).

Inductive ExportFlag : Type := Mk_NotExported : ExportFlag
                            |  Mk_Exported : ExportFlag.

Inductive IdScope : Type := Mk_GlobalId : IdScope
                         |  Mk_LocalId : (ExportFlag -> IdScope).

Inductive ExnStr : Type := Mk_VanStr : ExnStr
                        |  Mk_ExnStr : ExnStr.

Inductive Str s : Type := Mk_Lazy : (Str s)
                       |  Mk_Str : (ExnStr -> (s -> (Str s))).

Inductive EqRel : Type := Mk_NomEq : EqRel
                       |  Mk_ReprEq : EqRel.

Inductive EP a : Type := Mk_EP : (a -> (a -> (EP a))).

Inductive DefMethSpec ty : Type := Mk_VanillaDM : (DefMethSpec ty)
                                |  Mk_GenericDM : (ty -> (DefMethSpec ty)).

Inductive DataConBoxer : Type :=.

Definition DVarEnv elt := ((UniqDFM elt)%type).

Inductive Count : Type := Mk_One : Count
                       |  Mk_Many : Count.

Inductive Use u : Type := Mk_Abs : (Use u)
                       |  Mk_Use : (Count -> (u -> (Use u))).

Definition DmdShell := (((JointDmd ((Str unit))) ((Use unit)))%type).

Class ContainsModule t := {
  extractModule : (t -> Module) }.

Definition ConTag := (Int%type).

Inductive CompilerPhase : Type := Mk_Phase : (PhaseNum -> CompilerPhase)
                               |  Mk_InitialPhase : CompilerPhase.

Definition CoVarEnv elt := ((VarEnv elt)%type).

Inductive CoAxiomRule : Type :=.

Inductive CmmCat : Type := Mk_GcPtrCat : CmmCat
                        |  Mk_BitsCat : CmmCat
                        |  Mk_FloatCat : CmmCat
                        |  Mk_VecCat : (Length -> (CmmCat -> CmmCat)).

Inductive CmmType : Type := Mk_CmmType : (CmmCat -> (Width -> CmmType)).

Definition CcName := (FastString%type).

Inductive CostCentre : Type := Mk_NormalCC
                              : (Int -> (CcName -> (Module -> (SrcSpan -> (IsCafCC -> CostCentre)))))
                            |  Mk_AllCafsCC : (Module -> (SrcSpan -> CostCentre)).

Inductive CostCentreStack : Type := Mk_NoCCS : CostCentreStack
                                 |  Mk_CurrentCCS : CostCentreStack
                                 |  Mk_DontCareCCS : CostCentreStack
                                 |  Mk_SingletonCCS : (CostCentre -> CostCentreStack).

Definition CollectedCCs : Type := ((((list CostCentre) * (list CostCentre)) *
                                  (list CostCentreStack))%type).

Inductive Tickish id : Type := Mk_ProfNote
                              : (CostCentre -> (bool -> (bool -> (Tickish id))))
                            |  Mk_HpcTick : (Module -> (Int -> (Tickish id)))
                            |  Mk_Breakpoint : (Int -> ((list id) -> (Tickish id)))
                            |  Mk_SourceNote : (RealSrcSpan -> (String -> (Tickish id))).

Inductive CafInfo : Type := Mk_MayHaveCafRefs : CafInfo
                         |  Mk_NoCafRefs : CafInfo.

Inductive CType : Type := Mk_CType : (SourceText -> (((option
                                     Header)) -> ((SourceText * FastString) -> CType))).

Inductive CPRResult : Type := Mk_NoCPR : CPRResult
                           |  Mk_RetProd : CPRResult
                           |  Mk_RetSum : (ConTag -> CPRResult).

Definition DmdResult := ((Termination CPRResult)%type).

Definition CLabelString := (FastString%type).

Inductive PrimCall : Type := Mk_PrimCall
                            : (CLabelString -> (UnitId -> PrimCall)).

Inductive CCallTarget : Type := Mk_StaticTarget
                               : (SourceText -> (CLabelString -> (((option UnitId)) -> (bool -> CCallTarget))))
                             |  Mk_DynamicTarget : CCallTarget.

Inductive CCallConv : Type := Mk_CCallConv : CCallConv
                           |  Mk_CApiConv : CCallConv
                           |  Mk_StdCallConv : CCallConv
                           |  Mk_PrimCallConv : CCallConv
                           |  Mk_JavaScriptCallConv : CCallConv.

Inductive CCallSpec : Type := Mk_CCallSpec
                             : (CCallTarget -> (CCallConv -> (Safety -> CCallSpec))).

Inductive ForeignCall : Type := Mk_CCall : (CCallSpec -> ForeignCall).

Inductive CExportSpec : Type := Mk_CExportStatic
                               : (SourceText -> (CLabelString -> (CCallConv -> CExportSpec))).

Inductive BuiltInSyntax : Type := Mk_BuiltInSyntax : BuiltInSyntax
                               |  Mk_UserSyntax : BuiltInSyntax.

Inductive BuiltInSynFamily : Type :=.

Definition BranchIndex := (Int%type).

Inductive BranchFlag : Type := Mk_Branched : BranchFlag
                            |  Mk_Unbranched : BranchFlag.

Definition Branched := (Mk_Branched%type).

Definition Unbranched := (Mk_Unbranched%type).

Inductive Boxity : Type := Mk_Boxed : Boxity
                        |  Mk_Unboxed : Boxity.

Inductive LBooleanFormula__raw : Type :=.

Reserved Notation "'LBooleanFormula'".

Inductive BooleanFormula a : Type := Mk_BFVar : (a -> (BooleanFormula a))
                                  |  Mk_And : ((list (LBooleanFormula a)) -> (BooleanFormula a))
                                  |  Mk_Or : ((list (LBooleanFormula a)) -> (BooleanFormula a))
                                  |  Mk_Parens : (((LBooleanFormula a)) -> (BooleanFormula a))
where "'LBooleanFormula'" := ((Synonym LBooleanFormula__raw (fun a_ =>
                                         ((Located ((BooleanFormula a_)))%type)))).

Definition Arity := (Int%type).

Definition ArityInfo := (Arity%type).

Inductive UnfoldingGuidance : Type := Mk_UnfWhen
                                     : (Arity -> (bool -> (bool -> UnfoldingGuidance)))
                                   |  Mk_UnfIfGoodArgs : ((list Int) -> (Int -> (Int -> UnfoldingGuidance)))
                                   |  Mk_UnfNever : UnfoldingGuidance.

Inductive ArgUse__raw : Type :=.

Reserved Notation "'ArgUse'".

Inductive UseDmd : Type := Mk_UCall : (Count -> (UseDmd -> UseDmd))
                        |  Mk_UProd : ((list ArgUse) -> UseDmd)
                        |  Mk_UHead : UseDmd
                        |  Mk_Used : UseDmd
where "'ArgUse'" := ((Synonym ArgUse__raw ((Use UseDmd)%type))).

Inductive ArgStr__raw : Type :=.

Reserved Notation "'ArgStr'".

Inductive StrDmd : Type := Mk_HyperStr : StrDmd
                        |  Mk_SCall : (StrDmd -> StrDmd)
                        |  Mk_SProd : ((list ArgStr) -> StrDmd)
                        |  Mk_HeadStr : StrDmd
where "'ArgStr'" := ((Synonym ArgStr__raw ((Str StrDmd)%type))).

Definition Demand := (((JointDmd ArgStr) ArgUse)%type).

Definition DmdEnv := ((VarEnv Demand)%type).

Definition BothDmdArg := ((DmdEnv * (Termination unit))%type).

Inductive DmdType : Type := Mk_DmdType : (DmdEnv -> ((list
                                         Demand) -> (DmdResult -> DmdType))).

Inductive StrictSig : Type := Mk_StrictSig : (DmdType -> StrictSig).

Definition CleanDemand := (((JointDmd StrDmd) UseDmd)%type).

Definition Alignment := (Int%type).

Inductive CoVar__raw : Type :=.

Reserved Notation "'CoVar'".

Inductive Id__raw : Type :=.

Reserved Notation "'Id'".

Inductive CoercionN__raw : Type :=.

Reserved Notation "'CoercionN'".

Inductive KindCoercion__raw : Type :=.

Reserved Notation "'KindCoercion'".

Inductive TyVar__raw : Type :=.

Reserved Notation "'TyVar'".

Inductive KindOrType__raw : Type :=.

Reserved Notation "'KindOrType'".

Inductive FieldLabel__raw : Type :=.

Reserved Notation "'FieldLabel'".

Inductive ThetaType__raw : Type :=.

Reserved Notation "'ThetaType'".

Inductive PredType__raw : Type :=.

Reserved Notation "'PredType'".

Inductive Kind__raw : Type :=.

Reserved Notation "'Kind'".

Inductive TcType__raw : Type :=.

Reserved Notation "'TcType'".

Inductive TyConRepName__raw : Type :=.

Reserved Notation "'TyConRepName'".

Inductive FieldLabelEnv__raw : Type :=.

Reserved Notation "'FieldLabelEnv'".

Inductive ClassMinimalDef__raw : Type :=.

Reserved Notation "'ClassMinimalDef'".

Inductive ClassOpItem__raw : Type :=.

Reserved Notation "'ClassOpItem'".

Inductive DefMethInfo__raw : Type :=.

Reserved Notation "'DefMethInfo'".

Inductive AlgTyConFlav : Type := Mk_VanillaAlgTyCon
                                : (TyConRepName -> AlgTyConFlav)
                              |  Mk_UnboxedAlgTyCon : AlgTyConFlav
                              |  Mk_ClassTyCon : (Class -> (TyConRepName -> AlgTyConFlav))
                              |  Mk_DataFamInstTyCon : (((CoAxiom Unbranched)) -> (TyCon -> ((list
                                                       Type_) -> AlgTyConFlav)))
with Class : Type := Mk_Class : (TyCon -> (Name -> (Unique -> ((list
                                TyVar) -> ((list (FunDep TyVar)) -> ((list PredType) -> ((list Id) -> ((list
                                ClassATItem) -> ((list ClassOpItem) -> (ClassMinimalDef -> Class))))))))))
with ClassATItem : Type := Mk_ATI : (TyCon -> (((option (Type_ *
                                                        SrcSpan))) -> ClassATItem))
with TyCon : Type := Mk_FunTyCon
                    : (Unique -> (Name -> (Kind -> (Arity -> (TyConRepName -> TyCon)))))
                  |  Mk_AlgTyCon : (Unique -> (Name -> (Kind -> (Arity -> ((list TyVar) -> ((list
                                   Role) -> ((option CType) -> (bool -> ((list
                                   PredType) -> (AlgTyConRhs -> (FieldLabelEnv -> (RecFlag -> (AlgTyConFlav -> TyCon)))))))))))))
                  |  Mk_SynonymTyCon : (Unique -> (Name -> (Kind -> (Arity -> ((list
                                       TyVar) -> ((list Role) -> (Type_ -> TyCon)))))))
                  |  Mk_FamilyTyCon : (Unique -> (Name -> (Kind -> (Arity -> ((list
                                      TyVar) -> ((option Name) -> (FamTyConFlav -> ((option
                                      Class) -> (Injectivity -> TyCon)))))))))
                  |  Mk_PrimTyCon : (Unique -> (Name -> (Kind -> (Arity -> ((list
                                    Role) -> (PrimRep -> (bool -> ((option TyConRepName) -> TyCon))))))))
                  |  Mk_PromotedDataCon : (Unique -> (Name -> (Arity -> (Kind -> ((list
                                          Role) -> (DataCon -> (TyConRepName -> TyCon)))))))
                  |  Mk_TcTyCon : (Unique -> (Name -> (bool -> (Arity -> (Kind -> TyCon)))))
with AlgTyConRhs : Type := Mk_AbstractTyCon : (bool -> AlgTyConRhs)
                        |  Mk_DataTyCon : ((list DataCon) -> (bool -> AlgTyConRhs))
                        |  Mk_TupleTyCon : (DataCon -> (TupleSort -> AlgTyConRhs))
                        |  Mk_NewTyCon : (DataCon -> (Type_ -> (((list TyVar) * Type_) -> ((CoAxiom
                                         Unbranched) -> AlgTyConRhs))))
with CoAxiom : (forall br, Type) := Mk_CoAxiom : (forall {br},
                                                   (Unique -> (Name -> (Role -> (TyCon -> ((Branches
                                                   br) -> (bool -> (CoAxiom br))))))))
with Branches : (forall (br : BranchFlag), Type) := Mk_MkBranches : (forall {br
                                                                              : BranchFlag},
                                                                      (((Array BranchIndex) CoAxBranch) -> (Branches
                                                                      br)))
with CoAxBranch : Type := Mk_CoAxBranch : (SrcSpan -> ((list TyVar) -> ((list
                                          CoVar) -> ((list Role) -> ((list Type_) -> (Type_ -> ((list
                                          CoAxBranch) -> CoAxBranch)))))))
with Var : Type := Mk_TyVar : (Name -> (Int -> (Kind -> Var)))
                |  Mk_TcTyVar : (Name -> (Int -> (Kind -> (TcTyVarDetails -> Var))))
                |  Mk_Id
                  : (Name -> (Int -> (Type_ -> (IdScope -> (IdDetails -> (IdInfo -> Var))))))
with IdDetails : Type := Mk_VanillaId : IdDetails
                      |  Mk_RecSelId : (RecSelParent -> (bool -> IdDetails))
                      |  Mk_DataConWorkId : (DataCon -> IdDetails)
                      |  Mk_DataConWrapId : (DataCon -> IdDetails)
                      |  Mk_ClassOpId : (Class -> IdDetails)
                      |  Mk_PrimOpId : (PrimOp -> IdDetails)
                      |  Mk_FCallId : (ForeignCall -> IdDetails)
                      |  Mk_TickBoxOpId : (TickBoxOp -> IdDetails)
                      |  Mk_DFunId : (bool -> IdDetails)
                      |  Mk_CoVarId : IdDetails
with DataCon : Type := Mk_MkData
                      : (Name -> (Unique -> (ConTag -> (bool -> ((list TyVar) -> ((list
                        TyVar) -> ((list EqSpec) -> (ThetaType -> (ThetaType -> ((list
                        Type_) -> (Type_ -> ((list HsSrcBang) -> ((list
                        FieldLabel) -> (Id -> (DataConRep -> (Arity -> (Arity -> (TyCon -> (Type_ -> (bool -> (TyCon -> DataCon)))))))))))))))))))))
with DataConRep : Type := Mk_NoDataConRep : DataConRep
                       |  Mk_DCR : (Id -> (DataConBoxer -> ((list Type_) -> ((list
                                   StrictnessMark) -> ((list HsImplBang) -> DataConRep)))))
with HsImplBang : Type := Mk_HsLazy : HsImplBang
                       |  Mk_HsStrict : HsImplBang
                       |  Mk_HsUnpack : (((option Coercion)) -> HsImplBang)
with Coercion : Type := Mk_Refl : (Role -> (Type_ -> Coercion))
                     |  Mk_TyConAppCo : (Role -> (TyCon -> ((list Coercion) -> Coercion)))
                     |  Mk_AppCo : (Coercion -> (CoercionN -> Coercion))
                     |  Mk_ForAllCo : (TyVar -> (KindCoercion -> (Coercion -> Coercion)))
                     |  Mk_CoVarCo : (CoVar -> Coercion)
                     |  Mk_AxiomInstCo : (((CoAxiom Branched)) -> (BranchIndex -> ((list
                                         Coercion) -> Coercion)))
                     |  Mk_UnivCo : (UnivCoProvenance -> (Role -> (Type_ -> (Type_ -> Coercion))))
                     |  Mk_SymCo : (Coercion -> Coercion)
                     |  Mk_TransCo : (Coercion -> (Coercion -> Coercion))
                     |  Mk_AxiomRuleCo : (CoAxiomRule -> ((list Coercion) -> Coercion))
                     |  Mk_NthCo : (Int -> (Coercion -> Coercion))
                     |  Mk_LRCo : (LeftOrRight -> (CoercionN -> Coercion))
                     |  Mk_InstCo : (Coercion -> (CoercionN -> Coercion))
                     |  Mk_CoherenceCo : (Coercion -> (KindCoercion -> Coercion))
                     |  Mk_KindCo : (Coercion -> Coercion)
                     |  Mk_SubCo : (CoercionN -> Coercion)
with Type_ : Type := Mk_TyVarTy : (Var -> Type_)
                  |  Mk_AppTy : (Type_ -> (Type_ -> Type_))
                  |  Mk_TyConApp : (TyCon -> ((list KindOrType) -> Type_))
                  |  Mk_ForAllTy : (TyBinder -> (Type_ -> Type_))
                  |  Mk_LitTy : (TyLit -> Type_)
                  |  Mk_CastTy : (Type_ -> (KindCoercion -> Type_))
                  |  Mk_CoercionTy : (Coercion -> Type_)
with TyBinder : Type := Mk_Named : (TyVar -> (VisibilityFlag -> TyBinder))
                     |  Mk_Anon : (Type_ -> TyBinder)
with UnivCoProvenance : Type := Mk_UnsafeCoerceProv : UnivCoProvenance
                             |  Mk_PhantomProv : (KindCoercion -> UnivCoProvenance)
                             |  Mk_ProofIrrelProv : (KindCoercion -> UnivCoProvenance)
                             |  Mk_PluginProv : (String -> UnivCoProvenance)
                             |  Mk_HoleProv : (CoercionHole -> UnivCoProvenance)
with CoercionHole : Type := Mk_CoercionHole : (Unique -> ((IORef ((option
                                                                 Coercion))) -> CoercionHole))
with EqSpec : Type := Mk_EqSpec : (TyVar -> (Type_ -> EqSpec))
with Name : Type := Mk_Name
                   : (NameSort -> (OccName -> (Int -> (SrcSpan -> Name))))
with NameSort : Type := Mk_External : (Module -> NameSort)
                     |  Mk_WiredIn : (Module -> (TyThing -> (BuiltInSyntax -> NameSort)))
                     |  Mk_Internal : NameSort
                     |  Mk_System : NameSort
with TyThing : Type := Mk_AnId : (Id -> TyThing)
                    |  Mk_AConLike : (ConLike -> TyThing)
                    |  Mk_ATyCon : (TyCon -> TyThing)
                    |  Mk_ACoAxiom : (((CoAxiom Branched)) -> TyThing)
with ConLike : Type := Mk_RealDataCon : (DataCon -> ConLike)
                    |  Mk_PatSynCon : (PatSyn -> ConLike)
with PatSyn : Type := Mk_MkPatSyn : (Name -> (Unique -> ((list
                                    Type_) -> (Arity -> (bool -> ((list FieldLabel) -> ((list
                                    TyVar) -> (ThetaType -> ((list TyVar) -> (ThetaType -> (Type_ -> ((Id *
                                    bool) -> ((option (Id * bool)) -> PatSyn)))))))))))))
with RecSelParent : Type := Mk_RecSelData : (TyCon -> RecSelParent)
                         |  Mk_RecSelPatSyn : (PatSyn -> RecSelParent)
with TcTyVarDetails : Type := Mk_SkolemTv : (bool -> TcTyVarDetails)
                           |  Mk_FlatSkol : (TcType -> TcTyVarDetails)
                           |  Mk_RuntimeUnk : TcTyVarDetails
                           |  Mk_MetaTv : (MetaInfo -> ((IORef
                                          MetaDetails) -> (TcLevel -> TcTyVarDetails)))
with MetaDetails : Type := Mk_Flexi : MetaDetails
                        |  Mk_Indirect : (TcType -> MetaDetails)
with FamTyConFlav : Type := Mk_DataFamilyTyCon : (TyConRepName -> FamTyConFlav)
                         |  Mk_OpenSynFamilyTyCon : FamTyConFlav
                         |  Mk_ClosedSynFamilyTyCon : (((option ((CoAxiom Branched)))) -> FamTyConFlav)
                         |  Mk_AbstractClosedSynFamilyTyCon : FamTyConFlav
                         |  Mk_BuiltInSynFamTyCon : (BuiltInSynFamily -> FamTyConFlav)
where "'TyVar'" := ((Synonym TyVar__raw (Var%type)))
and   "'TyConRepName'" := ((Synonym TyConRepName__raw (Name%type)))
and   "'TcType'" := ((Synonym TcType__raw (Type_%type)))
and   "'PredType'" := ((Synonym PredType__raw (Type_%type)))
and   "'ThetaType'" := ((Synonym ThetaType__raw ((list PredType)%type)))
and   "'KindOrType'" := ((Synonym KindOrType__raw (Type_%type)))
and   "'Kind'" := ((Synonym Kind__raw (Type_%type)))
and   "'Id'" := ((Synonym Id__raw (Var%type)))
and   "'FieldLabel'" := ((Synonym FieldLabel__raw ((FieldLbl Name)%type)))
and   "'FieldLabelEnv'" := ((Synonym FieldLabelEnv__raw ((FastStringEnv
                                     FieldLabel)%type)))
and   "'DefMethInfo'" := ((Synonym DefMethInfo__raw ((option (Name *
                                                             (DefMethSpec Type_)))%type)))
and   "'CoercionN'" := ((Synonym CoercionN__raw (Coercion%type)))
and   "'KindCoercion'" := ((Synonym KindCoercion__raw (CoercionN%type)))
and   "'CoVar'" := ((Synonym CoVar__raw (Id%type)))
and   "'ClassOpItem'" := ((Synonym ClassOpItem__raw ((Id * DefMethInfo)%type)))
and   "'ClassMinimalDef'" := ((Synonym ClassMinimalDef__raw ((BooleanFormula
                                       Name)%type))).

Inductive PrimOpResultInfo : Type := Mk_ReturnsPrim
                                    : (PrimRep -> PrimOpResultInfo)
                                  |  Mk_ReturnsAlg : (TyCon -> PrimOpResultInfo).

Definition Eqn := ((Pair Type_)%type).

Definition TcKind := (Kind%type).

Inductive Literal : Type := Mk_MachChar : (Char -> Literal)
                         |  Mk_MachStr : (ByteString -> Literal)
                         |  Mk_MachNullAddr : Literal
                         |  Mk_MachInt : (Z -> Literal)
                         |  Mk_MachInt64 : (Z -> Literal)
                         |  Mk_MachWord : (Z -> Literal)
                         |  Mk_MachWord64 : (Z -> Literal)
                         |  Mk_MachFloat : (Rational -> Literal)
                         |  Mk_MachDouble : (Rational -> Literal)
                         |  Mk_MachLabel : (FastString -> (((option
                                           Int)) -> (FunctionOrData -> Literal)))
                         |  Mk_LitInteger : (Z -> (Type_ -> Literal)).

Definition PredWithSCs := ((PredType * (list PredType))%type).

Definition TcPredType := (PredType%type).

Definition TcThetaType := (ThetaType%type).

Inductive ExpType : Type := Mk_Check : (TcType -> ExpType)
                         |  Mk_Infer : (Unique -> (TcLevel -> (Kind -> (((IORef ((option
                                                                                TcType)))) -> ExpType)))).

Definition ExpRhoType := (ExpType%type).

Definition ExpSigmaType := (ExpType%type).

Inductive SyntaxOpType : Type := Mk_SynAny : SyntaxOpType
                              |  Mk_SynRho : SyntaxOpType
                              |  Mk_SynList : SyntaxOpType
                              |  Mk_SynFun : (SyntaxOpType -> (SyntaxOpType -> SyntaxOpType))
                              |  Mk_SynType : (ExpType -> SyntaxOpType).

Definition TcRhoType := (TcType%type).

Definition TcSigmaType := (TcType%type).

Definition TcTauType := (TcType%type).

Definition TvSubstEnv := ((TyVarEnv Type_)%type).

Definition UnaryType := (Type_%type).

Inductive RepType : Type := Mk_UbxTupleRep : ((list UnaryType) -> RepType)
                         |  Mk_UnaryRep : (UnaryType -> RepType).

Definition CoreBndr := (Var%type).

Inductive TaggedBndr t : Type := Mk_TB : (CoreBndr -> (t -> (TaggedBndr t))).

Definition DVarSet := ((UniqDSet Var)%type).

Definition CoVarSet := ((UniqSet CoVar)%type).

Definition TcCoVar := (CoVar%type).

Definition DFunId := (Id%type).

Definition DIdSet := ((UniqDSet Id)%type).

Definition EvId := (Id%type).

Definition DictId := (EvId%type).

Definition EqVar := (EvId%type).

Definition EvVar := (EvId%type).

Definition IpId := (EvId%type).

Definition IdSet := ((UniqSet Id)%type).

Definition TyCoVar := (Id%type).

Definition DTyCoVarSet := ((UniqDSet TyCoVar)%type).

Definition TcDTyCoVarSet := (DTyCoVarSet%type).

Definition TyCoVarSet := ((UniqSet TyCoVar)%type).

Definition TcTyCoVarSet := (TyCoVarSet%type).

Inductive InScopeSet : Type := Mk_InScope : (((VarEnv
                                            Var)) -> (Int -> InScopeSet)).

Definition KindVar := (Var%type).

Inductive RnEnv2 : Type := Mk_RV2 : ((VarEnv Var) -> ((VarEnv
                                    Var) -> (InScopeSet -> RnEnv2))).

Definition TKVar := (Var%type).

Definition TcTyCoVar := (Var%type).

Definition TidyEnv := ((TidyOccEnv * (VarEnv Var))%type).

Definition DTyVarSet := ((UniqDSet TyVar)%type).

Definition TcDTyVarSet := (DTyVarSet%type).

Definition CoercionP := (Coercion%type).

Definition CoercionR := (Coercion%type).

Definition CvSubstEnv := ((CoVarEnv Coercion)%type).

Inductive TCvSubst : Type := Mk_TCvSubst
                            : (InScopeSet -> (TvSubstEnv -> (CvSubstEnv -> TCvSubst))).

Definition LiftCoEnv := ((VarEnv Coercion)%type).

Inductive LiftingContext : Type := Mk_LC
                                  : (TCvSubst -> (LiftCoEnv -> LiftingContext)).

Inductive NormaliseStepResult : Type := Mk_NS_Done : NormaliseStepResult
                                     |  Mk_NS_Abort : NormaliseStepResult
                                     |  Mk_NS_Step : (RecTcChecker -> (Type_ -> (Coercion -> NormaliseStepResult))).

Definition NormaliseStepper := ((RecTcChecker -> (TyCon -> ((list
                               Type_) -> NormaliseStepResult)))%type).

Inductive PredTree : Type := Mk_ClassPred : (Class -> ((list
                                            Type_) -> PredTree))
                          |  Mk_EqPred : (EqRel -> (Type_ -> (Type_ -> PredTree)))
                          |  Mk_IrredPred : (PredType -> PredTree).

Inductive AltCon : Type := Mk_DataAlt : (DataCon -> AltCon)
                        |  Mk_LitAlt : (Literal -> AltCon)
                        |  Mk_DEFAULT : AltCon.

Inductive Alt__raw : Type :=.

Reserved Notation "'Alt'".

Inductive Arg__raw : Type :=.

Reserved Notation "'Arg'".

Inductive Expr b : Type := Mk_Var : (Id -> (Expr b))
                        |  Mk_Lit : (Literal -> (Expr b))
                        |  Mk_App : (((Expr b)) -> (((Arg b)) -> (Expr b)))
                        |  Mk_Lam : (b -> (((Expr b)) -> (Expr b)))
                        |  Mk_Let : (((Bind b)) -> (((Expr b)) -> (Expr b)))
                        |  Mk_Case : (((Expr b)) -> (b -> (Type_ -> ((list (Alt b)) -> (Expr b)))))
                        |  Mk_Cast : (((Expr b)) -> (Coercion -> (Expr b)))
                        |  Mk_Tick : (((Tickish Id)) -> (((Expr b)) -> (Expr b)))
                        |  Mk_Type : (Type_ -> (Expr b))
                        |  Mk_Coercion : (Coercion -> (Expr b))
with Bind b : Type := Mk_NonRec : (b -> (((Expr b)) -> (Bind b)))
                   |  Mk_Rec : ((list (b * ((Expr b)))) -> (Bind b))
where "'Arg'" := ((Synonym Arg__raw (fun b_ => ((Expr b_)%type))))
and   "'Alt'" := ((Synonym Alt__raw (fun b_ =>
                             (((AltCon * (list b_)) * (Expr b_))%type)))).

Definition CoreAlt := ((Alt CoreBndr)%type).

Definition CoreArg := ((Arg CoreBndr)%type).

Definition TaggedArg t := ((Arg ((TaggedBndr t)))%type).

Definition CoreBind := ((Bind CoreBndr)%type).

Definition CoreProgram := ((list CoreBind)%type).

Definition TaggedBind t := ((Bind ((TaggedBndr t)))%type).

Definition CoreExpr := ((Expr CoreBndr)%type).

Inductive Boxer : Type := Mk_UnitBox : Boxer
                       |  Mk_Boxer : (((TCvSubst -> (UniqSM ((list Var) * CoreExpr)))) -> Boxer).

Inductive CoreVect : Type := Mk_Vect : (Id -> (CoreExpr -> CoreVect))
                          |  Mk_NoVect : (Id -> CoreVect)
                          |  Mk_VectType : (bool -> (TyCon -> (((option TyCon)) -> CoreVect)))
                          |  Mk_VectClass : (TyCon -> CoreVect)
                          |  Mk_VectInst : (Id -> CoreVect).

Definition TaggedExpr t := ((Expr ((TaggedBndr t)))%type).

Definition TaggedAlt t := ((Alt ((TaggedBndr t)))%type).

Inductive AnnAlt__raw : Type :=.

Reserved Notation "'AnnAlt'".

Inductive AnnExpr__raw : Type :=.

Reserved Notation "'AnnExpr'".

Inductive AnnExpr' bndr annot : Type := Mk_AnnVar : (Id -> (AnnExpr' bndr
                                                                     annot))
                                     |  Mk_AnnLit : (Literal -> (AnnExpr' bndr annot))
                                     |  Mk_AnnLam : (bndr -> ((((AnnExpr bndr) annot)) -> (AnnExpr' bndr annot)))
                                     |  Mk_AnnApp : ((((AnnExpr bndr) annot)) -> ((((AnnExpr bndr)
                                                    annot)) -> (AnnExpr' bndr annot)))
                                     |  Mk_AnnCase : ((((AnnExpr bndr) annot)) -> (bndr -> (Type_ -> ((list ((AnnAlt
                                                                                                            bndr)
                                                                                                            annot)) -> (AnnExpr'
                                                     bndr annot)))))
                                     |  Mk_AnnLet : ((((AnnBind bndr) annot)) -> ((((AnnExpr bndr)
                                                    annot)) -> (AnnExpr' bndr annot)))
                                     |  Mk_AnnCast : ((((AnnExpr bndr) annot)) -> ((annot * Coercion) -> (AnnExpr'
                                                     bndr annot)))
                                     |  Mk_AnnTick : (((Tickish Id)) -> ((((AnnExpr bndr) annot)) -> (AnnExpr' bndr
                                                                                                               annot)))
                                     |  Mk_AnnType : (Type_ -> (AnnExpr' bndr annot))
                                     |  Mk_AnnCoercion : (Coercion -> (AnnExpr' bndr annot))
with AnnBind bndr annot : Type := Mk_AnnNonRec : (bndr -> ((((AnnExpr bndr)
                                                 annot)) -> (AnnBind bndr annot)))
                               |  Mk_AnnRec : ((list (bndr * ((AnnExpr bndr) annot))) -> (AnnBind bndr annot))
where "'AnnExpr'" := ((Synonym AnnExpr__raw (fun bndr_
                                                 annot_ =>
                                 ((annot_ * ((AnnExpr' bndr_) annot_))%type))))
and   "'AnnAlt'" := ((Synonym AnnAlt__raw (fun bndr_
                                               annot_ =>
                                (((AltCon * (list bndr_)) * ((AnnExpr bndr_) annot_))%type)))).

Class NamedThing a := {
  getName : (a -> Name) ;
  getOccName : (a -> OccName) }.

Inductive UserTypeCtxt : Type := Mk_FunSigCtxt
                                : (Name -> (bool -> UserTypeCtxt))
                              |  Mk_InfSigCtxt : (Name -> UserTypeCtxt)
                              |  Mk_ExprSigCtxt : UserTypeCtxt
                              |  Mk_TypeAppCtxt : UserTypeCtxt
                              |  Mk_ConArgCtxt : (Name -> UserTypeCtxt)
                              |  Mk_TySynCtxt : (Name -> UserTypeCtxt)
                              |  Mk_PatSynCtxt : (Name -> UserTypeCtxt)
                              |  Mk_PatSigCtxt : UserTypeCtxt
                              |  Mk_RuleSigCtxt : (Name -> UserTypeCtxt)
                              |  Mk_ResSigCtxt : UserTypeCtxt
                              |  Mk_ForSigCtxt : (Name -> UserTypeCtxt)
                              |  Mk_DefaultDeclCtxt : UserTypeCtxt
                              |  Mk_InstDeclCtxt : UserTypeCtxt
                              |  Mk_SpecInstCtxt : UserTypeCtxt
                              |  Mk_ThBrackCtxt : UserTypeCtxt
                              |  Mk_GenSigCtxt : UserTypeCtxt
                              |  Mk_GhciCtxt : UserTypeCtxt
                              |  Mk_ClassSCCtxt : (Name -> UserTypeCtxt)
                              |  Mk_SigmaCtxt : UserTypeCtxt
                              |  Mk_DataTyCtxt : (Name -> UserTypeCtxt).

Inductive PrimOpInfo : Type := Mk_Dyadic : (OccName -> (Type_ -> PrimOpInfo))
                            |  Mk_Monadic : (OccName -> (Type_ -> PrimOpInfo))
                            |  Mk_Compare : (OccName -> (Type_ -> PrimOpInfo))
                            |  Mk_GenPrimOp : (OccName -> ((list TyVar) -> ((list
                                              Type_) -> (Type_ -> PrimOpInfo)))).

Definition TcTyVar := (TyVar%type).

Definition TcTyBinder := (TyBinder%type).

Inductive TyCoMapper env m : Type := Mk_TyCoMapper
                                    : ((bool -> ((env -> (TyVar -> (m Type_))) -> ((env -> (CoVar -> (m
                                      Coercion))) -> ((env -> (CoercionHole -> (Role -> (Type_ -> (Type_ -> (m
                                      Coercion)))))) -> ((env -> (TyVar -> (VisibilityFlag -> (m (env *
                                                                                                 TyVar))))) -> (TyCoMapper
                                      env m))))))%type).

Definition TyVarSet := ((UniqSet TyVar)%type).

Definition TcTyVarSet := (TyVarSet%type).

Definition TypeVar := (Var%type).

Definition Unboxer := ((Var -> (UniqSM ((list Var) *
                                       (CoreExpr -> CoreExpr))))%type).

Inductive Unfolding : Type := Mk_NoUnfolding : Unfolding
                           |  Mk_OtherCon : ((list AltCon) -> Unfolding)
                           |  Mk_DFunUnfolding : ((list Var) -> (DataCon -> ((list
                                                 CoreExpr) -> Unfolding)))
                           |  Mk_CoreUnfolding
                             : (CoreExpr -> (UnfoldingSource -> (bool -> (bool -> (bool -> (bool -> (bool -> (UnfoldingGuidance -> Unfolding)))))))).

Definition IdUnfoldingFun := ((Id -> Unfolding)%type).

Definition InScopeEnv := ((InScopeSet * IdUnfoldingFun)%type).

Definition RuleFun := ((DynFlags -> (InScopeEnv -> (Id -> ((list
                      CoreExpr) -> (option CoreExpr)))))%type).

Definition VarSet := ((UniqSet Var)%type).

Inductive Activation : Type := Mk_NeverActive : Activation
                            |  Mk_AlwaysActive : Activation
                            |  Mk_ActiveBefore : (SourceText -> (PhaseNum -> Activation))
                            |  Mk_ActiveAfter : (SourceText -> (PhaseNum -> Activation)).

Inductive CoreRule : Type := Mk_Rule
                            : (RuleName -> (Activation -> (Name -> ((list (option Name)) -> ((list
                              CoreBndr) -> ((list
                              CoreExpr) -> (CoreExpr -> (bool -> (Module -> (IsOrphan -> (bool -> CoreRule)))))))))))
                          |  Mk_BuiltinRule : (RuleName -> (Name -> (Int -> (RuleFun -> CoreRule)))).

Definition RuleBase := ((NameEnv (list CoreRule))%type).

Inductive RuleEnv : Type := Mk_RuleEnv : (RuleBase -> (ModuleSet -> RuleEnv)).

Inductive RuleInfo : Type := Mk_RuleInfo : ((list
                                           CoreRule) -> (DVarSet -> RuleInfo)).

Inductive InlinePragma : Type := Mk_InlinePragma
                                : (SourceText -> (InlineSpec -> ((option
                                  Arity) -> (Activation -> (RuleMatchInfo -> InlinePragma))))).

Definition InlinePragInfo := (InlinePragma%type).

Arguments Mk_Diverges {_}.

Arguments Mk_ThrowsExn {_}.

Arguments Mk_OC_Forall {_}.

Arguments Mk_OC_NonTyVar {_}.

Arguments Mk_OC_Occurs {_}.

Arguments Mk_Lazy {_}.

Arguments Mk_VanillaDM {_}.

Arguments Mk_Abs {_}.

Arguments Mk_ProfNote {_} _ _ _.

Arguments Mk_HpcTick {_} _ _.

Arguments Mk_SourceNote {_} _ _.

Arguments Mk_Var {_} _.

Arguments Mk_Lit {_} _.

Arguments Mk_Type {_} _.

Arguments Mk_Coercion {_} _.

Arguments Mk_AnnVar {_} {_} _.

Arguments Mk_AnnLit {_} {_} _.

Arguments Mk_AnnType {_} {_} _.

Arguments Mk_AnnCoercion {_} {_} _.

Arguments Mk_TyCoMapper {_} {_} _ _ _ _ _.

Definition unUSM {result} (__arg_1__ : (UniqSM result)) := (match __arg_1__ with
                                                             | (Mk_USM unUSM) => unUSM
                                                           end).

Definition sl_fs (__arg_2__ : StringLiteral) := (match __arg_2__ with
                                                  | (Mk_StringLiteral _ sl_fs) => sl_fs
                                                end).

Definition sl_st (__arg_3__ : StringLiteral) := (match __arg_3__ with
                                                  | (Mk_StringLiteral sl_st _) => sl_st
                                                end).

Definition srcSpanECol (__arg_4__ : RealSrcSpan) := (match __arg_4__ with
                                                      | (Mk_RealSrcSpan' _ _ _ _ srcSpanECol) => srcSpanECol
                                                    end).

Definition srcSpanELine (__arg_5__ : RealSrcSpan) := (match __arg_5__ with
                                                       | (Mk_RealSrcSpan' _ _ _ srcSpanELine _) => srcSpanELine
                                                     end).

Definition srcSpanFile (__arg_6__ : RealSrcSpan) := (match __arg_6__ with
                                                      | (Mk_RealSrcSpan' srcSpanFile _ _ _ _) => srcSpanFile
                                                    end).

Definition srcSpanSCol (__arg_7__ : RealSrcSpan) := (match __arg_7__ with
                                                      | (Mk_RealSrcSpan' _ _ srcSpanSCol _ _) => srcSpanSCol
                                                    end).

Definition srcSpanSLine (__arg_8__ : RealSrcSpan) := (match __arg_8__ with
                                                       | (Mk_RealSrcSpan' _ srcSpanSLine _ _ _) => srcSpanSLine
                                                     end).

Definition pFst {a} (__arg_9__ : (Pair a)) := (match __arg_9__ with
                                                | (Mk_Pair pFst _) => pFst
                                              end).

Definition pSnd {a} (__arg_10__ : (Pair a)) := (match __arg_10__ with
                                                 | (Mk_Pair _ pSnd) => pSnd
                                               end).

Definition isSafeOverlap (__arg_11__ : OverlapFlag) := (match __arg_11__ with
                                                         | (Mk_OverlapFlag _ isSafeOverlap) => isSafeOverlap
                                                       end).

Definition overlapMode (__arg_12__ : OverlapFlag) := (match __arg_12__ with
                                                       | (Mk_OverlapFlag overlapMode _) => overlapMode
                                                     end).

Definition occNameFS (__arg_13__ : OccName) := (match __arg_13__ with
                                                 | (Mk_OccName _ occNameFS) => occNameFS
                                               end).

Definition occNameSpace (__arg_14__ : OccName) := (match __arg_14__ with
                                                    | (Mk_OccName occNameSpace _) => occNameSpace
                                                  end).

Definition moduleName (__arg_15__ : Module) := (match __arg_15__ with
                                                 | (Mk_Module _ moduleName) => moduleName
                                               end).

Definition moduleUnitId (__arg_16__ : Module) := (match __arg_16__ with
                                                   | (Mk_Module moduleUnitId _) => moduleUnitId
                                                 end).

Definition ml_hi_file (__arg_17__ : ModLocation) := (match __arg_17__ with
                                                      | (Mk_ModLocation _ ml_hi_file _) => ml_hi_file
                                                    end).

Definition ml_hs_file (__arg_18__ : ModLocation) := (match __arg_18__ with
                                                      | (Mk_ModLocation ml_hs_file _ _) => ml_hs_file
                                                    end).

Definition ml_obj_file (__arg_19__ : ModLocation) := (match __arg_19__ with
                                                       | (Mk_ModLocation _ _ ml_obj_file) => ml_obj_file
                                                     end).

Definition sd {s} {u} (__arg_20__ : (JointDmd s u)) := (match __arg_20__ with
                                                         | (Mk_JD sd _) => sd
                                                       end).

Definition ud {s} {u} (__arg_21__ : (JointDmd s u)) := (match __arg_21__ with
                                                         | (Mk_JD _ ud) => ud
                                                       end).

Definition fl_text (__arg_22__ : FractionalLit) := (match __arg_22__ with
                                                     | (Mk_FL fl_text _) => fl_text
                                                   end).

Definition fl_value (__arg_23__ : FractionalLit) := (match __arg_23__ with
                                                      | (Mk_FL _ fl_value) => fl_value
                                                    end).

Definition flIsOverloaded {a} (__arg_24__ : (FieldLbl a)) :=
  (match __arg_24__ with
    | (Mk_FieldLabel _ flIsOverloaded _) => flIsOverloaded
  end).

Definition flLabel {a} (__arg_25__ : (FieldLbl a)) := (match __arg_25__ with
                                                        | (Mk_FieldLabel flLabel _ _) => flLabel
                                                      end).

Definition flSelector {a} (__arg_26__ : (FieldLbl a)) := (match __arg_26__ with
                                                           | (Mk_FieldLabel _ _ flSelector) => flSelector
                                                         end).

Definition fromEP {a} (__arg_27__ : (EP a)) := (match __arg_27__ with
                                                 | (Mk_EP fromEP _) => fromEP
                                               end).

Definition toEP {a} (__arg_28__ : (EP a)) := (match __arg_28__ with
                                               | (Mk_EP _ toEP) => toEP
                                             end).

Definition cc_is_caf (__arg_29__ : CostCentre) := (match __arg_29__ with
                                                    | (Mk_NormalCC _ _ _ _ cc_is_caf) => cc_is_caf
                                                    | (Mk_AllCafsCC _ _) => (error
                                                                            &"Partial record selector: field `cc_is_caf' has no match in constructor `Mk_AllCafsCC' of type `CostCentre'")
                                                  end).

Definition cc_key (__arg_30__ : CostCentre) := (match __arg_30__ with
                                                 | (Mk_NormalCC cc_key _ _ _ _) => cc_key
                                                 | (Mk_AllCafsCC _ _) => (error
                                                                         &"Partial record selector: field `cc_key' has no match in constructor `Mk_AllCafsCC' of type `CostCentre'")
                                               end).

Definition cc_loc (__arg_31__ : CostCentre) := (match __arg_31__ with
                                                 | (Mk_NormalCC _ _ _ cc_loc _) => cc_loc
                                                 | (Mk_AllCafsCC _ cc_loc) => cc_loc
                                               end).

Definition cc_mod (__arg_32__ : CostCentre) := (match __arg_32__ with
                                                 | (Mk_NormalCC _ _ cc_mod _ _) => cc_mod
                                                 | (Mk_AllCafsCC cc_mod _) => cc_mod
                                               end).

Definition cc_name (__arg_33__ : CostCentre) := (match __arg_33__ with
                                                  | (Mk_NormalCC _ cc_name _ _ _) => cc_name
                                                  | (Mk_AllCafsCC _ _) => (error
                                                                          &"Partial record selector: field `cc_name' has no match in constructor `Mk_AllCafsCC' of type `CostCentre'")
                                                end).

Definition breakpointFVs {id} (__arg_34__ : (Tickish id)) :=
  (match __arg_34__ with
    | (Mk_ProfNote _ _ _) => (error
                             &"Partial record selector: field `breakpointFVs' has no match in constructor `Mk_ProfNote' of type `Tickish'")
    | (Mk_HpcTick _ _) => (error
                          &"Partial record selector: field `breakpointFVs' has no match in constructor `Mk_HpcTick' of type `Tickish'")
    | (Mk_Breakpoint _ breakpointFVs) => breakpointFVs
    | (Mk_SourceNote _ _) => (error
                             &"Partial record selector: field `breakpointFVs' has no match in constructor `Mk_SourceNote' of type `Tickish'")
  end).

Definition breakpointId {id} (__arg_35__ : (Tickish id)) :=
  (match __arg_35__ with
    | (Mk_ProfNote _ _ _) => (error
                             &"Partial record selector: field `breakpointId' has no match in constructor `Mk_ProfNote' of type `Tickish'")
    | (Mk_HpcTick _ _) => (error
                          &"Partial record selector: field `breakpointId' has no match in constructor `Mk_HpcTick' of type `Tickish'")
    | (Mk_Breakpoint breakpointId _) => breakpointId
    | (Mk_SourceNote _ _) => (error
                             &"Partial record selector: field `breakpointId' has no match in constructor `Mk_SourceNote' of type `Tickish'")
  end).

Definition profNoteCC {id} (__arg_36__ : (Tickish id)) := (match __arg_36__ with
                                                            | (Mk_ProfNote profNoteCC _ _) => profNoteCC
                                                            | (Mk_HpcTick _ _) => (error
                                                                                  &"Partial record selector: field `profNoteCC' has no match in constructor `Mk_HpcTick' of type `Tickish'")
                                                            | (Mk_Breakpoint _ _) => (error
                                                                                     &"Partial record selector: field `profNoteCC' has no match in constructor `Mk_Breakpoint' of type `Tickish'")
                                                            | (Mk_SourceNote _ _) => (error
                                                                                     &"Partial record selector: field `profNoteCC' has no match in constructor `Mk_SourceNote' of type `Tickish'")
                                                          end).

Definition profNoteCount {id} (__arg_37__ : (Tickish id)) :=
  (match __arg_37__ with
    | (Mk_ProfNote _ profNoteCount _) => profNoteCount
    | (Mk_HpcTick _ _) => (error
                          &"Partial record selector: field `profNoteCount' has no match in constructor `Mk_HpcTick' of type `Tickish'")
    | (Mk_Breakpoint _ _) => (error
                             &"Partial record selector: field `profNoteCount' has no match in constructor `Mk_Breakpoint' of type `Tickish'")
    | (Mk_SourceNote _ _) => (error
                             &"Partial record selector: field `profNoteCount' has no match in constructor `Mk_SourceNote' of type `Tickish'")
  end).

Definition profNoteScope {id} (__arg_38__ : (Tickish id)) :=
  (match __arg_38__ with
    | (Mk_ProfNote _ _ profNoteScope) => profNoteScope
    | (Mk_HpcTick _ _) => (error
                          &"Partial record selector: field `profNoteScope' has no match in constructor `Mk_HpcTick' of type `Tickish'")
    | (Mk_Breakpoint _ _) => (error
                             &"Partial record selector: field `profNoteScope' has no match in constructor `Mk_Breakpoint' of type `Tickish'")
    | (Mk_SourceNote _ _) => (error
                             &"Partial record selector: field `profNoteScope' has no match in constructor `Mk_SourceNote' of type `Tickish'")
  end).

Definition sourceName {id} (__arg_39__ : (Tickish id)) := (match __arg_39__ with
                                                            | (Mk_ProfNote _ _ _) => (error
                                                                                     &"Partial record selector: field `sourceName' has no match in constructor `Mk_ProfNote' of type `Tickish'")
                                                            | (Mk_HpcTick _ _) => (error
                                                                                  &"Partial record selector: field `sourceName' has no match in constructor `Mk_HpcTick' of type `Tickish'")
                                                            | (Mk_Breakpoint _ _) => (error
                                                                                     &"Partial record selector: field `sourceName' has no match in constructor `Mk_Breakpoint' of type `Tickish'")
                                                            | (Mk_SourceNote _ sourceName) => sourceName
                                                          end).

Definition sourceSpan {id} (__arg_40__ : (Tickish id)) := (match __arg_40__ with
                                                            | (Mk_ProfNote _ _ _) => (error
                                                                                     &"Partial record selector: field `sourceSpan' has no match in constructor `Mk_ProfNote' of type `Tickish'")
                                                            | (Mk_HpcTick _ _) => (error
                                                                                  &"Partial record selector: field `sourceSpan' has no match in constructor `Mk_HpcTick' of type `Tickish'")
                                                            | (Mk_Breakpoint _ _) => (error
                                                                                     &"Partial record selector: field `sourceSpan' has no match in constructor `Mk_Breakpoint' of type `Tickish'")
                                                            | (Mk_SourceNote sourceSpan _) => sourceSpan
                                                          end).

Definition tickId {id} (__arg_41__ : (Tickish id)) := (match __arg_41__ with
                                                        | (Mk_ProfNote _ _ _) => (error
                                                                                 &"Partial record selector: field `tickId' has no match in constructor `Mk_ProfNote' of type `Tickish'")
                                                        | (Mk_HpcTick _ tickId) => tickId
                                                        | (Mk_Breakpoint _ _) => (error
                                                                                 &"Partial record selector: field `tickId' has no match in constructor `Mk_Breakpoint' of type `Tickish'")
                                                        | (Mk_SourceNote _ _) => (error
                                                                                 &"Partial record selector: field `tickId' has no match in constructor `Mk_SourceNote' of type `Tickish'")
                                                      end).

Definition tickModule {id} (__arg_42__ : (Tickish id)) := (match __arg_42__ with
                                                            | (Mk_ProfNote _ _ _) => (error
                                                                                     &"Partial record selector: field `tickModule' has no match in constructor `Mk_ProfNote' of type `Tickish'")
                                                            | (Mk_HpcTick tickModule _) => tickModule
                                                            | (Mk_Breakpoint _ _) => (error
                                                                                     &"Partial record selector: field `tickModule' has no match in constructor `Mk_Breakpoint' of type `Tickish'")
                                                            | (Mk_SourceNote _ _) => (error
                                                                                     &"Partial record selector: field `tickModule' has no match in constructor `Mk_SourceNote' of type `Tickish'")
                                                          end).

Definition ug_args (__arg_43__ : UnfoldingGuidance) := (match __arg_43__ with
                                                         | (Mk_UnfWhen _ _ _) => (error
                                                                                 &"Partial record selector: field `ug_args' has no match in constructor `Mk_UnfWhen' of type `UnfoldingGuidance'")
                                                         | (Mk_UnfIfGoodArgs ug_args _ _) => ug_args
                                                         | Mk_UnfNever => (error
                                                                          &"Partial record selector: field `ug_args' has no match in constructor `Mk_UnfNever' of type `UnfoldingGuidance'")
                                                       end).

Definition ug_arity (__arg_44__ : UnfoldingGuidance) := (match __arg_44__ with
                                                          | (Mk_UnfWhen ug_arity _ _) => ug_arity
                                                          | (Mk_UnfIfGoodArgs _ _ _) => (error
                                                                                        &"Partial record selector: field `ug_arity' has no match in constructor `Mk_UnfIfGoodArgs' of type `UnfoldingGuidance'")
                                                          | Mk_UnfNever => (error
                                                                           &"Partial record selector: field `ug_arity' has no match in constructor `Mk_UnfNever' of type `UnfoldingGuidance'")
                                                        end).

Definition ug_boring_ok (__arg_45__ : UnfoldingGuidance) :=
  (match __arg_45__ with
    | (Mk_UnfWhen _ _ ug_boring_ok) => ug_boring_ok
    | (Mk_UnfIfGoodArgs _ _ _) => (error
                                  &"Partial record selector: field `ug_boring_ok' has no match in constructor `Mk_UnfIfGoodArgs' of type `UnfoldingGuidance'")
    | Mk_UnfNever => (error
                     &"Partial record selector: field `ug_boring_ok' has no match in constructor `Mk_UnfNever' of type `UnfoldingGuidance'")
  end).

Definition ug_res (__arg_46__ : UnfoldingGuidance) := (match __arg_46__ with
                                                        | (Mk_UnfWhen _ _ _) => (error
                                                                                &"Partial record selector: field `ug_res' has no match in constructor `Mk_UnfWhen' of type `UnfoldingGuidance'")
                                                        | (Mk_UnfIfGoodArgs _ _ ug_res) => ug_res
                                                        | Mk_UnfNever => (error
                                                                         &"Partial record selector: field `ug_res' has no match in constructor `Mk_UnfNever' of type `UnfoldingGuidance'")
                                                      end).

Definition ug_size (__arg_47__ : UnfoldingGuidance) := (match __arg_47__ with
                                                         | (Mk_UnfWhen _ _ _) => (error
                                                                                 &"Partial record selector: field `ug_size' has no match in constructor `Mk_UnfWhen' of type `UnfoldingGuidance'")
                                                         | (Mk_UnfIfGoodArgs _ ug_size _) => ug_size
                                                         | Mk_UnfNever => (error
                                                                          &"Partial record selector: field `ug_size' has no match in constructor `Mk_UnfNever' of type `UnfoldingGuidance'")
                                                       end).

Definition ug_unsat_ok (__arg_48__ : UnfoldingGuidance) :=
  (match __arg_48__ with
    | (Mk_UnfWhen _ ug_unsat_ok _) => ug_unsat_ok
    | (Mk_UnfIfGoodArgs _ _ _) => (error
                                  &"Partial record selector: field `ug_unsat_ok' has no match in constructor `Mk_UnfIfGoodArgs' of type `UnfoldingGuidance'")
    | Mk_UnfNever => (error
                     &"Partial record selector: field `ug_unsat_ok' has no match in constructor `Mk_UnfNever' of type `UnfoldingGuidance'")
  end).

Definition classATStuff (__arg_49__ : Class) := (match __arg_49__ with
                                                  | (Mk_Class _ _ _ _ _ _ _ classATStuff _ _) => classATStuff
                                                end).

Definition classFunDeps (__arg_50__ : Class) := (match __arg_50__ with
                                                  | (Mk_Class _ _ _ _ classFunDeps _ _ _ _ _) => classFunDeps
                                                end).

Definition classKey (__arg_51__ : Class) := (match __arg_51__ with
                                              | (Mk_Class _ _ classKey _ _ _ _ _ _ _) => classKey
                                            end).

Definition classMinimalDef (__arg_52__ : Class) := (match __arg_52__ with
                                                     | (Mk_Class _ _ _ _ _ _ _ _ _ classMinimalDef) => classMinimalDef
                                                   end).

Definition className (__arg_53__ : Class) := (match __arg_53__ with
                                               | (Mk_Class _ className _ _ _ _ _ _ _ _) => className
                                             end).

Definition classOpStuff (__arg_54__ : Class) := (match __arg_54__ with
                                                  | (Mk_Class _ _ _ _ _ _ _ _ classOpStuff _) => classOpStuff
                                                end).

Definition classSCSels (__arg_55__ : Class) := (match __arg_55__ with
                                                 | (Mk_Class _ _ _ _ _ _ classSCSels _ _ _) => classSCSels
                                               end).

Definition classSCTheta (__arg_56__ : Class) := (match __arg_56__ with
                                                  | (Mk_Class _ _ _ _ _ classSCTheta _ _ _ _) => classSCTheta
                                                end).

Definition classTyCon (__arg_57__ : Class) := (match __arg_57__ with
                                                | (Mk_Class classTyCon _ _ _ _ _ _ _ _ _) => classTyCon
                                              end).

Definition classTyVars (__arg_58__ : Class) := (match __arg_58__ with
                                                 | (Mk_Class _ _ _ classTyVars _ _ _ _ _ _) => classTyVars
                                               end).

Definition algTcFields (__arg_59__ : TyCon) := (match __arg_59__ with
                                                 | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                              &"Partial record selector: field `algTcFields' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                 | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ algTcFields _ _) => algTcFields
                                                 | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `algTcFields' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                                 | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                         &"Partial record selector: field `algTcFields' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                                 | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                     &"Partial record selector: field `algTcFields' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                                 | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                         &"Partial record selector: field `algTcFields' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                 | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                             &"Partial record selector: field `algTcFields' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                               end).

Definition algTcGadtSyntax (__arg_60__ : TyCon) := (match __arg_60__ with
                                                     | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                                  &"Partial record selector: field `algTcGadtSyntax' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                     | (Mk_AlgTyCon _ _ _ _ _ _ _ algTcGadtSyntax _ _ _ _ _) =>
                                                       algTcGadtSyntax
                                                     | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                          &"Partial record selector: field `algTcGadtSyntax' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                                     | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                             &"Partial record selector: field `algTcGadtSyntax' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                                     | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                         &"Partial record selector: field `algTcGadtSyntax' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                                     | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                             &"Partial record selector: field `algTcGadtSyntax' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                     | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                                 &"Partial record selector: field `algTcGadtSyntax' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                                   end).

Definition algTcParent (__arg_61__ : TyCon) := (match __arg_61__ with
                                                 | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                              &"Partial record selector: field `algTcParent' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                 | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ algTcParent) => algTcParent
                                                 | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `algTcParent' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                                 | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                         &"Partial record selector: field `algTcParent' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                                 | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                     &"Partial record selector: field `algTcParent' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                                 | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                         &"Partial record selector: field `algTcParent' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                 | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                             &"Partial record selector: field `algTcParent' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                               end).

Definition algTcRec (__arg_62__ : TyCon) := (match __arg_62__ with
                                              | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                           &"Partial record selector: field `algTcRec' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                              | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ algTcRec _) => algTcRec
                                              | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                   &"Partial record selector: field `algTcRec' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                              | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `algTcRec' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                              | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                  &"Partial record selector: field `algTcRec' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                              | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `algTcRec' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                              | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                          &"Partial record selector: field `algTcRec' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                            end).

Definition algTcRhs (__arg_63__ : TyCon) := (match __arg_63__ with
                                              | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                           &"Partial record selector: field `algTcRhs' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                              | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ algTcRhs _ _ _) => algTcRhs
                                              | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                   &"Partial record selector: field `algTcRhs' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                              | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `algTcRhs' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                              | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                  &"Partial record selector: field `algTcRhs' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                              | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `algTcRhs' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                              | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                          &"Partial record selector: field `algTcRhs' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                            end).

Definition algTcStupidTheta (__arg_64__ : TyCon) := (match __arg_64__ with
                                                      | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                                   &"Partial record selector: field `algTcStupidTheta' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                      | (Mk_AlgTyCon _ _ _ _ _ _ _ _ algTcStupidTheta _ _ _ _) =>
                                                        algTcStupidTheta
                                                      | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                           &"Partial record selector: field `algTcStupidTheta' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                                      | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                              &"Partial record selector: field `algTcStupidTheta' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                                      | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                          &"Partial record selector: field `algTcStupidTheta' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                                      | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                              &"Partial record selector: field `algTcStupidTheta' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                      | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                                  &"Partial record selector: field `algTcStupidTheta' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                                    end).

Definition dataCon (__arg_65__ : TyCon) := (match __arg_65__ with
                                             | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                          &"Partial record selector: field `dataCon' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                             | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                          &"Partial record selector: field `dataCon' has no match in constructor `Mk_AlgTyCon' of type `TyCon'")
                                             | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                  &"Partial record selector: field `dataCon' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                             | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                     &"Partial record selector: field `dataCon' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                             | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                 &"Partial record selector: field `dataCon' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                             | (Mk_PromotedDataCon _ _ _ _ _ dataCon _) => dataCon
                                             | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                         &"Partial record selector: field `dataCon' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                           end).

Definition famTcFlav (__arg_66__ : TyCon) := (match __arg_66__ with
                                               | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                            &"Partial record selector: field `famTcFlav' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                               | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                            &"Partial record selector: field `famTcFlav' has no match in constructor `Mk_AlgTyCon' of type `TyCon'")
                                               | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                    &"Partial record selector: field `famTcFlav' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                               | (Mk_FamilyTyCon _ _ _ _ _ _ famTcFlav _ _) => famTcFlav
                                               | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                   &"Partial record selector: field `famTcFlav' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                               | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                       &"Partial record selector: field `famTcFlav' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                               | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                           &"Partial record selector: field `famTcFlav' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                             end).

Definition famTcInj (__arg_67__ : TyCon) := (match __arg_67__ with
                                              | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                           &"Partial record selector: field `famTcInj' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                              | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                           &"Partial record selector: field `famTcInj' has no match in constructor `Mk_AlgTyCon' of type `TyCon'")
                                              | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                   &"Partial record selector: field `famTcInj' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                              | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ famTcInj) => famTcInj
                                              | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                  &"Partial record selector: field `famTcInj' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                              | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `famTcInj' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                              | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                          &"Partial record selector: field `famTcInj' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                            end).

Definition famTcParent (__arg_68__ : TyCon) := (match __arg_68__ with
                                                 | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                              &"Partial record selector: field `famTcParent' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                 | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                              &"Partial record selector: field `famTcParent' has no match in constructor `Mk_AlgTyCon' of type `TyCon'")
                                                 | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `famTcParent' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                                 | (Mk_FamilyTyCon _ _ _ _ _ _ _ famTcParent _) => famTcParent
                                                 | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                     &"Partial record selector: field `famTcParent' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                                 | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                         &"Partial record selector: field `famTcParent' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                 | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                             &"Partial record selector: field `famTcParent' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                               end).

Definition famTcResVar (__arg_69__ : TyCon) := (match __arg_69__ with
                                                 | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                              &"Partial record selector: field `famTcResVar' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                 | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                              &"Partial record selector: field `famTcResVar' has no match in constructor `Mk_AlgTyCon' of type `TyCon'")
                                                 | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `famTcResVar' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                                 | (Mk_FamilyTyCon _ _ _ _ _ famTcResVar _ _ _) => famTcResVar
                                                 | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                     &"Partial record selector: field `famTcResVar' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                                 | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                         &"Partial record selector: field `famTcResVar' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                 | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                             &"Partial record selector: field `famTcResVar' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                               end).

Definition isUnlifted (__arg_70__ : TyCon) := (match __arg_70__ with
                                                | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                             &"Partial record selector: field `isUnlifted' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                             &"Partial record selector: field `isUnlifted' has no match in constructor `Mk_AlgTyCon' of type `TyCon'")
                                                | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                     &"Partial record selector: field `isUnlifted' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                                | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                        &"Partial record selector: field `isUnlifted' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                                | (Mk_PrimTyCon _ _ _ _ _ _ isUnlifted _) => isUnlifted
                                                | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                        &"Partial record selector: field `isUnlifted' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                            &"Partial record selector: field `isUnlifted' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                              end).

Definition primRepName (__arg_71__ : TyCon) := (match __arg_71__ with
                                                 | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                              &"Partial record selector: field `primRepName' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                 | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                              &"Partial record selector: field `primRepName' has no match in constructor `Mk_AlgTyCon' of type `TyCon'")
                                                 | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `primRepName' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                                 | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                         &"Partial record selector: field `primRepName' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                                 | (Mk_PrimTyCon _ _ _ _ _ _ _ primRepName) => primRepName
                                                 | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                         &"Partial record selector: field `primRepName' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                 | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                             &"Partial record selector: field `primRepName' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                               end).

Definition primTyConRep (__arg_72__ : TyCon) := (match __arg_72__ with
                                                  | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                               &"Partial record selector: field `primTyConRep' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                  | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                               &"Partial record selector: field `primTyConRep' has no match in constructor `Mk_AlgTyCon' of type `TyCon'")
                                                  | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                       &"Partial record selector: field `primTyConRep' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                                  | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                          &"Partial record selector: field `primTyConRep' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                                  | (Mk_PrimTyCon _ _ _ _ _ primTyConRep _ _) => primTyConRep
                                                  | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                          &"Partial record selector: field `primTyConRep' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                  | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                              &"Partial record selector: field `primTyConRep' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                                end).

Definition synTcRhs (__arg_73__ : TyCon) := (match __arg_73__ with
                                              | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                           &"Partial record selector: field `synTcRhs' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                              | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                           &"Partial record selector: field `synTcRhs' has no match in constructor `Mk_AlgTyCon' of type `TyCon'")
                                              | (Mk_SynonymTyCon _ _ _ _ _ _ synTcRhs) => synTcRhs
                                              | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `synTcRhs' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                              | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                  &"Partial record selector: field `synTcRhs' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                              | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                      &"Partial record selector: field `synTcRhs' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                              | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                          &"Partial record selector: field `synTcRhs' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                            end).

Definition tcRepName (__arg_74__ : TyCon) := (match __arg_74__ with
                                               | (Mk_FunTyCon _ _ _ _ tcRepName) => tcRepName
                                               | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                            &"Partial record selector: field `tcRepName' has no match in constructor `Mk_AlgTyCon' of type `TyCon'")
                                               | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                    &"Partial record selector: field `tcRepName' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                               | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                       &"Partial record selector: field `tcRepName' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                               | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                   &"Partial record selector: field `tcRepName' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                               | (Mk_PromotedDataCon _ _ _ _ _ _ tcRepName) => tcRepName
                                               | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                           &"Partial record selector: field `tcRepName' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                             end).

Definition tcRoles (__arg_75__ : TyCon) := (match __arg_75__ with
                                             | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                          &"Partial record selector: field `tcRoles' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                             | (Mk_AlgTyCon _ _ _ _ _ tcRoles _ _ _ _ _ _ _) => tcRoles
                                             | (Mk_SynonymTyCon _ _ _ _ _ tcRoles _) => tcRoles
                                             | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                     &"Partial record selector: field `tcRoles' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                             | (Mk_PrimTyCon _ _ _ _ tcRoles _ _ _) => tcRoles
                                             | (Mk_PromotedDataCon _ _ _ _ tcRoles _ _) => tcRoles
                                             | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                         &"Partial record selector: field `tcRoles' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                           end).

Definition tyConArity (__arg_76__ : TyCon) := (match __arg_76__ with
                                                | (Mk_FunTyCon _ _ _ tyConArity _) => tyConArity
                                                | (Mk_AlgTyCon _ _ _ tyConArity _ _ _ _ _ _ _ _ _) => tyConArity
                                                | (Mk_SynonymTyCon _ _ _ tyConArity _ _ _) => tyConArity
                                                | (Mk_FamilyTyCon _ _ _ tyConArity _ _ _ _ _) => tyConArity
                                                | (Mk_PrimTyCon _ _ _ tyConArity _ _ _ _) => tyConArity
                                                | (Mk_PromotedDataCon _ _ tyConArity _ _ _ _) => tyConArity
                                                | (Mk_TcTyCon _ _ _ tyConArity _) => tyConArity
                                              end).

Definition tyConCType (__arg_77__ : TyCon) := (match __arg_77__ with
                                                | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                             &"Partial record selector: field `tyConCType' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                | (Mk_AlgTyCon _ _ _ _ _ _ tyConCType _ _ _ _ _ _) => tyConCType
                                                | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                     &"Partial record selector: field `tyConCType' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                                | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                        &"Partial record selector: field `tyConCType' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                                | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                    &"Partial record selector: field `tyConCType' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                                | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                        &"Partial record selector: field `tyConCType' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                            &"Partial record selector: field `tyConCType' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                              end).

Definition tyConKind (__arg_78__ : TyCon) := (match __arg_78__ with
                                               | (Mk_FunTyCon _ _ tyConKind _ _) => tyConKind
                                               | (Mk_AlgTyCon _ _ tyConKind _ _ _ _ _ _ _ _ _ _) => tyConKind
                                               | (Mk_SynonymTyCon _ _ tyConKind _ _ _ _) => tyConKind
                                               | (Mk_FamilyTyCon _ _ tyConKind _ _ _ _ _ _) => tyConKind
                                               | (Mk_PrimTyCon _ _ tyConKind _ _ _ _ _) => tyConKind
                                               | (Mk_PromotedDataCon _ _ _ tyConKind _ _ _) => tyConKind
                                               | (Mk_TcTyCon _ _ _ _ tyConKind) => tyConKind
                                             end).

Definition tyConName (__arg_79__ : TyCon) := (match __arg_79__ with
                                               | (Mk_FunTyCon _ tyConName _ _ _) => tyConName
                                               | (Mk_AlgTyCon _ tyConName _ _ _ _ _ _ _ _ _ _ _) => tyConName
                                               | (Mk_SynonymTyCon _ tyConName _ _ _ _ _) => tyConName
                                               | (Mk_FamilyTyCon _ tyConName _ _ _ _ _ _ _) => tyConName
                                               | (Mk_PrimTyCon _ tyConName _ _ _ _ _ _) => tyConName
                                               | (Mk_PromotedDataCon _ tyConName _ _ _ _ _) => tyConName
                                               | (Mk_TcTyCon _ tyConName _ _ _) => tyConName
                                             end).

Definition tyConTyVars (__arg_80__ : TyCon) := (match __arg_80__ with
                                                 | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                              &"Partial record selector: field `tyConTyVars' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                 | (Mk_AlgTyCon _ _ _ _ tyConTyVars _ _ _ _ _ _ _ _) => tyConTyVars
                                                 | (Mk_SynonymTyCon _ _ _ _ tyConTyVars _ _) => tyConTyVars
                                                 | (Mk_FamilyTyCon _ _ _ _ tyConTyVars _ _ _ _) => tyConTyVars
                                                 | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                     &"Partial record selector: field `tyConTyVars' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                                 | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                         &"Partial record selector: field `tyConTyVars' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                 | (Mk_TcTyCon _ _ _ _ _) => (error
                                                                             &"Partial record selector: field `tyConTyVars' has no match in constructor `Mk_TcTyCon' of type `TyCon'")
                                               end).

Definition tyConUnique (__arg_81__ : TyCon) := (match __arg_81__ with
                                                 | (Mk_FunTyCon tyConUnique _ _ _ _) => tyConUnique
                                                 | (Mk_AlgTyCon tyConUnique _ _ _ _ _ _ _ _ _ _ _ _) => tyConUnique
                                                 | (Mk_SynonymTyCon tyConUnique _ _ _ _ _ _) => tyConUnique
                                                 | (Mk_FamilyTyCon tyConUnique _ _ _ _ _ _ _ _) => tyConUnique
                                                 | (Mk_PrimTyCon tyConUnique _ _ _ _ _ _ _) => tyConUnique
                                                 | (Mk_PromotedDataCon tyConUnique _ _ _ _ _ _) => tyConUnique
                                                 | (Mk_TcTyCon tyConUnique _ _ _ _) => tyConUnique
                                               end).

Definition tyConUnsat (__arg_82__ : TyCon) := (match __arg_82__ with
                                                | (Mk_FunTyCon _ _ _ _ _) => (error
                                                                             &"Partial record selector: field `tyConUnsat' has no match in constructor `Mk_FunTyCon' of type `TyCon'")
                                                | (Mk_AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                             &"Partial record selector: field `tyConUnsat' has no match in constructor `Mk_AlgTyCon' of type `TyCon'")
                                                | (Mk_SynonymTyCon _ _ _ _ _ _ _) => (error
                                                                                     &"Partial record selector: field `tyConUnsat' has no match in constructor `Mk_SynonymTyCon' of type `TyCon'")
                                                | (Mk_FamilyTyCon _ _ _ _ _ _ _ _ _) => (error
                                                                                        &"Partial record selector: field `tyConUnsat' has no match in constructor `Mk_FamilyTyCon' of type `TyCon'")
                                                | (Mk_PrimTyCon _ _ _ _ _ _ _ _) => (error
                                                                                    &"Partial record selector: field `tyConUnsat' has no match in constructor `Mk_PrimTyCon' of type `TyCon'")
                                                | (Mk_PromotedDataCon _ _ _ _ _ _ _) => (error
                                                                                        &"Partial record selector: field `tyConUnsat' has no match in constructor `Mk_PromotedDataCon' of type `TyCon'")
                                                | (Mk_TcTyCon _ _ tyConUnsat _ _) => tyConUnsat
                                              end).

Definition data_con (__arg_83__ : AlgTyConRhs) := (match __arg_83__ with
                                                    | (Mk_AbstractTyCon _) => (error
                                                                              &"Partial record selector: field `data_con' has no match in constructor `Mk_AbstractTyCon' of type `AlgTyConRhs'")
                                                    | (Mk_DataTyCon _ _) => (error
                                                                            &"Partial record selector: field `data_con' has no match in constructor `Mk_DataTyCon' of type `AlgTyConRhs'")
                                                    | (Mk_TupleTyCon data_con _) => data_con
                                                    | (Mk_NewTyCon data_con _ _ _) => data_con
                                                  end).

Definition data_cons (__arg_84__ : AlgTyConRhs) := (match __arg_84__ with
                                                     | (Mk_AbstractTyCon _) => (error
                                                                               &"Partial record selector: field `data_cons' has no match in constructor `Mk_AbstractTyCon' of type `AlgTyConRhs'")
                                                     | (Mk_DataTyCon data_cons _) => data_cons
                                                     | (Mk_TupleTyCon _ _) => (error
                                                                              &"Partial record selector: field `data_cons' has no match in constructor `Mk_TupleTyCon' of type `AlgTyConRhs'")
                                                     | (Mk_NewTyCon _ _ _ _) => (error
                                                                                &"Partial record selector: field `data_cons' has no match in constructor `Mk_NewTyCon' of type `AlgTyConRhs'")
                                                   end).

Definition is_enum (__arg_85__ : AlgTyConRhs) := (match __arg_85__ with
                                                   | (Mk_AbstractTyCon _) => (error
                                                                             &"Partial record selector: field `is_enum' has no match in constructor `Mk_AbstractTyCon' of type `AlgTyConRhs'")
                                                   | (Mk_DataTyCon _ is_enum) => is_enum
                                                   | (Mk_TupleTyCon _ _) => (error
                                                                            &"Partial record selector: field `is_enum' has no match in constructor `Mk_TupleTyCon' of type `AlgTyConRhs'")
                                                   | (Mk_NewTyCon _ _ _ _) => (error
                                                                              &"Partial record selector: field `is_enum' has no match in constructor `Mk_NewTyCon' of type `AlgTyConRhs'")
                                                 end).

Definition nt_co (__arg_86__ : AlgTyConRhs) := (match __arg_86__ with
                                                 | (Mk_AbstractTyCon _) => (error
                                                                           &"Partial record selector: field `nt_co' has no match in constructor `Mk_AbstractTyCon' of type `AlgTyConRhs'")
                                                 | (Mk_DataTyCon _ _) => (error
                                                                         &"Partial record selector: field `nt_co' has no match in constructor `Mk_DataTyCon' of type `AlgTyConRhs'")
                                                 | (Mk_TupleTyCon _ _) => (error
                                                                          &"Partial record selector: field `nt_co' has no match in constructor `Mk_TupleTyCon' of type `AlgTyConRhs'")
                                                 | (Mk_NewTyCon _ _ _ nt_co) => nt_co
                                               end).

Definition nt_etad_rhs (__arg_87__ : AlgTyConRhs) := (match __arg_87__ with
                                                       | (Mk_AbstractTyCon _) => (error
                                                                                 &"Partial record selector: field `nt_etad_rhs' has no match in constructor `Mk_AbstractTyCon' of type `AlgTyConRhs'")
                                                       | (Mk_DataTyCon _ _) => (error
                                                                               &"Partial record selector: field `nt_etad_rhs' has no match in constructor `Mk_DataTyCon' of type `AlgTyConRhs'")
                                                       | (Mk_TupleTyCon _ _) => (error
                                                                                &"Partial record selector: field `nt_etad_rhs' has no match in constructor `Mk_TupleTyCon' of type `AlgTyConRhs'")
                                                       | (Mk_NewTyCon _ _ nt_etad_rhs _) => nt_etad_rhs
                                                     end).

Definition nt_rhs (__arg_88__ : AlgTyConRhs) := (match __arg_88__ with
                                                  | (Mk_AbstractTyCon _) => (error
                                                                            &"Partial record selector: field `nt_rhs' has no match in constructor `Mk_AbstractTyCon' of type `AlgTyConRhs'")
                                                  | (Mk_DataTyCon _ _) => (error
                                                                          &"Partial record selector: field `nt_rhs' has no match in constructor `Mk_DataTyCon' of type `AlgTyConRhs'")
                                                  | (Mk_TupleTyCon _ _) => (error
                                                                           &"Partial record selector: field `nt_rhs' has no match in constructor `Mk_TupleTyCon' of type `AlgTyConRhs'")
                                                  | (Mk_NewTyCon _ nt_rhs _ _) => nt_rhs
                                                end).

Definition tup_sort (__arg_89__ : AlgTyConRhs) := (match __arg_89__ with
                                                    | (Mk_AbstractTyCon _) => (error
                                                                              &"Partial record selector: field `tup_sort' has no match in constructor `Mk_AbstractTyCon' of type `AlgTyConRhs'")
                                                    | (Mk_DataTyCon _ _) => (error
                                                                            &"Partial record selector: field `tup_sort' has no match in constructor `Mk_DataTyCon' of type `AlgTyConRhs'")
                                                    | (Mk_TupleTyCon _ tup_sort) => tup_sort
                                                    | (Mk_NewTyCon _ _ _ _) => (error
                                                                               &"Partial record selector: field `tup_sort' has no match in constructor `Mk_NewTyCon' of type `AlgTyConRhs'")
                                                  end).

Definition co_ax_branches {br} (__arg_90__ : (CoAxiom br)) :=
  (match __arg_90__ with
    | (Mk_CoAxiom _ _ _ _ co_ax_branches _) => co_ax_branches
  end).

Definition co_ax_implicit {br} (__arg_91__ : (CoAxiom br)) :=
  (match __arg_91__ with
    | (Mk_CoAxiom _ _ _ _ _ co_ax_implicit) => co_ax_implicit
  end).

Definition co_ax_name {br} (__arg_92__ : (CoAxiom br)) := (match __arg_92__ with
                                                            | (Mk_CoAxiom _ co_ax_name _ _ _ _) => co_ax_name
                                                          end).

Definition co_ax_role {br} (__arg_93__ : (CoAxiom br)) := (match __arg_93__ with
                                                            | (Mk_CoAxiom _ _ co_ax_role _ _ _) => co_ax_role
                                                          end).

Definition co_ax_tc {br} (__arg_94__ : (CoAxiom br)) := (match __arg_94__ with
                                                          | (Mk_CoAxiom _ _ _ co_ax_tc _ _) => co_ax_tc
                                                        end).

Definition co_ax_unique {br} (__arg_95__ : (CoAxiom br)) :=
  (match __arg_95__ with
    | (Mk_CoAxiom co_ax_unique _ _ _ _ _) => co_ax_unique
  end).

Definition unMkBranches {br : BranchFlag} (__arg_96__ : (Branches br)) :=
  (match __arg_96__ with
    | (Mk_MkBranches unMkBranches) => unMkBranches
  end).

Definition cab_cvs (__arg_97__ : CoAxBranch) := (match __arg_97__ with
                                                  | (Mk_CoAxBranch _ _ cab_cvs _ _ _ _) => cab_cvs
                                                end).

Definition cab_incomps (__arg_98__ : CoAxBranch) := (match __arg_98__ with
                                                      | (Mk_CoAxBranch _ _ _ _ _ _ cab_incomps) => cab_incomps
                                                    end).

Definition cab_lhs (__arg_99__ : CoAxBranch) := (match __arg_99__ with
                                                  | (Mk_CoAxBranch _ _ _ _ cab_lhs _ _) => cab_lhs
                                                end).

Definition cab_loc (__arg_100__ : CoAxBranch) := (match __arg_100__ with
                                                   | (Mk_CoAxBranch cab_loc _ _ _ _ _ _) => cab_loc
                                                 end).

Definition cab_rhs (__arg_101__ : CoAxBranch) := (match __arg_101__ with
                                                   | (Mk_CoAxBranch _ _ _ _ _ cab_rhs _) => cab_rhs
                                                 end).

Definition cab_roles (__arg_102__ : CoAxBranch) := (match __arg_102__ with
                                                     | (Mk_CoAxBranch _ _ _ cab_roles _ _ _) => cab_roles
                                                   end).

Definition cab_tvs (__arg_103__ : CoAxBranch) := (match __arg_103__ with
                                                   | (Mk_CoAxBranch _ cab_tvs _ _ _ _ _) => cab_tvs
                                                 end).

Definition idScope (__arg_104__ : Var) := (match __arg_104__ with
                                            | (Mk_TyVar _ _ _) => (error
                                                                  &"Partial record selector: field `idScope' has no match in constructor `Mk_TyVar' of type `Var'")
                                            | (Mk_TcTyVar _ _ _ _) => (error
                                                                      &"Partial record selector: field `idScope' has no match in constructor `Mk_TcTyVar' of type `Var'")
                                            | (Mk_Id _ _ _ idScope _ _) => idScope
                                          end).

Definition id_details (__arg_105__ : Var) := (match __arg_105__ with
                                               | (Mk_TyVar _ _ _) => (error
                                                                     &"Partial record selector: field `id_details' has no match in constructor `Mk_TyVar' of type `Var'")
                                               | (Mk_TcTyVar _ _ _ _) => (error
                                                                         &"Partial record selector: field `id_details' has no match in constructor `Mk_TcTyVar' of type `Var'")
                                               | (Mk_Id _ _ _ _ id_details _) => id_details
                                             end).

Definition id_info (__arg_106__ : Var) := (match __arg_106__ with
                                            | (Mk_TyVar _ _ _) => (error
                                                                  &"Partial record selector: field `id_info' has no match in constructor `Mk_TyVar' of type `Var'")
                                            | (Mk_TcTyVar _ _ _ _) => (error
                                                                      &"Partial record selector: field `id_info' has no match in constructor `Mk_TcTyVar' of type `Var'")
                                            | (Mk_Id _ _ _ _ _ id_info) => id_info
                                          end).

Definition realUnique (__arg_107__ : Var) := (match __arg_107__ with
                                               | (Mk_TyVar _ realUnique _) => realUnique
                                               | (Mk_TcTyVar _ realUnique _ _) => realUnique
                                               | (Mk_Id _ realUnique _ _ _ _) => realUnique
                                             end).

Definition tc_tv_details (__arg_108__ : Var) := (match __arg_108__ with
                                                  | (Mk_TyVar _ _ _) => (error
                                                                        &"Partial record selector: field `tc_tv_details' has no match in constructor `Mk_TyVar' of type `Var'")
                                                  | (Mk_TcTyVar _ _ _ tc_tv_details) => tc_tv_details
                                                  | (Mk_Id _ _ _ _ _ _) => (error
                                                                           &"Partial record selector: field `tc_tv_details' has no match in constructor `Mk_Id' of type `Var'")
                                                end).

Definition varName (__arg_109__ : Var) := (match __arg_109__ with
                                            | (Mk_TyVar varName _ _) => varName
                                            | (Mk_TcTyVar varName _ _ _) => varName
                                            | (Mk_Id varName _ _ _ _ _) => varName
                                          end).

Definition varType (__arg_110__ : Var) := (match __arg_110__ with
                                            | (Mk_TyVar _ _ varType) => varType
                                            | (Mk_TcTyVar _ _ varType _) => varType
                                            | (Mk_Id _ _ varType _ _ _) => varType
                                          end).

Definition sel_naughty (__arg_111__ : IdDetails) := (match __arg_111__ with
                                                      | Mk_VanillaId => (error
                                                                        &"Partial record selector: field `sel_naughty' has no match in constructor `Mk_VanillaId' of type `IdDetails'")
                                                      | (Mk_RecSelId _ sel_naughty) => sel_naughty
                                                      | (Mk_DataConWorkId _) => (error
                                                                                &"Partial record selector: field `sel_naughty' has no match in constructor `Mk_DataConWorkId' of type `IdDetails'")
                                                      | (Mk_DataConWrapId _) => (error
                                                                                &"Partial record selector: field `sel_naughty' has no match in constructor `Mk_DataConWrapId' of type `IdDetails'")
                                                      | (Mk_ClassOpId _) => (error
                                                                            &"Partial record selector: field `sel_naughty' has no match in constructor `Mk_ClassOpId' of type `IdDetails'")
                                                      | (Mk_PrimOpId _) => (error
                                                                           &"Partial record selector: field `sel_naughty' has no match in constructor `Mk_PrimOpId' of type `IdDetails'")
                                                      | (Mk_FCallId _) => (error
                                                                          &"Partial record selector: field `sel_naughty' has no match in constructor `Mk_FCallId' of type `IdDetails'")
                                                      | (Mk_TickBoxOpId _) => (error
                                                                              &"Partial record selector: field `sel_naughty' has no match in constructor `Mk_TickBoxOpId' of type `IdDetails'")
                                                      | (Mk_DFunId _) => (error
                                                                         &"Partial record selector: field `sel_naughty' has no match in constructor `Mk_DFunId' of type `IdDetails'")
                                                      | Mk_CoVarId => (error
                                                                      &"Partial record selector: field `sel_naughty' has no match in constructor `Mk_CoVarId' of type `IdDetails'")
                                                    end).

Definition sel_tycon (__arg_112__ : IdDetails) := (match __arg_112__ with
                                                    | Mk_VanillaId => (error
                                                                      &"Partial record selector: field `sel_tycon' has no match in constructor `Mk_VanillaId' of type `IdDetails'")
                                                    | (Mk_RecSelId sel_tycon _) => sel_tycon
                                                    | (Mk_DataConWorkId _) => (error
                                                                              &"Partial record selector: field `sel_tycon' has no match in constructor `Mk_DataConWorkId' of type `IdDetails'")
                                                    | (Mk_DataConWrapId _) => (error
                                                                              &"Partial record selector: field `sel_tycon' has no match in constructor `Mk_DataConWrapId' of type `IdDetails'")
                                                    | (Mk_ClassOpId _) => (error
                                                                          &"Partial record selector: field `sel_tycon' has no match in constructor `Mk_ClassOpId' of type `IdDetails'")
                                                    | (Mk_PrimOpId _) => (error
                                                                         &"Partial record selector: field `sel_tycon' has no match in constructor `Mk_PrimOpId' of type `IdDetails'")
                                                    | (Mk_FCallId _) => (error
                                                                        &"Partial record selector: field `sel_tycon' has no match in constructor `Mk_FCallId' of type `IdDetails'")
                                                    | (Mk_TickBoxOpId _) => (error
                                                                            &"Partial record selector: field `sel_tycon' has no match in constructor `Mk_TickBoxOpId' of type `IdDetails'")
                                                    | (Mk_DFunId _) => (error
                                                                       &"Partial record selector: field `sel_tycon' has no match in constructor `Mk_DFunId' of type `IdDetails'")
                                                    | Mk_CoVarId => (error
                                                                    &"Partial record selector: field `sel_tycon' has no match in constructor `Mk_CoVarId' of type `IdDetails'")
                                                  end).

Definition dcEqSpec (__arg_113__ : DataCon) := (match __arg_113__ with
                                                 | (Mk_MkData _ _ _ _ _ _ dcEqSpec _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
                                                   dcEqSpec
                                               end).

Definition dcExTyVars (__arg_114__ : DataCon) := (match __arg_114__ with
                                                   | (Mk_MkData _ _ _ _ _ dcExTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
                                                     dcExTyVars
                                                 end).

Definition dcFields (__arg_115__ : DataCon) := (match __arg_115__ with
                                                 | (Mk_MkData _ _ _ _ _ _ _ _ _ _ _ _ dcFields _ _ _ _ _ _ _ _) =>
                                                   dcFields
                                               end).

Definition dcInfix (__arg_116__ : DataCon) := (match __arg_116__ with
                                                | (Mk_MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcInfix _) => dcInfix
                                              end).

Definition dcName (__arg_117__ : DataCon) := (match __arg_117__ with
                                               | (Mk_MkData dcName _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => dcName
                                             end).

Definition dcOrigArgTys (__arg_118__ : DataCon) := (match __arg_118__ with
                                                     | (Mk_MkData _ _ _ _ _ _ _ _ _ dcOrigArgTys _ _ _ _ _ _ _ _ _ _
                                                                  _) => dcOrigArgTys
                                                   end).

Definition dcOrigResTy (__arg_119__ : DataCon) := (match __arg_119__ with
                                                    | (Mk_MkData _ _ _ _ _ _ _ _ _ _ dcOrigResTy _ _ _ _ _ _ _ _ _ _) =>
                                                      dcOrigResTy
                                                  end).

Definition dcOtherTheta (__arg_120__ : DataCon) := (match __arg_120__ with
                                                     | (Mk_MkData _ _ _ _ _ _ _ dcOtherTheta _ _ _ _ _ _ _ _ _ _ _ _
                                                                  _) => dcOtherTheta
                                                   end).

Definition dcPromoted (__arg_121__ : DataCon) := (match __arg_121__ with
                                                   | (Mk_MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcPromoted) =>
                                                     dcPromoted
                                                 end).

Definition dcRep (__arg_122__ : DataCon) := (match __arg_122__ with
                                              | (Mk_MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRep _ _ _ _ _ _) => dcRep
                                            end).

Definition dcRepArity (__arg_123__ : DataCon) := (match __arg_123__ with
                                                   | (Mk_MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepArity _ _ _ _ _) =>
                                                     dcRepArity
                                                 end).

Definition dcRepTyCon (__arg_124__ : DataCon) := (match __arg_124__ with
                                                   | (Mk_MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepTyCon _ _ _) =>
                                                     dcRepTyCon
                                                 end).

Definition dcRepType (__arg_125__ : DataCon) := (match __arg_125__ with
                                                  | (Mk_MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepType _ _) =>
                                                    dcRepType
                                                end).

Definition dcSourceArity (__arg_126__ : DataCon) := (match __arg_126__ with
                                                      | (Mk_MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcSourceArity _ _ _
                                                                   _) => dcSourceArity
                                                    end).

Definition dcSrcBangs (__arg_127__ : DataCon) := (match __arg_127__ with
                                                   | (Mk_MkData _ _ _ _ _ _ _ _ _ _ _ dcSrcBangs _ _ _ _ _ _ _ _ _) =>
                                                     dcSrcBangs
                                                 end).

Definition dcStupidTheta (__arg_128__ : DataCon) := (match __arg_128__ with
                                                      | (Mk_MkData _ _ _ _ _ _ _ _ dcStupidTheta _ _ _ _ _ _ _ _ _ _ _
                                                                   _) => dcStupidTheta
                                                    end).

Definition dcTag (__arg_129__ : DataCon) := (match __arg_129__ with
                                              | (Mk_MkData _ _ dcTag _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => dcTag
                                            end).

Definition dcUnique (__arg_130__ : DataCon) := (match __arg_130__ with
                                                 | (Mk_MkData _ dcUnique _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
                                                   dcUnique
                                               end).

Definition dcUnivTyVars (__arg_131__ : DataCon) := (match __arg_131__ with
                                                     | (Mk_MkData _ _ _ _ dcUnivTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                                  _) => dcUnivTyVars
                                                   end).

Definition dcVanilla (__arg_132__ : DataCon) := (match __arg_132__ with
                                                  | (Mk_MkData _ _ _ dcVanilla _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
                                                    dcVanilla
                                                end).

Definition dcWorkId (__arg_133__ : DataCon) := (match __arg_133__ with
                                                 | (Mk_MkData _ _ _ _ _ _ _ _ _ _ _ _ _ dcWorkId _ _ _ _ _ _ _) =>
                                                   dcWorkId
                                               end).

Definition dcr_arg_tys (__arg_134__ : DataConRep) := (match __arg_134__ with
                                                       | Mk_NoDataConRep => (error
                                                                            &"Partial record selector: field `dcr_arg_tys' has no match in constructor `Mk_NoDataConRep' of type `DataConRep'")
                                                       | (Mk_DCR _ _ dcr_arg_tys _ _) => dcr_arg_tys
                                                     end).

Definition dcr_bangs (__arg_135__ : DataConRep) := (match __arg_135__ with
                                                     | Mk_NoDataConRep => (error
                                                                          &"Partial record selector: field `dcr_bangs' has no match in constructor `Mk_NoDataConRep' of type `DataConRep'")
                                                     | (Mk_DCR _ _ _ _ dcr_bangs) => dcr_bangs
                                                   end).

Definition dcr_boxer (__arg_136__ : DataConRep) := (match __arg_136__ with
                                                     | Mk_NoDataConRep => (error
                                                                          &"Partial record selector: field `dcr_boxer' has no match in constructor `Mk_NoDataConRep' of type `DataConRep'")
                                                     | (Mk_DCR _ dcr_boxer _ _ _) => dcr_boxer
                                                   end).

Definition dcr_stricts (__arg_137__ : DataConRep) := (match __arg_137__ with
                                                       | Mk_NoDataConRep => (error
                                                                            &"Partial record selector: field `dcr_stricts' has no match in constructor `Mk_NoDataConRep' of type `DataConRep'")
                                                       | (Mk_DCR _ _ _ dcr_stricts _) => dcr_stricts
                                                     end).

Definition dcr_wrap_id (__arg_138__ : DataConRep) := (match __arg_138__ with
                                                       | Mk_NoDataConRep => (error
                                                                            &"Partial record selector: field `dcr_wrap_id' has no match in constructor `Mk_NoDataConRep' of type `DataConRep'")
                                                       | (Mk_DCR dcr_wrap_id _ _ _ _) => dcr_wrap_id
                                                     end).

Definition chCoercion (__arg_139__ : CoercionHole) := (match __arg_139__ with
                                                        | (Mk_CoercionHole _ chCoercion) => chCoercion
                                                      end).

Definition chUnique (__arg_140__ : CoercionHole) := (match __arg_140__ with
                                                      | (Mk_CoercionHole chUnique _) => chUnique
                                                    end).

Definition n_loc (__arg_141__ : Name) := (match __arg_141__ with
                                           | (Mk_Name _ _ _ n_loc) => n_loc
                                         end).

Definition n_occ (__arg_142__ : Name) := (match __arg_142__ with
                                           | (Mk_Name _ n_occ _ _) => n_occ
                                         end).

Definition n_sort (__arg_143__ : Name) := (match __arg_143__ with
                                            | (Mk_Name n_sort _ _ _) => n_sort
                                          end).

Definition n_uniq (__arg_144__ : Name) := (match __arg_144__ with
                                            | (Mk_Name _ _ n_uniq _) => n_uniq
                                          end).

Definition psArgs (__arg_145__ : PatSyn) := (match __arg_145__ with
                                              | (Mk_MkPatSyn _ _ psArgs _ _ _ _ _ _ _ _ _ _) => psArgs
                                            end).

Definition psArity (__arg_146__ : PatSyn) := (match __arg_146__ with
                                               | (Mk_MkPatSyn _ _ _ psArity _ _ _ _ _ _ _ _ _) => psArity
                                             end).

Definition psBuilder (__arg_147__ : PatSyn) := (match __arg_147__ with
                                                 | (Mk_MkPatSyn _ _ _ _ _ _ _ _ _ _ _ _ psBuilder) => psBuilder
                                               end).

Definition psExTyVars (__arg_148__ : PatSyn) := (match __arg_148__ with
                                                  | (Mk_MkPatSyn _ _ _ _ _ _ _ _ psExTyVars _ _ _ _) => psExTyVars
                                                end).

Definition psFieldLabels (__arg_149__ : PatSyn) := (match __arg_149__ with
                                                     | (Mk_MkPatSyn _ _ _ _ _ psFieldLabels _ _ _ _ _ _ _) =>
                                                       psFieldLabels
                                                   end).

Definition psInfix (__arg_150__ : PatSyn) := (match __arg_150__ with
                                               | (Mk_MkPatSyn _ _ _ _ psInfix _ _ _ _ _ _ _ _) => psInfix
                                             end).

Definition psMatcher (__arg_151__ : PatSyn) := (match __arg_151__ with
                                                 | (Mk_MkPatSyn _ _ _ _ _ _ _ _ _ _ _ psMatcher _) => psMatcher
                                               end).

Definition psName (__arg_152__ : PatSyn) := (match __arg_152__ with
                                              | (Mk_MkPatSyn psName _ _ _ _ _ _ _ _ _ _ _ _) => psName
                                            end).

Definition psOrigResTy (__arg_153__ : PatSyn) := (match __arg_153__ with
                                                   | (Mk_MkPatSyn _ _ _ _ _ _ _ _ _ _ psOrigResTy _ _) => psOrigResTy
                                                 end).

Definition psProvTheta (__arg_154__ : PatSyn) := (match __arg_154__ with
                                                   | (Mk_MkPatSyn _ _ _ _ _ _ _ _ _ psProvTheta _ _ _) => psProvTheta
                                                 end).

Definition psReqTheta (__arg_155__ : PatSyn) := (match __arg_155__ with
                                                  | (Mk_MkPatSyn _ _ _ _ _ _ _ psReqTheta _ _ _ _ _) => psReqTheta
                                                end).

Definition psUnique (__arg_156__ : PatSyn) := (match __arg_156__ with
                                                | (Mk_MkPatSyn _ psUnique _ _ _ _ _ _ _ _ _ _ _) => psUnique
                                              end).

Definition psUnivTyVars (__arg_157__ : PatSyn) := (match __arg_157__ with
                                                    | (Mk_MkPatSyn _ _ _ _ _ _ psUnivTyVars _ _ _ _ _ _) => psUnivTyVars
                                                  end).

Definition mtv_info (__arg_158__ : TcTyVarDetails) := (match __arg_158__ with
                                                        | (Mk_SkolemTv _) => (error
                                                                             &"Partial record selector: field `mtv_info' has no match in constructor `Mk_SkolemTv' of type `TcTyVarDetails'")
                                                        | (Mk_FlatSkol _) => (error
                                                                             &"Partial record selector: field `mtv_info' has no match in constructor `Mk_FlatSkol' of type `TcTyVarDetails'")
                                                        | Mk_RuntimeUnk => (error
                                                                           &"Partial record selector: field `mtv_info' has no match in constructor `Mk_RuntimeUnk' of type `TcTyVarDetails'")
                                                        | (Mk_MetaTv mtv_info _ _) => mtv_info
                                                      end).

Definition mtv_ref (__arg_159__ : TcTyVarDetails) := (match __arg_159__ with
                                                       | (Mk_SkolemTv _) => (error
                                                                            &"Partial record selector: field `mtv_ref' has no match in constructor `Mk_SkolemTv' of type `TcTyVarDetails'")
                                                       | (Mk_FlatSkol _) => (error
                                                                            &"Partial record selector: field `mtv_ref' has no match in constructor `Mk_FlatSkol' of type `TcTyVarDetails'")
                                                       | Mk_RuntimeUnk => (error
                                                                          &"Partial record selector: field `mtv_ref' has no match in constructor `Mk_RuntimeUnk' of type `TcTyVarDetails'")
                                                       | (Mk_MetaTv _ mtv_ref _) => mtv_ref
                                                     end).

Definition mtv_tclvl (__arg_160__ : TcTyVarDetails) := (match __arg_160__ with
                                                         | (Mk_SkolemTv _) => (error
                                                                              &"Partial record selector: field `mtv_tclvl' has no match in constructor `Mk_SkolemTv' of type `TcTyVarDetails'")
                                                         | (Mk_FlatSkol _) => (error
                                                                              &"Partial record selector: field `mtv_tclvl' has no match in constructor `Mk_FlatSkol' of type `TcTyVarDetails'")
                                                         | Mk_RuntimeUnk => (error
                                                                            &"Partial record selector: field `mtv_tclvl' has no match in constructor `Mk_RuntimeUnk' of type `TcTyVarDetails'")
                                                         | (Mk_MetaTv _ _ mtv_tclvl) => mtv_tclvl
                                                       end).

Definition envL (__arg_161__ : RnEnv2) := (match __arg_161__ with
                                            | (Mk_RV2 envL _ _) => envL
                                          end).

Definition envR (__arg_162__ : RnEnv2) := (match __arg_162__ with
                                            | (Mk_RV2 _ envR _) => envR
                                          end).

Definition in_scope (__arg_163__ : RnEnv2) := (match __arg_163__ with
                                                | (Mk_RV2 _ _ in_scope) => in_scope
                                              end).

Definition tcm_covar {env} {m} (__arg_164__ : (TyCoMapper env m)) :=
  (match __arg_164__ with
    | (Mk_TyCoMapper _ _ tcm_covar _ _) => tcm_covar
  end).

Definition tcm_hole {env} {m} (__arg_165__ : (TyCoMapper env m)) :=
  (match __arg_165__ with
    | (Mk_TyCoMapper _ _ _ tcm_hole _) => tcm_hole
  end).

Definition tcm_smart {env} {m} (__arg_166__ : (TyCoMapper env m)) :=
  (match __arg_166__ with
    | (Mk_TyCoMapper tcm_smart _ _ _ _) => tcm_smart
  end).

Definition tcm_tybinder {env} {m} (__arg_167__ : (TyCoMapper env m)) :=
  (match __arg_167__ with
    | (Mk_TyCoMapper _ _ _ _ tcm_tybinder) => tcm_tybinder
  end).

Definition tcm_tyvar {env} {m} (__arg_168__ : (TyCoMapper env m)) :=
  (match __arg_168__ with
    | (Mk_TyCoMapper _ tcm_tyvar _ _ _) => tcm_tyvar
  end).

Definition df_args (__arg_169__ : Unfolding) := (match __arg_169__ with
                                                  | Mk_NoUnfolding => (error
                                                                      &"Partial record selector: field `df_args' has no match in constructor `Mk_NoUnfolding' of type `Unfolding'")
                                                  | (Mk_OtherCon _) => (error
                                                                       &"Partial record selector: field `df_args' has no match in constructor `Mk_OtherCon' of type `Unfolding'")
                                                  | (Mk_DFunUnfolding _ _ df_args) => df_args
                                                  | (Mk_CoreUnfolding _ _ _ _ _ _ _ _) => (error
                                                                                          &"Partial record selector: field `df_args' has no match in constructor `Mk_CoreUnfolding' of type `Unfolding'")
                                                end).

Definition df_bndrs (__arg_170__ : Unfolding) := (match __arg_170__ with
                                                   | Mk_NoUnfolding => (error
                                                                       &"Partial record selector: field `df_bndrs' has no match in constructor `Mk_NoUnfolding' of type `Unfolding'")
                                                   | (Mk_OtherCon _) => (error
                                                                        &"Partial record selector: field `df_bndrs' has no match in constructor `Mk_OtherCon' of type `Unfolding'")
                                                   | (Mk_DFunUnfolding df_bndrs _ _) => df_bndrs
                                                   | (Mk_CoreUnfolding _ _ _ _ _ _ _ _) => (error
                                                                                           &"Partial record selector: field `df_bndrs' has no match in constructor `Mk_CoreUnfolding' of type `Unfolding'")
                                                 end).

Definition df_con (__arg_171__ : Unfolding) := (match __arg_171__ with
                                                 | Mk_NoUnfolding => (error
                                                                     &"Partial record selector: field `df_con' has no match in constructor `Mk_NoUnfolding' of type `Unfolding'")
                                                 | (Mk_OtherCon _) => (error
                                                                      &"Partial record selector: field `df_con' has no match in constructor `Mk_OtherCon' of type `Unfolding'")
                                                 | (Mk_DFunUnfolding _ df_con _) => df_con
                                                 | (Mk_CoreUnfolding _ _ _ _ _ _ _ _) => (error
                                                                                         &"Partial record selector: field `df_con' has no match in constructor `Mk_CoreUnfolding' of type `Unfolding'")
                                               end).

Definition uf_expandable (__arg_172__ : Unfolding) := (match __arg_172__ with
                                                        | Mk_NoUnfolding => (error
                                                                            &"Partial record selector: field `uf_expandable' has no match in constructor `Mk_NoUnfolding' of type `Unfolding'")
                                                        | (Mk_OtherCon _) => (error
                                                                             &"Partial record selector: field `uf_expandable' has no match in constructor `Mk_OtherCon' of type `Unfolding'")
                                                        | (Mk_DFunUnfolding _ _ _) => (error
                                                                                      &"Partial record selector: field `uf_expandable' has no match in constructor `Mk_DFunUnfolding' of type `Unfolding'")
                                                        | (Mk_CoreUnfolding _ _ _ _ _ _ uf_expandable _) =>
                                                          uf_expandable
                                                      end).

Definition uf_guidance (__arg_173__ : Unfolding) := (match __arg_173__ with
                                                      | Mk_NoUnfolding => (error
                                                                          &"Partial record selector: field `uf_guidance' has no match in constructor `Mk_NoUnfolding' of type `Unfolding'")
                                                      | (Mk_OtherCon _) => (error
                                                                           &"Partial record selector: field `uf_guidance' has no match in constructor `Mk_OtherCon' of type `Unfolding'")
                                                      | (Mk_DFunUnfolding _ _ _) => (error
                                                                                    &"Partial record selector: field `uf_guidance' has no match in constructor `Mk_DFunUnfolding' of type `Unfolding'")
                                                      | (Mk_CoreUnfolding _ _ _ _ _ _ _ uf_guidance) => uf_guidance
                                                    end).

Definition uf_is_conlike (__arg_174__ : Unfolding) := (match __arg_174__ with
                                                        | Mk_NoUnfolding => (error
                                                                            &"Partial record selector: field `uf_is_conlike' has no match in constructor `Mk_NoUnfolding' of type `Unfolding'")
                                                        | (Mk_OtherCon _) => (error
                                                                             &"Partial record selector: field `uf_is_conlike' has no match in constructor `Mk_OtherCon' of type `Unfolding'")
                                                        | (Mk_DFunUnfolding _ _ _) => (error
                                                                                      &"Partial record selector: field `uf_is_conlike' has no match in constructor `Mk_DFunUnfolding' of type `Unfolding'")
                                                        | (Mk_CoreUnfolding _ _ _ _ uf_is_conlike _ _ _) =>
                                                          uf_is_conlike
                                                      end).

Definition uf_is_top (__arg_175__ : Unfolding) := (match __arg_175__ with
                                                    | Mk_NoUnfolding => (error
                                                                        &"Partial record selector: field `uf_is_top' has no match in constructor `Mk_NoUnfolding' of type `Unfolding'")
                                                    | (Mk_OtherCon _) => (error
                                                                         &"Partial record selector: field `uf_is_top' has no match in constructor `Mk_OtherCon' of type `Unfolding'")
                                                    | (Mk_DFunUnfolding _ _ _) => (error
                                                                                  &"Partial record selector: field `uf_is_top' has no match in constructor `Mk_DFunUnfolding' of type `Unfolding'")
                                                    | (Mk_CoreUnfolding _ _ uf_is_top _ _ _ _ _) => uf_is_top
                                                  end).

Definition uf_is_value (__arg_176__ : Unfolding) := (match __arg_176__ with
                                                      | Mk_NoUnfolding => (error
                                                                          &"Partial record selector: field `uf_is_value' has no match in constructor `Mk_NoUnfolding' of type `Unfolding'")
                                                      | (Mk_OtherCon _) => (error
                                                                           &"Partial record selector: field `uf_is_value' has no match in constructor `Mk_OtherCon' of type `Unfolding'")
                                                      | (Mk_DFunUnfolding _ _ _) => (error
                                                                                    &"Partial record selector: field `uf_is_value' has no match in constructor `Mk_DFunUnfolding' of type `Unfolding'")
                                                      | (Mk_CoreUnfolding _ _ _ uf_is_value _ _ _ _) => uf_is_value
                                                    end).

Definition uf_is_work_free (__arg_177__ : Unfolding) := (match __arg_177__ with
                                                          | Mk_NoUnfolding => (error
                                                                              &"Partial record selector: field `uf_is_work_free' has no match in constructor `Mk_NoUnfolding' of type `Unfolding'")
                                                          | (Mk_OtherCon _) => (error
                                                                               &"Partial record selector: field `uf_is_work_free' has no match in constructor `Mk_OtherCon' of type `Unfolding'")
                                                          | (Mk_DFunUnfolding _ _ _) => (error
                                                                                        &"Partial record selector: field `uf_is_work_free' has no match in constructor `Mk_DFunUnfolding' of type `Unfolding'")
                                                          | (Mk_CoreUnfolding _ _ _ _ _ uf_is_work_free _ _) =>
                                                            uf_is_work_free
                                                        end).

Definition uf_src (__arg_178__ : Unfolding) := (match __arg_178__ with
                                                 | Mk_NoUnfolding => (error
                                                                     &"Partial record selector: field `uf_src' has no match in constructor `Mk_NoUnfolding' of type `Unfolding'")
                                                 | (Mk_OtherCon _) => (error
                                                                      &"Partial record selector: field `uf_src' has no match in constructor `Mk_OtherCon' of type `Unfolding'")
                                                 | (Mk_DFunUnfolding _ _ _) => (error
                                                                               &"Partial record selector: field `uf_src' has no match in constructor `Mk_DFunUnfolding' of type `Unfolding'")
                                                 | (Mk_CoreUnfolding _ uf_src _ _ _ _ _ _) => uf_src
                                               end).

Definition uf_tmpl (__arg_179__ : Unfolding) := (match __arg_179__ with
                                                  | Mk_NoUnfolding => (error
                                                                      &"Partial record selector: field `uf_tmpl' has no match in constructor `Mk_NoUnfolding' of type `Unfolding'")
                                                  | (Mk_OtherCon _) => (error
                                                                       &"Partial record selector: field `uf_tmpl' has no match in constructor `Mk_OtherCon' of type `Unfolding'")
                                                  | (Mk_DFunUnfolding _ _ _) => (error
                                                                                &"Partial record selector: field `uf_tmpl' has no match in constructor `Mk_DFunUnfolding' of type `Unfolding'")
                                                  | (Mk_CoreUnfolding uf_tmpl _ _ _ _ _ _ _) => uf_tmpl
                                                end).

Definition ru_act (__arg_180__ : CoreRule) := (match __arg_180__ with
                                                | (Mk_Rule _ ru_act _ _ _ _ _ _ _ _ _) => ru_act
                                                | (Mk_BuiltinRule _ _ _ _) => (error
                                                                              &"Partial record selector: field `ru_act' has no match in constructor `Mk_BuiltinRule' of type `CoreRule'")
                                              end).

Definition ru_args (__arg_181__ : CoreRule) := (match __arg_181__ with
                                                 | (Mk_Rule _ _ _ _ _ ru_args _ _ _ _ _) => ru_args
                                                 | (Mk_BuiltinRule _ _ _ _) => (error
                                                                               &"Partial record selector: field `ru_args' has no match in constructor `Mk_BuiltinRule' of type `CoreRule'")
                                               end).

Definition ru_auto (__arg_182__ : CoreRule) := (match __arg_182__ with
                                                 | (Mk_Rule _ _ _ _ _ _ _ ru_auto _ _ _) => ru_auto
                                                 | (Mk_BuiltinRule _ _ _ _) => (error
                                                                               &"Partial record selector: field `ru_auto' has no match in constructor `Mk_BuiltinRule' of type `CoreRule'")
                                               end).

Definition ru_bndrs (__arg_183__ : CoreRule) := (match __arg_183__ with
                                                  | (Mk_Rule _ _ _ _ ru_bndrs _ _ _ _ _ _) => ru_bndrs
                                                  | (Mk_BuiltinRule _ _ _ _) => (error
                                                                                &"Partial record selector: field `ru_bndrs' has no match in constructor `Mk_BuiltinRule' of type `CoreRule'")
                                                end).

Definition ru_fn (__arg_184__ : CoreRule) := (match __arg_184__ with
                                               | (Mk_Rule _ _ ru_fn _ _ _ _ _ _ _ _) => ru_fn
                                               | (Mk_BuiltinRule _ ru_fn _ _) => ru_fn
                                             end).

Definition ru_local (__arg_185__ : CoreRule) := (match __arg_185__ with
                                                  | (Mk_Rule _ _ _ _ _ _ _ _ _ _ ru_local) => ru_local
                                                  | (Mk_BuiltinRule _ _ _ _) => (error
                                                                                &"Partial record selector: field `ru_local' has no match in constructor `Mk_BuiltinRule' of type `CoreRule'")
                                                end).

Definition ru_name (__arg_186__ : CoreRule) := (match __arg_186__ with
                                                 | (Mk_Rule ru_name _ _ _ _ _ _ _ _ _ _) => ru_name
                                                 | (Mk_BuiltinRule ru_name _ _ _) => ru_name
                                               end).

Definition ru_nargs (__arg_187__ : CoreRule) := (match __arg_187__ with
                                                  | (Mk_Rule _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                       &"Partial record selector: field `ru_nargs' has no match in constructor `Mk_Rule' of type `CoreRule'")
                                                  | (Mk_BuiltinRule _ _ ru_nargs _) => ru_nargs
                                                end).

Definition ru_origin (__arg_188__ : CoreRule) := (match __arg_188__ with
                                                   | (Mk_Rule _ _ _ _ _ _ _ _ ru_origin _ _) => ru_origin
                                                   | (Mk_BuiltinRule _ _ _ _) => (error
                                                                                 &"Partial record selector: field `ru_origin' has no match in constructor `Mk_BuiltinRule' of type `CoreRule'")
                                                 end).

Definition ru_orphan (__arg_189__ : CoreRule) := (match __arg_189__ with
                                                   | (Mk_Rule _ _ _ _ _ _ _ _ _ ru_orphan _) => ru_orphan
                                                   | (Mk_BuiltinRule _ _ _ _) => (error
                                                                                 &"Partial record selector: field `ru_orphan' has no match in constructor `Mk_BuiltinRule' of type `CoreRule'")
                                                 end).

Definition ru_rhs (__arg_190__ : CoreRule) := (match __arg_190__ with
                                                | (Mk_Rule _ _ _ _ _ _ ru_rhs _ _ _ _) => ru_rhs
                                                | (Mk_BuiltinRule _ _ _ _) => (error
                                                                              &"Partial record selector: field `ru_rhs' has no match in constructor `Mk_BuiltinRule' of type `CoreRule'")
                                              end).

Definition ru_rough (__arg_191__ : CoreRule) := (match __arg_191__ with
                                                  | (Mk_Rule _ _ _ ru_rough _ _ _ _ _ _ _) => ru_rough
                                                  | (Mk_BuiltinRule _ _ _ _) => (error
                                                                                &"Partial record selector: field `ru_rough' has no match in constructor `Mk_BuiltinRule' of type `CoreRule'")
                                                end).

Definition ru_try (__arg_192__ : CoreRule) := (match __arg_192__ with
                                                | (Mk_Rule _ _ _ _ _ _ _ _ _ _ _) => (error
                                                                                     &"Partial record selector: field `ru_try' has no match in constructor `Mk_Rule' of type `CoreRule'")
                                                | (Mk_BuiltinRule _ _ _ ru_try) => ru_try
                                              end).

Definition re_base (__arg_193__ : RuleEnv) := (match __arg_193__ with
                                                | (Mk_RuleEnv re_base _) => re_base
                                              end).

Definition re_visible_orphs (__arg_194__ : RuleEnv) := (match __arg_194__ with
                                                         | (Mk_RuleEnv _ re_visible_orphs) => re_visible_orphs
                                                       end).

Definition inl_act (__arg_195__ : InlinePragma) := (match __arg_195__ with
                                                     | (Mk_InlinePragma _ _ _ inl_act _) => inl_act
                                                   end).

Definition inl_inline (__arg_196__ : InlinePragma) := (match __arg_196__ with
                                                        | (Mk_InlinePragma _ inl_inline _ _ _) => inl_inline
                                                      end).

Definition inl_rule (__arg_197__ : InlinePragma) := (match __arg_197__ with
                                                      | (Mk_InlinePragma _ _ _ _ inl_rule) => inl_rule
                                                    end).

Definition inl_sat (__arg_198__ : InlinePragma) := (match __arg_198__ with
                                                     | (Mk_InlinePragma _ _ inl_sat _ _) => inl_sat
                                                   end).

Definition inl_src (__arg_199__ : InlinePragma) := (match __arg_199__ with
                                                     | (Mk_InlinePragma inl_src _ _ _ _) => inl_src
                                                   end).
