{-# LANGUAGE TemplateHaskell, StandaloneDeriving, DeriveDataTypeable, DeriveGeneric #-}

module CoqCoreBind where

import qualified Prelude
import qualified Data.ByteString
import qualified Data.Array
import qualified Data.IntMap
import qualified FastString

import qualified Data.Data    as Data
import qualified GHC.Generics as Generics

import qualified Prelude             as P
import qualified Control.Monad       as M
import qualified Language.Haskell.TH as TH

data Width =
   Mk_W8
 | Mk_W16
 | Mk_W32
 | Mk_W64
 | Mk_W80
 | Mk_W128
 | Mk_W256
 | Mk_W512

data VisibilityFlag =
   Mk_Visible
 | Mk_Specified
 | Mk_Invisible

data UnitId =
   Mk_PId FastString.FastString

data Unique =
   Mk_MkUnique Prelude.Int

data UniqFM ele =
   Mk_UFM (Data.IntMap.IntMap ele)

data TyLit =
   Mk_NumTyLit Prelude.Integer
 | Mk_StrTyLit FastString.FastString

data TupleSort =
   Mk_BoxedTuple
 | Mk_UnboxedTuple
 | Mk_ConstraintTuple

type TickBoxId = Prelude.Int

data TcLevel =
   Mk_TcLevel Prelude.Int

data StrictnessMark =
   Mk_MarkedStrict
 | Mk_NotMarkedStrict

data SrcUnpackedness =
   Mk_SrcUnpack
 | Mk_SrcNoUnpack
 | Mk_NoSrcUnpack

data SrcStrictness =
   Mk_SrcLazy
 | Mk_SrcStrict
 | Mk_NoSrcStrict

type SourceText = Prelude.String

data Safety =
   Mk_PlaySafe
 | Mk_PlayInterruptible
 | Mk_PlayRisky

data Role =
   Mk_Nominal
 | Mk_Representational
 | Mk_Phantom

data RecFlag =
   Mk_Recursive
 | Mk_NonRecursive

data RealSrcSpan =
   Mk_RealSrcSpan' FastString.FastString Prelude.Int Prelude.Int Prelude.Int 
 Prelude.Int

data SrcSpan =
   Mk_RealSrcSpan RealSrcSpan
 | Mk_UnhelpfulSpan FastString.FastString

data PrimOpVecCat =
   Mk_IntVec
 | Mk_WordVec
 | Mk_FloatVec

data NameSpace =
   Mk_VarName
 | Mk_DataName
 | Mk_TvName
 | Mk_TcClsName

data OccName =
   Mk_OccName NameSpace FastString.FastString

data ModuleName =
   Mk_ModuleName FastString.FastString

data Module =
   Mk_Module UnitId ModuleName

data TickBoxOp =
   Mk_TickBox Module TickBoxId

data MetaInfo =
   Mk_TauTv
 | Mk_SigTv
 | Mk_FlatMetaTv

type Length = Prelude.Int

data PrimOp =
   Mk_CharGtOp
 | Mk_CharGeOp
 | Mk_CharEqOp
 | Mk_CharNeOp
 | Mk_CharLtOp
 | Mk_CharLeOp
 | Mk_OrdOp
 | Mk_IntAddOp
 | Mk_IntSubOp
 | Mk_IntMulOp
 | Mk_IntMulMayOfloOp
 | Mk_IntQuotOp
 | Mk_IntRemOp
 | Mk_IntQuotRemOp
 | Mk_AndIOp
 | Mk_OrIOp
 | Mk_XorIOp
 | Mk_NotIOp
 | Mk_IntNegOp
 | Mk_IntAddCOp
 | Mk_IntSubCOp
 | Mk_IntGtOp
 | Mk_IntGeOp
 | Mk_IntEqOp
 | Mk_IntNeOp
 | Mk_IntLtOp
 | Mk_IntLeOp
 | Mk_ChrOp
 | Mk_Int2WordOp
 | Mk_Int2FloatOp
 | Mk_Int2DoubleOp
 | Mk_Word2FloatOp
 | Mk_Word2DoubleOp
 | Mk_ISllOp
 | Mk_ISraOp
 | Mk_ISrlOp
 | Mk_WordAddOp
 | Mk_WordSubCOp
 | Mk_WordAdd2Op
 | Mk_WordSubOp
 | Mk_WordMulOp
 | Mk_WordMul2Op
 | Mk_WordQuotOp
 | Mk_WordRemOp
 | Mk_WordQuotRemOp
 | Mk_WordQuotRem2Op
 | Mk_AndOp
 | Mk_OrOp
 | Mk_XorOp
 | Mk_NotOp
 | Mk_SllOp
 | Mk_SrlOp
 | Mk_Word2IntOp
 | Mk_WordGtOp
 | Mk_WordGeOp
 | Mk_WordEqOp
 | Mk_WordNeOp
 | Mk_WordLtOp
 | Mk_WordLeOp
 | Mk_PopCnt8Op
 | Mk_PopCnt16Op
 | Mk_PopCnt32Op
 | Mk_PopCnt64Op
 | Mk_PopCntOp
 | Mk_Clz8Op
 | Mk_Clz16Op
 | Mk_Clz32Op
 | Mk_Clz64Op
 | Mk_ClzOp
 | Mk_Ctz8Op
 | Mk_Ctz16Op
 | Mk_Ctz32Op
 | Mk_Ctz64Op
 | Mk_CtzOp
 | Mk_BSwap16Op
 | Mk_BSwap32Op
 | Mk_BSwap64Op
 | Mk_BSwapOp
 | Mk_Narrow8IntOp
 | Mk_Narrow16IntOp
 | Mk_Narrow32IntOp
 | Mk_Narrow8WordOp
 | Mk_Narrow16WordOp
 | Mk_Narrow32WordOp
 | Mk_DoubleGtOp
 | Mk_DoubleGeOp
 | Mk_DoubleEqOp
 | Mk_DoubleNeOp
 | Mk_DoubleLtOp
 | Mk_DoubleLeOp
 | Mk_DoubleAddOp
 | Mk_DoubleSubOp
 | Mk_DoubleMulOp
 | Mk_DoubleDivOp
 | Mk_DoubleNegOp
 | Mk_Double2IntOp
 | Mk_Double2FloatOp
 | Mk_DoubleExpOp
 | Mk_DoubleLogOp
 | Mk_DoubleSqrtOp
 | Mk_DoubleSinOp
 | Mk_DoubleCosOp
 | Mk_DoubleTanOp
 | Mk_DoubleAsinOp
 | Mk_DoubleAcosOp
 | Mk_DoubleAtanOp
 | Mk_DoubleSinhOp
 | Mk_DoubleCoshOp
 | Mk_DoubleTanhOp
 | Mk_DoublePowerOp
 | Mk_DoubleDecode_2IntOp
 | Mk_DoubleDecode_Int64Op
 | Mk_FloatGtOp
 | Mk_FloatGeOp
 | Mk_FloatEqOp
 | Mk_FloatNeOp
 | Mk_FloatLtOp
 | Mk_FloatLeOp
 | Mk_FloatAddOp
 | Mk_FloatSubOp
 | Mk_FloatMulOp
 | Mk_FloatDivOp
 | Mk_FloatNegOp
 | Mk_Float2IntOp
 | Mk_FloatExpOp
 | Mk_FloatLogOp
 | Mk_FloatSqrtOp
 | Mk_FloatSinOp
 | Mk_FloatCosOp
 | Mk_FloatTanOp
 | Mk_FloatAsinOp
 | Mk_FloatAcosOp
 | Mk_FloatAtanOp
 | Mk_FloatSinhOp
 | Mk_FloatCoshOp
 | Mk_FloatTanhOp
 | Mk_FloatPowerOp
 | Mk_Float2DoubleOp
 | Mk_FloatDecode_IntOp
 | Mk_NewArrayOp
 | Mk_SameMutableArrayOp
 | Mk_ReadArrayOp
 | Mk_WriteArrayOp
 | Mk_SizeofArrayOp
 | Mk_SizeofMutableArrayOp
 | Mk_IndexArrayOp
 | Mk_UnsafeFreezeArrayOp
 | Mk_UnsafeThawArrayOp
 | Mk_CopyArrayOp
 | Mk_CopyMutableArrayOp
 | Mk_CloneArrayOp
 | Mk_CloneMutableArrayOp
 | Mk_FreezeArrayOp
 | Mk_ThawArrayOp
 | Mk_CasArrayOp
 | Mk_NewSmallArrayOp
 | Mk_SameSmallMutableArrayOp
 | Mk_ReadSmallArrayOp
 | Mk_WriteSmallArrayOp
 | Mk_SizeofSmallArrayOp
 | Mk_SizeofSmallMutableArrayOp
 | Mk_IndexSmallArrayOp
 | Mk_UnsafeFreezeSmallArrayOp
 | Mk_UnsafeThawSmallArrayOp
 | Mk_CopySmallArrayOp
 | Mk_CopySmallMutableArrayOp
 | Mk_CloneSmallArrayOp
 | Mk_CloneSmallMutableArrayOp
 | Mk_FreezeSmallArrayOp
 | Mk_ThawSmallArrayOp
 | Mk_CasSmallArrayOp
 | Mk_NewByteArrayOp_Char
 | Mk_NewPinnedByteArrayOp_Char
 | Mk_NewAlignedPinnedByteArrayOp_Char
 | Mk_ByteArrayContents_Char
 | Mk_SameMutableByteArrayOp
 | Mk_ShrinkMutableByteArrayOp_Char
 | Mk_ResizeMutableByteArrayOp_Char
 | Mk_UnsafeFreezeByteArrayOp
 | Mk_SizeofByteArrayOp
 | Mk_SizeofMutableByteArrayOp
 | Mk_GetSizeofMutableByteArrayOp
 | Mk_IndexByteArrayOp_Char
 | Mk_IndexByteArrayOp_WideChar
 | Mk_IndexByteArrayOp_Int
 | Mk_IndexByteArrayOp_Word
 | Mk_IndexByteArrayOp_Addr
 | Mk_IndexByteArrayOp_Float
 | Mk_IndexByteArrayOp_Double
 | Mk_IndexByteArrayOp_StablePtr
 | Mk_IndexByteArrayOp_Int8
 | Mk_IndexByteArrayOp_Int16
 | Mk_IndexByteArrayOp_Int32
 | Mk_IndexByteArrayOp_Int64
 | Mk_IndexByteArrayOp_Word8
 | Mk_IndexByteArrayOp_Word16
 | Mk_IndexByteArrayOp_Word32
 | Mk_IndexByteArrayOp_Word64
 | Mk_ReadByteArrayOp_Char
 | Mk_ReadByteArrayOp_WideChar
 | Mk_ReadByteArrayOp_Int
 | Mk_ReadByteArrayOp_Word
 | Mk_ReadByteArrayOp_Addr
 | Mk_ReadByteArrayOp_Float
 | Mk_ReadByteArrayOp_Double
 | Mk_ReadByteArrayOp_StablePtr
 | Mk_ReadByteArrayOp_Int8
 | Mk_ReadByteArrayOp_Int16
 | Mk_ReadByteArrayOp_Int32
 | Mk_ReadByteArrayOp_Int64
 | Mk_ReadByteArrayOp_Word8
 | Mk_ReadByteArrayOp_Word16
 | Mk_ReadByteArrayOp_Word32
 | Mk_ReadByteArrayOp_Word64
 | Mk_WriteByteArrayOp_Char
 | Mk_WriteByteArrayOp_WideChar
 | Mk_WriteByteArrayOp_Int
 | Mk_WriteByteArrayOp_Word
 | Mk_WriteByteArrayOp_Addr
 | Mk_WriteByteArrayOp_Float
 | Mk_WriteByteArrayOp_Double
 | Mk_WriteByteArrayOp_StablePtr
 | Mk_WriteByteArrayOp_Int8
 | Mk_WriteByteArrayOp_Int16
 | Mk_WriteByteArrayOp_Int32
 | Mk_WriteByteArrayOp_Int64
 | Mk_WriteByteArrayOp_Word8
 | Mk_WriteByteArrayOp_Word16
 | Mk_WriteByteArrayOp_Word32
 | Mk_WriteByteArrayOp_Word64
 | Mk_CopyByteArrayOp
 | Mk_CopyMutableByteArrayOp
 | Mk_CopyByteArrayToAddrOp
 | Mk_CopyMutableByteArrayToAddrOp
 | Mk_CopyAddrToByteArrayOp
 | Mk_SetByteArrayOp
 | Mk_AtomicReadByteArrayOp_Int
 | Mk_AtomicWriteByteArrayOp_Int
 | Mk_CasByteArrayOp_Int
 | Mk_FetchAddByteArrayOp_Int
 | Mk_FetchSubByteArrayOp_Int
 | Mk_FetchAndByteArrayOp_Int
 | Mk_FetchNandByteArrayOp_Int
 | Mk_FetchOrByteArrayOp_Int
 | Mk_FetchXorByteArrayOp_Int
 | Mk_NewArrayArrayOp
 | Mk_SameMutableArrayArrayOp
 | Mk_UnsafeFreezeArrayArrayOp
 | Mk_SizeofArrayArrayOp
 | Mk_SizeofMutableArrayArrayOp
 | Mk_IndexArrayArrayOp_ByteArray
 | Mk_IndexArrayArrayOp_ArrayArray
 | Mk_ReadArrayArrayOp_ByteArray
 | Mk_ReadArrayArrayOp_MutableByteArray
 | Mk_ReadArrayArrayOp_ArrayArray
 | Mk_ReadArrayArrayOp_MutableArrayArray
 | Mk_WriteArrayArrayOp_ByteArray
 | Mk_WriteArrayArrayOp_MutableByteArray
 | Mk_WriteArrayArrayOp_ArrayArray
 | Mk_WriteArrayArrayOp_MutableArrayArray
 | Mk_CopyArrayArrayOp
 | Mk_CopyMutableArrayArrayOp
 | Mk_AddrAddOp
 | Mk_AddrSubOp
 | Mk_AddrRemOp
 | Mk_Addr2IntOp
 | Mk_Int2AddrOp
 | Mk_AddrGtOp
 | Mk_AddrGeOp
 | Mk_AddrEqOp
 | Mk_AddrNeOp
 | Mk_AddrLtOp
 | Mk_AddrLeOp
 | Mk_IndexOffAddrOp_Char
 | Mk_IndexOffAddrOp_WideChar
 | Mk_IndexOffAddrOp_Int
 | Mk_IndexOffAddrOp_Word
 | Mk_IndexOffAddrOp_Addr
 | Mk_IndexOffAddrOp_Float
 | Mk_IndexOffAddrOp_Double
 | Mk_IndexOffAddrOp_StablePtr
 | Mk_IndexOffAddrOp_Int8
 | Mk_IndexOffAddrOp_Int16
 | Mk_IndexOffAddrOp_Int32
 | Mk_IndexOffAddrOp_Int64
 | Mk_IndexOffAddrOp_Word8
 | Mk_IndexOffAddrOp_Word16
 | Mk_IndexOffAddrOp_Word32
 | Mk_IndexOffAddrOp_Word64
 | Mk_ReadOffAddrOp_Char
 | Mk_ReadOffAddrOp_WideChar
 | Mk_ReadOffAddrOp_Int
 | Mk_ReadOffAddrOp_Word
 | Mk_ReadOffAddrOp_Addr
 | Mk_ReadOffAddrOp_Float
 | Mk_ReadOffAddrOp_Double
 | Mk_ReadOffAddrOp_StablePtr
 | Mk_ReadOffAddrOp_Int8
 | Mk_ReadOffAddrOp_Int16
 | Mk_ReadOffAddrOp_Int32
 | Mk_ReadOffAddrOp_Int64
 | Mk_ReadOffAddrOp_Word8
 | Mk_ReadOffAddrOp_Word16
 | Mk_ReadOffAddrOp_Word32
 | Mk_ReadOffAddrOp_Word64
 | Mk_WriteOffAddrOp_Char
 | Mk_WriteOffAddrOp_WideChar
 | Mk_WriteOffAddrOp_Int
 | Mk_WriteOffAddrOp_Word
 | Mk_WriteOffAddrOp_Addr
 | Mk_WriteOffAddrOp_Float
 | Mk_WriteOffAddrOp_Double
 | Mk_WriteOffAddrOp_StablePtr
 | Mk_WriteOffAddrOp_Int8
 | Mk_WriteOffAddrOp_Int16
 | Mk_WriteOffAddrOp_Int32
 | Mk_WriteOffAddrOp_Int64
 | Mk_WriteOffAddrOp_Word8
 | Mk_WriteOffAddrOp_Word16
 | Mk_WriteOffAddrOp_Word32
 | Mk_WriteOffAddrOp_Word64
 | Mk_NewMutVarOp
 | Mk_ReadMutVarOp
 | Mk_WriteMutVarOp
 | Mk_SameMutVarOp
 | Mk_AtomicModifyMutVarOp
 | Mk_CasMutVarOp
 | Mk_CatchOp
 | Mk_RaiseOp
 | Mk_RaiseIOOp
 | Mk_MaskAsyncExceptionsOp
 | Mk_MaskUninterruptibleOp
 | Mk_UnmaskAsyncExceptionsOp
 | Mk_MaskStatus
 | Mk_AtomicallyOp
 | Mk_RetryOp
 | Mk_CatchRetryOp
 | Mk_CatchSTMOp
 | Mk_CheckOp
 | Mk_NewTVarOp
 | Mk_ReadTVarOp
 | Mk_ReadTVarIOOp
 | Mk_WriteTVarOp
 | Mk_SameTVarOp
 | Mk_NewMVarOp
 | Mk_TakeMVarOp
 | Mk_TryTakeMVarOp
 | Mk_PutMVarOp
 | Mk_TryPutMVarOp
 | Mk_ReadMVarOp
 | Mk_TryReadMVarOp
 | Mk_SameMVarOp
 | Mk_IsEmptyMVarOp
 | Mk_DelayOp
 | Mk_WaitReadOp
 | Mk_WaitWriteOp
 | Mk_ForkOp
 | Mk_ForkOnOp
 | Mk_KillThreadOp
 | Mk_YieldOp
 | Mk_MyThreadIdOp
 | Mk_LabelThreadOp
 | Mk_IsCurrentThreadBoundOp
 | Mk_NoDuplicateOp
 | Mk_ThreadStatusOp
 | Mk_MkWeakOp
 | Mk_MkWeakNoFinalizerOp
 | Mk_AddCFinalizerToWeakOp
 | Mk_DeRefWeakOp
 | Mk_FinalizeWeakOp
 | Mk_TouchOp
 | Mk_MakeStablePtrOp
 | Mk_DeRefStablePtrOp
 | Mk_EqStablePtrOp
 | Mk_MakeStableNameOp
 | Mk_EqStableNameOp
 | Mk_StableNameToIntOp
 | Mk_ReallyUnsafePtrEqualityOp
 | Mk_ParOp
 | Mk_SparkOp
 | Mk_SeqOp
 | Mk_GetSparkOp
 | Mk_NumSparks
 | Mk_DataToTagOp
 | Mk_TagToEnumOp
 | Mk_AddrToAnyOp
 | Mk_MkApUpd0_Op
 | Mk_NewBCOOp
 | Mk_UnpackClosureOp
 | Mk_GetApStackValOp
 | Mk_GetCCSOfOp
 | Mk_GetCurrentCCSOp
 | Mk_ClearCCSOp
 | Mk_TraceEventOp
 | Mk_TraceMarkerOp
 | Mk_VecBroadcastOp PrimOpVecCat Length Width
 | Mk_VecPackOp PrimOpVecCat Length Width
 | Mk_VecUnpackOp PrimOpVecCat Length Width
 | Mk_VecInsertOp PrimOpVecCat Length Width
 | Mk_VecAddOp PrimOpVecCat Length Width
 | Mk_VecSubOp PrimOpVecCat Length Width
 | Mk_VecMulOp PrimOpVecCat Length Width
 | Mk_VecDivOp PrimOpVecCat Length Width
 | Mk_VecQuotOp PrimOpVecCat Length Width
 | Mk_VecRemOp PrimOpVecCat Length Width
 | Mk_VecNegOp PrimOpVecCat Length Width
 | Mk_VecIndexByteArrayOp PrimOpVecCat Length Width
 | Mk_VecReadByteArrayOp PrimOpVecCat Length Width
 | Mk_VecWriteByteArrayOp PrimOpVecCat Length Width
 | Mk_VecIndexOffAddrOp PrimOpVecCat Length Width
 | Mk_VecReadOffAddrOp PrimOpVecCat Length Width
 | Mk_VecWriteOffAddrOp PrimOpVecCat Length Width
 | Mk_VecIndexScalarByteArrayOp PrimOpVecCat Length Width
 | Mk_VecReadScalarByteArrayOp PrimOpVecCat Length Width
 | Mk_VecWriteScalarByteArrayOp PrimOpVecCat Length Width
 | Mk_VecIndexScalarOffAddrOp PrimOpVecCat Length Width
 | Mk_VecReadScalarOffAddrOp PrimOpVecCat Length Width
 | Mk_VecWriteScalarOffAddrOp PrimOpVecCat Length Width
 | Mk_PrefetchByteArrayOp3
 | Mk_PrefetchMutableByteArrayOp3
 | Mk_PrefetchAddrOp3
 | Mk_PrefetchValueOp3
 | Mk_PrefetchByteArrayOp2
 | Mk_PrefetchMutableByteArrayOp2
 | Mk_PrefetchAddrOp2
 | Mk_PrefetchValueOp2
 | Mk_PrefetchByteArrayOp1
 | Mk_PrefetchMutableByteArrayOp1
 | Mk_PrefetchAddrOp1
 | Mk_PrefetchValueOp1
 | Mk_PrefetchByteArrayOp0
 | Mk_PrefetchMutableByteArrayOp0
 | Mk_PrefetchAddrOp0
 | Mk_PrefetchValueOp0

data LeftOrRight =
   Mk_CLeft
 | Mk_CRight

data IsCafCC =
   Mk_NotCafCC
 | Mk_CafCC

data Injectivity =
   Mk_NotInjective
 | Mk_Injective ([] Prelude.Bool)

data HsSrcBang =
   Mk_HsSrcBang (Prelude.Maybe SourceText) SrcUnpackedness SrcStrictness

data Header =
   Mk_Header SourceText FastString.FastString

data GenLocated l e =
   Mk_L l e

type Located e = GenLocated SrcSpan e

data FunctionOrData =
   Mk_IsFunction
 | Mk_IsData

type FunDep a = (,) ([] a) ([] a)

type FieldLabelString = FastString.FastString

data FieldLbl a =
   Mk_FieldLabel FieldLabelString Prelude.Bool a

type FastStringEnv a = UniqFM a

data ExportFlag =
   Mk_NotExported
 | Mk_Exported

data IdScope =
   Mk_GlobalId
 | Mk_LocalId ExportFlag

data DefMethSpec ty =
   Mk_VanillaDM
 | Mk_GenericDM ty

type ConTag = Prelude.Int

type CcName = FastString.FastString

data CostCentre =
   Mk_NormalCC Prelude.Int CcName Module SrcSpan IsCafCC
 | Mk_AllCafsCC Module SrcSpan

data Tickish id =
   Mk_ProfNote CostCentre Prelude.Bool Prelude.Bool
 | Mk_HpcTick Module Prelude.Int
 | Mk_Breakpoint Prelude.Int ([] id)
 | Mk_SourceNote RealSrcSpan Prelude.String

data CType =
   Mk_CType SourceText (Prelude.Maybe Header) ((,) SourceText
                                              FastString.FastString)

type CLabelString = FastString.FastString

data CCallTarget =
   Mk_StaticTarget SourceText CLabelString (Prelude.Maybe UnitId) Prelude.Bool
 | Mk_DynamicTarget

data CCallConv =
   Mk_CCallConv
 | Mk_CApiConv
 | Mk_StdCallConv
 | Mk_PrimCallConv
 | Mk_JavaScriptCallConv

data CCallSpec =
   Mk_CCallSpec CCallTarget CCallConv Safety

data ForeignCall =
   Mk_CCall CCallSpec

data BuiltInSyntax =
   Mk_BuiltInSyntax
 | Mk_UserSyntax

type BranchIndex = Prelude.Int

data BranchFlag =
   Mk_Branched
 | Mk_Unbranched

data BooleanFormula a =
   Mk_BFVar a
 | Mk_And ([] (Located (BooleanFormula a)))
 | Mk_Or ([] (Located (BooleanFormula a)))
 | Mk_Parens (Located (BooleanFormula a))

type Arity = Prelude.Int

data AlgTyConFlav =
   Mk_VanillaAlgTyCon Name
 | Mk_UnboxedAlgTyCon
 | Mk_ClassTyCon Class Name
 | Mk_DataFamInstTyCon CoAxiom TyCon ([] Type_)
data Class =
   Mk_Class TyCon Name Unique ([] Var) ([] (FunDep Var)) ([] Type_) ([] Var) 
 ([] ClassATItem) ([]
                  ((,) Var (Prelude.Maybe ((,) Name (DefMethSpec Type_))))) 
 (BooleanFormula Name)
data ClassATItem =
   Mk_ATI TyCon (Prelude.Maybe ((,) Type_ SrcSpan))
data TyCon =
   Mk_FunTyCon Unique Name ([] TyBinder) Type_ Type_ Arity Name
 | Mk_AlgTyCon Unique Name ([] TyBinder) Type_ Type_ Arity ([] Var) ([] Role) 
 (Prelude.Maybe CType) Prelude.Bool ([] Type_) AlgTyConRhs (FastStringEnv
                                                           (FieldLbl Name)) 
 RecFlag AlgTyConFlav
 | Mk_SynonymTyCon Unique Name ([] TyBinder) Type_ Type_ Arity ([] Var) 
 ([] Role) Type_
 | Mk_FamilyTyCon Unique Name ([] TyBinder) Type_ Type_ Arity ([] Var) 
 (Prelude.Maybe Name) FamTyConFlav (Prelude.Maybe Class) Injectivity
 | Mk_PrimTyCon Unique Name ([] TyBinder) Type_ Type_ Arity ([] Role) 
 Prelude.Bool (Prelude.Maybe Name)
 | Mk_PromotedDataCon Unique Name Arity ([] TyBinder) Type_ Type_ ([] Role) 
 DataCon Name
 | Mk_TcTyCon Unique Name Prelude.Bool ([] Var) ([] TyBinder) Type_ Type_ 
 Arity ([] Var)
data AlgTyConRhs =
   Mk_AbstractTyCon Prelude.Bool
 | Mk_DataTyCon ([] DataCon) Prelude.Bool
 | Mk_TupleTyCon DataCon TupleSort
 | Mk_NewTyCon DataCon Type_ ((,) ([] Var) Type_) CoAxiom
data CoAxiom =
   Mk_CoAxiom BranchFlag Unique Name Role TyCon Branches Prelude.Bool
data Branches =
   Mk_MkBranches BranchFlag (Data.Array.Array BranchIndex CoAxBranch)
data CoAxBranch =
   Mk_CoAxBranch SrcSpan ([] Var) ([] Var) ([] Role) ([] Type_) Type_ 
 ([] CoAxBranch)
data Var =
   Mk_TyVar Name Prelude.Int Type_
 | Mk_TcTyVar Name Prelude.Int Type_ TcTyVarDetails
 | Mk_Id Name Prelude.Int Type_ IdScope IdDetails
data IdDetails =
   Mk_VanillaId
 | Mk_RecSelId RecSelParent Prelude.Bool
 | Mk_DataConWorkId DataCon
 | Mk_DataConWrapId DataCon
 | Mk_ClassOpId Class
 | Mk_PrimOpId PrimOp
 | Mk_FCallId ForeignCall
 | Mk_TickBoxOpId TickBoxOp
 | Mk_DFunId Prelude.Bool
 | Mk_CoVarId
data DataCon =
   Mk_MkData Name Unique ConTag Prelude.Bool ([] Var) ([] TyBinder) ([] Var) 
 ([] TyBinder) ([] EqSpec) ([] Type_) ([] Type_) ([] Type_) Type_ ([]
                                                                  HsSrcBang) 
 ([] (FieldLbl Name)) Var DataConRep Arity Arity TyCon Type_ Prelude.Bool 
 TyCon
data DataConRep =
   Mk_NoDataConRep
 | Mk_DCR Var ([] Type_) ([] StrictnessMark) ([] HsImplBang)
data HsImplBang =
   Mk_HsLazy
 | Mk_HsStrict
 | Mk_HsUnpack (Prelude.Maybe Coercion)
data Coercion =
   Mk_Refl Role Type_
 | Mk_TyConAppCo Role TyCon ([] Coercion)
 | Mk_AppCo Coercion Coercion
 | Mk_ForAllCo Var Coercion Coercion
 | Mk_CoVarCo Var
 | Mk_AxiomInstCo CoAxiom BranchIndex ([] Coercion)
 | Mk_UnivCo UnivCoProvenance Role Type_ Type_
 | Mk_SymCo Coercion
 | Mk_TransCo Coercion Coercion
 | Mk_AxiomRuleCo ([] Coercion)
 | Mk_NthCo Prelude.Int Coercion
 | Mk_LRCo LeftOrRight Coercion
 | Mk_InstCo Coercion Coercion
 | Mk_CoherenceCo Coercion Coercion
 | Mk_KindCo Coercion
 | Mk_SubCo Coercion
data Type_ =
   Mk_TyVarTy Var
 | Mk_AppTy Type_ Type_
 | Mk_TyConApp TyCon ([] Type_)
 | Mk_ForAllTy TyBinder Type_
 | Mk_LitTy TyLit
 | Mk_CastTy Type_ Coercion
 | Mk_CoercionTy Coercion
data TyBinder =
   Mk_Named Var VisibilityFlag
 | Mk_Anon Type_
data UnivCoProvenance =
   Mk_UnsafeCoerceProv
 | Mk_PhantomProv Coercion
 | Mk_ProofIrrelProv Coercion
 | Mk_PluginProv Prelude.String
 | Mk_HoleProv CoercionHole
data CoercionHole =
   Mk_CoercionHole Unique
data EqSpec =
   Mk_EqSpec Var Type_
data Name =
   Mk_Name NameSort OccName Prelude.Int SrcSpan
data NameSort =
   Mk_External Module
 | Mk_WiredIn Module TyThing BuiltInSyntax
 | Mk_Internal
 | Mk_System
data TyThing =
   Mk_AnId Var
 | Mk_AConLike ConLike
 | Mk_ATyCon TyCon
 | Mk_ACoAxiom CoAxiom
data ConLike =
   Mk_RealDataCon DataCon
 | Mk_PatSynCon PatSyn
data PatSyn =
   Mk_MkPatSyn Name Unique ([] Type_) Arity Prelude.Bool ([] (FieldLbl Name)) 
 ([] Var) ([] TyBinder) ([] Type_) ([] Var) ([] TyBinder) ([] Type_) 
 Type_ ((,) Var Prelude.Bool) (Prelude.Maybe ((,) Var Prelude.Bool))
data RecSelParent =
   Mk_RecSelData TyCon
 | Mk_RecSelPatSyn PatSyn
data TcTyVarDetails =
   Mk_SkolemTv Prelude.Bool
 | Mk_FlatSkol Type_
 | Mk_RuntimeUnk
 | Mk_MetaTv MetaInfo TcLevel
data MetaDetails =
   Mk_Flexi
 | Mk_Indirect Type_
data FamTyConFlav =
   Mk_DataFamilyTyCon Name
 | Mk_OpenSynFamilyTyCon
 | Mk_ClosedSynFamilyTyCon (Prelude.Maybe CoAxiom)
 | Mk_AbstractClosedSynFamilyTyCon
 | Mk_BuiltInSynFamTyCon

data Literal =
   Mk_MachChar Prelude.Char
 | Mk_MachStr Data.ByteString.ByteString
 | Mk_MachNullAddr
 | Mk_MachInt Prelude.Integer
 | Mk_MachInt64 Prelude.Integer
 | Mk_MachWord Prelude.Integer
 | Mk_MachWord64 Prelude.Integer
 | Mk_MachFloat Prelude.Rational
 | Mk_MachDouble Prelude.Rational
 | Mk_MachLabel FastString.FastString (Prelude.Maybe Prelude.Int) FunctionOrData
 | Mk_LitInteger Prelude.Integer Type_

type CoreBndr = Var

data AltCon =
   Mk_DataAlt DataCon
 | Mk_LitAlt Literal
 | Mk_DEFAULT

data Expr b =
   Mk_Var Var
 | Mk_Lit Literal
 | Mk_App (Expr b) (Expr b)
 | Mk_Lam b (Expr b)
 | Mk_Let (Bind b) (Expr b)
 | Mk_Case (Expr b) b Type_ ([] ((,) ((,) AltCon ([] b)) (Expr b)))
 | Mk_Cast (Expr b) Coercion
 | Mk_Tick (Tickish Var) (Expr b)
 | Mk_Type Type_
 | Mk_Coercion Coercion
data Bind b =
   Mk_NonRec b (Expr b)
 | Mk_Rec ([] ((,) b (Expr b)))

type CoreBind = Bind CoreBndr

P.sequence
  [ do let constraint = (TH.ConT cls `TH.AppT`)
       tvs <- M.replicateM arity P.$ TH.VarT P.<$> TH.newName "a"
       P.pure P.$ TH.StandaloneDerivD (P.map constraint tvs)
                                      (constraint P.$ P.foldl TH.AppT (TH.ConT ty) tvs)
  | cls        <- [''P.Eq, ''P.Ord, ''P.Show, ''Data.Data, ''Generics.Generic]
  , (ty,arity) <- [ (''Width            , 0)
                  , (''VisibilityFlag   , 0)
                  , (''UnitId           , 0)
                  , (''Unique           , 0)
                  , (''UniqFM           , 1)
                  , (''TyLit            , 0)
                  , (''TupleSort        , 0)
                  , (''TcLevel          , 0)
                  , (''StrictnessMark   , 0)
                  , (''SrcUnpackedness  , 0)
                  , (''SrcStrictness    , 0)
                  , (''Safety           , 0)
                  , (''Role             , 0)
                  , (''RecFlag          , 0)
                  , (''RealSrcSpan      , 0)
                  , (''SrcSpan          , 0)
                  , (''PrimOpVecCat     , 0)
                  , (''NameSpace        , 0)
                  , (''OccName          , 0)
                  , (''ModuleName       , 0)
                  , (''Module           , 0)
                  , (''TickBoxOp        , 0)
                  , (''MetaInfo         , 0)
                  , (''PrimOp           , 0)
                  , (''LeftOrRight      , 0)
                  , (''IsCafCC          , 0)
                  , (''Injectivity      , 0)
                  , (''HsSrcBang        , 0)
                  , (''Header           , 0)
                  , (''GenLocated       , 2)
                  , (''FunctionOrData   , 0)
                  , (''FieldLbl         , 1)
                  , (''ExportFlag       , 0)
                  , (''IdScope          , 0)
                  , (''DefMethSpec      , 1)
                  , (''CostCentre       , 0)
                  , (''Tickish          , 1)
                  , (''CType            , 0)
                  , (''CCallTarget      , 0)
                  , (''CCallConv        , 0)
                  , (''CCallSpec        , 0)
                  , (''ForeignCall      , 0)
                  , (''BuiltInSyntax    , 0)
                  , (''BranchFlag       , 0)
                  , (''BooleanFormula   , 1)
                  , (''AlgTyConFlav     , 0)
                  , (''Class            , 0)
                  , (''ClassATItem      , 0)
                  , (''TyCon            , 0)
                  , (''AlgTyConRhs      , 0)
                  , (''CoAxiom          , 0)
                  , (''Branches         , 0)
                  , (''CoAxBranch       , 0)
                  , (''Var              , 0)
                  , (''IdDetails        , 0)
                  , (''DataCon          , 0)
                  , (''DataConRep       , 0)
                  , (''HsImplBang       , 0)
                  , (''Coercion         , 0)
                  , (''Type_            , 0)
                  , (''TyBinder         , 0)
                  , (''UnivCoProvenance , 0)
                  , (''CoercionHole     , 0)
                  , (''EqSpec           , 0)
                  , (''Name             , 0)
                  , (''NameSort         , 0)
                  , (''TyThing          , 0)
                  , (''ConLike          , 0)
                  , (''PatSyn           , 0)
                  , (''RecSelParent     , 0)
                  , (''TcTyVarDetails   , 0)
                  , (''MetaDetails      , 0)
                  , (''FamTyConFlav     , 0)
                  , (''Literal          , 0)
                  , (''AltCon           , 0)
                  , (''Expr             , 1)
                  , (''Bind             , 1) ] ]
