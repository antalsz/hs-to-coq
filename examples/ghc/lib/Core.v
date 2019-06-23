(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(* Converted imports: *)

Require BasicTypes.
Require BinNat.
Require BinNums.
Require BooleanFormula.
Require Coq.Init.Datatypes.
Require Coq.Init.Peano.
Require Coq.Lists.List.
Require Data.Foldable.
Require Data.Function.
Require Data.Maybe.
Require Data.Tuple.
Require Datatypes.
Require DynFlags.
Require FastStringEnv.
Require FieldLabel.
Require GHC.Base.
Require GHC.Char.
Require GHC.DeferredFix.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Require GHC.Wf.
Require Literal.
Require Maybes.
Require Module.
Require Name.
Require NameEnv.
Require OccName.
Require Panic.
Require PrelNames.
Require SrcLoc.
Require UniqDFM.
Require UniqDSet.
Require UniqFM.
Require UniqSet.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition VarEnv :=
  UniqFM.UniqFM%type.

Inductive UnfoldingSource : Type
  := | InlineRhs : UnfoldingSource
  |  InlineStable : UnfoldingSource
  |  InlineCompulsory : UnfoldingSource.

Inductive UnfoldingGuidance : Type
  := | UnfWhen (ug_arity : BasicTypes.Arity) (ug_unsat_ok : bool) (ug_boring_ok
    : bool)
   : UnfoldingGuidance
  |  UnfIfGoodArgs (ug_args : list nat) (ug_size : nat) (ug_res : nat)
   : UnfoldingGuidance
  |  UnfNever : UnfoldingGuidance.

Inductive Unfolding : Type := | NoUnfolding.

Inductive TypeShape : Type
  := | TsFun : TypeShape -> TypeShape
  |  TsProd : list TypeShape -> TypeShape
  |  TsUnk : TypeShape.

Definition TyVarEnv :=
  VarEnv%type.

Inductive TyVarBndr tyvar argf : Type
  := | TvBndr : tyvar -> argf -> TyVarBndr tyvar argf.

Definition TyConRepName :=
  Name.Name%type.

Inductive TyConFlavour : Type
  := | ClassFlavour : TyConFlavour
  |  TupleFlavour : BasicTypes.Boxity -> TyConFlavour
  |  SumFlavour : TyConFlavour
  |  DataTypeFlavour : TyConFlavour
  |  NewtypeFlavour : TyConFlavour
  |  AbstractTypeFlavour : TyConFlavour
  |  DataFamilyFlavour : TyConFlavour
  |  OpenTypeFamilyFlavour : TyConFlavour
  |  ClosedTypeFamilyFlavour : TyConFlavour
  |  TypeSynonymFlavour : TyConFlavour
  |  BuiltInTypeFlavour : TyConFlavour
  |  PromotedDataConFlavour : TyConFlavour.

Definition TyCoVarEnv :=
  VarEnv%type.

Inductive TickishScoping : Type
  := | NoScope : TickishScoping
  |  SoftScope : TickishScoping
  |  CostCentreScope : TickishScoping.

Inductive TickishPlacement : Type
  := | PlaceRuntime : TickishPlacement
  |  PlaceNonLam : TickishPlacement
  |  PlaceCostCentre : TickishPlacement.

Inductive Tickish id : Type
  := | ProfNote (profNoteCC : unit) (profNoteCount : bool) (profNoteScope : bool)
   : Tickish id
  |  HpcTick (tickModule : Module.Module) (tickId : nat) : Tickish id
  |  Breakpoint (breakpointId : nat) (breakpointFVs : list id) : Tickish id
  |  SourceNote (sourceSpan : SrcLoc.RealSrcSpan) (sourceName : GHC.Base.String)
   : Tickish id.

Definition TickBoxId :=
  nat%type.

Inductive TickBoxOp : Type
  := | TickBox : Module.Module -> TickBoxId -> TickBoxOp.

Inductive Termination r : Type
  := | Diverges : Termination r
  |  ThrowsExn : Termination r
  |  Dunno : r -> Termination r.

Inductive StrictnessMark : Type
  := | MarkedStrict : StrictnessMark
  |  NotMarkedStrict : StrictnessMark.

Inductive SrcUnpackedness : Type
  := | SrcUnpack : SrcUnpackedness
  |  SrcNoUnpack : SrcUnpackedness
  |  NoSrcUnpack : SrcUnpackedness.

Inductive SrcStrictness : Type
  := | SrcLazy : SrcStrictness
  |  SrcStrict : SrcStrictness
  |  NoSrcStrict : SrcStrictness.

Inductive RuleInfo : Type := | EmptyRuleInfo.

Inductive RecTcChecker : Type
  := | RC : nat -> (NameEnv.NameEnv nat) -> RecTcChecker.

Inductive PrimElemRep : Type
  := | Int8ElemRep : PrimElemRep
  |  Int16ElemRep : PrimElemRep
  |  Int32ElemRep : PrimElemRep
  |  Int64ElemRep : PrimElemRep
  |  Word8ElemRep : PrimElemRep
  |  Word16ElemRep : PrimElemRep
  |  Word32ElemRep : PrimElemRep
  |  Word64ElemRep : PrimElemRep
  |  FloatElemRep : PrimElemRep
  |  DoubleElemRep : PrimElemRep.

Inductive PrimRep : Type
  := | VoidRep : PrimRep
  |  LiftedRep : PrimRep
  |  UnliftedRep : PrimRep
  |  IntRep : PrimRep
  |  WordRep : PrimRep
  |  Int64Rep : PrimRep
  |  Word64Rep : PrimRep
  |  AddrRep : PrimRep
  |  FloatRep : PrimRep
  |  DoubleRep : PrimRep
  |  VecRep : nat -> PrimElemRep -> PrimRep.

Inductive RuntimeRepInfo : Type
  := | NoRRI : RuntimeRepInfo
  |  RuntimeRep : (list unit -> list PrimRep) -> RuntimeRepInfo
  |  VecCount : nat -> RuntimeRepInfo
  |  VecElem : PrimElemRep -> RuntimeRepInfo.

Definition OutType :=
  unit%type.

Definition OutKind :=
  unit%type.

Definition OutCoercion :=
  unit%type.

Inductive LevityInfo : Type
  := | NoLevityInfo : LevityInfo
  |  NeverLevityPolymorphic : LevityInfo.

Inductive KillFlags : Type
  := | Mk_KillFlags (kf_abs : bool) (kf_used_once : bool) (kf_called_once : bool)
   : KillFlags.

Inductive JointDmd s u : Type := | JD (sd : s) (ud : u) : JointDmd s u.

Inductive IsOrphan : Type
  := | Mk_IsOrphan : IsOrphan
  |  NotOrphan : OccName.OccName -> IsOrphan.

Definition InlinePragInfo :=
  BasicTypes.InlinePragma%type.

Inductive Injectivity : Type
  := | NotInjective : Injectivity
  |  Injective : list bool -> Injectivity.

Definition InType :=
  unit%type.

Definition InKind :=
  unit%type.

Definition InCoercion :=
  unit%type.

Definition IdEnv :=
  VarEnv%type.

Inductive HsSrcBang : Type
  := | Mk_HsSrcBang
   : BasicTypes.SourceText -> SrcUnpackedness -> SrcStrictness -> HsSrcBang.

Inductive HsImplBang : Type
  := | HsLazy : HsImplBang
  |  HsStrict : HsImplBang
  |  HsUnpack : (option unit) -> HsImplBang.

Definition FunDep a :=
  (list a * list a)%type%type.

Inductive FamTyConFlav : Type
  := | DataFamilyTyCon : TyConRepName -> FamTyConFlav
  |  OpenSynFamilyTyCon : FamTyConFlav
  |  ClosedSynFamilyTyCon : (option (list unit)) -> FamTyConFlav
  |  AbstractClosedSynFamilyTyCon : FamTyConFlav
  |  BuiltInSynFamTyCon : unit -> FamTyConFlav.

Inductive ExportFlag : Type
  := | NotExported : ExportFlag
  |  Exported : ExportFlag.

Inductive IdScope : Type
  := | GlobalId : IdScope
  |  LocalId : ExportFlag -> IdScope.

Inductive ExnStr : Type := | VanStr : ExnStr |  Mk_ExnStr : ExnStr.

Inductive Str s : Type := | Lazy : Str s |  Mk_Str : ExnStr -> s -> Str s.

Definition DefMethInfo :=
  (option (Name.Name * BasicTypes.DefMethSpec unit)%type)%type.

Definition DVarEnv :=
  UniqDFM.UniqDFM%type.

Definition DTyVarEnv :=
  DVarEnv%type.

Definition DIdEnv :=
  DVarEnv%type.

Inductive Count : Type := | One : Count |  Many : Count.

Inductive Use u : Type := | Abs : Use u |  Mk_Use : Count -> u -> Use u.

Definition DmdShell :=
  (JointDmd (Str unit) (Use unit))%type.

Definition CoVarEnv :=
  VarEnv%type.

Definition ClassMinimalDef :=
  (BooleanFormula.BooleanFormula Name.Name)%type.

Inductive CafInfo : Type := | MayHaveCafRefs : CafInfo |  NoCafRefs : CafInfo.

Inductive CPRResult : Type
  := | NoCPR : CPRResult
  |  RetProd : CPRResult
  |  RetSum : BasicTypes.ConTag -> CPRResult.

Definition DmdResult :=
  (Termination CPRResult)%type.

Definition ArityInfo :=
  BasicTypes.Arity%type.

Inductive UseDmd : Type
  := | UCall : Count -> UseDmd -> UseDmd
  |  UProd : list (Use UseDmd)%type -> UseDmd
  |  UHead : UseDmd
  |  Used : UseDmd.

Definition ArgUse :=
  (Use UseDmd)%type.

Inductive StrDmd : Type
  := | HyperStr : StrDmd
  |  SCall : StrDmd -> StrDmd
  |  SProd : list (Str StrDmd)%type -> StrDmd
  |  HeadStr : StrDmd.

Definition ArgStr :=
  (Str StrDmd)%type.

Definition Demand :=
  (JointDmd ArgStr ArgUse)%type.

Definition DmdEnv :=
  (VarEnv Demand)%type.

Definition BothDmdArg :=
  (DmdEnv * Termination unit)%type%type.

Inductive DmdType : Type
  := | Mk_DmdType : DmdEnv -> list Demand -> DmdResult -> DmdType.

Inductive StrictSig : Type := | Mk_StrictSig : DmdType -> StrictSig.

Inductive IdInfo : Type
  := | Mk_IdInfo (arityInfo : ArityInfo) (ruleInfo : RuleInfo) (unfoldingInfo
    : Unfolding) (cafInfo : CafInfo) (oneShotInfo : BasicTypes.OneShotInfo)
  (inlinePragInfo : BasicTypes.InlinePragma) (occInfo : BasicTypes.OccInfo)
  (strictnessInfo : StrictSig) (demandInfo : Demand) (callArityInfo : ArityInfo)
  (levityInfo : LevityInfo)
   : IdInfo.

Definition CleanDemand :=
  (JointDmd StrDmd UseDmd)%type.

Inductive ArgFlag : Type
  := | Required : ArgFlag
  |  Specified : ArgFlag
  |  Inferred : ArgFlag.

Inductive TyConBndrVis : Type
  := | NamedTCB : ArgFlag -> TyConBndrVis
  |  AnonTCB : TyConBndrVis.

Inductive AlgTyConFlav : Type
  := | VanillaAlgTyCon : TyConRepName -> AlgTyConFlav
  |  UnboxedAlgTyCon : (option TyConRepName) -> AlgTyConFlav
  |  ClassTyCon : Class -> TyConRepName -> AlgTyConFlav
  |  DataFamInstTyCon : (list unit) -> TyCon -> list unit -> AlgTyConFlav
with Class : Type
  := | Mk_Class (classTyCon : TyCon) (className : Name.Name) (classKey
    : Unique.Unique) (classTyVars : list Var%type) (classFunDeps
    : list (FunDep Var%type)) (classBody : ClassBody)
   : Class
with ClassBody : Type
  := | AbstractClass : ClassBody
  |  ConcreteClass (classSCThetaStuff : list unit) (classSCSels : list Var%type)
  (classATStuff : list ClassATItem) (classOpStuff
    : list (Var%type * DefMethInfo)%type%type) (classMinimalDefStuff
    : ClassMinimalDef)
   : ClassBody
with ClassATItem : Type
  := | ATI : TyCon -> (option (unit * SrcLoc.SrcSpan)%type) -> ClassATItem
with TyCon : Type
  := | FunTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name)
  (tyConBinders : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConResKind
    : unit) (tyConKind : unit) (tyConArity : BasicTypes.Arity) (tcRepName
    : TyConRepName)
   : TyCon
  |  AlgTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name) (tyConBinders
    : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConTyVars : list Var%type)
  (tyConResKind : unit) (tyConKind : unit) (tyConArity : BasicTypes.Arity)
  (tcRoles : list unit) (tyConCType : option unit) (algTcGadtSyntax : bool)
  (algTcStupidTheta : list unit) (algTcRhs : AlgTyConRhs) (algTcFields
    : FieldLabel.FieldLabelEnv) (algTcParent : AlgTyConFlav)
   : TyCon
  |  SynonymTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name)
  (tyConBinders : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConTyVars
    : list Var%type) (tyConResKind : unit) (tyConKind : unit) (tyConArity
    : BasicTypes.Arity) (tcRoles : list unit) (synTcRhs : unit) (synIsTau : bool)
  (synIsFamFree : bool)
   : TyCon
  |  FamilyTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name)
  (tyConBinders : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConTyVars
    : list Var%type) (tyConResKind : unit) (tyConKind : unit) (tyConArity
    : BasicTypes.Arity) (famTcResVar : option Name.Name) (famTcFlav : FamTyConFlav)
  (famTcParent : option Class) (famTcInj : Injectivity)
   : TyCon
  |  PrimTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name) (tyConBinders
    : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConResKind : unit) (tyConKind
    : unit) (tyConArity : BasicTypes.Arity) (tcRoles : list unit) (isUnlifted
    : bool) (primRepName : option TyConRepName)
   : TyCon
  |  PromotedDataCon (tyConUnique : Unique.Unique) (tyConName : Name.Name)
  (tyConBinders : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConResKind
    : unit) (tyConKind : unit) (tyConArity : BasicTypes.Arity) (tcRoles
    : list unit) (dataCon : DataCon) (tcRepName : TyConRepName) (promDcRepInfo
    : RuntimeRepInfo)
   : TyCon
  |  TcTyCon (tyConUnique : Unique.Unique) (tyConName : Name.Name) (tyConBinders
    : list (TyVarBndr Var%type TyConBndrVis)%type) (tyConTyVars : list Var%type)
  (tyConResKind : unit) (tyConKind : unit) (tyConArity : BasicTypes.Arity)
  (tcTyConScopedTyVars : list (Name.Name * Var%type)%type) (tcTyConFlavour
    : TyConFlavour)
   : TyCon
with AlgTyConRhs : Type
  := | AbstractTyCon : AlgTyConRhs
  |  DataTyCon (data_cons : list DataCon) (is_enum : bool) : AlgTyConRhs
  |  TupleTyCon (data_con : DataCon) (tup_sort : BasicTypes.TupleSort)
   : AlgTyConRhs
  |  SumTyCon (data_cons : list DataCon) : AlgTyConRhs
  |  NewTyCon (data_con : DataCon) (nt_rhs : unit) (nt_etad_rhs
    : (list Var%type * unit)%type) (nt_co : list unit)
   : AlgTyConRhs
with DataCon : Type
  := | MkData (dcName : Name.Name) (dcUnique : Unique.Unique) (dcTag
    : BasicTypes.ConTag) (dcVanilla : bool) (dcUnivTyVars : list Var%type)
  (dcExTyVars : list Var%type) (dcUserTyVarBinders
    : list (TyVarBndr Var%type ArgFlag)%type) (dcEqSpec : list EqSpec)
  (dcOtherTheta : unit) (dcStupidTheta : unit) (dcOrigArgTys : list unit)
  (dcOrigResTy : unit) (dcSrcBangs : list HsSrcBang) (dcFields
    : list FieldLabel.FieldLabel) (dcWorkId : Var%type) (dcRep : DataConRep)
  (dcRepArity : BasicTypes.Arity) (dcSourceArity : BasicTypes.Arity) (dcRepTyCon
    : TyCon) (dcRepType : unit) (dcInfix : bool) (dcPromoted : TyCon)
   : DataCon
with DataConRep : Type
  := | NoDataConRep : DataConRep
  |  DCR (dcr_wrap_id : Var%type) (dcr_boxer : unit) (dcr_arg_tys : list unit)
  (dcr_stricts : list StrictnessMark) (dcr_bangs : list HsImplBang)
   : DataConRep
with Var : Type
  := | Mk_TyVar (varName : Name.Name) (realUnique : BinNums.N) (varType : unit)
   : Var
  |  Mk_TcTyVar (varName : Name.Name) (realUnique : BinNums.N) (varType : unit)
  (tc_tv_details : unit)
   : Var
  |  Mk_Id (varName : Name.Name) (realUnique : BinNums.N) (varType : unit)
  (idScope : IdScope) (id_details : IdDetails) (id_info : IdInfo)
   : Var
with IdDetails : Type
  := | VanillaId : IdDetails
  |  RecSelId (sel_tycon : RecSelParent) (sel_naughty : bool) : IdDetails
  |  DataConWorkId : DataCon -> IdDetails
  |  DataConWrapId : DataCon -> IdDetails
  |  ClassOpId : Class -> IdDetails
  |  PrimOpId : unit -> IdDetails
  |  FCallId : unit -> IdDetails
  |  TickBoxOpId : TickBoxOp -> IdDetails
  |  Mk_DFunId : bool -> IdDetails
  |  CoVarId : IdDetails
  |  Mk_JoinId : BasicTypes.JoinArity -> IdDetails
with RecSelParent : Type
  := | RecSelData : TyCon -> RecSelParent
  |  RecSelPatSyn : PatSyn -> RecSelParent
with PatSyn : Type
  := | MkPatSyn (psName : Name.Name) (psUnique : Unique.Unique) (psArgs
    : list unit) (psArity : BasicTypes.Arity) (psInfix : bool) (psFieldLabels
    : list FieldLabel.FieldLabel) (psUnivTyVars
    : list (TyVarBndr Var%type ArgFlag)%type) (psReqTheta : unit) (psExTyVars
    : list (TyVarBndr Var%type ArgFlag)%type) (psProvTheta : unit) (psResultTy
    : unit) (psMatcher : (Var%type * bool)%type) (psBuilder
    : option (Var%type * bool)%type)
   : PatSyn
with EqSpec : Type := | Mk_EqSpec : Var%type -> unit -> EqSpec.

Definition TyVar :=
  Var%type.

Definition TyVarBinder :=
  (TyVarBndr TyVar ArgFlag)%type.

Definition TyConBinder :=
  (TyVarBndr TyVar TyConBndrVis)%type.

Definition Id :=
  Var%type.

Definition ClassOpItem :=
  (Id * DefMethInfo)%type%type.

Definition CoreBndr :=
  Var%type.

Definition InBndr :=
  CoreBndr%type.

Definition OutBndr :=
  CoreBndr%type.

Inductive TaggedBndr t : Type := | TB : CoreBndr -> t -> TaggedBndr t.

Definition DVarSet :=
  (UniqDSet.UniqDSet Var)%type.

Definition CoVar :=
  Id%type.

Definition CoVarSet :=
  (UniqSet.UniqSet CoVar)%type.

Definition InCoVar :=
  CoVar%type.

Definition OutCoVar :=
  CoVar%type.

Definition DFunId :=
  Id%type.

Definition DIdSet :=
  (UniqDSet.UniqDSet Id)%type.

Definition EvId :=
  Id%type.

Definition DictId :=
  EvId%type.

Definition EqVar :=
  EvId%type.

Definition EvVar :=
  EvId%type.

Definition IpId :=
  EvId%type.

Definition IdSet :=
  (UniqSet.UniqSet Id)%type.

Definition IdUnfoldingFun :=
  (Id -> Unfolding)%type.

Definition InId :=
  Id%type.

Definition JoinId :=
  Id%type.

Definition NcId :=
  Id%type.

Definition OutId :=
  Id%type.

Definition TyCoVar :=
  Id%type.

Definition DTyCoVarSet :=
  (UniqDSet.UniqDSet TyCoVar)%type.

Definition TyCoVarSet :=
  (UniqSet.UniqSet TyCoVar)%type.

Definition InVar :=
  Var%type.

Definition KindVar :=
  Var%type.

Definition OutVar :=
  Var%type.

Definition TKVar :=
  Var%type.

Definition TidyEnv :=
  (OccName.TidyOccEnv * VarEnv Var)%type%type.

Definition DTyVarSet :=
  (UniqDSet.UniqDSet TyVar)%type.

Definition InTyVar :=
  TyVar%type.

Definition OutTyVar :=
  TyVar%type.

Inductive AltCon : Type
  := | DataAlt : DataCon -> AltCon
  |  LitAlt : Literal.Literal -> AltCon
  |  DEFAULT : AltCon.

Inductive Expr b : Type
  := | Mk_Var : Id -> Expr b
  |  Lit : Literal.Literal -> Expr b
  |  App : (Expr b) -> (Expr%type b) -> Expr b
  |  Lam : b -> (Expr b) -> Expr b
  |  Let : (Bind b) -> (Expr b) -> Expr b
  |  Case
   : (Expr b) ->
     b ->
     unit -> list ((fun b_ => (AltCon * list b_ * Expr b_)%type%type) b) -> Expr b
  |  Cast : (Expr b) -> unit -> Expr b
  |  Tick : (Tickish Id) -> (Expr b) -> Expr b
  |  Type_ : unit -> Expr b
  |  Coercion : unit -> Expr b
with Bind b : Type
  := | NonRec : b -> (Expr b) -> Bind b
  |  Rec : list (b * (Expr b))%type -> Bind b.

Definition Arg :=
  Expr%type.

Definition Alt :=
  fun b_ => (AltCon * list b_ * Expr b_)%type%type.

Definition CoreAlt :=
  (Alt CoreBndr)%type.

Definition InAlt :=
  CoreAlt%type.

Definition OutAlt :=
  CoreAlt%type.

Definition CoreArg :=
  (Arg CoreBndr)%type.

Definition InArg :=
  CoreArg%type.

Definition OutArg :=
  CoreArg%type.

Definition TaggedArg t :=
  (Arg (TaggedBndr t))%type.

Definition CoreBind :=
  (Bind CoreBndr)%type.

Definition CoreProgram :=
  (list CoreBind)%type.

Definition InBind :=
  CoreBind%type.

Definition OutBind :=
  CoreBind%type.

Definition TaggedBind t :=
  (Bind (TaggedBndr t))%type.

Definition CoreExpr :=
  (Expr CoreBndr)%type.

Inductive CoreVect : Type
  := | Vect : Id -> CoreExpr -> CoreVect
  |  NoVect : Id -> CoreVect
  |  VectType : bool -> TyCon -> (option TyCon) -> CoreVect
  |  VectClass : TyCon -> CoreVect
  |  VectInst : Id -> CoreVect.

Definition InExpr :=
  CoreExpr%type.

Definition OutExpr :=
  CoreExpr%type.

Definition TaggedExpr t :=
  (Expr (TaggedBndr t))%type.

Definition TaggedAlt t :=
  (Alt (TaggedBndr t))%type.

Inductive AnnExpr' bndr annot : Type
  := | AnnVar : Id -> AnnExpr' bndr annot
  |  AnnLit : Literal.Literal -> AnnExpr' bndr annot
  |  AnnLam
   : bndr ->
     ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr annot) ->
     AnnExpr' bndr annot
  |  AnnApp
   : ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr
      annot) ->
     ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr annot) ->
     AnnExpr' bndr annot
  |  AnnCase
   : ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr
      annot) ->
     bndr ->
     unit ->
     list ((fun bndr_ annot_ =>
              (AltCon * list bndr_ *
               (fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr_
               annot_)%type%type) bndr annot) ->
     AnnExpr' bndr annot
  |  AnnLet
   : (AnnBind bndr annot) ->
     ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr annot) ->
     AnnExpr' bndr annot
  |  AnnCast
   : ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr
      annot) ->
     (annot * unit)%type -> AnnExpr' bndr annot
  |  AnnTick
   : (Tickish Id) ->
     ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr annot) ->
     AnnExpr' bndr annot
  |  AnnType : unit -> AnnExpr' bndr annot
  |  AnnCoercion : unit -> AnnExpr' bndr annot
with AnnBind bndr annot : Type
  := | AnnNonRec
   : bndr ->
     ((fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr annot) ->
     AnnBind bndr annot
  |  AnnRec
   : list (bndr *
           (fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type) bndr
           annot)%type ->
     AnnBind bndr annot.

Definition AnnExpr :=
  fun bndr_ annot_ => (annot_ * AnnExpr' bndr_ annot_)%type%type.

Definition AnnAlt :=
  fun bndr_ annot_ => (AltCon * list bndr_ * AnnExpr bndr_ annot_)%type%type.

Definition TyVarSet :=
  (UniqSet.UniqSet TyVar)%type.

Definition TypeVar :=
  Var%type.

Definition VarSet :=
  (UniqSet.UniqSet Var)%type.

Inductive InScopeSet : Type := | InScope : VarSet -> nat -> InScopeSet.

Definition InScopeEnv :=
  (InScopeSet * IdUnfoldingFun)%type%type.

Definition RuleFun :=
  (DynFlags.DynFlags ->
   InScopeEnv -> Id -> list CoreExpr -> option CoreExpr)%type.

Inductive CoreRule : Type
  := | Rule (ru_name : BasicTypes.RuleName) (ru_act : BasicTypes.Activation)
  (ru_fn : Name.Name) (ru_rough : list (option Name.Name)) (ru_bndrs
    : list CoreBndr) (ru_args : list CoreExpr) (ru_rhs : CoreExpr) (ru_auto : bool)
  (ru_origin : Module.Module) (ru_orphan : IsOrphan) (ru_local : bool)
   : CoreRule
  |  BuiltinRule (ru_name : BasicTypes.RuleName) (ru_fn : Name.Name) (ru_nargs
    : nat) (ru_try : RuleFun)
   : CoreRule.

Definition RuleBase :=
  (NameEnv.NameEnv (list CoreRule))%type.

Inductive RuleEnv : Type
  := | Mk_RuleEnv (re_base : RuleBase) (re_visible_orphs : Module.ModuleSet)
   : RuleEnv.

Inductive RnEnv2 : Type
  := | RV2 (envL : VarEnv Var) (envR : VarEnv Var) (in_scope : InScopeSet)
   : RnEnv2.

Arguments TvBndr {_} {_} _ _.

Arguments ProfNote {_} _ _ _.

Arguments HpcTick {_} _ _.

Arguments Breakpoint {_} _ _.

Arguments SourceNote {_} _ _.

Arguments Diverges {_}.

Arguments ThrowsExn {_}.

Arguments Dunno {_} _.

Arguments JD {_} {_} _ _.

Arguments Lazy {_}.

Arguments Mk_Str {_} _ _.

Arguments Abs {_}.

Arguments Mk_Use {_} _ _.

Arguments TB {_} _ _.

Arguments Mk_Var {_} _.

Arguments Lit {_} _.

Arguments App {_} _ _.

Arguments Lam {_} _ _.

Arguments Let {_} _ _.

Arguments Case {_} _ _ _ _.

Arguments Cast {_} _ _.

Arguments Tick {_} _ _.

Arguments Type_ {_} _.

Arguments Coercion {_} _.

Arguments NonRec {_} _ _.

Arguments Rec {_} _.

Arguments AnnVar {_} {_} _.

Arguments AnnLit {_} {_} _.

Arguments AnnLam {_} {_} _ _.

Arguments AnnApp {_} {_} _ _.

Arguments AnnCase {_} {_} _ _ _ _.

Arguments AnnLet {_} {_} _ _.

Arguments AnnCast {_} {_} _ _.

Arguments AnnTick {_} {_} _ _.

Arguments AnnType {_} {_} _.

Arguments AnnCoercion {_} {_} _.

Arguments AnnNonRec {_} {_} _ _.

Arguments AnnRec {_} {_} _.

Instance Default__UnfoldingSource : GHC.Err.Default UnfoldingSource :=
  GHC.Err.Build_Default _ InlineRhs.

Instance Default__UnfoldingGuidance : GHC.Err.Default UnfoldingGuidance :=
  GHC.Err.Build_Default _ (UnfWhen GHC.Err.default GHC.Err.default
                         GHC.Err.default).

Instance Default__TypeShape : GHC.Err.Default TypeShape :=
  GHC.Err.Build_Default _ TsUnk.

Instance Default__TyConFlavour : GHC.Err.Default TyConFlavour :=
  GHC.Err.Build_Default _ ClassFlavour.

Instance Default__TickishScoping : GHC.Err.Default TickishScoping :=
  GHC.Err.Build_Default _ NoScope.

Instance Default__TickishPlacement : GHC.Err.Default TickishPlacement :=
  GHC.Err.Build_Default _ PlaceRuntime.

Instance Default__StrictnessMark : GHC.Err.Default StrictnessMark :=
  GHC.Err.Build_Default _ MarkedStrict.

Instance Default__SrcUnpackedness : GHC.Err.Default SrcUnpackedness :=
  GHC.Err.Build_Default _ SrcUnpack.

Instance Default__SrcStrictness : GHC.Err.Default SrcStrictness :=
  GHC.Err.Build_Default _ SrcLazy.

Instance Default__PrimElemRep : GHC.Err.Default PrimElemRep :=
  GHC.Err.Build_Default _ Int8ElemRep.

Instance Default__PrimRep : GHC.Err.Default PrimRep :=
  GHC.Err.Build_Default _ VoidRep.

Instance Default__RuntimeRepInfo : GHC.Err.Default RuntimeRepInfo :=
  GHC.Err.Build_Default _ NoRRI.

Instance Default__LevityInfo : GHC.Err.Default LevityInfo :=
  GHC.Err.Build_Default _ NoLevityInfo.

Instance Default__KillFlags : GHC.Err.Default KillFlags :=
  GHC.Err.Build_Default _ (Mk_KillFlags GHC.Err.default GHC.Err.default
                         GHC.Err.default).

Instance Default__IsOrphan : GHC.Err.Default IsOrphan :=
  GHC.Err.Build_Default _ Mk_IsOrphan.

Instance Default__Injectivity : GHC.Err.Default Injectivity :=
  GHC.Err.Build_Default _ NotInjective.

Instance Default__HsImplBang : GHC.Err.Default HsImplBang :=
  GHC.Err.Build_Default _ HsLazy.

Instance Default__FamTyConFlav : GHC.Err.Default FamTyConFlav :=
  GHC.Err.Build_Default _ OpenSynFamilyTyCon.

Instance Default__ExportFlag : GHC.Err.Default ExportFlag :=
  GHC.Err.Build_Default _ NotExported.

Instance Default__IdScope : GHC.Err.Default IdScope :=
  GHC.Err.Build_Default _ GlobalId.

Instance Default__ExnStr : GHC.Err.Default ExnStr :=
  GHC.Err.Build_Default _ VanStr.

Instance Default__Count : GHC.Err.Default Count := GHC.Err.Build_Default _ One.

Instance Default__CafInfo : GHC.Err.Default CafInfo :=
  GHC.Err.Build_Default _ MayHaveCafRefs.

Instance Default__CPRResult : GHC.Err.Default CPRResult :=
  GHC.Err.Build_Default _ NoCPR.

Instance Default__UseDmd : GHC.Err.Default UseDmd :=
  GHC.Err.Build_Default _ UHead.

Instance Default__StrDmd : GHC.Err.Default StrDmd :=
  GHC.Err.Build_Default _ HyperStr.

Instance Default__ArgFlag : GHC.Err.Default ArgFlag :=
  GHC.Err.Build_Default _ Required.

Instance Default__TyConBndrVis : GHC.Err.Default TyConBndrVis :=
  GHC.Err.Build_Default _ AnonTCB.

Instance Default__ClassBody : GHC.Err.Default ClassBody :=
  GHC.Err.Build_Default _ AbstractClass.

Instance Default__TyCon : GHC.Err.Default TyCon :=
  GHC.Err.Build_Default _ (FunTyCon GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default).

Instance Default__AlgTyConRhs : GHC.Err.Default AlgTyConRhs :=
  GHC.Err.Build_Default _ AbstractTyCon.

Instance Default__DataConRep : GHC.Err.Default DataConRep :=
  GHC.Err.Build_Default _ NoDataConRep.

Instance Default__IdDetails : GHC.Err.Default IdDetails :=
  GHC.Err.Build_Default _ VanillaId.

Instance Default__AltCon : GHC.Err.Default AltCon :=
  GHC.Err.Build_Default _ DEFAULT.

Definition ug_args (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_args' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs ug_args _ _ => ug_args
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_args' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_arity (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen ug_arity _ _ => ug_arity
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_arity' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_arity' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_boring_ok (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ ug_boring_ok => ug_boring_ok
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_boring_ok' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_boring_ok' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_res (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_res' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs _ _ ug_res => ug_res
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_res' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_size (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_size' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
  | UnfIfGoodArgs _ ug_size _ => ug_size
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_size' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_unsat_ok (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
  | UnfWhen _ ug_unsat_ok _ => ug_unsat_ok
  | UnfIfGoodArgs _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_unsat_ok' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
  | UnfNever =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ug_unsat_ok' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition breakpointFVs {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointFVs' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointFVs' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ breakpointFVs => breakpointFVs
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointFVs' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition breakpointId {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointId' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointId' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint breakpointId _ => breakpointId
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `breakpointId' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition profNoteCC {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote profNoteCC _ _ => profNoteCC
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCC' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCC' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCC' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition profNoteCount {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ profNoteCount _ => profNoteCount
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCount' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCount' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteCount' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition profNoteScope {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ profNoteScope => profNoteScope
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteScope' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteScope' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `profNoteScope' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition sourceName {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceName' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceName' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceName' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ sourceName => sourceName
  end.

Definition sourceSpan {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceSpan' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceSpan' has no match in constructor `HpcTick' of type `Tickish'")
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sourceSpan' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote sourceSpan _ => sourceSpan
  end.

Definition tickId {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickId' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick _ tickId => tickId
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickId' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickId' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition tickModule {id} (arg_0__ : Tickish id) :=
  match arg_0__ with
  | ProfNote _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickModule' has no match in constructor `ProfNote' of type `Tickish'")
  | HpcTick tickModule _ => tickModule
  | Breakpoint _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickModule' has no match in constructor `Breakpoint' of type `Tickish'")
  | SourceNote _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tickModule' has no match in constructor `SourceNote' of type `Tickish'")
  end.

Definition kf_abs (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags kf_abs _ _ := arg_0__ in
  kf_abs.

Definition kf_called_once (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags _ _ kf_called_once := arg_0__ in
  kf_called_once.

Definition kf_used_once (arg_0__ : KillFlags) :=
  let 'Mk_KillFlags _ kf_used_once _ := arg_0__ in
  kf_used_once.

Definition sd {s} {u} (arg_0__ : JointDmd s u) :=
  let 'JD sd _ := arg_0__ in
  sd.

Definition ud {s} {u} (arg_0__ : JointDmd s u) :=
  let 'JD _ ud := arg_0__ in
  ud.

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

Definition classBody (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ _ _ classBody := arg_0__ in
  classBody.

Definition classFunDeps (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ _ classFunDeps _ := arg_0__ in
  classFunDeps.

Definition classKey (arg_0__ : Class) :=
  let 'Mk_Class _ _ classKey _ _ _ := arg_0__ in
  classKey.

Definition className (arg_0__ : Class) :=
  let 'Mk_Class _ className _ _ _ _ := arg_0__ in
  className.

Definition classTyCon (arg_0__ : Class) :=
  let 'Mk_Class classTyCon _ _ _ _ _ := arg_0__ in
  classTyCon.

Definition classTyVars (arg_0__ : Class) :=
  let 'Mk_Class _ _ _ classTyVars _ _ := arg_0__ in
  classTyVars.

Definition classATStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classATStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ classATStuff _ _ => classATStuff
  end.

Definition classMinimalDefStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classMinimalDefStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ _ _ classMinimalDefStuff => classMinimalDefStuff
  end.

Definition classOpStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classOpStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ _ _ classOpStuff _ => classOpStuff
  end.

Definition classSCSels (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classSCSels' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass _ classSCSels _ _ _ => classSCSels
  end.

Definition classSCThetaStuff (arg_0__ : ClassBody) :=
  match arg_0__ with
  | AbstractClass =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `classSCThetaStuff' has no match in constructor `AbstractClass' of type `ClassBody'")
  | ConcreteClass classSCThetaStuff _ _ _ _ => classSCThetaStuff
  end.

Definition algTcFields (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ algTcFields _ => algTcFields
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcFields' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition algTcGadtSyntax (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ algTcGadtSyntax _ _ _ _ => algTcGadtSyntax
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcGadtSyntax' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition algTcRhs (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ algTcRhs _ _ => algTcRhs
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcRhs' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition algTcStupidTheta (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ algTcStupidTheta _ _ _ => algTcStupidTheta
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcStupidTheta' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition famTcFlav (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ famTcFlav _ _ => famTcFlav
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcFlav' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition famTcInj (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ famTcInj => famTcInj
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcInj' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition famTcParent (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ famTcParent _ => famTcParent
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcParent' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition famTcResVar (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ famTcResVar _ _ _ => famTcResVar
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `famTcResVar' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition isUnlifted (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ isUnlifted _ => isUnlifted
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `isUnlifted' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition primRepName (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ primRepName => primRepName
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `primRepName' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition synIsFamFree (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ synIsFamFree => synIsFamFree
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsFamFree' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition synIsTau (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ synIsTau _ => synIsTau
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synIsTau' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition synTcRhs (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ synTcRhs _ _ => synTcRhs
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `synTcRhs' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition tcRepName (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ tcRepName => tcRepName
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ tcRepName _ => tcRepName
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRepName' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition tcRoles (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRoles' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ tcRoles _ _ _ _ _ _ => tcRoles
  | SynonymTyCon _ _ _ _ _ _ _ tcRoles _ _ _ => tcRoles
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRoles' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ tcRoles _ _ => tcRoles
  | PromotedDataCon _ _ _ _ _ _ tcRoles _ _ _ => tcRoles
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcRoles' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition tcTyConFlavour (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConFlavour' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ tcTyConFlavour => tcTyConFlavour
  end.

Definition tcTyConScopedTyVars (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tcTyConScopedTyVars' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ tcTyConScopedTyVars _ => tcTyConScopedTyVars
  end.

Definition tyConArity (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ tyConArity _ => tyConArity
  | AlgTyCon _ _ _ _ _ _ tyConArity _ _ _ _ _ _ _ => tyConArity
  | SynonymTyCon _ _ _ _ _ _ tyConArity _ _ _ _ => tyConArity
  | FamilyTyCon _ _ _ _ _ _ tyConArity _ _ _ _ => tyConArity
  | PrimTyCon _ _ _ _ _ tyConArity _ _ _ => tyConArity
  | PromotedDataCon _ _ _ _ _ tyConArity _ _ _ _ => tyConArity
  | TcTyCon _ _ _ _ _ _ tyConArity _ _ => tyConArity
  end.

Definition tyConBinders (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ tyConBinders _ _ _ _ => tyConBinders
  | AlgTyCon _ _ tyConBinders _ _ _ _ _ _ _ _ _ _ _ => tyConBinders
  | SynonymTyCon _ _ tyConBinders _ _ _ _ _ _ _ _ => tyConBinders
  | FamilyTyCon _ _ tyConBinders _ _ _ _ _ _ _ _ => tyConBinders
  | PrimTyCon _ _ tyConBinders _ _ _ _ _ _ => tyConBinders
  | PromotedDataCon _ _ tyConBinders _ _ _ _ _ _ _ => tyConBinders
  | TcTyCon _ _ tyConBinders _ _ _ _ _ _ => tyConBinders
  end.

Definition tyConCType (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ tyConCType _ _ _ _ _ => tyConCType
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConCType' has no match in constructor `TcTyCon' of type `TyCon'")
  end.

Definition tyConKind (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ tyConKind _ _ => tyConKind
  | AlgTyCon _ _ _ _ _ tyConKind _ _ _ _ _ _ _ _ => tyConKind
  | SynonymTyCon _ _ _ _ _ tyConKind _ _ _ _ _ => tyConKind
  | FamilyTyCon _ _ _ _ _ tyConKind _ _ _ _ _ => tyConKind
  | PrimTyCon _ _ _ _ tyConKind _ _ _ _ => tyConKind
  | PromotedDataCon _ _ _ _ tyConKind _ _ _ _ _ => tyConKind
  | TcTyCon _ _ _ _ _ tyConKind _ _ _ => tyConKind
  end.

Definition tyConName (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ tyConName _ _ _ _ _ => tyConName
  | AlgTyCon _ tyConName _ _ _ _ _ _ _ _ _ _ _ _ => tyConName
  | SynonymTyCon _ tyConName _ _ _ _ _ _ _ _ _ => tyConName
  | FamilyTyCon _ tyConName _ _ _ _ _ _ _ _ _ => tyConName
  | PrimTyCon _ tyConName _ _ _ _ _ _ _ => tyConName
  | PromotedDataCon _ tyConName _ _ _ _ _ _ _ _ => tyConName
  | TcTyCon _ tyConName _ _ _ _ _ _ _ => tyConName
  end.

Definition tyConResKind (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ tyConResKind _ _ _ => tyConResKind
  | AlgTyCon _ _ _ _ tyConResKind _ _ _ _ _ _ _ _ _ => tyConResKind
  | SynonymTyCon _ _ _ _ tyConResKind _ _ _ _ _ _ => tyConResKind
  | FamilyTyCon _ _ _ _ tyConResKind _ _ _ _ _ _ => tyConResKind
  | PrimTyCon _ _ _ tyConResKind _ _ _ _ _ => tyConResKind
  | PromotedDataCon _ _ _ tyConResKind _ _ _ _ _ _ => tyConResKind
  | TcTyCon _ _ _ _ tyConResKind _ _ _ _ => tyConResKind
  end.

Definition tyConTyVars (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConTyVars' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ tyConTyVars _ _ _ _ _ _ _ _ _ _ => tyConTyVars
  | SynonymTyCon _ _ _ tyConTyVars _ _ _ _ _ _ _ => tyConTyVars
  | FamilyTyCon _ _ _ tyConTyVars _ _ _ _ _ _ _ => tyConTyVars
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConTyVars' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tyConTyVars' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ tyConTyVars _ _ _ _ _ => tyConTyVars
  end.

Definition tyConUnique (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon tyConUnique _ _ _ _ _ _ => tyConUnique
  | AlgTyCon tyConUnique _ _ _ _ _ _ _ _ _ _ _ _ _ => tyConUnique
  | SynonymTyCon tyConUnique _ _ _ _ _ _ _ _ _ _ => tyConUnique
  | FamilyTyCon tyConUnique _ _ _ _ _ _ _ _ _ _ => tyConUnique
  | PrimTyCon tyConUnique _ _ _ _ _ _ _ _ => tyConUnique
  | PromotedDataCon tyConUnique _ _ _ _ _ _ _ _ _ => tyConUnique
  | TcTyCon tyConUnique _ _ _ _ _ _ _ _ => tyConUnique
  end.

Definition data_cons (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon data_cons _ => data_cons
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon data_cons => data_cons
  | NewTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_cons' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

Definition is_enum (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ is_enum => is_enum
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `is_enum' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

Definition nt_co (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_co' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ nt_co => nt_co
  end.

Definition nt_etad_rhs (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_etad_rhs' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ nt_etad_rhs _ => nt_etad_rhs
  end.

Definition nt_rhs (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
  | SumTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `nt_rhs' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ nt_rhs _ _ => nt_rhs
  end.

Definition tup_sort (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon _ tup_sort => tup_sort
  | SumTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tup_sort' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

Definition dcEqSpec (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ dcEqSpec _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcEqSpec.

Definition dcExTyVars (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ dcExTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcExTyVars.

Definition dcFields (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ dcFields _ _ _ _ _ _ _ _ := arg_0__ in
  dcFields.

Definition dcInfix (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcInfix _ := arg_0__ in
  dcInfix.

Definition dcName (arg_0__ : DataCon) :=
  let 'MkData dcName _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcName.

Definition dcOrigArgTys (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ dcOrigArgTys _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcOrigArgTys.

Definition dcOrigResTy (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ dcOrigResTy _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcOrigResTy.

Definition dcOtherTheta (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ dcOtherTheta _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcOtherTheta.

Definition dcPromoted (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcPromoted := arg_0__ in
  dcPromoted.

Definition dcRep (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRep _ _ _ _ _ _ := arg_0__ in
  dcRep.

Definition dcRepArity (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepArity _ _ _ _ _ := arg_0__ in
  dcRepArity.

Definition dcRepTyCon (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepTyCon _ _ _ := arg_0__ in
  dcRepTyCon.

Definition dcRepType (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcRepType _ _ := arg_0__ in
  dcRepType.

Definition dcSourceArity (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcSourceArity _ _ _ _ :=
    arg_0__ in
  dcSourceArity.

Definition dcSrcBangs (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ dcSrcBangs _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcSrcBangs.

Definition dcStupidTheta (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ dcStupidTheta _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcStupidTheta.

Definition dcTag (arg_0__ : DataCon) :=
  let 'MkData _ _ dcTag _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcTag.

Definition dcUnique (arg_0__ : DataCon) :=
  let 'MkData _ dcUnique _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcUnique.

Definition dcUnivTyVars (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ dcUnivTyVars _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcUnivTyVars.

Definition dcUserTyVarBinders (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ dcUserTyVarBinders _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
    arg_0__ in
  dcUserTyVarBinders.

Definition dcVanilla (arg_0__ : DataCon) :=
  let 'MkData _ _ _ dcVanilla _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  dcVanilla.

Definition dcWorkId (arg_0__ : DataCon) :=
  let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ dcWorkId _ _ _ _ _ _ _ := arg_0__ in
  dcWorkId.

Definition dcr_arg_tys (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_arg_tys' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ dcr_arg_tys _ _ => dcr_arg_tys
  end.

Definition dcr_bangs (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_bangs' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ _ _ dcr_bangs => dcr_bangs
  end.

Definition dcr_boxer (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_boxer' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ dcr_boxer _ _ _ => dcr_boxer
  end.

Definition dcr_stricts (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_stricts' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR _ _ _ dcr_stricts _ => dcr_stricts
  end.

Definition idScope (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `idScope' has no match in constructor `Mk_TyVar' of type `Var'")
  | Mk_TcTyVar _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `idScope' has no match in constructor `Mk_TcTyVar' of type `Var'")
  | Mk_Id _ _ _ idScope _ _ => idScope
  end.

Definition id_details (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_details' has no match in constructor `Mk_TyVar' of type `Var'")
  | Mk_TcTyVar _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_details' has no match in constructor `Mk_TcTyVar' of type `Var'")
  | Mk_Id _ _ _ _ id_details _ => id_details
  end.

Definition realUnique (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar _ realUnique _ => realUnique
  | Mk_TcTyVar _ realUnique _ _ => realUnique
  | Mk_Id _ realUnique _ _ _ _ => realUnique
  end.

Definition tc_tv_details (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tc_tv_details' has no match in constructor `Mk_TyVar' of type `Var'")
  | Mk_TcTyVar _ _ _ tc_tv_details => tc_tv_details
  | Mk_Id _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tc_tv_details' has no match in constructor `Mk_Id' of type `Var'")
  end.

Definition varName (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar varName _ _ => varName
  | Mk_TcTyVar varName _ _ _ => varName
  | Mk_Id varName _ _ _ _ _ => varName
  end.

Definition varType (arg_0__ : Var) :=
  match arg_0__ with
  | Mk_TyVar _ _ varType => varType
  | Mk_TcTyVar _ _ varType _ => varType
  | Mk_Id _ _ varType _ _ _ => varType
  end.

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
  | Mk_DFunId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `Mk_DFunId' of type `IdDetails'")
  | CoVarId =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `CoVarId' of type `IdDetails'")
  | Mk_JoinId _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `sel_naughty' has no match in constructor `Mk_JoinId' of type `IdDetails'")
  end.

Definition psArgs (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ psArgs _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psArgs.

Definition psArity (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ psArity _ _ _ _ _ _ _ _ _ := arg_0__ in
  psArity.

Definition psBuilder (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ _ _ psBuilder := arg_0__ in
  psBuilder.

Definition psExTyVars (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ psExTyVars _ _ _ _ := arg_0__ in
  psExTyVars.

Definition psFieldLabels (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ psFieldLabels _ _ _ _ _ _ _ := arg_0__ in
  psFieldLabels.

Definition psInfix (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ psInfix _ _ _ _ _ _ _ _ := arg_0__ in
  psInfix.

Definition psMatcher (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ _ psMatcher _ := arg_0__ in
  psMatcher.

Definition psName (arg_0__ : PatSyn) :=
  let 'MkPatSyn psName _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psName.

Definition psProvTheta (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ psProvTheta _ _ _ := arg_0__ in
  psProvTheta.

Definition psReqTheta (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ psReqTheta _ _ _ _ _ := arg_0__ in
  psReqTheta.

Definition psResultTy (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ _ _ _ _ psResultTy _ _ := arg_0__ in
  psResultTy.

Definition psUnique (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ psUnique _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  psUnique.

Definition psUnivTyVars (arg_0__ : PatSyn) :=
  let 'MkPatSyn _ _ _ _ _ _ psUnivTyVars _ _ _ _ _ _ := arg_0__ in
  psUnivTyVars.

Definition ru_act (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ ru_act _ _ _ _ _ _ _ _ _ => ru_act
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_act' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_args (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ ru_args _ _ _ _ _ => ru_args
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_args' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_auto (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ ru_auto _ _ _ => ru_auto
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_auto' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_bndrs (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ ru_bndrs _ _ _ _ _ _ => ru_bndrs
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_bndrs' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_fn (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ ru_fn _ _ _ _ _ _ _ _ => ru_fn
  | BuiltinRule _ ru_fn _ _ => ru_fn
  end.

Definition ru_local (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ ru_local => ru_local
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_local' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_name (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule ru_name _ _ _ _ _ _ _ _ _ _ => ru_name
  | BuiltinRule ru_name _ _ _ => ru_name
  end.

Definition ru_nargs (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_nargs' has no match in constructor `Rule' of type `CoreRule'")
  | BuiltinRule _ _ ru_nargs _ => ru_nargs
  end.

Definition ru_origin (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ ru_origin _ _ => ru_origin
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_origin' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_orphan (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ ru_orphan _ => ru_orphan
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_orphan' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_rough (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ ru_rough _ _ _ _ _ _ _ => ru_rough
  | BuiltinRule _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_rough' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_try (arg_0__ : CoreRule) :=
  match arg_0__ with
  | Rule _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `ru_try' has no match in constructor `Rule' of type `CoreRule'")
  | BuiltinRule _ _ _ ru_try => ru_try
  end.

Definition re_base (arg_0__ : RuleEnv) :=
  let 'Mk_RuleEnv re_base _ := arg_0__ in
  re_base.

Definition re_visible_orphs (arg_0__ : RuleEnv) :=
  let 'Mk_RuleEnv _ re_visible_orphs := arg_0__ in
  re_visible_orphs.

Definition envL (arg_0__ : RnEnv2) :=
  let 'RV2 envL _ _ := arg_0__ in
  envL.

Definition envR (arg_0__ : RnEnv2) :=
  let 'RV2 _ envR _ := arg_0__ in
  envR.

Definition in_scope (arg_0__ : RnEnv2) :=
  let 'RV2 _ _ in_scope := arg_0__ in
  in_scope.

(* Midamble *)

(*  IdInfo: midamble *)

Require GHC.Err.

(* --------------------- *)


(*****)

Instance Default_RuleInfo : GHC.Err.Default RuleInfo :=
  GHC.Err.Build_Default _ EmptyRuleInfo.

Instance Default_Unfolding : GHC.Err.Default Unfolding :=
  GHC.Err.Build_Default _ NoUnfolding.

Instance Default_TickBoxOp : GHC.Err.Default TickBoxOp :=
  GHC.Err.Build_Default _ (TickBox GHC.Err.default GHC.Err.default).

Instance Default_CafInfo : GHC.Err.Default CafInfo :=
  GHC.Err.Build_Default _ MayHaveCafRefs.

Instance Default_Termination {r} : GHC.Err.Default (Termination r) :=
  GHC.Err.Build_Default _ Diverges.

Instance Default_DmdType : GHC.Err.Default DmdType :=
  GHC.Err.Build_Default _ (Mk_DmdType GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default_StrictSig : GHC.Err.Default StrictSig :=
  GHC.Err.Build_Default _ (Mk_StrictSig GHC.Err.default).

Instance Default_JointDmd `{GHC.Err.Default a} `{GHC.Err.Default b} : GHC.Err.Default (JointDmd a b) :=
  GHC.Err.Build_Default _ (JD GHC.Err.default GHC.Err.default).

Instance Default_Str {s} : GHC.Err.Default (Str s) :=
  GHC.Err.Build_Default _ Lazy.
Instance Default_Use {s} : GHC.Err.Default (Use s) :=
  GHC.Err.Build_Default _ Abs.

Instance Default_IdInfo : GHC.Err.Default IdInfo :=
  GHC.Err.Build_Default _ (Mk_IdInfo GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default_TyCon : GHC.Err.Default TyCon :=
  GHC.Err.Build_Default _ (PrimTyCon GHC.Err.default GHC.Err.default nil tt tt GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default ).

Instance Default_RecSelParent : GHC.Err.Default RecSelParent :=
  GHC.Err.Build_Default _ (RecSelData GHC.Err.default).

Instance Default__Var : GHC.Err.Default Var := GHC.Err.Build_Default _ (Mk_Id GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default__DataCon : GHC.Err.Default DataCon :=
 Err.Build_Default _ (MkData GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default nil nil nil nil tt tt nil tt nil nil GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default tt GHC.Err.default GHC.Err.default).
(* ---- TyCon midamble ----- *)
Instance Default__AlgTyConFlav : Err.Default AlgTyConFlav :=
  Err.Build_Default _ (VanillaAlgTyCon Err.default).
Instance Default__RuntimRepInfo : Err.Default RuntimeRepInfo :=
  Err.Build_Default _ NoRRI.




Instance Name_NamedThing_TyCoVar : Name.NamedThing TyCoVar.
Admitted.
Instance Name_NamedThing_VarId : Name.NamedThing Id.
Admitted.
(* ------------- VarEnv midamble.v ------------ *)
Require GHC.Err.

Instance Default__InScopeSet : GHC.Err.Default InScopeSet :=
  GHC.Err.Build_Default _ (InScope GHC.Err.default GHC.Err.default).
Instance Default__RnEnv2 : GHC.Err.Default RnEnv2 :=
  GHC.Err.Build_Default _ (RV2 GHC.Err.default GHC.Err.default GHC.Err.default).
Instance Default__TidyEnv : GHC.Err.Default TidyEnv :=
  GHC.Err.Build_Default _ (pair GHC.Err.default GHC.Err.default).


(* ------------- CoreSyn midamble.v ------------ *)
Require Import Coq.ZArith.ZArith.
Require Import Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

Ltac intro_split := 
  try intros [? [? [? ?]]];
  try intros [? [? ?]];
  try intros [? ?].
  
Ltac distinguish3 := 
  split; intros; unfold not;  intro_split; discriminate.

Ltac solve_collectAnnArgsTicks :=   
  Tactics.program_simpl;
  try solve [distinguish3];
  try solve [repeat match goal with [ f : AnnExpr _ _ |- _ ] => destruct f end;
             Tactics.program_simpl;
             omega].

(* This function is needed to show the termination of collectAnnArgs, 
   collectAnnArgsTicks. *)
Fixpoint size_AnnExpr' {a}{b} (e: AnnExpr' a b) :=
  match e with 
  | AnnVar _ => 0
  | AnnLit _ => 0
  | AnnLam _ (_ , bdy) => S (size_AnnExpr' bdy)
  | AnnApp (_,e1) (_, e2) => S (size_AnnExpr' e1 + size_AnnExpr' e2)
  | AnnCase (_,scrut) bndr _ alts => 
    S (size_AnnExpr' scrut + 
       List.fold_right plus 0 
                          (List.map (fun p =>
                                       match p with 
                                         | (_,_,(_,e)) => size_AnnExpr' e
                                    end) 
                                    alts))
  | AnnLet (AnnNonRec v (_,rhs)) (_,body) => 
        S (size_AnnExpr' rhs + size_AnnExpr' body)
  | AnnLet (AnnRec pairs) (_,body) => 
        S (Lists.List.fold_right plus 0 
          (Lists.List.map (fun p => size_AnnExpr' (snd (snd p))) pairs) +
           size_AnnExpr' body)

  | AnnCast (_,e) _ => S (size_AnnExpr' e)
  | AnnTick _ (_,e) => S (size_AnnExpr' e)
  | AnnType _ => 0
  | AnnCoercion _ => 0
  end.

(* ---------------------------------- *)

Instance Default__Expr {b} : GHC.Err.Default (Expr b) :=
  GHC.Err.Build_Default _ (Mk_Var GHC.Err.default).

Instance Default__Tickish {a} : GHC.Err.Default (Tickish a) :=
  GHC.Err.Build_Default _ (Breakpoint GHC.Err.default GHC.Err.default).

Instance Default_TaggedBndr {t}`{GHC.Err.Default t} : GHC.Err.Default (TaggedBndr t) :=
  GHC.Err.Build_Default _ (TB GHC.Err.default GHC.Err.default).

Instance Default__AnnExpr' {a}{b} : GHC.Err.Default (AnnExpr' a b) :=
  GHC.Err.Build_Default _ (AnnVar GHC.Err.default). 

Instance Default__AnnBind {a}{b} : GHC.Err.Default (AnnBind a b) :=
  GHC.Err.Build_Default _ (AnnRec GHC.Err.default). 

Instance Default__Bind {b} : GHC.Err.Default (Bind b) :=
  GHC.Err.Build_Default _ (Rec GHC.Err.default). 

Instance Default__CoreVect : GHC.Err.Default CoreVect :=
  GHC.Err.Build_Default _ (Vect GHC.Err.default GHC.Err.default). 

Instance Default__CoreRule : GHC.Err.Default CoreRule :=
  GHC.Err.Build_Default _ (BuiltinRule GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default__RuleEnv : GHC.Err.Default RuleEnv :=
  GHC.Err.Build_Default _ (Mk_RuleEnv GHC.Err.default GHC.Err.default).


(* ---------------------------------- *)

(* See comments in CoreSyn/edits file. We can't use termination edits for collect. *)

Definition collectNAnnBndrs {bndr} {annot}`{GHC.Err.Default annot}
    : nat -> AnnExpr bndr annot -> (list bndr * AnnExpr bndr annot)%type :=
          fun orig_n e =>
            let fix collect (arg_0__:nat) (arg_1__ : list bndr) (arg_2__:AnnExpr bndr annot) :=
                               match arg_0__, arg_1__, arg_2__ with
                               | O, bs, body =>
                                 pair (GHC.List.reverse bs) body 
                               | S m, bs, body =>
                                   match arg_0__, arg_1__, arg_2__ with
                                   | n, bs, pair _ (AnnLam b body) => collect m (cons b bs) body
                                   | _, _, _ =>
                                       Panic.panicStr (GHC.Base.hs_string__ "collectNBinders") Panic.someSDoc
                                   end
                               end in
            collect orig_n nil e.
(* DEMAND midamble file. Termination defs and tactics . *)

Require Import GHC.Nat.
Require Import Omega.

Ltac solve_not_zero_N := match goal with 
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] => 
    unfold GHC.Base.op_zeze__ in H;
    unfold GHC.Base.Eq_Char___ in H;
    simpl in H;
    apply N.eqb_neq in H end;
    zify;
    omega.
Ltac simpl_not_zero := match goal with 
  | [ H : GHC.Base.op_zeze__ ?x ?y = false |- _ ] =>
  unfold GHC.Base.op_zeze__ in H;
    unfold Eq_nat in H;
    simpl in H;
  apply Nat.eqb_neq in H end.
Ltac solve_error_sub :=
  unfold error_sub;
  let Hltb := fresh in
  let HeqHltb := fresh in
  match goal with 
    [ |- context[ Nat.ltb ?x (Pos.to_nat 1) ] ] =>
    remember (Nat.ltb x (Pos.to_nat 1)) as Hltb eqn:HeqHltb; 
      destruct Hltb;
      symmetry in HeqHltb;
      try (rewrite Nat.ltb_lt in HeqHltb);
      try (rewrite Nat.ltb_ge in HeqHltb);
      try solve [zify; omega]
  end.

Ltac distinguish := split; intros; unfold not; intros [? ?]; discriminate.
Ltac solve_mkWorkerDemand := Tactics.program_simpl; simpl_not_zero; solve_error_sub.

Ltac solve_dmdTransform := Tactics.program_simpl; try solve_mkWorkerDemand; try distinguish.


Instance Unpeel_StrictSig : Prim.Unpeel StrictSig DmdType :=
  Prim.Build_Unpeel _ _ (fun x => match x with | Mk_StrictSig y => y end) Mk_StrictSig.


(* size metric, incase it is useful *)

Definition Str_size {a} (f : a -> nat) (x : Str a) : nat :=
  match x with
  | Lazy => 0
  | Mk_Str _ s => f s
  end.

Fixpoint StrDmd_size (s1 : StrDmd): nat :=
  match s1 with
  | HyperStr => 0
  | SCall s => Nat.add 1 (StrDmd_size s)
  | SProd ss => List.fold_left Nat.add (List.map (Str_size StrDmd_size) ss) 1
  | HeadStr => 0
  end.

Definition ArgStrDmd_size := Str_size StrDmd_size.

(* Converted value declarations: *)

Definition visibleDataCons : AlgTyConRhs -> list DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AbstractTyCon => nil
    | DataTyCon cs _ => cs
    | NewTyCon c _ _ _ => cons c nil
    | TupleTyCon c _ => cons c nil
    | SumTyCon cs => cs
    end.

Definition varUnique : Var -> Unique.Unique :=
  fun var => Unique.mkUniqueGrimily (realUnique var).

Definition vanillaCprProdRes : BasicTypes.Arity -> DmdResult :=
  fun _arity => Dunno RetProd.

Definition vanillaCafInfo : CafInfo :=
  MayHaveCafRefs.

Definition useTop : ArgUse :=
  Mk_Use Many Used.

Definition zap_usg : KillFlags -> UseDmd -> UseDmd :=
  fix zap_usg (arg_0__ : KillFlags) (arg_1__ : UseDmd) : UseDmd
        := let zap_musg (arg_0__ : KillFlags) (arg_1__ : ArgUse) : ArgUse :=
             match arg_0__, arg_1__ with
             | kfs, Abs => if kf_abs kfs : bool then useTop else Abs
             | kfs, Mk_Use c u =>
                 if kf_used_once kfs : bool then Mk_Use Many (zap_usg kfs u) else
                 Mk_Use c (zap_usg kfs u)
             end in
           match arg_0__, arg_1__ with
           | kfs, UCall c u =>
               if kf_called_once kfs : bool then UCall Many (zap_usg kfs u) else
               UCall c (zap_usg kfs u)
           | _, _ =>
               match arg_0__, arg_1__ with
               | kfs, UProd us => UProd (GHC.Base.map (zap_musg kfs) us)
               | _, u => u
               end
           end.

Definition zap_musg : KillFlags -> ArgUse -> ArgUse :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | kfs, Abs => if kf_abs kfs : bool then useTop else Abs
    | kfs, Mk_Use c u =>
        if kf_used_once kfs : bool then Mk_Use Many (zap_usg kfs u) else
        Mk_Use c (zap_usg kfs u)
    end.

Definition useCount {u} : Use u -> Count :=
  fun arg_0__ =>
    match arg_0__ with
    | Abs => One
    | Mk_Use One _ => One
    | _ => Many
    end.

Definition useBot : ArgUse :=
  Abs.

Definition updateVarTypeM {m} `{GHC.Base.Monad m}
   : (unit -> m unit) -> Id -> m Id :=
  fun f id =>
    f (varType id) GHC.Base.>>=
    (fun ty' =>
       GHC.Base.return_ (match id with
                         | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
                             Mk_TyVar varName_0__ realUnique_1__ ty'
                         | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
                             Mk_TcTyVar varName_3__ realUnique_4__ ty' tc_tv_details_6__
                         | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
                         id_info_12__ =>
                             Mk_Id varName_7__ realUnique_8__ ty' idScope_10__ id_details_11__ id_info_12__
                         end)).

Definition updateVarType : (unit -> unit) -> Id -> Id :=
  fun f id =>
    match id with
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar varName_0__ realUnique_1__ (f (varType id))
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar varName_3__ realUnique_4__ (f (varType id)) tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id varName_7__ realUnique_8__ (f (varType id)) idScope_10__ id_details_11__
              id_info_12__
    end.

Definition unwrapNewTyCon_maybe
   : TyCon -> option (list TyVar * unit * list unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ tvs _ _ _ _ _ _ _ (NewTyCon _ rhs _ co) _ _ =>
        Some (pair (pair tvs rhs) co)
    | _ => None
    end.

Definition unwrapNewTyConEtad_maybe
   : TyCon -> option (list TyVar * unit * list unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ (pair tvs rhs) co) _ _ =>
        Some (pair (pair tvs rhs) co)
    | _ => None
    end.

Definition unknownArity : BasicTypes.Arity :=
  #0.

Local Definition Uniquable__Var_getUnique : Var -> Unique.Unique :=
  varUnique.

Program Instance Uniquable__Var : Unique.Uniquable Var :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__Var_getUnique |}.

Definition unitDVarEnv {a} : Var -> a -> DVarEnv a :=
  UniqDFM.unitUDFM.

Definition unitVarEnv {a} : Var -> a -> VarEnv a :=
  UniqFM.unitUFM.

Definition unitDVarSet : Var -> DVarSet :=
  UniqDSet.unitUniqDSet.

Definition unitVarSet : Var -> VarSet :=
  UniqSet.unitUniqSet.

Definition unionVarSets : list VarSet -> VarSet :=
  UniqSet.unionManyUniqSets.

Definition unionVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.unionUniqSets.

Definition unionInScope : InScopeSet -> InScopeSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope s1 _, InScope s2 n2 => InScope (unionVarSet s1 s2) n2
    end.

Definition unionDVarSets : list DVarSet -> DVarSet :=
  UniqDSet.unionManyUniqDSets.

Definition unionDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.unionUniqDSets.

Definition unSaturatedOk : bool :=
  true.

Definition tyVarName : TyVar -> Name.Name :=
  varName.

Definition tyVarKind : TyVar -> unit :=
  varType.

Definition updateTyVarKind : (unit -> unit) -> TyVar -> TyVar :=
  fun update tv =>
    match tv with
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar varName_0__ realUnique_1__ (update (tyVarKind tv))
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar varName_3__ realUnique_4__ (update (tyVarKind tv)) tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id varName_7__ realUnique_8__ (update (tyVarKind tv)) idScope_10__
              id_details_11__ id_info_12__
    end.

Definition updateTyVarKindM {m} `{(GHC.Base.Monad m)}
   : (unit -> m unit) -> TyVar -> m TyVar :=
  fun update tv =>
    update (tyVarKind tv) GHC.Base.>>=
    (fun k' =>
       GHC.Base.return_ (match tv with
                         | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
                             Mk_TyVar varName_0__ realUnique_1__ k'
                         | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
                             Mk_TcTyVar varName_3__ realUnique_4__ k' tc_tv_details_6__
                         | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
                         id_info_12__ =>
                             Mk_Id varName_7__ realUnique_8__ k' idScope_10__ id_details_11__ id_info_12__
                         end)).

Definition tyConTuple_maybe : TyCon -> option BasicTypes.TupleSort :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | TupleTyCon _ sort => Some sort
        | _ => None
        end
    | _ => None
    end.

Definition tyConStupidTheta : TyCon -> list unit :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ stupid _ _ _ => stupid
    | tycon =>
        Panic.panicStr (GHC.Base.hs_string__ "tyConStupidTheta") (Panic.someSDoc)
    end.

Definition tyConSingleDataCon_maybe : TyCon -> option DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | DataTyCon (cons c nil) _ => Some c
        | TupleTyCon c _ => Some c
        | NewTyCon c _ _ _ => Some c
        | _ => None
        end
    | _ => None
    end.

Definition tyConSingleDataCon : TyCon -> DataCon :=
  fun tc =>
    match tyConSingleDataCon_maybe tc with
    | Some c => c
    | None => Panic.panicStr (GHC.Base.hs_string__ "tyConDataCon") (Panic.someSDoc)
    end.

Definition tyConSingleAlgDataCon_maybe : TyCon -> option DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | DataTyCon (cons c nil) _ => Some c
        | TupleTyCon c _ => Some c
        | _ => None
        end
    | _ => None
    end.

Definition tyConRoles : TyCon -> list unit :=
  fun tc =>
    let const_role := fun r => Coq.Lists.List.repeat r (tyConArity tc) in
    match tc with
    | FunTyCon _ _ _ _ _ _ _ => const_role tt
    | AlgTyCon _ _ _ _ _ _ _ roles _ _ _ _ _ _ => roles
    | SynonymTyCon _ _ _ _ _ _ _ roles _ _ _ => roles
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ => const_role tt
    | PrimTyCon _ _ _ _ _ _ roles _ _ => roles
    | PromotedDataCon _ _ _ _ _ _ roles _ _ _ => roles
    | TcTyCon _ _ _ _ _ _ _ _ _ => const_role tt
    end.

Definition tyConRepName_maybe : TyCon -> option TyConRepName :=
  fun arg_0__ =>
    let j_3__ :=
      match arg_0__ with
      | FamilyTyCon _ _ _ _ _ _ _ _ (DataFamilyTyCon rep_nm) _ _ => Some rep_nm
      | PromotedDataCon _ _ _ _ _ _ _ _ rep_nm _ => Some rep_nm
      | _ => None
      end in
    match arg_0__ with
    | FunTyCon _ _ _ _ _ _ rep_nm => Some rep_nm
    | PrimTyCon _ _ _ _ _ _ _ _ mb_rep_nm => mb_rep_nm
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ parent =>
        match parent with
        | VanillaAlgTyCon rep_nm => Some rep_nm
        | _ =>
            match parent with
            | ClassTyCon _ rep_nm => Some rep_nm
            | _ => match parent with | UnboxedAlgTyCon rep_nm => rep_nm | _ => j_3__ end
            end
        end
    | _ => j_3__
    end.

Definition tyConRepModOcc
   : Module.Module -> OccName.OccName -> (Module.Module * OccName.OccName)%type :=
  fun tc_module tc_occ =>
    let rep_module :=
      if tc_module GHC.Base.== PrelNames.gHC_PRIM : bool then PrelNames.gHC_TYPES else
      tc_module in
    pair rep_module (OccName.mkTyConRepOcc tc_occ).

Definition tyConFlavour : TyCon -> TyConFlavour :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ parent =>
        match parent with
        | ClassTyCon _ _ => ClassFlavour
        | _ =>
            match rhs with
            | TupleTyCon _ sort => TupleFlavour (BasicTypes.tupleSortBoxity sort)
            | SumTyCon _ => SumFlavour
            | DataTyCon _ _ => DataTypeFlavour
            | NewTyCon _ _ _ _ => NewtypeFlavour
            | AbstractTyCon => AbstractTypeFlavour
            end
        end
    | FamilyTyCon _ _ _ _ _ _ _ _ flav _ _ =>
        match flav with
        | DataFamilyTyCon _ => DataFamilyFlavour
        | OpenSynFamilyTyCon => OpenTypeFamilyFlavour
        | ClosedSynFamilyTyCon _ => ClosedTypeFamilyFlavour
        | AbstractClosedSynFamilyTyCon => ClosedTypeFamilyFlavour
        | BuiltInSynFamTyCon _ => ClosedTypeFamilyFlavour
        end
    | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ => TypeSynonymFlavour
    | FunTyCon _ _ _ _ _ _ _ => BuiltInTypeFlavour
    | PrimTyCon _ _ _ _ _ _ _ _ _ => BuiltInTypeFlavour
    | PromotedDataCon _ _ _ _ _ _ _ _ _ _ => PromotedDataConFlavour
    | TcTyCon _ _ _ _ _ _ _ _ flav => flav
    end.

Definition tyConFamilySizeAtMost : TyCon -> nat -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ as tc), n =>
        match rhs with
        | DataTyCon cons_ _ => Util.lengthAtMost cons_ n
        | NewTyCon _ _ _ _ => #1 GHC.Base.<= n
        | TupleTyCon _ _ => #1 GHC.Base.<= n
        | SumTyCon cons_ => Util.lengthAtMost cons_ n
        | _ =>
            Panic.panicStr (GHC.Base.hs_string__ "tyConFamilySizeAtMost 1") (Panic.someSDoc)
        end
    | tc, _ =>
        Panic.panicStr (GHC.Base.hs_string__ "tyConFamilySizeAtMost 2") (Panic.someSDoc)
    end.

Definition tyConFamilySize : TyCon -> nat :=
  fun arg_0__ =>
    match arg_0__ with
    | (AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ as tc) =>
        match rhs with
        | DataTyCon cons_ _ => Coq.Lists.List.length cons_
        | NewTyCon _ _ _ _ => #1
        | TupleTyCon _ _ => #1
        | SumTyCon cons_ => Coq.Lists.List.length cons_
        | _ =>
            Panic.panicStr (GHC.Base.hs_string__ "tyConFamilySize 1") (Panic.someSDoc)
        end
    | tc =>
        Panic.panicStr (GHC.Base.hs_string__ "tyConFamilySize 2") (Panic.someSDoc)
    end.

Definition tyConFamilyResVar_maybe : TyCon -> option Name.Name :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ res _ _ _ => res
    | _ => None
    end.

Definition tyConFamilyCoercion_maybe : TyCon -> option (list unit) :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (DataFamInstTyCon ax _ _) => Some ax
    | _ => None
    end.

Definition tyConFamInst_maybe : TyCon -> option (TyCon * list unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (DataFamInstTyCon _ f ts) =>
        Some (pair f ts)
    | _ => None
    end.

Definition tyConFamInstSig_maybe
   : TyCon -> option (TyCon * list unit * list unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (DataFamInstTyCon ax f ts) =>
        Some (pair (pair f ts) ax)
    | _ => None
    end.

Definition tyConDataCons_maybe : TyCon -> option (list DataCon) :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | DataTyCon cons_ _ => Some cons_
        | NewTyCon con _ _ _ => Some (cons con nil)
        | TupleTyCon con _ => Some (cons con nil)
        | SumTyCon cons_ => Some cons_
        | _ => None
        end
    | _ => None
    end.

Definition tyConDataCons : TyCon -> list DataCon :=
  fun tycon => Maybes.orElse (tyConDataCons_maybe tycon) nil.

Definition tyConClass_maybe : TyCon -> option Class :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (ClassTyCon clas _) => Some clas
    | _ => None
    end.

Definition tyConCType_maybe : TyCon -> option unit :=
  fun arg_0__ =>
    match arg_0__ with
    | (AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ as tc) => tyConCType tc
    | _ => None
    end.

Definition tyConBinderArgFlag : TyConBinder -> ArgFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | TvBndr _ (NamedTCB vis) => vis
    | TvBndr _ AnonTCB => Required
    end.

Definition tyConAssoc_maybe : TyCon -> option Class :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ _ mb_cls _ => mb_cls
    | _ => None
    end.

Definition trimCPRInfo : bool -> bool -> DmdResult -> DmdResult :=
  fun trim_all trim_sums res =>
    let trimC :=
      fun arg_0__ =>
        match arg_0__ with
        | RetSum n => if orb trim_all trim_sums : bool then NoCPR else RetSum n
        | RetProd => if trim_all : bool then NoCPR else RetProd
        | NoCPR => NoCPR
        end in
    let trimR :=
      fun arg_5__ =>
        match arg_5__ with
        | Dunno c => Dunno (trimC c)
        | res => res
        end in
    trimR res.

Definition strBot : ArgStr :=
  Mk_Str VanStr HyperStr.

Definition botDmd : Demand :=
  JD strBot useBot.

Definition topDmd : Demand :=
  JD Lazy useTop.

Definition resTypeArgDmd {r} : Termination r -> Demand :=
  fun arg_0__ => match arg_0__ with | Dunno _ => topDmd | _ => botDmd end.

Definition topRes : DmdResult :=
  Dunno NoCPR.

Definition zapDemandInfo : IdInfo -> option IdInfo :=
  fun info =>
    Some (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
             oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
             callArityInfo_9__ levityInfo_10__ := info in
          Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                    oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ topDmd
                    callArityInfo_9__ levityInfo_10__).

Definition toBothDmdArg : DmdType -> BothDmdArg :=
  fun '(Mk_DmdType fv _ r) =>
    let go :=
      fun arg_1__ =>
        match arg_1__ with
        | Dunno _ => Dunno tt
        | ThrowsExn => ThrowsExn
        | Diverges => Diverges
        end in
    pair fv (go r).

Definition tidyPatSynIds : (Id -> Id) -> PatSyn -> PatSyn :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | tidy_fn, (MkPatSyn _ _ _ _ _ _ _ _ _ _ _ matcher builder as ps) =>
        let tidy_pr := fun '(pair id dummy) => pair (tidy_fn id) dummy in
        let 'MkPatSyn psName_5__ psUnique_6__ psArgs_7__ psArity_8__ psInfix_9__
           psFieldLabels_10__ psUnivTyVars_11__ psReqTheta_12__ psExTyVars_13__
           psProvTheta_14__ psResultTy_15__ psMatcher_16__ psBuilder_17__ := ps in
        MkPatSyn psName_5__ psUnique_6__ psArgs_7__ psArity_8__ psInfix_9__
                 psFieldLabels_10__ psUnivTyVars_11__ psReqTheta_12__ psExTyVars_13__
                 psProvTheta_14__ psResultTy_15__ (tidy_pr matcher) (GHC.Base.fmap tidy_pr
                  builder)
    end.

Definition tickishScoped {id} : Tickish id -> TickishScoping :=
  fun arg_0__ =>
    match arg_0__ with
    | (ProfNote _ _ _ as n) =>
        if profNoteScope n : bool then CostCentreScope else
        NoScope
    | HpcTick _ _ => NoScope
    | Breakpoint _ _ => CostCentreScope
    | SourceNote _ _ => SoftScope
    end.

Definition tickishScopesLike {id} : Tickish id -> TickishScoping -> bool :=
  fun t scope =>
    let like :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | NoScope, _ => true
        | _, NoScope => false
        | SoftScope, _ => true
        | _, SoftScope => false
        | CostCentreScope, _ => true
        end in
    like (tickishScoped t) scope.

Definition tickishPlace {id} : Tickish id -> TickishPlacement :=
  fun arg_0__ =>
    match arg_0__ with
    | (ProfNote _ _ _ as n) =>
        if profNoteCount n : bool then PlaceRuntime else
        PlaceCostCentre
    | HpcTick _ _ => PlaceRuntime
    | Breakpoint _ _ => PlaceRuntime
    | SourceNote _ _ => PlaceNonLam
    end.

Axiom tickishIsCode : forall {id}, Tickish id -> bool.

Axiom tickishCounts : forall {id}, Tickish id -> bool.

Definition tickishFloatable {id} : Tickish id -> bool :=
  fun t => andb (tickishScopesLike t SoftScope) (negb (tickishCounts t)).

Definition tcTyVarDetails : TyVar -> unit :=
  fun x => tt.

Definition tcFlavourIsOpen : TyConFlavour -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | DataFamilyFlavour => true
    | OpenTypeFamilyFlavour => true
    | ClosedTypeFamilyFlavour => false
    | ClassFlavour => false
    | DataTypeFlavour => false
    | NewtypeFlavour => false
    | TupleFlavour _ => false
    | SumFlavour => false
    | AbstractTypeFlavour => false
    | BuiltInTypeFlavour => false
    | PromotedDataConFlavour => false
    | TypeSynonymFlavour => false
    end.

Definition tcFlavourCanBeUnsaturated : TyConFlavour -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | ClassFlavour => true
    | DataTypeFlavour => true
    | NewtypeFlavour => true
    | DataFamilyFlavour => true
    | TupleFlavour _ => true
    | SumFlavour => true
    | AbstractTypeFlavour => true
    | BuiltInTypeFlavour => true
    | PromotedDataConFlavour => true
    | TypeSynonymFlavour => false
    | OpenTypeFamilyFlavour => false
    | ClosedTypeFamilyFlavour => false
    end.

Definition synTyConRhs_maybe : TyCon -> option unit :=
  fun arg_0__ =>
    match arg_0__ with
    | SynonymTyCon _ _ _ _ _ _ _ _ rhs _ _ => Some rhs
    | _ => None
    end.

Definition synTyConDefn_maybe : TyCon -> option (list TyVar * unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | SynonymTyCon _ _ _ tyvars _ _ _ _ ty _ _ => Some (pair tyvars ty)
    | _ => None
    end.

Definition strictenDmd : Demand -> CleanDemand :=
  fun '(JD s u) =>
    let poke_u :=
      fun arg_1__ => match arg_1__ with | Abs => UHead | Mk_Use _ u => u end in
    let poke_s :=
      fun arg_3__ => match arg_3__ with | Lazy => HeadStr | Mk_Str _ s => s end in
    JD (poke_s s) (poke_u u).

Definition strictSigDmdEnv : StrictSig -> DmdEnv :=
  fun '(Mk_StrictSig (Mk_DmdType env _ _)) => env.

Definition strictApply1Dmd : Demand :=
  JD (Mk_Str VanStr (SCall HeadStr)) (Mk_Use Many (UCall One Used)).

Definition strTop : ArgStr :=
  Lazy.

Definition splitUseProdDmd : nat -> UseDmd -> option (list ArgUse) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, Used => Some (Coq.Lists.List.repeat useTop n)
    | n, UHead => Some (Coq.Lists.List.repeat Abs n)
    | n, UProd ds =>
        Panic.warnPprTrace (negb (Util.lengthIs ds n)) (GHC.Base.hs_string__
                            "ghc/compiler/basicTypes/Demand.hs") #645 (Datatypes.id (GHC.Base.hs_string__
                                                                                     "splitUseProdDmd")) (Some ds)
    | _, UCall _ _ => None
    end.

Definition splitStrictSig : StrictSig -> (list Demand * DmdResult)%type :=
  fun '(Mk_StrictSig (Mk_DmdType _ dmds res)) => pair dmds res.

Definition splitStrProdDmd : nat -> StrDmd -> option (list ArgStr) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, HyperStr => Some (Coq.Lists.List.repeat strBot n)
    | n, HeadStr => Some (Coq.Lists.List.repeat strTop n)
    | n, SProd ds =>
        Panic.warnPprTrace (negb (Util.lengthIs ds n)) (GHC.Base.hs_string__
                            "ghc/compiler/basicTypes/Demand.hs") #359 (Datatypes.id (GHC.Base.hs_string__
                                                                                     "splitStrProdDmd")) (Some ds)
    | _, SCall _ => None
    end.

Definition splitArgStrProdDmd : nat -> ArgStr -> option (list ArgStr) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, Lazy => Some (Coq.Lists.List.repeat Lazy n)
    | n, Mk_Str _ s => splitStrProdDmd n s
    end.

Definition sizeVarSet : VarSet -> nat :=
  UniqSet.sizeUniqSet.

Definition sizeDVarSet : DVarSet -> nat :=
  UniqDSet.sizeUniqDSet.

Definition setVarUnique : Var -> Unique.Unique -> Var :=
  fun var uniq =>
    match var with
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq)
                 varType_2__
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq)
                   varType_5__ tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq) varType_9__
              idScope_10__ id_details_11__ id_info_12__
    end.

Definition setVarType : Id -> unit -> Id :=
  fun id ty =>
    match id with
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar varName_0__ realUnique_1__ ty
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar varName_3__ realUnique_4__ ty tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id varName_7__ realUnique_8__ ty idScope_10__ id_details_11__ id_info_12__
    end.

Definition setVarName : Var -> Name.Name -> Var :=
  fun var new_name =>
    match var with
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar new_name (Unique.getKey (Unique.getUnique new_name)) varType_2__
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar new_name (Unique.getKey (Unique.getUnique new_name)) varType_5__
                   tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id new_name (Unique.getKey (Unique.getUnique new_name)) varType_9__
              idScope_10__ id_details_11__ id_info_12__
    end.

Definition setUnfoldingInfo : IdInfo -> Unfolding -> IdInfo :=
  fun info uf =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ uf cafInfo_3__ oneShotInfo_4__
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

Definition setTyVarUnique : TyVar -> Unique.Unique -> TyVar :=
  setVarUnique.

Definition setTyVarName : TyVar -> Name.Name -> TyVar :=
  setVarName.

Definition setTyVarKind : TyVar -> unit -> TyVar :=
  fun tv k =>
    match tv with
    | Mk_TyVar varName_0__ realUnique_1__ varType_2__ =>
        Mk_TyVar varName_0__ realUnique_1__ k
    | Mk_TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        Mk_TcTyVar varName_3__ realUnique_4__ k tc_tv_details_6__
    | Mk_Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Mk_Id varName_7__ realUnique_8__ k idScope_10__ id_details_11__ id_info_12__
    end.

Definition setTcTyVarDetails : TyVar -> unit -> TyVar :=
  fun tv details =>
    match tv with
    | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_TcTyVar varName_0__ realUnique_1__ varType_2__ tc_tv_details_3__ =>
        Mk_TcTyVar varName_0__ realUnique_1__ varType_2__ details
    | Mk_Id _ _ _ _ _ _ =>
        GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    end.

Definition setStrictnessInfo : IdInfo -> StrictSig -> IdInfo :=
  fun info dd =>
    GHC.Prim.seq dd (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                            oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ dd demandInfo_8__
                            callArityInfo_9__ levityInfo_10__).

Definition setRuleInfoHead : Name.Name -> RuleInfo -> RuleInfo :=
  fun x y => EmptyRuleInfo.

Definition setRuleInfo : IdInfo -> RuleInfo -> IdInfo :=
  fun info sp =>
    GHC.Prim.seq sp (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ sp unfoldingInfo_2__ cafInfo_3__ oneShotInfo_4__
                            inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
                            callArityInfo_9__ levityInfo_10__).

Definition setRuleIdName : Name.Name -> CoreRule -> CoreRule :=
  fun nm ru =>
    match ru with
    | Rule ru_name_0__ ru_act_1__ ru_fn_2__ ru_rough_3__ ru_bndrs_4__ ru_args_5__
    ru_rhs_6__ ru_auto_7__ ru_origin_8__ ru_orphan_9__ ru_local_10__ =>
        Rule ru_name_0__ ru_act_1__ nm ru_rough_3__ ru_bndrs_4__ ru_args_5__ ru_rhs_6__
             ru_auto_7__ ru_origin_8__ ru_orphan_9__ ru_local_10__
    | BuiltinRule ru_name_11__ ru_fn_12__ ru_nargs_13__ ru_try_14__ =>
        BuiltinRule ru_name_11__ nm ru_nargs_13__ ru_try_14__
    end.

Definition setOneShotInfo : IdInfo -> BasicTypes.OneShotInfo -> IdInfo :=
  fun info lb =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__ lb
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

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

Axiom resultIsLevPoly : unit -> bool.

Definition setNeverLevPoly `{Util.HasDebugCallStack}
   : IdInfo -> unit -> IdInfo :=
  fun info ty =>
    if andb Util.debugIsOn (negb (negb (resultIsLevPoly ty))) : bool
    then (GHC.Err.error Panic.someSDoc)
    else let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
            oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
            callArityInfo_9__ levityInfo_10__ := info in
         Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                   oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
                   callArityInfo_9__ NeverLevityPolymorphic.

Definition setInlinePragInfo : IdInfo -> BasicTypes.InlinePragma -> IdInfo :=
  fun info pr =>
    GHC.Prim.seq pr (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                            oneShotInfo_4__ pr occInfo_6__ strictnessInfo_7__ demandInfo_8__
                            callArityInfo_9__ levityInfo_10__).

Definition setIdExported : Id -> Id :=
  fun arg_0__ =>
    match arg_0__ with
    | (Mk_Id _ _ _ (LocalId _) _ _ as id) =>
        match id with
        | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | Mk_TcTyVar _ _ _ _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | Mk_Id varName_1__ realUnique_2__ varType_3__ idScope_4__ id_details_5__
        id_info_6__ =>
            Mk_Id varName_1__ realUnique_2__ varType_3__ (LocalId Exported) id_details_5__
                  id_info_6__
        end
    | (Mk_Id _ _ _ GlobalId _ _ as id) => id
    | tv => Panic.panicStr (GHC.Base.hs_string__ "setIdExported") (Panic.someSDoc)
    end.

Definition setIdDetails : Id -> IdDetails -> Id :=
  fun id details =>
    match id with
    | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_TcTyVar _ _ _ _ =>
        GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
    id_info_5__ =>
        Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ details id_info_5__
    end.

Definition setDemandInfo : IdInfo -> Demand -> IdInfo :=
  fun info dd =>
    GHC.Prim.seq dd (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                        cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                        demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
                  Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                            oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ dd
                            callArityInfo_9__ levityInfo_10__).

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

Definition setCafInfo : IdInfo -> CafInfo -> IdInfo :=
  fun info caf =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ caf oneShotInfo_4__
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

Definition setArityInfo : IdInfo -> ArityInfo -> IdInfo :=
  fun info ar =>
    let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
       oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
       callArityInfo_9__ levityInfo_10__ := info in
    Mk_IdInfo ar ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__ oneShotInfo_4__
              inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
              callArityInfo_9__ levityInfo_10__.

Definition seqVarSet : VarSet -> unit :=
  fun s => GHC.Prim.seq (sizeVarSet s) tt.

Definition seqUseDmd : UseDmd -> unit :=
  fun x => tt.

Definition seqStrictSig : StrictSig -> unit :=
  fun x => tt.

Definition seqStrDmdList : list ArgStr -> unit :=
  fun x => tt.

Definition seqStrDmd : StrDmd -> unit :=
  fun x => tt.

Definition seqDmdType : DmdType -> unit :=
  fun x => tt.

Definition seqDmdResult : DmdResult -> unit :=
  fun x => tt.

Definition seqDmdEnv : DmdEnv -> unit :=
  fun x => tt.

Definition seqDmd : Demand :=
  JD (Mk_Str VanStr HeadStr) (Mk_Use One UHead).

Definition seqDemandList : list Demand -> unit :=
  fun x => tt.

Definition seqDemand : Demand -> unit :=
  fun x => tt.

Definition seqDVarSet : DVarSet -> unit :=
  fun s => GHC.Prim.seq (sizeDVarSet s) tt.

Definition seqCPRResult : CPRResult -> unit :=
  fun x => tt.

Definition seqArgUseList : list ArgUse -> unit :=
  fun x => tt.

Definition seqArgUse : ArgUse -> unit :=
  fun x => tt.

Definition seqArgStr : ArgStr -> unit :=
  fun x => tt.

Definition saturatedByOneShots : nat -> Demand -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | n, JD _ usg =>
        let fix go arg_2__ arg_3__
                  := match arg_2__, arg_3__ with
                     | num_4__, _ =>
                         if num_4__ GHC.Base.== #0 : bool then true else
                         match arg_2__, arg_3__ with
                         | n, UCall One u => go (n GHC.Num.- #1) u
                         | _, _ => false
                         end
                     end in
        match usg with
        | Mk_Use _ arg_usg => go n arg_usg
        | _ => false
        end
    end.

Definition sameVis : ArgFlag -> ArgFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Required, Required => true
    | Required, _ => false
    | _, Required => false
    | _, _ => true
    end.

Definition ruleName : CoreRule -> BasicTypes.RuleName :=
  ru_name.

Definition ruleModule : CoreRule -> option Module.Module :=
  fun arg_0__ =>
    match arg_0__ with
    | Rule _ _ _ _ _ _ _ _ ru_origin _ _ => Some ru_origin
    | BuiltinRule _ _ _ _ => None
    end.

Definition ruleInfoRules : RuleInfo -> list CoreRule :=
  fun x => nil.

Definition ruleIdName : CoreRule -> Name.Name :=
  ru_fn.

Definition ruleArity : CoreRule -> nat :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ n _ => n
    | Rule _ _ _ _ _ args _ _ _ _ _ => Coq.Lists.List.length args
    end.

Definition ruleActivation : CoreRule -> BasicTypes.Activation :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => BasicTypes.AlwaysActive
    | Rule _ act _ _ _ _ _ _ _ _ _ => act
    end.

Definition rnSwap : RnEnv2 -> RnEnv2 :=
  fun '(RV2 envL envR in_scope) => RV2 envR envL in_scope.

Definition rnInScopeSet : RnEnv2 -> InScopeSet :=
  in_scope.

Definition rnEnvR : RnEnv2 -> VarEnv Var :=
  envR.

Definition rnEnvL : RnEnv2 -> VarEnv Var :=
  envL.

Definition rhssOfBind {b} : Bind b -> list (Expr b) :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec _ rhs => cons rhs nil
    | Rec pairs =>
        let cont_2__ arg_3__ := let 'pair _ rhs := arg_3__ in cons rhs nil in
        Coq.Lists.List.flat_map cont_2__ pairs
    end.

Definition rhssOfAlts {b} : list (Alt b) -> list (Expr b) :=
  fun alts =>
    let cont_0__ arg_1__ := let 'pair (pair _ _) e := arg_1__ in cons e nil in
    Coq.Lists.List.flat_map cont_0__ alts.

Definition retCPR_maybe : CPRResult -> option BasicTypes.ConTag :=
  fun arg_0__ =>
    match arg_0__ with
    | RetSum t => Some t
    | RetProd => Some BasicTypes.fIRST_TAG
    | NoCPR => None
    end.

Definition returnsCPR_maybe : DmdResult -> option BasicTypes.ConTag :=
  fun arg_0__ => match arg_0__ with | Dunno c => retCPR_maybe c | _ => None end.

Definition promoteDataCon : DataCon -> TyCon :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc) => tc.

Definition primRepIsFloat : PrimRep -> option bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FloatRep => Some true
    | DoubleRep => Some true
    | VecRep _ _ => None
    | _ => Some false
    end.

Definition primElemRepSizeB : PrimElemRep -> nat :=
  fun arg_0__ =>
    match arg_0__ with
    | Int8ElemRep => #1
    | Int16ElemRep => #2
    | Int32ElemRep => #4
    | Int64ElemRep => #8
    | Word8ElemRep => #1
    | Word16ElemRep => #2
    | Word32ElemRep => #4
    | Word64ElemRep => #8
    | FloatElemRep => #4
    | DoubleElemRep => #8
    end.

Definition pprPromotionQuote : TyCon -> GHC.Base.String :=
  fun tc =>
    match tc with
    | PromotedDataCon _ _ _ _ _ _ _ _ _ _ => Panic.someSDoc
    | _ => Panic.someSDoc
    end.

Definition postProcessDmdResult : Str unit -> DmdResult -> DmdResult :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Lazy, _ => topRes
    | Mk_Str Mk_ExnStr _, ThrowsExn => topRes
    | _, res => res
    end.

Definition plusVarEnv_CD {a}
   : (a -> a -> a) -> VarEnv a -> a -> VarEnv a -> a -> VarEnv a :=
  UniqFM.plusUFM_CD.

Definition plusVarEnv_C {a}
   : (a -> a -> a) -> VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM_C.

Definition plusVarEnvList {a} : list (VarEnv a) -> VarEnv a :=
  UniqFM.plusUFMList.

Definition plusVarEnv {a} : VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM.

Definition plusMaybeVarEnv_C {a}
   : (a -> a -> option a) -> VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusMaybeUFM_C.

Definition plusDVarEnv_C {a}
   : (a -> a -> a) -> DVarEnv a -> DVarEnv a -> DVarEnv a :=
  UniqDFM.plusUDFM_C.

Definition plusDVarEnv {a} : DVarEnv a -> DVarEnv a -> DVarEnv a :=
  UniqDFM.plusUDFM.

Definition peelUseCall : UseDmd -> option (Count * UseDmd)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | UCall c u => Some (pair c u)
    | _ => None
    end.

Program Definition peelManyCalls : nat -> CleanDemand -> DmdShell :=
          fun arg_0__ arg_1__ =>
            match arg_0__, arg_1__ with
            | n, JD str abs =>
                let go_abs : nat -> UseDmd -> Use unit :=
                  GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun (arg_2__ : nat) (arg_3__ : UseDmd) =>
                                   arg_2__) _ (fun (arg_2__ : nat) (arg_3__ : UseDmd) go_abs =>
                                   match arg_2__, arg_3__ with
                                   | num_4__, _ =>
                                       if Bool.Sumbool.sumbool_of_bool (num_4__ GHC.Base.== #0) then Mk_Use One tt else
                                       match arg_2__, arg_3__ with
                                       | n, UCall One d' => go_abs (n GHC.Num.- #1) d'
                                       | _, _ => Mk_Use Many tt
                                       end
                                   end) in
                let go_str : nat -> StrDmd -> Str unit :=
                  GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun (arg_10__ : nat) (arg_11__ : StrDmd) =>
                                   arg_10__) _ (fun (arg_10__ : nat) (arg_11__ : StrDmd) go_str =>
                                   match arg_10__, arg_11__ with
                                   | num_12__, _ =>
                                       if Bool.Sumbool.sumbool_of_bool (num_12__ GHC.Base.== #0)
                                       then Mk_Str VanStr tt else
                                       match arg_10__, arg_11__ with
                                       | _, HyperStr => Mk_Str VanStr tt
                                       | n, SCall d' => go_str (n GHC.Num.- #1) d'
                                       | _, _ => Lazy
                                       end
                                   end) in
                JD (go_str n str) (go_abs n abs)
            end.
Solve Obligations with (solve_dmdTransform).

Definition peelCallDmd : CleanDemand -> (CleanDemand * DmdShell)%type :=
  fun '(JD s u) =>
    let 'pair u' us := (match u with
                          | UCall c u' => pair u' (Mk_Use c tt)
                          | _ => pair Used (Mk_Use Many tt)
                          end) in
    let 'pair s' ss := (match s with
                          | SCall s' => pair s' (Mk_Str VanStr tt)
                          | HyperStr => pair HyperStr (Mk_Str VanStr tt)
                          | _ => pair HeadStr Lazy
                          end) in
    pair (JD s' u') (JD ss us).

Definition patSynUnivTyVarBinders : PatSyn -> list TyVarBinder :=
  psUnivTyVars.

Definition patSynName : PatSyn -> Name.Name :=
  psName.

Definition patSynMatcher : PatSyn -> (Id * bool)%type :=
  psMatcher.

Definition patSynIsInfix : PatSyn -> bool :=
  psInfix.

Definition patSynFieldType : PatSyn -> FieldLabel.FieldLabelString -> unit :=
  fun ps label =>
    match Data.Foldable.find ((fun arg_0__ => arg_0__ GHC.Base.== label) GHC.Base.∘
                              (FieldLabel.flLabel GHC.Base.∘ Data.Tuple.fst)) (GHC.List.zip (psFieldLabels ps)
                                                                                            (psArgs ps)) with
    | Some (pair _ ty) => ty
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "dataConFieldType") (GHC.Base.mappend
                                                                  Panic.someSDoc Panic.someSDoc)
    end.

Definition patSynFieldLabels : PatSyn -> list FieldLabel.FieldLabel :=
  psFieldLabels.

Definition patSynExTyVarBinders : PatSyn -> list TyVarBinder :=
  psExTyVars.

Definition patSynBuilder : PatSyn -> option (Id * bool)%type :=
  psBuilder.

Definition patSynArity : PatSyn -> BasicTypes.Arity :=
  psArity.

Definition patSynArgs : PatSyn -> list unit :=
  psArgs.

Definition partitionVarEnv {a}
   : (a -> bool) -> VarEnv a -> (VarEnv a * VarEnv a)%type :=
  UniqFM.partitionUFM.

Definition partitionDVarSet
   : (Var -> bool) -> DVarSet -> (DVarSet * DVarSet)%type :=
  UniqDSet.partitionUniqDSet.

Definition partitionDVarEnv {a}
   : (a -> bool) -> DVarEnv a -> (DVarEnv a * DVarEnv a)%type :=
  UniqDFM.partitionUDFM.

Definition otherCons : Unfolding -> list AltCon :=
  fun u => nil.

Definition oneifyDmd : Demand -> Demand :=
  fun arg_0__ =>
    match arg_0__ with
    | JD s (Mk_Use _ a) => JD s (Mk_Use One a)
    | jd => jd
    end.

Definition okParent : Name.Name -> AlgTyConFlav -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, VanillaAlgTyCon _ => true
    | _, UnboxedAlgTyCon _ => true
    | tc_name, ClassTyCon cls _ => tc_name GHC.Base.== tyConName (classTyCon cls)
    | _, DataFamInstTyCon _ fam_tc tys => Util.lengthAtLeast tys (tyConArity fam_tc)
    end.

Definition notOrphan : IsOrphan -> bool :=
  fun arg_0__ => match arg_0__ with | NotOrphan _ => true | _ => false end.

Definition nonDetCmpVar : Var -> Var -> comparison :=
  fun a b => Unique.nonDetCmpUnique (varUnique a) (varUnique b).

Definition noUnfolding : Unfolding :=
  NoUnfolding.

Definition newTyConRhs : TyCon -> (list TyVar * unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ tvs _ _ _ _ _ _ _ (NewTyCon _ rhs _ _) _ _ => pair tvs rhs
    | tycon => Panic.panicStr (GHC.Base.hs_string__ "newTyConRhs") (Panic.someSDoc)
    end.

Definition newTyConEtadRhs : TyCon -> (list TyVar * unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ tvs_rhs _) _ _ => tvs_rhs
    | tycon =>
        Panic.panicStr (GHC.Base.hs_string__ "newTyConEtadRhs") (Panic.someSDoc)
    end.

Definition newTyConEtadArity : TyCon -> nat :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ tvs_rhs _) _ _ =>
        Coq.Lists.List.length (Data.Tuple.fst tvs_rhs)
    | tycon =>
        Panic.panicStr (GHC.Base.hs_string__ "newTyConEtadArity") (Panic.someSDoc)
    end.

Definition newTyConDataCon_maybe : TyCon -> option DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon con _ _ _) _ _ => Some con
    | _ => None
    end.

Definition newTyConCo_maybe : TyCon -> option (list unit) :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ _ co) _ _ => Some co
    | _ => None
    end.

Definition newTyConCo : TyCon -> list unit :=
  fun tc =>
    match newTyConCo_maybe tc with
    | Some co => co
    | None => Panic.panicStr (GHC.Base.hs_string__ "newTyConCo") (Panic.someSDoc)
    end.

Definition neverUnfoldGuidance : UnfoldingGuidance -> bool :=
  fun arg_0__ => match arg_0__ with | UnfNever => true | _ => false end.

Definition needSaturated : bool :=
  false.

Definition modifyVarEnv_Directly {a}
   : (a -> a) -> UniqFM.UniqFM a -> Unique.Unique -> UniqFM.UniqFM a :=
  fun mangle_fn env key =>
    match (UniqFM.lookupUFM_Directly env key) with
    | None => env
    | Some xx => UniqFM.addToUFM_Directly env key (mangle_fn xx)
    end.

Definition mk_id : Name.Name -> unit -> IdScope -> IdDetails -> IdInfo -> Id :=
  fun name ty scope details info =>
    Mk_Id name (Unique.getKey (Name.nameUnique name)) ty scope details info.

Definition mkDVarEnv {a} : list (Var * a)%type -> DVarEnv a :=
  UniqDFM.listToUDFM.

Definition mkVarEnv {a} : list (Var * a)%type -> VarEnv a :=
  UniqFM.listToUFM.

Definition mkDVarSet : list Var -> DVarSet :=
  UniqDSet.mkUniqDSet.

Definition mkVarSet : list Var -> VarSet :=
  UniqSet.mkUniqSet.

Definition mkVarEnv_Directly {a} : list (Unique.Unique * a)%type -> VarEnv a :=
  UniqFM.listToUFM_Directly.

Definition zipVarEnv {a} : list Var -> list a -> VarEnv a :=
  fun tyvars tys =>
    mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipVarEnv") tyvars tys).

Local Definition Eq___Count_op_zeze__ : Count -> Count -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | One, One => true
    | Many, Many => true
    | _, _ => false
    end.

Local Definition Eq___Count_op_zsze__ : Count -> Count -> bool :=
  fun x y => negb (Eq___Count_op_zeze__ x y).

Program Instance Eq___Count : GHC.Base.Eq_ Count :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Count_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Count_op_zsze__ |}.

Local Definition Eq___Use_op_zeze__ {inst_u} `{GHC.Base.Eq_ inst_u}
   : Use inst_u -> Use inst_u -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Abs, Abs => true
    | Mk_Use a1 a2, Mk_Use b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___Use_op_zsze__ {inst_u} `{GHC.Base.Eq_ inst_u}
   : Use inst_u -> Use inst_u -> bool :=
  fun x y => negb (Eq___Use_op_zeze__ x y).

Program Instance Eq___Use {u} `{GHC.Base.Eq_ u} : GHC.Base.Eq_ (Use u) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Use_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Use_op_zsze__ |}.

Local Definition Eq___UseDmd_op_zeze__ : UseDmd -> UseDmd -> bool :=
  fix UseDmd_eq x y
        := let eq' : GHC.Base.Eq_ UseDmd := GHC.Base.eq_default UseDmd_eq in
           match x, y with
           | UCall a1 a2, UCall b1 b2 => andb (a1 GHC.Base.== b1) (a2 GHC.Base.== b2)
           | UProd a1, UProd b1 => a1 GHC.Base.== b1
           | UHead, UHead => true
           | Used, Used => true
           | _, _ => false
           end.

Local Definition Eq___UseDmd_op_zsze__ : UseDmd -> UseDmd -> bool :=
  fun x y => negb (Eq___UseDmd_op_zeze__ x y).

Program Instance Eq___UseDmd : GHC.Base.Eq_ UseDmd :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___UseDmd_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___UseDmd_op_zsze__ |}.

Definition mkUProd : list ArgUse -> UseDmd :=
  fun ux =>
    if Data.Foldable.all (fun arg_1__ => arg_1__ GHC.Base.== Abs) ux : bool
    then UHead else
    UProd ux.

Definition mkUCall : Count -> UseDmd -> UseDmd :=
  fun c a => UCall c a.

Program Definition mkWorkerDemand : nat -> Demand :=
          fun n =>
            let go :=
              GHC.Wf.wfFix1 Coq.Init.Peano.lt (fun arg_0__ => arg_0__) _ (fun arg_0__ go =>
                               let 'num_1__ := arg_0__ in
                               if Bool.Sumbool.sumbool_of_bool (num_1__ GHC.Base.== #0) then Used else
                               let 'n := arg_0__ in
                               mkUCall One (go (n GHC.Num.- #1))) in
            JD Lazy (Mk_Use One (go n)).
Solve Obligations with (solve_mkWorkerDemand).

Definition mkTyVarBinder : ArgFlag -> Var -> TyVarBinder :=
  fun vis var => TvBndr var vis.

Definition mkTyVarBinders : ArgFlag -> list TyVar -> list TyVarBinder :=
  fun vis => GHC.Base.map (mkTyVarBinder vis).

Definition tyConTyVarBinders : list TyConBinder -> list TyVarBinder :=
  fun tc_bndrs =>
    let mk_binder :=
      fun '(TvBndr tv tc_vis) =>
        let vis :=
          match tc_vis with
          | AnonTCB => Specified
          | NamedTCB Required => Specified
          | NamedTCB vis => vis
          end in
        mkTyVarBinder vis tv in
    GHC.Base.map mk_binder tc_bndrs.

Definition mkTyVar : Name.Name -> unit -> TyVar :=
  fun name kind => Mk_TyVar name (Unique.getKey (Name.nameUnique name)) kind.

Definition mkTyBind : TyVar -> unit -> CoreBind :=
  fun tv ty => NonRec tv (Type_ ty).

Axiom isCoercionTy_maybe : unit -> option unit.

Definition mkTyArg {b} : unit -> Expr b :=
  fun ty =>
    match isCoercionTy_maybe ty with
    | Some co => Coercion co
    | _ => Type_ ty
    end.

Definition mkTyApps {b} : Expr b -> list unit -> Expr b :=
  fun f args => Data.Foldable.foldl (fun e a => App e (mkTyArg a)) f args.

Definition mkTcTyVar : Name.Name -> unit -> unit -> TyVar :=
  fun name kind details =>
    Mk_TcTyVar name (Unique.getKey (Name.nameUnique name)) kind details.

Definition mkSumTyCon
   : Name.Name ->
     list TyConBinder ->
     unit ->
     BasicTypes.Arity -> list TyVar -> list DataCon -> AlgTyConFlav -> TyCon :=
  fun name binders res_kind arity tyvars cons_ parent =>
    AlgTyCon (Name.nameUnique name) name binders tyvars res_kind tt arity
             (Coq.Lists.List.repeat tt arity) None false nil (SumTyCon cons_)
             FastStringEnv.emptyDFsEnv parent.

Definition mkStringLit {b} : GHC.Base.String -> Expr b :=
  fun s => Lit (Literal.mkMachString s).

Definition mkStrictSig : DmdType -> StrictSig :=
  fun dmd_ty => Mk_StrictSig dmd_ty.

Definition mkSCall : StrDmd -> StrDmd :=
  fun arg_0__ => match arg_0__ with | HyperStr => HyperStr | s => SCall s end.

Definition mkRuleEnv : RuleBase -> list Module.Module -> RuleEnv :=
  fun rules vis_orphs => Mk_RuleEnv rules (Module.mkModuleSet vis_orphs).

Definition mkPromotedDataCon
   : DataCon ->
     Name.Name ->
     TyConRepName ->
     list TyConBinder -> unit -> list unit -> RuntimeRepInfo -> TyCon :=
  fun con name rep_name binders res_kind roles rep_info =>
    PromotedDataCon (Name.nameUnique name) name binders res_kind tt
                    (Coq.Lists.List.length roles) roles con rep_name rep_info.

Definition mkPrimTyCon'
   : Name.Name ->
     list TyConBinder -> unit -> list unit -> bool -> option TyConRepName -> TyCon :=
  fun name binders res_kind roles is_unlifted rep_nm =>
    PrimTyCon (Name.nameUnique name) name binders res_kind tt (Coq.Lists.List.length
               roles) roles is_unlifted rep_nm.

Definition mkPrelTyConRepName : Name.Name -> TyConRepName :=
  fun tc_name =>
    let name_uniq := Name.nameUnique tc_name in
    let name_mod := Name.nameModule tc_name in
    let name_occ := Name.nameOccName tc_name in
    let rep_uniq :=
      if OccName.isTcOcc name_occ : bool then Unique.tyConRepNameUnique name_uniq else
      Unique.dataConRepNameUnique name_uniq in
    let 'pair rep_mod rep_occ := tyConRepModOcc name_mod name_occ in
    Name.mkExternalName rep_uniq rep_mod rep_occ (Name.nameSrcSpan tc_name).

Definition mkPrimTyCon
   : Name.Name -> list TyConBinder -> unit -> list unit -> TyCon :=
  fun name binders res_kind roles =>
    mkPrimTyCon' name binders res_kind roles true (Some (mkPrelTyConRepName name)).

Definition mkPatSyn
   : Name.Name ->
     bool ->
     (list TyVarBinder * unit)%type ->
     (list TyVarBinder * unit)%type ->
     list unit ->
     unit ->
     (Id * bool)%type ->
     option (Id * bool)%type -> list FieldLabel.FieldLabel -> PatSyn :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ arg_6__ arg_7__ arg_8__ =>
    match arg_0__
        , arg_1__
        , arg_2__
        , arg_3__
        , arg_4__
        , arg_5__
        , arg_6__
        , arg_7__
        , arg_8__ with
    | name
    , declared_infix
    , pair univ_tvs req_theta
    , pair ex_tvs prov_theta
    , orig_args
    , orig_res_ty
    , matcher
    , builder
    , field_labels =>
        MkPatSyn name (Unique.getUnique name) orig_args (Coq.Lists.List.length
                  orig_args) declared_infix field_labels univ_tvs req_theta ex_tvs prov_theta
                 orig_res_ty matcher builder
    end.

Axiom mkOtherCon : list AltCon -> Unfolding.

Definition mkOnceUsedDmd : CleanDemand -> Demand :=
  fun '(JD s a) => JD (Mk_Str VanStr s) (Mk_Use One a).

Definition mkNamedTyConBinder : ArgFlag -> TyVar -> TyConBinder :=
  fun vis tv => TvBndr tv (NamedTCB vis).

Definition mkNamedTyConBinders : ArgFlag -> list TyVar -> list TyConBinder :=
  fun vis tvs => GHC.Base.map (mkNamedTyConBinder vis) tvs.

Definition mkManyUsedDmd : CleanDemand -> Demand :=
  fun '(JD s a) => JD (Mk_Str VanStr s) (Mk_Use Many a).

Definition mkLocalVar : IdDetails -> Name.Name -> unit -> IdInfo -> Id :=
  fun details name ty info => mk_id name ty (LocalId NotExported) details info.

Definition mkLiftedPrimTyCon
   : Name.Name -> list TyConBinder -> unit -> list unit -> TyCon :=
  fun name binders res_kind roles =>
    let rep_nm := mkPrelTyConRepName name in
    mkPrimTyCon' name binders res_kind roles false (Some rep_nm).

Definition mkLetRec {b} : list (b * Expr b)%type -> Expr b -> Expr b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | nil, body => body
    | bs, body => Let (Rec bs) body
    end.

Definition mkLetNonRec {b} : b -> Expr b -> Expr b -> Expr b :=
  fun b rhs body => Let (NonRec b rhs) body.

Definition mkLet {b} : Bind b -> Expr b -> Expr b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Rec nil, body => body
    | bind, body => Let bind body
    end.

Definition mkLets {b} : list (Bind b) -> Expr b -> Expr b :=
  fun binds body => Data.Foldable.foldr mkLet body binds.

Definition mkLams {b} : list b -> Expr b -> Expr b :=
  fun binders body => Data.Foldable.foldr Lam body binders.

Definition mkKindTyCon
   : Name.Name -> list TyConBinder -> unit -> list unit -> Name.Name -> TyCon :=
  fun name binders res_kind roles rep_nm =>
    let tc := mkPrimTyCon' name binders res_kind roles false (Some rep_nm) in tc.

Definition mkJointDmd {s} {u} : s -> u -> JointDmd s u :=
  fun s u => JD s u.

Definition mkJointDmds {s} {u} : list s -> list u -> list (JointDmd s u) :=
  fun ss as_ =>
    Util.zipWithEqual (GHC.Base.hs_string__ "mkJointDmds") mkJointDmd ss as_.

Definition splitProdDmd_maybe : Demand -> option (list Demand) :=
  fun '(JD s u) =>
    let scrut_1__ := pair s u in
    let j_3__ :=
      match scrut_1__ with
      | pair Lazy (Mk_Use _ (UProd ux)) =>
          Some (mkJointDmds (Coq.Lists.List.repeat Lazy (Coq.Lists.List.length ux)) ux)
      | _ => None
      end in
    let j_5__ :=
      match scrut_1__ with
      | pair (Mk_Str _ s) (Mk_Use _ (UProd ux)) =>
          match splitStrProdDmd (Coq.Lists.List.length ux) s with
          | Some sx => Some (mkJointDmds sx ux)
          | _ => j_3__
          end
      | _ => j_3__
      end in
    match scrut_1__ with
    | pair (Mk_Str _ (SProd sx)) (Mk_Use _ u) =>
        match splitUseProdDmd (Coq.Lists.List.length sx) u with
        | Some ux => Some (mkJointDmds sx ux)
        | _ => j_5__
        end
    | _ => j_5__
    end.

Definition mkInScopeSet : VarSet -> InScopeSet :=
  fun in_scope => InScope in_scope #1.

Definition mkHeadStrict : CleanDemand -> CleanDemand :=
  fun '(JD sd_0__ ud_1__) => JD HeadStr ud_1__.

Definition mkGlobalVar : IdDetails -> Name.Name -> unit -> IdInfo -> Id :=
  fun details name ty info => mk_id name ty GlobalId details info.

Definition mkFunTyCon : Name.Name -> list TyConBinder -> Name.Name -> TyCon :=
  fun name binders rep_nm =>
    FunTyCon (Name.nameUnique name) name binders tt tt (Coq.Lists.List.length
              binders) rep_nm.

Definition mkFloatLit {b} : GHC.Real.Rational -> Expr b :=
  fun f => Lit (Literal.mkMachFloat f).

Definition mkExportedLocalVar
   : IdDetails -> Name.Name -> unit -> IdInfo -> Id :=
  fun details name ty info => mk_id name ty (LocalId Exported) details info.

Definition mkEqSpec : TyVar -> unit -> EqSpec :=
  fun tv ty => Mk_EqSpec tv ty.

Definition mkDoubleLit {b} : GHC.Real.Rational -> Expr b :=
  fun d => Lit (Literal.mkMachDouble d).

Definition mkDmdType : DmdEnv -> list Demand -> DmdResult -> DmdType :=
  fun fv ds res => Mk_DmdType fv ds res.

Definition mkCoBind : CoVar -> unit -> CoreBind :=
  fun cv co => NonRec cv (Coercion co).

Definition mkCoApps {b} : Expr b -> list unit -> Expr b :=
  fun f args => Data.Foldable.foldl (fun e a => App e (Coercion a)) f args.

Definition mkClass
   : Name.Name ->
     list TyVar ->
     list (FunDep TyVar) ->
     list unit ->
     list Id ->
     list ClassATItem -> list ClassOpItem -> ClassMinimalDef -> TyCon -> Class :=
  fun cls_name
  tyvars
  fds
  super_classes
  superdict_sels
  at_stuff
  op_stuff
  mindef
  tycon =>
    Mk_Class tycon cls_name (Name.nameUnique cls_name) tyvars fds (ConcreteClass
              super_classes superdict_sels at_stuff op_stuff mindef).

Definition mkCharLit {b} : GHC.Char.Char -> Expr b :=
  fun c => Lit (Literal.mkMachChar c).

Definition mkCallDmd : CleanDemand -> CleanDemand :=
  fun '(JD d u) => JD (mkSCall d) (mkUCall One u).

Definition mkBothDmdArg : DmdEnv -> BothDmdArg :=
  fun env => pair env (Dunno tt).

Definition mkApps {b} : Expr b -> list (Arg b) -> Expr b :=
  fun f args => Data.Foldable.foldl App f args.

Definition mkAnonTyConBinder : TyVar -> TyConBinder :=
  fun tv => TvBndr tv AnonTCB.

Definition mkAnonTyConBinders : list TyVar -> list TyConBinder :=
  fun tvs => GHC.Base.map mkAnonTyConBinder tvs.

Definition mkAbstractClass
   : Name.Name -> list TyVar -> list (FunDep TyVar) -> TyCon -> Class :=
  fun cls_name tyvars fds tycon =>
    Mk_Class tycon cls_name (Name.nameUnique cls_name) tyvars fds AbstractClass.

Definition minusVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.minusUniqSet.

Definition minusVarEnv {a} {b} : VarEnv a -> VarEnv b -> VarEnv a :=
  UniqFM.minusUFM.

Definition minusDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.minusUniqDSet.

Definition minusDVarEnv {a} {a'} : DVarEnv a -> DVarEnv a' -> DVarEnv a :=
  UniqDFM.minusUDFM.

Definition mightBeUnsaturatedTyCon : TyCon -> bool :=
  tcFlavourCanBeUnsaturated GHC.Base.∘ tyConFlavour.

Definition mayHaveCafRefs : CafInfo -> bool :=
  fun arg_0__ => match arg_0__ with | MayHaveCafRefs => true | _ => false end.

Definition markReused : UseDmd -> UseDmd :=
  fix markReused (arg_0__ : UseDmd) : UseDmd
        := let markReusedDmd (arg_0__ : ArgUse) : ArgUse :=
             match arg_0__ with
             | Abs => Abs
             | Mk_Use _ a => Mk_Use Many (markReused a)
             end in
           match arg_0__ with
           | UCall _ u => UCall Many u
           | UProd ux => UProd (GHC.Base.map markReusedDmd ux)
           | u => u
           end.

Definition markReusedDmd : ArgUse -> ArgUse :=
  fun arg_0__ =>
    match arg_0__ with
    | Abs => Abs
    | Mk_Use _ a => Mk_Use Many (markReused a)
    end.

Definition markExnStr : ArgStr -> ArgStr :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Str VanStr s => Mk_Str Mk_ExnStr s
    | s => s
    end.

Definition postProcessDmd : DmdShell -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD ss us, JD s a =>
        let a' :=
          match us with
          | Abs => Abs
          | Mk_Use Many _ => markReusedDmd a
          | Mk_Use One _ => a
          end in
        let s' :=
          match ss with
          | Lazy => Lazy
          | Mk_Str Mk_ExnStr _ => markExnStr s
          | Mk_Str VanStr _ => s
          end in
        JD s' a'
    end.

Definition mapVarEnv {a} {b} : (a -> b) -> VarEnv a -> VarEnv b :=
  UniqFM.mapUFM.

Definition reuseEnv : DmdEnv -> DmdEnv :=
  mapVarEnv (postProcessDmd (JD (Mk_Str VanStr tt) (Mk_Use Many tt))).

Definition mapDVarEnv {a} {b} : (a -> b) -> DVarEnv a -> DVarEnv b :=
  UniqDFM.mapUDFM.

Axiom lubUse : UseDmd -> UseDmd -> UseDmd.

Definition lubExnStr : ExnStr -> ExnStr -> ExnStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | VanStr, VanStr => VanStr
    | _, _ => Mk_ExnStr
    end.

Definition lubCount : Count -> Count -> Count :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Many => Many
    | Many, _ => Many
    | x, _ => x
    end.

Definition lubCPR : CPRResult -> CPRResult -> CPRResult :=
  fun arg_0__ arg_1__ =>
    let j_2__ :=
      match arg_0__, arg_1__ with
      | RetProd, RetProd => RetProd
      | _, _ => NoCPR
      end in
    match arg_0__, arg_1__ with
    | RetSum t1, RetSum t2 => if t1 GHC.Base.== t2 : bool then RetSum t1 else j_2__
    | _, _ => j_2__
    end.

Definition lubDmdResult : DmdResult -> DmdResult -> DmdResult :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Diverges, r => r
    | ThrowsExn, Diverges => ThrowsExn
    | ThrowsExn, r => r
    | Dunno c1, Diverges => Dunno c1
    | Dunno c1, ThrowsExn => Dunno c1
    | Dunno c1, Dunno c2 => Dunno (lubCPR c1 c2)
    end.

Axiom lubArgUse : ArgUse -> ArgUse -> ArgUse.

Definition lookupDVarEnv {a} : DVarEnv a -> Var -> option a :=
  UniqDFM.lookupUDFM.

Definition lookupVarEnv {a} : VarEnv a -> Var -> option a :=
  UniqFM.lookupUFM.

Definition lookupVarEnv_Directly {a} : VarEnv a -> Unique.Unique -> option a :=
  UniqFM.lookupUFM_Directly.

Definition lookupVarEnv_NF {a} `{_ : GHC.Err.Default a} (env : VarEnv a) id
   : a :=
  match lookupVarEnv env id with
  | Some xx => xx
  | None => GHC.Err.default
  end.

Definition lookupVarSet : VarSet -> Var -> option Var :=
  UniqSet.lookupUniqSet.

Definition lookupVarSetByName : VarSet -> Name.Name -> option Var :=
  UniqSet.lookupUniqSet.

Definition lookupVarSet_Directly : VarSet -> Unique.Unique -> option Var :=
  UniqSet.lookupUniqSet_Directly.

Definition lookupWithDefaultVarEnv {a} : VarEnv a -> a -> Var -> a :=
  UniqFM.lookupWithDefaultUFM.

Definition rnOccL : RnEnv2 -> Var -> Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => Maybes.orElse (lookupVarEnv env v) v
    end.

Definition rnOccL_maybe : RnEnv2 -> Var -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => lookupVarEnv env v
    end.

Definition rnOccR : RnEnv2 -> Var -> Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => Maybes.orElse (lookupVarEnv env v) v
    end.

Definition rnOccR_maybe : RnEnv2 -> Var -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => lookupVarEnv env v
    end.

Definition lookupInScope_Directly : InScopeSet -> Unique.Unique -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope _, uniq => lookupVarSet_Directly in_scope uniq
    end.

Definition lookupInScope : InScopeSet -> Var -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope _, v => lookupVarSet in_scope v
    end.

Definition lookupRnInScope : RnEnv2 -> Var -> Var :=
  fun env v => Maybes.orElse (lookupInScope (in_scope env) v) v.

Definition lazySetIdInfo : Id -> IdInfo -> Var :=
  fun id info =>
    match id with
    | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_TcTyVar _ _ _ _ =>
        GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
    id_info_5__ =>
        Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__ info
    end.

Definition lazyApply2Dmd : Demand :=
  JD Lazy (Mk_Use One (UCall One (UCall One Used))).

Definition lazyApply1Dmd : Demand :=
  JD Lazy (Mk_Use One (UCall One Used)).

Definition kill_usage : KillFlags -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | kfs, JD s u => JD s (zap_musg kfs u)
    end.

Definition zapUsageDemand : Demand -> Demand :=
  kill_usage (Mk_KillFlags true true true).

Definition zapUsageInfo : IdInfo -> option IdInfo :=
  fun info =>
    Some (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
             oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
             callArityInfo_9__ levityInfo_10__ := info in
          Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                    oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                    (zapUsageDemand (demandInfo info)) callArityInfo_9__ levityInfo_10__).

Definition zapUsedOnceDemand : Demand -> Demand :=
  kill_usage (Mk_KillFlags false true false).

Definition zapUsedOnceSig : StrictSig -> StrictSig :=
  fun '(Mk_StrictSig (Mk_DmdType env ds r)) =>
    Mk_StrictSig (Mk_DmdType env (GHC.Base.map zapUsedOnceDemand ds) r).

Definition zapUsedOnceInfo : IdInfo -> option IdInfo :=
  fun info =>
    Some (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
             oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__ demandInfo_8__
             callArityInfo_9__ levityInfo_10__ := info in
          Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                    oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ (zapUsedOnceSig (strictnessInfo
                                                                                    info)) (zapUsedOnceDemand
                     (demandInfo info)) callArityInfo_9__ levityInfo_10__).

Definition killFlags : DynFlags.DynFlags -> option KillFlags :=
  fun dflags =>
    let kf_used_once := DynFlags.gopt DynFlags.Opt_KillOneShot dflags in
    let kf_called_once := kf_used_once in
    let kf_abs := DynFlags.gopt DynFlags.Opt_KillAbsence dflags in
    if andb (negb kf_abs) (negb kf_used_once) : bool then None else
    Some (Mk_KillFlags kf_abs kf_used_once kf_called_once).

Definition killUsageDemand : DynFlags.DynFlags -> Demand -> Demand :=
  fun dflags dmd =>
    match killFlags dflags with
    | Some kfs => kill_usage kfs dmd
    | _ => dmd
    end.

Definition killUsageSig : DynFlags.DynFlags -> StrictSig -> StrictSig :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | dflags, (Mk_StrictSig (Mk_DmdType env ds r) as sig) =>
        match killFlags dflags with
        | Some kfs => Mk_StrictSig (Mk_DmdType env (GHC.Base.map (kill_usage kfs) ds) r)
        | _ => sig
        end
    end.

Definition isVoidRep : PrimRep -> bool :=
  fun arg_0__ => match arg_0__ with | VoidRep => true | _other => false end.

Definition isVisibleArgFlag : ArgFlag -> bool :=
  fun arg_0__ => match arg_0__ with | Required => true | _ => false end.

Definition isVisibleTcbVis : TyConBndrVis -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | NamedTCB vis => isVisibleArgFlag vis
    | AnonTCB => true
    end.

Definition isVisibleTyConBinder {tv} : TyVarBndr tv TyConBndrVis -> bool :=
  fun '(TvBndr _ tcb_vis) => isVisibleTcbVis tcb_vis.

Definition tyConVisibleTyVars : TyCon -> list TyVar :=
  fun tc =>
    let cont_0__ arg_1__ :=
      let 'TvBndr tv vis := arg_1__ in
      if isVisibleTcbVis vis : bool then cons tv nil else
      nil in
    Coq.Lists.List.flat_map cont_0__ (tyConBinders tc).

Definition isVanillaDataCon : DataCon -> bool :=
  fun dc => dcVanilla dc.

Definition isVanillaAlgTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (VanillaAlgTyCon _) => true
    | _ => false
    end.

Definition isValueUnfolding : Unfolding -> bool :=
  fun x => false.

Definition isUsedU : UseDmd -> bool :=
  fix isUsedU (arg_0__ : UseDmd) : bool
        := let isUsedMU (arg_0__ : ArgUse) : bool :=
             match arg_0__ with
             | Abs => true
             | Mk_Use One _ => false
             | Mk_Use Many u => isUsedU u
             end in
           match arg_0__ with
           | Used => true
           | UHead => true
           | UProd us => Data.Foldable.all isUsedMU us
           | UCall One _ => false
           | UCall Many _ => true
           end.

Definition isUsedOnce : Demand -> bool :=
  fun '(JD _ a) => match useCount a with | One => true | Many => false end.

Definition isUsedMU : ArgUse -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Abs => true
    | Mk_Use One _ => false
    | Mk_Use Many u => isUsedU u
    end.

Definition isUnliftedTyCon : TyCon -> bool :=
  fun arg_0__ =>
    let j_2__ :=
      match arg_0__ with
      | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
          match rhs with
          | SumTyCon _ => true
          | _ => false
          end
      | _ => false
      end in
    match arg_0__ with
    | PrimTyCon _ _ _ _ _ _ _ is_unlifted _ => is_unlifted
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | TupleTyCon _ sort =>
            negb (BasicTypes.isBoxed (BasicTypes.tupleSortBoxity sort))
        | _ => j_2__
        end
    | _ => j_2__
    end.

Definition isUnboxedTupleTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | TupleTyCon _ sort =>
            negb (BasicTypes.isBoxed (BasicTypes.tupleSortBoxity sort))
        | _ => false
        end
    | _ => false
    end.

Definition isUnboxedTupleCon : DataCon -> bool :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _) =>
    isUnboxedTupleTyCon tc.

Definition isUnboxedSumTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | SumTyCon _ => true
        | _ => false
        end
    | _ => false
    end.

Definition isUnboxedSumCon : DataCon -> bool :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _) =>
    isUnboxedSumTyCon tc.

Definition isTypeSynonymTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isTypeArg {b} : Expr b -> bool :=
  fun arg_0__ => match arg_0__ with | Type_ _ => true | _ => false end.

Definition isValArg {b} : Expr b -> bool :=
  fun e => negb (isTypeArg e).

Definition valArgCount {b} : list (Arg b) -> nat :=
  Util.count isValArg.

Definition isTyVar : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_TyVar _ _ _ => true
    | Mk_TcTyVar _ _ _ _ => true
    | _ => false
    end.

Definition isTyConAssoc : TyCon -> bool :=
  fun tc => Data.Maybe.isJust (tyConAssoc_maybe tc).

Axiom isTyCoVar : Var -> bool.

Definition isTyCoArg {b} : Expr b -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Type_ _ => true
    | Coercion _ => true
    | _ => false
    end.

Definition isTupleTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (TupleTyCon _ _) _ _ => true
    | _ => false
    end.

Definition isTupleDataCon : DataCon -> bool :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _) => isTupleTyCon tc.

Definition isTopRes : DmdResult -> bool :=
  fun arg_0__ => match arg_0__ with | Dunno NoCPR => true | _ => false end.

Definition isTopDmd : Demand -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | JD Lazy (Mk_Use Many Used) => true
    | _ => false
    end.

Definition isTcTyVar : Var -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_TcTyVar _ _ _ _ => true | _ => false end.

Definition isTcTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | TcTyCon _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isTcLevPoly : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FunTyCon _ _ _ _ _ _ _ => false
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (UnboxedAlgTyCon _) => true
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ => false
    | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ => true
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ => true
    | PrimTyCon _ _ _ _ _ _ _ _ _ => false
    | TcTyCon _ _ _ _ _ _ _ _ _ => false
    | (PromotedDataCon _ _ _ _ _ _ _ _ _ _ as tc) =>
        Panic.panicStr (GHC.Base.hs_string__ "isTcLevPoly datacon") (Panic.someSDoc)
    end.

Definition isTauTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | SynonymTyCon _ _ _ _ _ _ _ _ _ is_tau _ => is_tau
    | _ => true
    end.

Definition isStrictDmd : Demand -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | JD _ Abs => false
    | JD Lazy _ => false
    | _ => true
    end.

Definition zapLamInfo : IdInfo -> option IdInfo :=
  fun '((Mk_IdInfo _ _ _ _ _ _ occ _ demand _ _ as info)) =>
    let is_safe_dmd := fun dmd => negb (isStrictDmd dmd) in
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
                    oneShotInfo_35__ inlinePragInfo_36__ safe_occ strictnessInfo_38__ topDmd
                    callArityInfo_40__ levityInfo_41__).

Definition isStableUnfolding : Unfolding -> bool :=
  fun x => false.

Definition isStableSource : UnfoldingSource -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | InlineCompulsory => true
    | InlineStable => true
    | InlineRhs => false
    end.

Definition isSrcUnpacked : SrcUnpackedness -> bool :=
  fun arg_0__ => match arg_0__ with | SrcUnpack => true | _ => false end.

Definition isSrcStrict : SrcStrictness -> bool :=
  fun arg_0__ => match arg_0__ with | SrcStrict => true | _ => false end.

Definition isSeqDmd : Demand -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | JD (Mk_Str VanStr HeadStr) (Mk_Use _ UHead) => true
    | _ => false
    end.

Definition isRuntimeArg : CoreExpr -> bool :=
  isValArg.

Definition isPromotedDataCon_maybe : TyCon -> option DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | PromotedDataCon _ _ _ _ _ _ _ dc _ _ => Some dc
    | _ => None
    end.

Definition isPromotedDataCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | PromotedDataCon _ _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isPrimTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | PrimTyCon _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isOrphan : IsOrphan -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_IsOrphan => true | _ => false end.

Definition isOpenTypeFamilyTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ OpenSynFamilyTyCon _ _ => true
    | _ => false
    end.

Definition isOpenFamilyTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ flav _ _ =>
        match flav with
        | OpenSynFamilyTyCon => true
        | _ => match flav with | DataFamilyTyCon _ => true | _ => false end
        end
    | _ => false
    end.

Definition isNoParent : AlgTyConFlav -> bool :=
  fun arg_0__ => match arg_0__ with | VanillaAlgTyCon _ => true | _ => false end.

Definition isTyConWithSrcDataCons : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ parent =>
        let isSrcParent := isNoParent parent in
        match rhs with
        | DataTyCon _ _ => isSrcParent
        | NewTyCon _ _ _ _ => isSrcParent
        | TupleTyCon _ _ => isSrcParent
        | _ => false
        end
    | FamilyTyCon _ _ _ _ _ _ _ _ (DataFamilyTyCon _) _ _ => true
    | _ => false
    end.

Definition isNewTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ _ _) _ _ => true
    | _ => false
    end.

Definition isNeverLevPolyIdInfo : IdInfo -> bool :=
  fun info =>
    match levityInfo info with
    | NeverLevityPolymorphic => true
    | _ => false
    end.

Definition isNamedTyConBinder : TyConBinder -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | TvBndr _ (NamedTCB _) => true
    | _ => false
    end.

Definition isMarkedStrict : StrictnessMark -> bool :=
  fun arg_0__ => match arg_0__ with | NotMarkedStrict => false | _ => true end.

Definition isLocalRule : CoreRule -> bool :=
  ru_local.

Definition isLocalId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ (LocalId _) _ _ => true
    | _ => false
    end.

Definition setIdNotExported : Id -> Id :=
  fun id =>
    if andb Util.debugIsOn (negb (isLocalId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Var.hs")
          #591)
    else match id with
         | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
         | Mk_TcTyVar _ _ _ _ =>
             GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
         | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
         id_info_5__ =>
             Mk_Id varName_0__ realUnique_1__ varType_2__ (LocalId NotExported)
                   id_details_4__ id_info_5__
         end.

Definition isLazy : ArgStr -> bool :=
  fun arg_0__ => match arg_0__ with | Lazy => true | Mk_Str _ _ => false end.

Definition isWeakDmd : Demand -> bool :=
  fun '(JD s a) => andb (isLazy s) (isUsedMU a).

Definition isJoinIdDetails_maybe : IdDetails -> option BasicTypes.JoinArity :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_JoinId join_arity => Some join_arity
    | _ => None
    end.

Definition isInvisibleTyConBinder {tv} : TyVarBndr tv TyConBndrVis -> bool :=
  fun tcb => negb (isVisibleTyConBinder tcb).

Definition isInvisibleArgFlag : ArgFlag -> bool :=
  negb GHC.Base.∘ isVisibleArgFlag.

Definition isImplicitTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FunTyCon _ _ _ _ _ _ _ => true
    | PrimTyCon _ _ _ _ _ _ _ _ _ => true
    | PromotedDataCon _ _ _ _ _ _ _ _ _ _ => true
    | AlgTyCon _ name _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | TupleTyCon _ _ => Name.isWiredInName name
        | _ => match rhs with | SumTyCon _ => true | _ => false end
        end
    | FamilyTyCon _ _ _ _ _ _ _ _ _ parent _ => Data.Maybe.isJust parent
    | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ => false
    | TcTyCon _ _ _ _ _ _ _ _ _ => false
    end.

Definition isId : Var -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_Id _ _ _ _ _ _ => true | _ => false end.

Definition isRuntimeVar : Var -> bool :=
  isId.

Definition valBndrCount : list CoreBndr -> nat :=
  Util.count isId.

Definition isHyperStr : ArgStr -> bool :=
  fun arg_0__ => match arg_0__ with | Mk_Str _ HyperStr => true | _ => false end.

Definition mkSProd : list ArgStr -> StrDmd :=
  fun sx =>
    if Data.Foldable.any isHyperStr sx : bool then HyperStr else
    if Data.Foldable.all isLazy sx : bool then HeadStr else
    SProd sx.

Definition lubStr : StrDmd -> StrDmd -> StrDmd :=
  fix lubStr (arg_0__ arg_1__ : StrDmd) : StrDmd
        := let lubArgStr (arg_0__ arg_1__ : ArgStr) : ArgStr :=
             match arg_0__, arg_1__ with
             | Lazy, _ => Lazy
             | _, Lazy => Lazy
             | Mk_Str x1 s1, Mk_Str x2 s2 => Mk_Str (lubExnStr x1 x2) (lubStr s1 s2)
             end in
           match arg_0__, arg_1__ with
           | HyperStr, s => s
           | SCall s1, HyperStr => SCall s1
           | SCall _, HeadStr => HeadStr
           | SCall s1, SCall s2 => SCall (lubStr s1 s2)
           | SCall _, SProd _ => HeadStr
           | SProd sx, HyperStr => SProd sx
           | SProd _, HeadStr => HeadStr
           | SProd s1, SProd s2 =>
               if Util.equalLength s1 s2 : bool
               then mkSProd (GHC.List.zipWith lubArgStr s1 s2) else
               HeadStr
           | SProd _, SCall _ => HeadStr
           | HeadStr, _ => HeadStr
           end.

Definition lubArgStr : ArgStr -> ArgStr -> ArgStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Lazy, _ => Lazy
    | _, Lazy => Lazy
    | Mk_Str x1 s1, Mk_Str x2 s2 => Mk_Str (lubExnStr x1 x2) (lubStr s1 s2)
    end.

Definition lubDmd : Demand -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD s1 a1, JD s2 a2 => JD (lubArgStr s1 s2) (lubArgUse a1 a2)
    end.

Definition isGlobalId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ GlobalId _ _ => true
    | _ => false
    end.

Definition isLocalVar : Var -> bool :=
  fun v => negb (isGlobalId v).

Definition mustHaveLocalBinding : Var -> bool :=
  fun var => isLocalVar var.

Definition isGenInjAlgRhs : AlgTyConRhs -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | TupleTyCon _ _ => true
    | SumTyCon _ => true
    | DataTyCon _ _ => true
    | AbstractTyCon => false
    | NewTyCon _ _ _ _ => false
    end.

Definition isGcPtrRep : PrimRep -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | LiftedRep => true
    | UnliftedRep => true
    | _ => false
    end.

Definition isGadtSyntaxTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ res _ _ _ _ => res
    | _ => false
    end.

Definition isFunTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FunTyCon _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isFragileUnfolding : Unfolding -> bool :=
  fun u => false.

Definition zapFragileUnfolding : Unfolding -> Unfolding :=
  fun unf => if isFragileUnfolding unf : bool then noUnfolding else unf.

Definition isFamilyTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isFamInstTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (DataFamInstTyCon _ _ _) => true
    | _ => false
    end.

Definition isExportedId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ GlobalId _ _ => true
    | Mk_Id _ _ _ (LocalId Exported) _ _ => true
    | _ => false
    end.

Definition isExpandableUnfolding : Unfolding -> bool :=
  fun x => false.

Definition isEvaldUnfolding : Unfolding -> bool :=
  fun x => false.

Definition isEnumerationTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ arity _ _ _ _ rhs _ _ =>
        match rhs with
        | DataTyCon _ res => res
        | TupleTyCon _ _ => arity GHC.Base.== #0
        | _ => false
        end
    | _ => false
    end.

Definition isEmptyVarSet : VarSet -> bool :=
  UniqSet.isEmptyUniqSet.

Definition subVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => isEmptyVarSet (minusVarSet s1 s2).

Definition varSetInScope : VarSet -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | vars, InScope s1 _ => subVarSet vars s1
    end.

Definition transCloVarSet : (VarSet -> VarSet) -> VarSet -> VarSet :=
  fun fn seeds =>
    let go : VarSet -> VarSet -> VarSet :=
      GHC.DeferredFix.deferredFix1 (fun go (acc candidates : VarSet) =>
                                      let new_vs := minusVarSet (fn candidates) acc in
                                      if isEmptyVarSet new_vs : bool then acc else
                                      go (unionVarSet acc new_vs) new_vs) in
    go seeds seeds.

Definition isEmptyVarEnv {a} : VarEnv a -> bool :=
  UniqFM.isNullUFM.

Definition isTopDmdType : DmdType -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_DmdType env nil res =>
        if andb (isTopRes res) (isEmptyVarEnv env) : bool then true else
        false
    | _ => false
    end.

Definition isTopSig : StrictSig -> bool :=
  fun '(Mk_StrictSig ty) => isTopDmdType ty.

Definition isEmptyRuleInfo : RuleInfo -> bool :=
  fun x => true.

Definition isEmptyDVarSet : DVarSet -> bool :=
  UniqDSet.isEmptyUniqDSet.

Definition subDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => isEmptyDVarSet (minusDVarSet s1 s2).

Definition transCloDVarSet : (DVarSet -> DVarSet) -> DVarSet -> DVarSet :=
  fun fn seeds =>
    let go : DVarSet -> DVarSet -> DVarSet :=
      GHC.DeferredFix.deferredFix1 (fun go (acc candidates : DVarSet) =>
                                      let new_vs := minusDVarSet (fn candidates) acc in
                                      if isEmptyDVarSet new_vs : bool then acc else
                                      go (unionDVarSet acc new_vs) new_vs) in
    go seeds seeds.

Definition isEmptyDVarEnv {a} : DVarEnv a -> bool :=
  UniqDFM.isNullUDFM.

Definition isDataTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | TupleTyCon _ sort => BasicTypes.isBoxed (BasicTypes.tupleSortBoxity sort)
        | SumTyCon _ => false
        | DataTyCon _ _ => true
        | NewTyCon _ _ _ _ => false
        | AbstractTyCon => false
        end
    | _ => false
    end.

Definition isDataFamFlav : FamTyConFlav -> bool :=
  fun arg_0__ => match arg_0__ with | DataFamilyTyCon _ => true | _ => false end.

Definition isDataFamilyTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ flav _ _ => isDataFamFlav flav
    | _ => false
    end.

Definition isFamFreeTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | SynonymTyCon _ _ _ _ _ _ _ _ _ _ fam_free => fam_free
    | FamilyTyCon _ _ _ _ _ _ _ _ flav _ _ => isDataFamFlav flav
    | _ => true
    end.

Definition isTypeFamilyTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ flav _ _ => negb (isDataFamFlav flav)
    | _ => false
    end.

Definition isConLikeUnfolding : Unfolding -> bool :=
  fun x => false.

Definition isCompulsoryUnfolding : Unfolding -> bool :=
  fun x => false.

Definition isCoVarDetails : IdDetails -> bool :=
  fun arg_0__ => match arg_0__ with | CoVarId => true | _ => false end.

Definition isNonCoVarId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ _ details _ => negb (isCoVarDetails details)
    | _ => false
    end.

Definition isCoVar : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ _ details _ => isCoVarDetails details
    | _ => false
    end.

Definition varToCoreExpr {b} : CoreBndr -> Expr b :=
  fun v =>
    if isTyVar v : bool then Type_ (tt) else
    if isCoVar v : bool then Coercion (tt) else
    if andb Util.debugIsOn (negb (isId v)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreSyn.hs")
          #1920)
    else Mk_Var v.

Definition mkVarApps {b} : Expr b -> list Var -> Expr b :=
  fun f vars => Data.Foldable.foldl (fun e a => App e (varToCoreExpr a)) f vars.

Definition varsToCoreExprs {b} : list CoreBndr -> list (Expr b) :=
  fun vs => GHC.Base.map varToCoreExpr vs.

Definition isClosedSynFamilyTyConWithAxiom_maybe
   : TyCon -> option (list unit) :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ (ClosedSynFamilyTyCon mb) _ _ => mb
    | _ => None
    end.

Definition isClassTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (ClassTyCon _ _) => true
    | _ => false
    end.

Definition isCheapUnfolding : Unfolding -> bool :=
  fun x => false.

Definition isBuiltinRule : CoreRule -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => true
    | _ => false
    end.

Definition isBuiltInSynFamTyCon_maybe : TyCon -> option unit :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ (BuiltInSynFamTyCon ops) _ _ => Some ops
    | _ => None
    end.

Definition isBoxedTupleTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | TupleTyCon _ sort => BasicTypes.isBoxed (BasicTypes.tupleSortBoxity sort)
        | _ => false
        end
    | _ => false
    end.

Definition isBotRes : DmdResult -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Diverges => true
    | ThrowsExn => true
    | Dunno _ => false
    end.

Definition isBottomingSig : StrictSig -> bool :=
  fun '(Mk_StrictSig (Mk_DmdType _ _ res)) => isBotRes res.

Definition isBootUnfolding : Unfolding -> bool :=
  fun u => false.

Definition isBanged : HsImplBang -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | HsUnpack _ => true
    | HsStrict => true
    | HsLazy => false
    end.

Definition isAutoRule : CoreRule -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | BuiltinRule _ _ _ _ => false
    | Rule _ _ _ _ _ _ _ is_auto _ _ _ => is_auto
    end.

Definition isAlgTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition tyConFieldLabelEnv : TyCon -> FieldLabel.FieldLabelEnv :=
  fun tc =>
    if isAlgTyCon tc : bool then algTcFields tc else
    FastStringEnv.emptyDFsEnv.

Definition lookupTyConFieldLabel
   : FieldLabel.FieldLabelString -> TyCon -> option FieldLabel.FieldLabel :=
  fun lbl tc => FastStringEnv.lookupDFsEnv (tyConFieldLabelEnv tc) lbl.

Definition tyConFieldLabels : TyCon -> list FieldLabel.FieldLabel :=
  fun tc => FastStringEnv.dFsEnvElts (tyConFieldLabelEnv tc).

Definition isAbstractTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ AbstractTyCon _ _ => true
    | _ => false
    end.

Definition isAbstractClass : Class -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ AbstractClass => true
    | _ => false
    end.

Definition isAbsDmd : Demand -> bool :=
  fun arg_0__ => match arg_0__ with | JD _ Abs => true | _ => false end.

Definition intersectsVarEnv {a} : VarEnv a -> VarEnv a -> bool :=
  fun e1 e2 => negb (isEmptyVarEnv (UniqFM.intersectUFM e1 e2)).

Definition intersectVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.intersectUniqSets.

Definition intersectDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.intersectUniqDSets.

Definition initRecTc : RecTcChecker :=
  RC #100 NameEnv.emptyNameEnv.

Definition increaseStrictSigArity : nat -> StrictSig -> StrictSig :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | arity_increase, Mk_StrictSig (Mk_DmdType env dmds res) =>
        Mk_StrictSig (Mk_DmdType env (Coq.Init.Datatypes.app (Coq.Lists.List.repeat
                                                              topDmd arity_increase) dmds) res)
    end.

Definition idInfo `{Util.HasDebugCallStack} : Id -> IdInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ _ _ info => info
    | other => Panic.panicStr (GHC.Base.hs_string__ "idInfo") (Panic.someSDoc)
    end.

Definition idDetails : Id -> IdDetails :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Id _ _ _ _ details _ => details
    | other => Panic.panicStr (GHC.Base.hs_string__ "idDetails") (Panic.someSDoc)
    end.

Definition hasSomeUnfolding : Unfolding -> bool :=
  fun x => false.

Definition hasDemandEnvSig : StrictSig -> bool :=
  fun '(Mk_StrictSig (Mk_DmdType env _ _)) => negb (isEmptyVarEnv env).

Definition globaliseId : Id -> Id :=
  fun id =>
    match id with
    | Mk_TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_TcTyVar _ _ _ _ =>
        GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Mk_Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
    id_info_5__ =>
        Mk_Id varName_0__ realUnique_1__ varType_2__ GlobalId id_details_4__ id_info_5__
    end.

Definition getUseDmd {s} {u} : JointDmd s u -> u :=
  ud.

Definition getStrDmd {s} {u} : JointDmd s u -> s :=
  sd.

Definition mkProdDmd : list Demand -> CleanDemand :=
  fun dx =>
    JD (mkSProd (GHC.Base.map getStrDmd dx)) (mkUProd (GHC.Base.map getUseDmd dx)).

Definition getInScopeVars : InScopeSet -> VarSet :=
  fun '(InScope vs _) => vs.

Definition foldDVarSet {a} : (Var -> a -> a) -> a -> DVarSet -> a :=
  UniqDSet.foldUniqDSet.

Definition foldDVarEnv {a} {b} : (a -> b -> b) -> b -> DVarEnv a -> b :=
  UniqDFM.foldUDFM.

Definition flattenBinds {b} : list (Bind b) -> list (b * Expr b)%type :=
  fix flattenBinds (arg_0__ : list (Bind b)) : list (b * Expr b)%type
        := match arg_0__ with
           | cons (NonRec b r) binds => cons (pair b r) (flattenBinds binds)
           | cons (Rec prs1) binds => Coq.Init.Datatypes.app prs1 (flattenBinds binds)
           | nil => nil
           end.

Definition fixVarSet : (VarSet -> VarSet) -> VarSet -> VarSet :=
  GHC.DeferredFix.deferredFix2 (fun fixVarSet
                                (fn : (VarSet -> VarSet))
                                (vars : VarSet) =>
                                  let new_vars := fn vars in
                                  if subVarSet new_vars vars : bool then vars else
                                  fixVarSet fn new_vars).

Definition filterVarSet : (Var -> bool) -> VarSet -> VarSet :=
  UniqSet.filterUniqSet.

Definition filterVarEnv_Directly {a}
   : (Unique.Unique -> a -> bool) -> VarEnv a -> VarEnv a :=
  UniqFM.filterUFM_Directly.

Definition filterVarEnv {a} : (a -> bool) -> VarEnv a -> VarEnv a :=
  UniqFM.filterUFM.

Definition filterDVarSet : (Var -> bool) -> DVarSet -> DVarSet :=
  UniqDSet.filterUniqDSet.

Definition filterDVarEnv {a} : (a -> bool) -> DVarEnv a -> DVarEnv a :=
  UniqDFM.filterUDFM.

Definition famTyConFlav_maybe : TyCon -> option FamTyConFlav :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ flav _ _ => Some flav
    | _ => None
    end.

Definition extendDVarEnv {a} : DVarEnv a -> Var -> a -> DVarEnv a :=
  UniqDFM.addToUDFM.

Definition extendVarEnv {a} : VarEnv a -> Var -> a -> VarEnv a :=
  UniqFM.addToUFM.

Definition extendDVarEnvList {a}
   : DVarEnv a -> list (Var * a)%type -> DVarEnv a :=
  UniqDFM.addListToUDFM.

Definition extendVarEnvList {a} : VarEnv a -> list (Var * a)%type -> VarEnv a :=
  UniqFM.addListToUFM.

Definition extendDVarEnv_C {a}
   : (a -> a -> a) -> DVarEnv a -> Var -> a -> DVarEnv a :=
  UniqDFM.addToUDFM_C.

Definition extendVarEnv_Acc {a} {b}
   : (a -> b -> b) -> (a -> b) -> VarEnv b -> Var -> a -> VarEnv b :=
  UniqFM.addToUFM_Acc.

Definition extendVarEnv_C {a}
   : (a -> a -> a) -> VarEnv a -> Var -> a -> VarEnv a :=
  UniqFM.addToUFM_C.

Definition extendVarEnv_Directly {a}
   : VarEnv a -> Unique.Unique -> a -> VarEnv a :=
  UniqFM.addToUFM_Directly.

Definition extendVarSet : VarSet -> Var -> VarSet :=
  UniqSet.addOneToUniqSet.

Definition extendDVarSet : DVarSet -> Var -> DVarSet :=
  UniqDSet.addOneToUniqDSet.

Definition extendDVarSetList : DVarSet -> list Var -> DVarSet :=
  UniqDSet.addListToUniqDSet.

Definition extendVarSetList : VarSet -> list Var -> VarSet :=
  UniqSet.addListToUniqSet.

Definition modifyVarEnv {a} : (a -> a) -> VarEnv a -> Var -> VarEnv a :=
  fun mangle_fn env key =>
    match (lookupVarEnv env key) with
    | None => env
    | Some xx => extendVarEnv env key (mangle_fn xx)
    end.

Definition extendInScopeSetSet : InScopeSet -> VarSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, vs =>
        InScope (unionVarSet in_scope vs) (n GHC.Num.+ UniqSet.sizeUniqSet vs)
    end.

Definition extendInScopeSetList : InScopeSet -> list Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, vs =>
        InScope (Data.Foldable.foldl (fun s v => extendVarSet s v) in_scope vs) (n
                                                                                 GHC.Num.+
                                                                                 Coq.Lists.List.length vs)
    end.

Definition extendInScopeSet : InScopeSet -> Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, v => InScope (extendVarSet in_scope v) (n GHC.Num.+ #1)
    end.

Definition modifyDVarEnv {a} : (a -> a) -> DVarEnv a -> Var -> DVarEnv a :=
  fun mangle_fn env key =>
    match (lookupDVarEnv env key) with
    | None => env
    | Some xx => extendDVarEnv env key (mangle_fn xx)
    end.

Definition exprToCoercion_maybe : CoreExpr -> option unit :=
  fun arg_0__ => match arg_0__ with | Coercion co => Some co | _ => None end.

Definition expandSynTyCon_maybe {tyco}
   : TyCon ->
     list tyco -> option (list (TyVar * tyco)%type * unit * list tyco)%type :=
  fun tc tys =>
    match tc with
    | SynonymTyCon _ _ _ tvs _ _ arity _ rhs _ _ =>
        match Util.listLengthCmp tys arity with
        | Gt =>
            Some (pair (pair (GHC.List.zip tvs tys) rhs) (Coq.Lists.List.skipn arity tys))
        | Eq => Some (pair (pair (GHC.List.zip tvs tys) rhs) nil)
        | Lt => None
        end
    | _ => None
    end.

Definition exnRes : DmdResult :=
  ThrowsExn.

Axiom evaldUnfolding : Unfolding.

Definition evalDmd : Demand :=
  JD (Mk_Str VanStr HeadStr) useTop.

Definition eqSpecType : EqSpec -> unit :=
  fun '(Mk_EqSpec _ ty) => ty.

Definition eqSpecTyVar : EqSpec -> TyVar :=
  fun '(Mk_EqSpec tv _) => tv.

Local Definition Eq___Var_op_zeze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.== realUnique b.

Local Definition Eq___Var_op_zsze__ : Var -> Var -> bool :=
  fun x y => negb (Eq___Var_op_zeze__ x y).

Program Instance Eq___Var : GHC.Base.Eq_ Var :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Var_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Var_op_zsze__ |}.

Definition filterEqSpec : list EqSpec -> list TyVar -> list TyVar :=
  fun eq_spec =>
    let not_in_eq_spec :=
      fun var =>
        Data.Foldable.all (negb GHC.Base.∘
                           ((fun arg_0__ => arg_0__ GHC.Base.== var) GHC.Base.∘ eqSpecTyVar)) eq_spec in
    GHC.List.filter not_in_eq_spec.

Definition eqSpecPair : EqSpec -> (TyVar * unit)%type :=
  fun '(Mk_EqSpec tv ty) => pair tv ty.

Definition emptyVarSet : VarSet :=
  UniqSet.emptyUniqSet.

Definition mapUnionVarSet {a} : (a -> VarSet) -> list a -> VarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionVarSet GHC.Base.∘ get_set) emptyVarSet xs.

Definition emptyVarEnv {a} : VarEnv a :=
  UniqFM.emptyUFM.

Definition mkRnEnv2 : InScopeSet -> RnEnv2 :=
  fun vars => RV2 emptyVarEnv emptyVarEnv vars.

Definition nukeRnEnvL : RnEnv2 -> RnEnv2 :=
  fun '(RV2 envL_0__ envR_1__ in_scope_2__) =>
    RV2 emptyVarEnv envR_1__ in_scope_2__.

Definition nukeRnEnvR : RnEnv2 -> RnEnv2 :=
  fun '(RV2 envL_0__ envR_1__ in_scope_2__) =>
    RV2 envL_0__ emptyVarEnv in_scope_2__.

Definition splitFVs : bool -> DmdEnv -> (DmdEnv * DmdEnv)%type :=
  fun is_thunk rhs_fvs =>
    let add :=
      fun arg_0__ arg_1__ arg_2__ =>
        match arg_0__, arg_1__, arg_2__ with
        | uniq, (JD s u as dmd), pair lazy_fv sig_fv =>
            match s with
            | Lazy => pair (UniqFM.addToUFM_Directly lazy_fv uniq dmd) sig_fv
            | _ =>
                pair (UniqFM.addToUFM_Directly lazy_fv uniq (JD Lazy u))
                     (UniqFM.addToUFM_Directly sig_fv uniq (JD s Abs))
            end
        end in
    if is_thunk : bool
    then UniqFM.nonDetFoldUFM_Directly add (pair emptyVarEnv emptyVarEnv)
         rhs_fvs else
    partitionVarEnv isWeakDmd rhs_fvs.

Definition emptyTidyEnv : TidyEnv :=
  pair OccName.emptyTidyOccEnv emptyVarEnv.

Definition emptyRuleInfo :=
  EmptyRuleInfo.

Definition zapFragileInfo : IdInfo -> option IdInfo :=
  fun '((Mk_IdInfo _ _ unf _ _ _ occ _ _ _ _ as info)) =>
    let new_unf := zapFragileUnfolding unf in
    GHC.Prim.seq new_unf (Some (setOccInfo (setUnfoldingInfo (setRuleInfo info
                                                                          emptyRuleInfo) new_unf)
                                           (BasicTypes.zapFragileOcc occ))).

Definition emptyRuleEnv : RuleEnv :=
  Mk_RuleEnv NameEnv.emptyNameEnv Module.emptyModuleSet.

Definition emptyInScopeSet : InScopeSet :=
  InScope emptyVarSet #1.

Definition emptyDmdEnv : VarEnv Demand :=
  emptyVarEnv.

Definition exnDmdType : DmdType :=
  Mk_DmdType emptyDmdEnv nil exnRes.

Definition exnSig : StrictSig :=
  Mk_StrictSig exnDmdType.

Definition mkClosedStrictSig : list Demand -> DmdResult -> StrictSig :=
  fun ds res => mkStrictSig (Mk_DmdType emptyDmdEnv ds res).

Definition zapUsageEnvSig : StrictSig -> StrictSig :=
  fun '(Mk_StrictSig (Mk_DmdType _ ds r)) => mkClosedStrictSig ds r.

Definition zapUsageEnvInfo : IdInfo -> option IdInfo :=
  fun info =>
    if hasDemandEnvSig (strictnessInfo info) : bool
    then Some (let 'Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__
                  cafInfo_3__ oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ strictnessInfo_7__
                  demandInfo_8__ callArityInfo_9__ levityInfo_10__ := info in
               Mk_IdInfo arityInfo_0__ ruleInfo_1__ unfoldingInfo_2__ cafInfo_3__
                         oneShotInfo_4__ inlinePragInfo_5__ occInfo_6__ (zapUsageEnvSig (strictnessInfo
                                                                                         info)) demandInfo_8__
                         callArityInfo_9__ levityInfo_10__) else
    None.

Definition nopDmdType : DmdType :=
  Mk_DmdType emptyDmdEnv nil topRes.

Definition nopSig : StrictSig :=
  Mk_StrictSig nopDmdType.

Definition vanillaIdInfo : IdInfo :=
  Mk_IdInfo unknownArity emptyRuleInfo noUnfolding vanillaCafInfo
            BasicTypes.NoOneShotInfo BasicTypes.defaultInlinePragma BasicTypes.noOccInfo
            nopSig topDmd unknownArity NoLevityInfo.

Definition noCafIdInfo : IdInfo :=
  setCafInfo vanillaIdInfo NoCafRefs.

Definition postProcessDmdEnv : DmdShell -> DmdEnv -> DmdEnv :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (JD ss us as ds), env =>
        match us with
        | Abs => emptyDmdEnv
        | _ =>
            let j_2__ := mapVarEnv (postProcessDmd ds) env in
            match ss with
            | Mk_Str VanStr _ => match us with | Mk_Use One _ => env | _ => j_2__ end
            | _ => j_2__
            end
        end
    end.

Definition postProcessDmdType : DmdShell -> DmdType -> BothDmdArg :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (JD ss _ as du), Mk_DmdType fv _ res_ty =>
        let term_info :=
          match postProcessDmdResult ss res_ty with
          | Dunno _ => Dunno tt
          | ThrowsExn => ThrowsExn
          | Diverges => Diverges
          end in
        pair (postProcessDmdEnv du fv) term_info
    end.

Definition postProcessUnsat : DmdShell -> DmdType -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (JD ss _ as ds), Mk_DmdType fv args res_ty =>
        Mk_DmdType (postProcessDmdEnv ds fv) (GHC.Base.map (postProcessDmd ds) args)
        (postProcessDmdResult ss res_ty)
    end.

Definition emptyDVarSet : DVarSet :=
  UniqDSet.emptyUniqDSet.

Definition mapUnionDVarSet {a} : (a -> DVarSet) -> list a -> DVarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionDVarSet GHC.Base.∘ get_set) emptyDVarSet xs.

Definition ruleInfoFreeVars : RuleInfo -> DVarSet :=
  fun x => emptyDVarSet.

Definition emptyDVarEnv {a} : DVarEnv a :=
  UniqDFM.emptyUDFM.

Definition elemVarSetByKey : Unique.Unique -> VarSet -> bool :=
  UniqSet.elemUniqSet_Directly.

Definition restrictVarEnv {a} : VarEnv a -> VarSet -> VarEnv a :=
  fun env vs =>
    let keep :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | u, _ => elemVarSetByKey u vs
        end in
    filterVarEnv_Directly keep env.

Definition uniqAway' : InScopeSet -> Var -> Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope set n, var =>
        let orig_unique := Unique.getUnique var in
        let try :=
          GHC.DeferredFix.deferredFix1 (fun try k =>
                                          let uniq := Unique.deriveUnique orig_unique (BinNat.N.of_nat n GHC.Num.* k) in
                                          let msg :=
                                            GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend Panic.someSDoc
                                                                                                 (Datatypes.id
                                                                                                  (GHC.Base.hs_string__
                                                                                                   "tries")))
                                                                               Panic.someSDoc) Panic.someSDoc in
                                          if andb Util.debugIsOn (k GHC.Base.> #1000) : bool
                                          then Panic.panicStr (GHC.Base.hs_string__ "uniqAway loop:") msg else
                                          if elemVarSetByKey uniq set : bool then try (k GHC.Num.+ #1) else
                                          if k GHC.Base.> #3 : bool then setVarUnique var uniq else
                                          setVarUnique var uniq) in
        try #1
    end.

Definition alterDVarEnv {a}
   : (option a -> option a) -> DVarEnv a -> Var -> DVarEnv a :=
  UniqDFM.alterUDFM.

Definition alterVarEnv {a}
   : (option a -> option a) -> VarEnv a -> Var -> VarEnv a :=
  UniqFM.alterUFM.

Definition delDVarEnv {a} : DVarEnv a -> Var -> DVarEnv a :=
  UniqDFM.delFromUDFM.

Definition delVarEnv {a} : VarEnv a -> Var -> VarEnv a :=
  UniqFM.delFromUFM.

Definition delDVarEnvList {a} : DVarEnv a -> list Var -> DVarEnv a :=
  UniqDFM.delListFromUDFM.

Definition delVarEnvList {a} : VarEnv a -> list Var -> VarEnv a :=
  UniqFM.delListFromUFM.

Definition delDVarSet : DVarSet -> Var -> DVarSet :=
  UniqDSet.delOneFromUniqDSet.

Definition delVarSet : VarSet -> Var -> VarSet :=
  UniqSet.delOneFromUniqSet.

Definition delDVarSetList : DVarSet -> list Var -> DVarSet :=
  UniqDSet.delListFromUniqDSet.

Definition delVarSetList : VarSet -> list Var -> VarSet :=
  UniqSet.delListFromUniqSet.

Definition delVarEnv_Directly {a} : VarEnv a -> Unique.Unique -> VarEnv a :=
  UniqFM.delFromUFM_Directly.

Definition delVarSetByKey : VarSet -> Unique.Unique -> VarSet :=
  UniqSet.delOneFromUniqSet_Directly.

Definition elemDVarEnv {a} : Var -> DVarEnv a -> bool :=
  UniqDFM.elemUDFM.

Definition elemVarEnv {a} : Var -> VarEnv a -> bool :=
  UniqFM.elemUFM.

Definition elemDVarSet : Var -> DVarSet -> bool :=
  UniqDSet.elementOfUniqDSet.

Definition elemVarSet : Var -> VarSet -> bool :=
  UniqSet.elementOfUniqSet.

Definition elemVarEnvByKey {a} : Unique.Unique -> VarEnv a -> bool :=
  UniqFM.elemUFM_Directly.

Definition inRnEnvL : RnEnv2 -> Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 env _ _, v => elemVarEnv v env
    end.

Definition inRnEnvR : RnEnv2 -> Var -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 _ env _, v => elemVarEnv v env
    end.

Definition elemInScopeSet : Var -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, InScope in_scope _ => elemVarSet v in_scope
    end.

Definition rnBndr2_var : RnEnv2 -> Var -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | RV2 envL envR in_scope, bL, bR =>
        let new_b :=
          if negb (elemInScopeSet bL in_scope) : bool then bL else
          if negb (elemInScopeSet bR in_scope) : bool then bR else
          uniqAway' in_scope bL in
        pair (RV2 (extendVarEnv envL bL new_b) (extendVarEnv envR bR new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

Definition rnBndr2 : RnEnv2 -> Var -> Var -> RnEnv2 :=
  fun env bL bR => Data.Tuple.fst (rnBndr2_var env bL bR).

Definition rnBndrs2 : RnEnv2 -> list Var -> list Var -> RnEnv2 :=
  fun env bsL bsR => Util.foldl2 rnBndr2 env bsL bsR.

Definition rnInScope : Var -> RnEnv2 -> bool :=
  fun x env => elemInScopeSet x (in_scope env).

Definition uniqAway : InScopeSet -> Var -> Var :=
  fun in_scope var =>
    if elemInScopeSet var in_scope : bool then uniqAway' in_scope var else
    var.

Definition rnBndrL : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bL =>
        let new_b := uniqAway in_scope bL in
        pair (RV2 (extendVarEnv envL bL new_b) envR (extendInScopeSet in_scope new_b))
             new_b
    end.

Definition rnBndrR : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bR =>
        let new_b := uniqAway in_scope bR in
        pair (RV2 envL (extendVarEnv envR bR new_b) (extendInScopeSet in_scope new_b))
             new_b
    end.

Definition rnEtaL : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bL =>
        let new_b := uniqAway in_scope bL in
        pair (RV2 (extendVarEnv envL bL new_b) (extendVarEnv envR new_b new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

Definition rnEtaR : RnEnv2 -> Var -> (RnEnv2 * Var)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RV2 envL envR in_scope, bR =>
        let new_b := uniqAway in_scope bR in
        pair (RV2 (extendVarEnv envL new_b new_b) (extendVarEnv envR bR new_b)
                  (extendInScopeSet in_scope new_b)) new_b
    end.

Definition dmdTypeDepth : DmdType -> BasicTypes.Arity :=
  fun '(Mk_DmdType _ ds _) => Coq.Lists.List.length ds.

Definition dmdTransformSig : StrictSig -> CleanDemand -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_StrictSig (Mk_DmdType _ arg_ds _ as dmd_ty), cd =>
        postProcessUnsat (peelManyCalls (Coq.Lists.List.length arg_ds) cd) dmd_ty
    end.

Definition dmdTransformDictSelSig : StrictSig -> CleanDemand -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_StrictSig (Mk_DmdType _ (cons dict_dmd nil) _), cd =>
        let enhance :=
          fun cd old => if isAbsDmd old : bool then old else mkOnceUsedDmd cd in
        let 'pair cd' defer_use := peelCallDmd cd in
        match splitProdDmd_maybe dict_dmd with
        | Some jds =>
            postProcessUnsat defer_use (Mk_DmdType emptyDmdEnv (cons (mkOnceUsedDmd
                                                                      (mkProdDmd (GHC.Base.map (enhance cd') jds))) nil)
                                                   topRes)
        | _ => nopDmdType
        end
    | _, _ => Panic.panic (GHC.Base.hs_string__ "dmdTransformDictSelSig: no args")
    end.

Program Definition dmdTransformDataConSig
           : BasicTypes.Arity -> StrictSig -> CleanDemand -> DmdType :=
          fun arg_0__ arg_1__ arg_2__ =>
            match arg_0__, arg_1__, arg_2__ with
            | arity, Mk_StrictSig (Mk_DmdType _ _ con_res), JD str abs =>
                let fix go_abs arg_3__ arg_4__
                          := match arg_3__, arg_4__ with
                             | num_5__, dmd =>
                                 if Bool.Sumbool.sumbool_of_bool (num_5__ GHC.Base.== #0)
                                 then splitUseProdDmd arity dmd else
                                 match arg_3__, arg_4__ with
                                 | n, UCall One u' => go_abs (n GHC.Num.- #1) u'
                                 | _, _ => None
                                 end
                             end in
                let go_str :=
                  GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_10__ arg_11__ => arg_10__) _
                                (fun arg_10__ arg_11__ go_str =>
                                   match arg_10__, arg_11__ with
                                   | num_12__, dmd =>
                                       if Bool.Sumbool.sumbool_of_bool (num_12__ GHC.Base.== #0)
                                       then splitStrProdDmd arity dmd else
                                       match arg_10__, arg_11__ with
                                       | n, SCall s' => go_str (n GHC.Num.- #1) s'
                                       | n, HyperStr => go_str (n GHC.Num.- #1) HyperStr
                                       | _, _ => None
                                       end
                                   end) in
                match go_str arity str with
                | Some str_dmds =>
                    match go_abs arity abs with
                    | Some abs_dmds =>
                        Mk_DmdType emptyDmdEnv (mkJointDmds str_dmds abs_dmds) con_res
                    | _ => nopDmdType
                    end
                | _ => nopDmdType
                end
            end.
Solve Obligations with (solve_dmdTransform).

Definition disjointVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => UniqFM.disjointUFM (UniqSet.getUniqSet s1) (UniqSet.getUniqSet s2).

Definition intersectsVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => negb (disjointVarSet s1 s2).

Definition disjointVarEnv {a} : VarEnv a -> VarEnv a -> bool :=
  UniqFM.disjointUFM.

Definition disjointDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => UniqDFM.disjointUDFM s1 s2.

Definition intersectsDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => negb (disjointDVarSet s1 s2).

Definition delInScopeSet : InScopeSet -> Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, v => InScope (delVarSet in_scope v) n
    end.

Definition delBndrsR : RnEnv2 -> list Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 _ env in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 envL_2__ (delVarEnvList env v) (extendInScopeSetList in_scope v)
    end.

Definition delBndrsL : RnEnv2 -> list Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 env _ in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 (delVarEnvList env v) envR_3__ (extendInScopeSetList in_scope v)
    end.

Definition delBndrR : RnEnv2 -> Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 _ env in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 envL_2__ (delVarEnv env v) (extendInScopeSet in_scope v)
    end.

Definition delBndrL : RnEnv2 -> Var -> RnEnv2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (RV2 env _ in_scope as rn), v =>
        let 'RV2 envL_2__ envR_3__ in_scope_4__ := rn in
        RV2 (delVarEnv env v) envR_3__ (extendInScopeSet in_scope v)
    end.

Definition deTagExpr {t} : TaggedExpr t -> CoreExpr :=
  fix deTagExpr (arg_0__ : TaggedExpr t) : CoreExpr
        := let deTagBind (arg_0__ : TaggedBind t) : CoreBind :=
             match arg_0__ with
             | NonRec (TB b _) rhs => NonRec b (deTagExpr rhs)
             | Rec prs =>
                 Rec (let cont_2__ arg_3__ :=
                        let 'pair (TB b _) rhs := arg_3__ in
                        cons (pair b (deTagExpr rhs)) nil in
                      Coq.Lists.List.flat_map cont_2__ prs)
             end in
           let deTagAlt (arg_0__ : TaggedAlt t) : CoreAlt :=
             let 'pair (pair con bndrs) rhs := arg_0__ in
             pair (pair con (let cont_1__ arg_2__ := let 'TB b _ := arg_2__ in cons b nil in
                         Coq.Lists.List.flat_map cont_1__ bndrs)) (deTagExpr rhs) in
           match arg_0__ with
           | Mk_Var v => Mk_Var v
           | Lit l => Lit l
           | Type_ ty => Type_ ty
           | Coercion co => Coercion co
           | App e1 e2 => App (deTagExpr e1) (deTagExpr e2)
           | Lam (TB b _) e => Lam b (deTagExpr e)
           | Let bind body => Let (deTagBind bind) (deTagExpr body)
           | Case e (TB b _) ty alts =>
               Case (deTagExpr e) b ty (GHC.Base.map deTagAlt alts)
           | Tick t e => Tick t (deTagExpr e)
           | Cast e co => Cast (deTagExpr e) co
           end.

Definition deTagBind {t} : TaggedBind t -> CoreBind :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec (TB b _) rhs => NonRec b (deTagExpr rhs)
    | Rec prs =>
        Rec (let cont_2__ arg_3__ :=
               let 'pair (TB b _) rhs := arg_3__ in
               cons (pair b (deTagExpr rhs)) nil in
             Coq.Lists.List.flat_map cont_2__ prs)
    end.

Definition deTagAlt {t} : TaggedAlt t -> CoreAlt :=
  fun '(pair (pair con bndrs) rhs) =>
    pair (pair con (let cont_1__ arg_2__ := let 'TB b _ := arg_2__ in cons b nil in
                Coq.Lists.List.flat_map cont_1__ bndrs)) (deTagExpr rhs).

Definition deAnnotate'
   : forall {bndr} {annot}, AnnExpr' bndr annot -> Expr bndr :=
  fix deAnnotate' {bndr} {annot} (arg_0__ : AnnExpr' bndr annot) : Expr bndr
        := let deAnnotate {bndr} {annot} (arg_0__ : AnnExpr bndr annot) : Expr bndr :=
             let 'pair _ e := arg_0__ in
             deAnnotate' e in
           let deAnnAlt {bndr} {annot} (arg_0__ : AnnAlt bndr annot) : Alt bndr :=
             let 'pair (pair con args) rhs := arg_0__ in
             pair (pair con args) (deAnnotate rhs) in
           match arg_0__ with
           | AnnType t => Type_ t
           | AnnCoercion co => Coercion co
           | AnnVar v => Mk_Var v
           | AnnLit lit => Lit lit
           | AnnLam binder body => Lam binder (deAnnotate body)
           | AnnApp fun_ arg => App (deAnnotate fun_) (deAnnotate arg)
           | AnnCast e (pair _ co) => Cast (deAnnotate e) co
           | AnnTick tick body => Tick tick (deAnnotate body)
           | AnnLet bind body => Let (deAnnBind bind) (deAnnotate body)
           | AnnCase scrut v t alts =>
               Case (deAnnotate scrut) v t (GHC.Base.map deAnnAlt alts)
           end with deAnnBind {b} {annot} (arg_0__ : AnnBind b annot) : Bind b
                      := let deAnnotate {bndr} {annot} (arg_0__ : AnnExpr bndr annot) : Expr bndr :=
                           let 'pair _ e := arg_0__ in
                           deAnnotate' e in
                         match arg_0__ with
                         | AnnNonRec var rhs => NonRec var (deAnnotate rhs)
                         | AnnRec pairs =>
                             Rec (let cont_2__ arg_3__ :=
                                    let 'pair v rhs := arg_3__ in
                                    cons (pair v (deAnnotate rhs)) nil in
                                  Coq.Lists.List.flat_map cont_2__ pairs)
                         end for deAnnotate'.

Definition deAnnotate {bndr} {annot} : AnnExpr bndr annot -> Expr bndr :=
  fun '(pair _ e) => deAnnotate' e.

Definition deAnnBind : forall {b} {annot}, AnnBind b annot -> Bind b :=
  fix deAnnotate' {bndr} {annot} (arg_0__ : AnnExpr' bndr annot) : Expr bndr
        := let deAnnotate {bndr} {annot} (arg_0__ : AnnExpr bndr annot) : Expr bndr :=
             let 'pair _ e := arg_0__ in
             deAnnotate' e in
           let deAnnAlt {bndr} {annot} (arg_0__ : AnnAlt bndr annot) : Alt bndr :=
             let 'pair (pair con args) rhs := arg_0__ in
             pair (pair con args) (deAnnotate rhs) in
           match arg_0__ with
           | AnnType t => Type_ t
           | AnnCoercion co => Coercion co
           | AnnVar v => Mk_Var v
           | AnnLit lit => Lit lit
           | AnnLam binder body => Lam binder (deAnnotate body)
           | AnnApp fun_ arg => App (deAnnotate fun_) (deAnnotate arg)
           | AnnCast e (pair _ co) => Cast (deAnnotate e) co
           | AnnTick tick body => Tick tick (deAnnotate body)
           | AnnLet bind body => Let (deAnnBind bind) (deAnnotate body)
           | AnnCase scrut v t alts =>
               Case (deAnnotate scrut) v t (GHC.Base.map deAnnAlt alts)
           end with deAnnBind {b} {annot} (arg_0__ : AnnBind b annot) : Bind b
                      := let deAnnotate {bndr} {annot} (arg_0__ : AnnExpr bndr annot) : Expr bndr :=
                           let 'pair _ e := arg_0__ in
                           deAnnotate' e in
                         match arg_0__ with
                         | AnnNonRec var rhs => NonRec var (deAnnotate rhs)
                         | AnnRec pairs =>
                             Rec (let cont_2__ arg_3__ :=
                                    let 'pair v rhs := arg_3__ in
                                    cons (pair v (deAnnotate rhs)) nil in
                                  Coq.Lists.List.flat_map cont_2__ pairs)
                         end for deAnnBind.

Definition deAnnAlt {bndr} {annot} : AnnAlt bndr annot -> Alt bndr :=
  fun '(pair (pair con args) rhs) => pair (pair con args) (deAnnotate rhs).

Definition dataConWrapId_maybe : DataCon -> option Id :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep => None
    | DCR wrap_id _ _ _ _ => Some wrap_id
    end.

Definition dataConWrapId : DataCon -> Id :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep => dcWorkId dc
    | DCR wrap_id _ _ _ _ => wrap_id
    end.

Definition dataConWorkId : DataCon -> Id :=
  fun dc => dcWorkId dc.

Definition mkConApp {b} : DataCon -> list (Arg b) -> Expr b :=
  fun con args => mkApps (Mk_Var (dataConWorkId con)) args.

Definition mkConApp2 {b} : DataCon -> list unit -> list Var -> Expr b :=
  fun con tys arg_ids =>
    mkApps (mkApps (Mk_Var (dataConWorkId con)) (GHC.Base.map Type_ tys))
           (GHC.Base.map varToCoreExpr arg_ids).

Definition dataConUserTyVarBinders : DataCon -> list TyVarBinder :=
  dcUserTyVarBinders.

Definition dataConUnivTyVars : DataCon -> list TyVar :=
  fun '(MkData _ _ _ _ tvbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => tvbs.

Definition dataConUnivAndExTyVars : DataCon -> list TyVar :=
  fun '(MkData _ _ _ _ univ_tvs ex_tvs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
    Coq.Init.Datatypes.app univ_tvs ex_tvs.

Definition dataConTyCon : DataCon -> TyCon :=
  dcRepTyCon.

Definition dataConTag : DataCon -> BasicTypes.ConTag :=
  dcTag.

Definition dataConTagZ : DataCon -> BasicTypes.ConTagZ :=
  fun con => dataConTag con GHC.Num.- BasicTypes.fIRST_TAG.

Definition dataConStupidTheta : DataCon -> unit :=
  fun dc => dcStupidTheta dc.

Definition dataConSrcBangs : DataCon -> list HsSrcBang :=
  dcSrcBangs.

Definition dataConSourceArity : DataCon -> BasicTypes.Arity :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arity _ _ _ _) => arity.

Definition isNullarySrcDataCon : DataCon -> bool :=
  fun dc => dataConSourceArity dc GHC.Base.== #0.

Definition dataConRepType : DataCon -> unit :=
  dcRepType.

Definition dataConRepArity : DataCon -> BasicTypes.Arity :=
  fun '(MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arity _ _ _ _ _) => arity.

Definition isNullaryRepDataCon : DataCon -> bool :=
  fun dc => dataConRepArity dc GHC.Base.== #0.

Definition dataConName : DataCon -> Name.Name :=
  dcName.

Definition dataConIsInfix : DataCon -> bool :=
  dcInfix.

Definition dataConImplBangs : DataCon -> list HsImplBang :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep => Coq.Lists.List.repeat HsLazy (dcSourceArity dc)
    | DCR _ _ _ _ bangs => bangs
    end.

Definition dataConFullSig
   : DataCon ->
     (list TyVar * list TyVar * list EqSpec * unit * list unit * unit)%type :=
  fun '(MkData _ _ _ _ univ_tvs ex_tvs _ eq_spec theta _ arg_tys res_ty _ _ _ _ _
  _ _ _ _ _) =>
    pair (pair (pair (pair (pair univ_tvs ex_tvs) eq_spec) theta) arg_tys) res_ty.

Definition dataConFieldType_maybe
   : DataCon ->
     FieldLabel.FieldLabelString -> option (FieldLabel.FieldLabel * unit)%type :=
  fun con label =>
    Data.Foldable.find ((fun arg_0__ => arg_0__ GHC.Base.== label) GHC.Base.∘
                        (FieldLabel.flLabel GHC.Base.∘ Data.Tuple.fst)) (GHC.List.zip (dcFields con)
                                                                                      (dcOrigArgTys con)).

Definition dataConFieldLabels : DataCon -> list FieldLabel.FieldLabel :=
  dcFields.

Definition fieldsOfAlgTcRhs : AlgTyConRhs -> FieldLabel.FieldLabelEnv :=
  fun rhs =>
    let dataConsFields :=
      fun dcs => Data.Foldable.concatMap dataConFieldLabels dcs in
    FastStringEnv.mkDFsEnv (Coq.Lists.List.flat_map (fun fl =>
                                                       cons (pair (FieldLabel.flLabel fl) fl) nil) (dataConsFields
                                                     (visibleDataCons rhs))).

Axiom dataConCannotMatch : list unit -> DataCon -> bool.

Definition dataConBoxer : DataCon -> option unit :=
  fun arg_0__ =>
    match arg_0__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (DCR _ boxer _ _ _) _ _ _ _ _ _ =>
        Some boxer
    | _ => None
    end.

Definition dVarSetToVarSet : DVarSet -> VarSet :=
  UniqSet.unsafeUFMToUniqSet GHC.Base.∘ UniqDFM.udfmToUfm.

Definition dVarSetMinusVarSet : DVarSet -> VarSet -> DVarSet :=
  UniqDSet.uniqDSetMinusUniqSet.

Definition dVarSetIntersectVarSet : DVarSet -> VarSet -> DVarSet :=
  UniqDSet.uniqDSetIntersectUniqSet.

Definition dVarSetElems : DVarSet -> list Var :=
  UniqDSet.uniqDSetToList.

Definition dVarEnvElts {a} : DVarEnv a -> list a :=
  UniqDFM.eltsUDFM.

Definition cprSumRes : BasicTypes.ConTag -> DmdResult :=
  fun tag => Dunno (RetSum tag).

Definition cprProdRes : list DmdType -> DmdResult :=
  fun _arg_tys => Dunno RetProd.

Definition cprProdDmdType : BasicTypes.Arity -> DmdType :=
  fun arity => Mk_DmdType emptyDmdEnv nil (vanillaCprProdRes arity).

Definition cprProdSig : BasicTypes.Arity -> StrictSig :=
  fun arity => Mk_StrictSig (cprProdDmdType arity).

Definition collectValBinders : CoreExpr -> (list Id * CoreExpr)%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
              := let j_3__ :=
                   match arg_0__, arg_1__ with
                   | ids, body => pair (GHC.List.reverse ids) body
                   end in
                 match arg_0__, arg_1__ with
                 | ids, Lam b e => if isId b : bool then go (cons b ids) e else j_3__
                 | _, _ => j_3__
                 end in
    go nil expr.

Definition collectTyBinders : CoreExpr -> (list TyVar * CoreExpr)%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
              := let j_3__ :=
                   match arg_0__, arg_1__ with
                   | tvs, e => pair (GHC.List.reverse tvs) e
                   end in
                 match arg_0__, arg_1__ with
                 | tvs, Lam b e => if isTyVar b : bool then go (cons b tvs) e else j_3__
                 | _, _ => j_3__
                 end in
    go nil expr.

Definition collectTyAndValBinders
   : CoreExpr -> (list TyVar * list Id * CoreExpr)%type :=
  fun expr =>
    let 'pair tvs body1 := collectTyBinders expr in
    let 'pair ids body := collectValBinders body1 in
    pair (pair tvs ids) body.

Definition collectNBinders {b} : nat -> Expr b -> (list b * Expr b)%type :=
  fun orig_n orig_expr =>
    let fix go arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | num_3__, bs, expr =>
                     if num_3__ GHC.Base.== #0 : bool then pair (GHC.List.reverse bs) expr else
                     match arg_0__, arg_1__, arg_2__ with
                     | n, bs, Lam b e => go (n GHC.Num.- #1) (cons b bs) e
                     | _, _, _ =>
                         Panic.panicStr (GHC.Base.hs_string__ "collectNBinders") Panic.someSDoc
                     end
                 end in
    go orig_n nil orig_expr.

Definition collectBinders {b} : Expr b -> (list b * Expr b)%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | bs, Lam b e => go (cons b bs) e
                 | bs, e => pair (GHC.List.reverse bs) e
                 end in
    go nil expr.

Definition collectArgsTicks {b}
   : (Tickish Id -> bool) ->
     Expr b -> (Expr b * list (Arg b) * list (Tickish Id))%type :=
  fun skipTick expr =>
    let fix go arg_0__ arg_1__ arg_2__
              := let j_4__ :=
                   match arg_0__, arg_1__, arg_2__ with
                   | e, as_, ts => pair (pair e as_) (GHC.List.reverse ts)
                   end in
                 match arg_0__, arg_1__, arg_2__ with
                 | App f a, as_, ts => go f (cons a as_) ts
                 | Tick t e, as_, ts => if skipTick t : bool then go e as_ (cons t ts) else j_4__
                 | _, _, _ => j_4__
                 end in
    go expr nil nil.

Definition collectArgs {b} : Expr b -> (Expr b * list (Arg b))%type :=
  fun expr =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | App f a, as_ => go f (cons a as_)
                 | e, as_ => pair e as_
                 end in
    go expr nil.

Program Definition collectAnnBndrs {bndr} {annot}
           : AnnExpr bndr annot -> (list bndr * AnnExpr bndr annot)%type :=
          fun e =>
            let collect :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                               size_AnnExpr' (snd arg_1__)) _ (fun arg_0__ arg_1__ collect =>
                               match arg_0__, arg_1__ with
                               | bs, pair _ (AnnLam b body) => collect (cons b bs) body
                               | bs, body => pair (GHC.List.reverse bs) body
                               end) in
            collect nil e.

Program Definition collectAnnArgsTicks {b} {a}
           : (Tickish Var -> bool) ->
             AnnExpr b a -> (AnnExpr b a * list (AnnExpr b a) * list (Tickish Var))%type :=
          fun tickishOk expr =>
            let go :=
              GHC.Wf.wfFix3 Coq.Init.Peano.lt (fun arg_0__ arg_1__ arg_2__ =>
                               size_AnnExpr' (snd arg_0__)) _ (fun arg_0__ arg_1__ arg_2__ go =>
                               let j_4__ :=
                                 match arg_0__, arg_1__, arg_2__ with
                                 | e, as_, ts => pair (pair e as_) (GHC.List.reverse ts)
                                 end in
                               match arg_0__, arg_1__, arg_2__ with
                               | pair _ (AnnApp f a), as_, ts => go f (cons a as_) ts
                               | pair _ (AnnTick t e), as_, ts =>
                                   if Bool.Sumbool.sumbool_of_bool (tickishOk t) then go e as_ (cons t ts) else
                                   j_4__
                               | _, _, _ => j_4__
                               end) in
            go expr nil nil.
Solve Obligations with (solve_collectAnnArgsTicks).

Program Definition collectAnnArgs {b} {a}
           : AnnExpr b a -> (AnnExpr b a * list (AnnExpr b a))%type :=
          fun expr =>
            let go :=
              GHC.Wf.wfFix2 Coq.Init.Peano.lt (fun arg_0__ arg_1__ =>
                               size_AnnExpr' (snd arg_0__)) _ (fun arg_0__ arg_1__ go =>
                               match arg_0__, arg_1__ with
                               | pair _ (AnnApp f a), as_ => go f (cons a as_)
                               | e, as_ => pair e as_
                               end) in
            go expr nil.
Solve Obligations with (solve_collectAnnArgsTicks).

Definition coVarDetails : IdDetails :=
  CoVarId.

Definition mkCoVar : Name.Name -> unit -> CoVar :=
  fun name ty => mk_id name ty (LocalId NotExported) coVarDetails vanillaIdInfo.

Definition cmpAltCon : AltCon -> AltCon -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | DEFAULT, DEFAULT => Eq
    | DEFAULT, _ => Lt
    | DataAlt d1, DataAlt d2 => GHC.Base.compare (dataConTag d1) (dataConTag d2)
    | DataAlt _, DEFAULT => Gt
    | LitAlt l1, LitAlt l2 => GHC.Base.compare l1 l2
    | LitAlt _, DEFAULT => Gt
    | con1, con2 =>
        Panic.warnPprTrace (true) (GHC.Base.hs_string__
                            "ghc/compiler/coreSyn/CoreSyn.hs") #1700 (GHC.Base.mappend (GHC.Base.mappend
                                                                                        (Datatypes.id
                                                                                         (GHC.Base.hs_string__
                                                                                          "Comparing incomparable AltCons"))
                                                                                        Panic.someSDoc) Panic.someSDoc)
        Lt
    end.

Definition cmpAlt {a} {b}
   : (AltCon * a * b)%type -> (AltCon * a * b)%type -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair (pair con1 _) _, pair (pair con2 _) _ => cmpAltCon con1 con2
    end.

Definition ltAlt {a} {b}
   : (AltCon * a * b)%type -> (AltCon * a * b)%type -> bool :=
  fun a1 a2 => (cmpAlt a1 a2) GHC.Base.== Lt.

Definition cleanUseDmd_maybe : Demand -> option UseDmd :=
  fun arg_0__ => match arg_0__ with | JD _ (Mk_Use _ u) => Some u | _ => None end.

Definition cleanEvalProdDmd : BasicTypes.Arity -> CleanDemand :=
  fun n => JD HeadStr (UProd (Coq.Lists.List.repeat useTop n)).

Definition cleanEvalDmd : CleanDemand :=
  JD HeadStr Used.

Definition classTvsFds : Class -> (list TyVar * list (FunDep TyVar))%type :=
  fun c => pair (classTyVars c) (classFunDeps c).

Definition classSCTheta : Class -> list unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass theta_stuff _ _ _ _) => theta_stuff
    | _ => nil
    end.

Definition classOpItems : Class -> list ClassOpItem :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass _ _ _ op_stuff _) => op_stuff
    | _ => nil
    end.

Definition classMinimalDef : Class -> ClassMinimalDef :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass _ _ _ _ d) => d
    | _ => BooleanFormula.mkTrue
    end.

Definition classMethods : Class -> list Id :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass _ _ _ op_stuff _) =>
        let cont_1__ arg_2__ := let 'pair op_sel _ := arg_2__ in cons op_sel nil in
        Coq.Lists.List.flat_map cont_1__ op_stuff
    | _ => nil
    end.

Definition classHasFds : Class -> bool :=
  fun '(Mk_Class _ _ _ _ fds _) => negb (Data.Foldable.null fds).

Definition classExtraBigSig
   : Class ->
     (list TyVar * list (FunDep TyVar) * list unit * list Id * list ClassATItem *
      list ClassOpItem)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ tyvars fundeps AbstractClass =>
        pair (pair (pair (pair (pair tyvars fundeps) nil) nil) nil) nil
    | Mk_Class _ _ _ tyvars fundeps (ConcreteClass sc_theta sc_sels ats op_stuff
     _) =>
        pair (pair (pair (pair (pair tyvars fundeps) sc_theta) sc_sels) ats) op_stuff
    end.

Definition classBigSig
   : Class -> (list TyVar * list unit * list Id * list ClassOpItem)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ tyvars _ AbstractClass => pair (pair (pair tyvars nil) nil) nil
    | Mk_Class _ _ _ tyvars _ (ConcreteClass sc_theta sc_sels _ op_stuff _) =>
        pair (pair (pair tyvars sc_theta) sc_sels) op_stuff
    end.

Definition classArity : Class -> BasicTypes.Arity :=
  fun clas => Coq.Lists.List.length (classTyVars clas).

Definition classAllSelIds : Class -> list Id :=
  fun arg_0__ =>
    match arg_0__ with
    | (Mk_Class _ _ _ _ _ (ConcreteClass _ sc_sels _ _ _) as c) =>
        Coq.Init.Datatypes.app sc_sels (classMethods c)
    | c =>
        if andb Util.debugIsOn (negb (Data.Foldable.null (classMethods c))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Class.hs")
              #244)
        else nil
    end.

Definition classATs : Class -> list TyCon :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass _ _ at_stuff _ _) =>
        let cont_1__ arg_2__ := let 'ATI tc _ := arg_2__ in cons tc nil in
        Coq.Lists.List.flat_map cont_1__ at_stuff
    | _ => nil
    end.

Definition classATItems : Class -> list ClassATItem :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_Class _ _ _ _ _ (ConcreteClass _ _ at_stuff _ _) => at_stuff
    | _ => nil
    end.

Definition chooseOrphanAnchor (local_names : list Name.Name) : IsOrphan :=
  match GHC.Base.map Name.nameOccName local_names with
  | cons hd tl => NotOrphan (Data.Foldable.foldr GHC.Base.min hd tl)
  | nil => Mk_IsOrphan
  end.

Definition checkRecTc : RecTcChecker -> TyCon -> option RecTcChecker :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | RC bound rec_nts, tc =>
        let tc_name := tyConName tc in
        match NameEnv.lookupNameEnv rec_nts tc_name with
        | Some n =>
            if n GHC.Base.>= bound : bool then None else
            Some (RC bound (NameEnv.extendNameEnv rec_nts tc_name (n GHC.Num.+ #1)))
        | None => Some (RC bound (NameEnv.extendNameEnv rec_nts tc_name #1))
        end
    end.

Definition catchArgDmd : Demand :=
  JD (Mk_Str Mk_ExnStr (SCall HeadStr)) (Mk_Use One (UCall One Used)).

Definition canUnfold : Unfolding -> bool :=
  fun x => false.

Axiom bothUse : UseDmd -> UseDmd -> UseDmd.

Definition bothExnStr : ExnStr -> ExnStr -> ExnStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_ExnStr, Mk_ExnStr => Mk_ExnStr
    | _, _ => VanStr
    end.

Definition bothStr : StrDmd -> StrDmd -> StrDmd :=
  fix bothStr (arg_0__ arg_1__ : StrDmd) : StrDmd
        := let bothArgStr (arg_0__ arg_1__ : ArgStr) : ArgStr :=
             match arg_0__, arg_1__ with
             | Lazy, s => s
             | s, Lazy => s
             | Mk_Str x1 s1, Mk_Str x2 s2 => Mk_Str (bothExnStr x1 x2) (bothStr s1 s2)
             end in
           match arg_0__, arg_1__ with
           | HyperStr, _ => HyperStr
           | HeadStr, s => s
           | SCall _, HyperStr => HyperStr
           | SCall s1, HeadStr => SCall s1
           | SCall s1, SCall s2 => SCall (bothStr s1 s2)
           | SCall _, SProd _ => HyperStr
           | SProd _, HyperStr => HyperStr
           | SProd s1, HeadStr => SProd s1
           | SProd s1, SProd s2 =>
               if Util.equalLength s1 s2 : bool
               then mkSProd (GHC.List.zipWith bothArgStr s1 s2) else
               HyperStr
           | SProd _, SCall _ => HyperStr
           end.

Definition bothDmdResult : DmdResult -> Termination unit -> DmdResult :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Diverges => Diverges
    | r, ThrowsExn => match r with | Diverges => r | _ => ThrowsExn end
    | r, Dunno _ => r
    end.

Definition bothCleanDmd : CleanDemand -> CleanDemand -> CleanDemand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD s1 a1, JD s2 a2 => JD (bothStr s1 s2) (bothUse a1 a2)
    end.

Axiom bothArgUse : ArgUse -> ArgUse -> ArgUse.

Definition bothArgStr : ArgStr -> ArgStr -> ArgStr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Lazy, s => s
    | s, Lazy => s
    | Mk_Str x1 s1, Mk_Str x2 s2 => Mk_Str (bothExnStr x1 x2) (bothStr s1 s2)
    end.

Definition bothDmd : Demand -> Demand -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD s1 a1, JD s2 a2 => JD (bothArgStr s1 s2) (bothArgUse a1 a2)
    end.

Definition botRes : DmdResult :=
  Diverges.

Definition botDmdType : DmdType :=
  Mk_DmdType emptyDmdEnv nil botRes.

Definition botSig : StrictSig :=
  Mk_StrictSig botDmdType.

Definition ensureArgs : BasicTypes.Arity -> DmdType -> DmdType :=
  fun n d =>
    let 'Mk_DmdType fv ds r := d in
    let ds' :=
      Coq.Lists.List.firstn n (app ds (Coq.Lists.List.repeat (resTypeArgDmd r) n)) in
    let r' := match r with | Dunno _ => topRes | _ => r end in
    let depth := dmdTypeDepth d in
    if n GHC.Base.== depth : bool then d else
    Mk_DmdType fv ds' r'.

Definition removeDmdTyArgs : DmdType -> DmdType :=
  ensureArgs #0.

Definition splitDmdTy : DmdType -> (Demand * DmdType)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_DmdType fv (cons dmd dmds) res_ty => pair dmd (Mk_DmdType fv dmds res_ty)
    | (Mk_DmdType _ nil res_ty as ty) => pair (resTypeArgDmd res_ty) ty
    end.

Definition boringCxtOk : bool :=
  true.

Definition boringCxtNotOk : bool :=
  false.

Axiom bootUnfolding : Unfolding.

Definition bindersOf {b} : Bind b -> list b :=
  fun arg_0__ =>
    match arg_0__ with
    | NonRec binder _ => cons binder nil
    | Rec pairs =>
        let cont_2__ arg_3__ := let 'pair binder _ := arg_3__ in cons binder nil in
        Coq.Lists.List.flat_map cont_2__ pairs
    end.

Definition bindersOfBinds {b} : list (Bind b) -> list b :=
  fun binds =>
    Data.Foldable.foldr (Coq.Init.Datatypes.app GHC.Base.∘ bindersOf) nil binds.

Definition binderVar {tv} {argf} : TyVarBndr tv argf -> tv :=
  fun '(TvBndr v _) => v.

Definition binderVars {tv} {argf} : list (TyVarBndr tv argf) -> list tv :=
  fun tvbs => GHC.Base.map binderVar tvbs.

Definition dataConUserTyVars : DataCon -> list TyVar :=
  fun '(MkData _ _ _ _ _ _ tvbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => binderVars tvbs.

Definition dataConUserTyVarsArePermuted : DataCon -> bool :=
  fun '(MkData _ _ _ _ univ_tvs ex_tvs user_tvbs eq_spec _ _ _ _ _ _ _ _ _ _ _ _ _
  _) =>
    (Coq.Init.Datatypes.app (filterEqSpec eq_spec univ_tvs) ex_tvs) GHC.Base./=
    binderVars user_tvbs.

Definition mkAlgTyCon
   : Name.Name ->
     list TyConBinder ->
     unit ->
     list unit ->
     option unit -> list unit -> AlgTyConRhs -> AlgTyConFlav -> bool -> TyCon :=
  fun name binders res_kind roles cType stupid rhs parent gadt_syn =>
    AlgTyCon (Name.nameUnique name) name binders (binderVars binders) res_kind tt
             (Coq.Lists.List.length binders) roles cType gadt_syn stupid rhs
             (fieldsOfAlgTcRhs rhs) (if andb Util.debugIsOn (negb (okParent name
                                                                   parent)) : bool
              then (GHC.Err.error Panic.someSDoc)
              else parent).

Definition mkClassTyCon
   : Name.Name ->
     list TyConBinder -> list unit -> AlgTyConRhs -> Class -> Name.Name -> TyCon :=
  fun name binders roles rhs clas tc_rep_name =>
    mkAlgTyCon name binders tt roles None nil rhs (ClassTyCon clas tc_rep_name)
    false.

Definition mkFamilyTyCon
   : Name.Name ->
     list TyConBinder ->
     unit ->
     option Name.Name -> FamTyConFlav -> option Class -> Injectivity -> TyCon :=
  fun name binders res_kind resVar flav parent inj =>
    FamilyTyCon (Name.nameUnique name) name binders (binderVars binders) res_kind tt
                (Coq.Lists.List.length binders) resVar flav parent inj.

Definition mkSynonymTyCon
   : Name.Name ->
     list TyConBinder -> unit -> list unit -> unit -> bool -> bool -> TyCon :=
  fun name binders res_kind roles rhs is_tau is_fam_free =>
    SynonymTyCon (Name.nameUnique name) name binders (binderVars binders) res_kind
                 tt (Coq.Lists.List.length binders) roles rhs is_tau is_fam_free.

Definition mkTcTyCon
   : Name.Name ->
     list TyConBinder ->
     unit -> list (Name.Name * TyVar)%type -> TyConFlavour -> TyCon :=
  fun name binders res_kind scoped_tvs flav =>
    TcTyCon (Unique.getUnique name) name binders (binderVars binders) res_kind tt
            (Coq.Lists.List.length binders) scoped_tvs flav.

Definition makeRecoveryTyCon : TyCon -> TyCon :=
  fun tc =>
    mkTcTyCon (tyConName tc) (tyConBinders tc) (tyConResKind tc) nil (tyConFlavour
                                                                      tc).

Definition mkTupleTyCon
   : Name.Name ->
     list TyConBinder ->
     unit ->
     BasicTypes.Arity -> DataCon -> BasicTypes.TupleSort -> AlgTyConFlav -> TyCon :=
  fun name binders res_kind arity con sort parent =>
    AlgTyCon (Name.nameUnique name) name binders (binderVars binders) res_kind tt
             arity (Coq.Lists.List.repeat tt arity) None false nil (TupleTyCon con sort)
             FastStringEnv.emptyDFsEnv parent.

Definition patSynExTyVars : PatSyn -> list TyVar :=
  fun ps => binderVars (psExTyVars ps).

Definition patSynSig
   : PatSyn -> (list TyVar * unit * list TyVar * unit * list unit * unit)%type :=
  fun '(MkPatSyn _ _ arg_tys _ _ _ univ_tvs req ex_tvs prov res_ty _ _) =>
    pair (pair (pair (pair (pair (binderVars univ_tvs) req) (binderVars ex_tvs))
                     prov) arg_tys) res_ty.

Definition binderKind {argf} : TyVarBndr TyVar argf -> unit :=
  fun '(TvBndr tv _) => tyVarKind tv.

Definition binderArgFlag {tv} {argf} : TyVarBndr tv argf -> argf :=
  fun '(TvBndr _ argf) => argf.

Definition argOneShots : Demand -> list BasicTypes.OneShotInfo :=
  fun '(JD _ usg) =>
    let fix go arg_1__
              := match arg_1__ with
                 | UCall One u => cons BasicTypes.OneShotLam (go u)
                 | UCall Many u => cons BasicTypes.NoOneShotInfo (go u)
                 | _ => nil
                 end in
    match usg with
    | Mk_Use _ arg_usg => go arg_usg
    | _ => nil
    end.

Definition argsOneShots
   : StrictSig -> BasicTypes.Arity -> list (list BasicTypes.OneShotInfo) :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_StrictSig (Mk_DmdType _ arg_ds _), n_val_args =>
        let cons_ :=
          fun arg_2__ arg_3__ =>
            match arg_2__, arg_3__ with
            | nil, nil => nil
            | a, as_ => cons a as_
            end in
        let fix go arg_6__
                  := match arg_6__ with
                     | nil => nil
                     | cons arg_d arg_ds => cons_ (argOneShots arg_d) (go arg_ds)
                     end in
        let unsaturated_call := Util.lengthExceeds arg_ds n_val_args in
        if unsaturated_call : bool then nil else
        go arg_ds
    end.

Definition appIsBottom : StrictSig -> nat -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_StrictSig (Mk_DmdType _ ds res), n =>
        if isBotRes res : bool then negb (Util.lengthExceeds ds n) else
        false
    end.

Definition anyVarSet : (Var -> bool) -> VarSet -> bool :=
  UniqSet.uniqSetAny.

Definition anyDVarSet : (Var -> bool) -> DVarSet -> bool :=
  UniqDFM.anyUDFM.

Definition anyDVarEnv {a} : (a -> bool) -> DVarEnv a -> bool :=
  UniqDFM.anyUDFM.

Definition allVarSet : (Var -> bool) -> VarSet -> bool :=
  UniqSet.uniqSetAll.

Definition allDVarSet : (Var -> bool) -> DVarSet -> bool :=
  UniqDFM.allUDFM.

Definition algTyConRhs : TyCon -> AlgTyConRhs :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ => rhs
    | other => Panic.panicStr (GHC.Base.hs_string__ "algTyConRhs") (Panic.someSDoc)
    end.

Definition addRnInScopeSet : RnEnv2 -> VarSet -> RnEnv2 :=
  fun env vs =>
    if isEmptyVarSet vs : bool then env else
    let 'RV2 envL_0__ envR_1__ in_scope_2__ := env in
    RV2 envL_0__ envR_1__ (extendInScopeSetSet (in_scope env) vs).

Definition addDemand : Demand -> DmdType -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | dmd, Mk_DmdType fv ds res => Mk_DmdType fv (cons dmd ds) res
    end.

Definition absDmd : Demand :=
  JD Lazy Abs.

Definition defaultDmd {r} : Termination r -> Demand :=
  fun arg_0__ => match arg_0__ with | Dunno _ => absDmd | _ => botDmd end.

Definition bothDmdType : DmdType -> BothDmdArg -> DmdType :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_DmdType fv1 ds1 r1, pair fv2 t2 =>
        Mk_DmdType (plusVarEnv_CD bothDmd fv1 (defaultDmd r1) fv2 (defaultDmd t2)) ds1
        (bothDmdResult r1 t2)
    end.

Definition findIdDemand : DmdType -> Var -> Demand :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_DmdType fv _ res, id => Maybes.orElse (lookupVarEnv fv id) (defaultDmd res)
    end.

Definition lubDmdType : DmdType -> DmdType -> DmdType :=
  fun d1 d2 =>
    let n := GHC.Base.max (dmdTypeDepth d1) (dmdTypeDepth d2) in
    let 'Mk_DmdType fv1 ds1 r1 := ensureArgs n d1 in
    let 'Mk_DmdType fv2 ds2 r2 := ensureArgs n d2 in
    let lub_fv := plusVarEnv_CD lubDmd fv1 (defaultDmd r1) fv2 (defaultDmd r2) in
    let lub_ds :=
      Util.zipWithEqual (GHC.Base.hs_string__ "lubDmdType") lubDmd ds1 ds2 in
    let lub_res := lubDmdResult r1 r2 in Mk_DmdType lub_fv lub_ds lub_res.

Definition deferAfterIO : DmdType -> DmdType :=
  fun '((Mk_DmdType _ _ res as d)) =>
    let defer_res :=
      fun arg_1__ => match arg_1__ with | (Dunno _ as r) => r | _ => topRes end in
    let 'Mk_DmdType fv ds _ := lubDmdType d nopDmdType in
    Mk_DmdType fv ds (defer_res res).

Definition peelFV : DmdType -> Var -> (DmdType * Demand)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_DmdType fv ds res, id =>
        let dmd := Maybes.orElse (lookupVarEnv fv id) (defaultDmd res) in
        let fv' := delVarEnv fv id in pair (Mk_DmdType fv' ds res) dmd
    end.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__InScopeSet' *)

Local Definition Eq___ArgFlag_op_zeze__ : ArgFlag -> ArgFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Required, Required => true
    | Specified, Specified => true
    | Inferred, Inferred => true
    | _, _ => false
    end.

Local Definition Eq___ArgFlag_op_zsze__ : ArgFlag -> ArgFlag -> bool :=
  fun x y => negb (Eq___ArgFlag_op_zeze__ x y).

Program Instance Eq___ArgFlag : GHC.Base.Eq_ ArgFlag :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___ArgFlag_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___ArgFlag_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__ArgFlag' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__TyVarBndr' *)

Local Definition HasOccName__Var_occName : Var -> OccName.OccName :=
  Name.nameOccName GHC.Base.∘ varName.

Program Instance HasOccName__Var : OccName.HasOccName Var :=
  fun _ k__ => k__ {| OccName.occName__ := HasOccName__Var_occName |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Var' *)

Local Definition Ord__Var_op_zl__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.< realUnique b.

Local Definition Ord__Var_op_zlze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.<= realUnique b.

Local Definition Ord__Var_op_zg__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.> realUnique b.

Local Definition Ord__Var_op_zgze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.>= realUnique b.

Local Definition Ord__Var_compare : Var -> Var -> comparison :=
  fun a b => nonDetCmpVar a b.

Local Definition Ord__Var_max : Var -> Var -> Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then y else x.

Local Definition Ord__Var_min : Var -> Var -> Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then x else y.

Program Instance Ord__Var : GHC.Base.Ord Var :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Var_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Var_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Var_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Var_op_zgze__ ;
           GHC.Base.compare__ := Ord__Var_compare ;
           GHC.Base.max__ := Ord__Var_max ;
           GHC.Base.min__ := Ord__Var_min |}.

Local Definition NamedThing__Var_getName : Var -> Name.Name :=
  varName.

Local Definition NamedThing__Var_getOccName : Var -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__Var_getName n).

Program Instance NamedThing__Var : Name.NamedThing Var :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__Var_getName ;
           Name.getOccName__ := NamedThing__Var_getOccName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Var' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__ArgFlag' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__ArgFlag' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__TyVarBndr' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyVarBndr__ArgFlag__11' *)

Local Definition Eq___Injectivity_op_zeze__
   : Injectivity -> Injectivity -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NotInjective, NotInjective => true
    | Injective a1, Injective b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___Injectivity_op_zsze__
   : Injectivity -> Injectivity -> bool :=
  fun x y => negb (Eq___Injectivity_op_zeze__ x y).

Program Instance Eq___Injectivity : GHC.Base.Eq_ Injectivity :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Injectivity_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Injectivity_op_zsze__ |}.

Local Definition Eq___PrimElemRep_op_zeze__
   : PrimElemRep -> PrimElemRep -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Int8ElemRep, Int8ElemRep => true
    | Int16ElemRep, Int16ElemRep => true
    | Int32ElemRep, Int32ElemRep => true
    | Int64ElemRep, Int64ElemRep => true
    | Word8ElemRep, Word8ElemRep => true
    | Word16ElemRep, Word16ElemRep => true
    | Word32ElemRep, Word32ElemRep => true
    | Word64ElemRep, Word64ElemRep => true
    | FloatElemRep, FloatElemRep => true
    | DoubleElemRep, DoubleElemRep => true
    | _, _ => false
    end.

Local Definition Eq___PrimElemRep_op_zsze__
   : PrimElemRep -> PrimElemRep -> bool :=
  fun x y => negb (Eq___PrimElemRep_op_zeze__ x y).

Program Instance Eq___PrimElemRep : GHC.Base.Eq_ PrimElemRep :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___PrimElemRep_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___PrimElemRep_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__PrimElemRep' *)

Local Definition Eq___PrimRep_op_zeze__ : PrimRep -> PrimRep -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | VoidRep, VoidRep => true
    | LiftedRep, LiftedRep => true
    | UnliftedRep, UnliftedRep => true
    | IntRep, IntRep => true
    | WordRep, WordRep => true
    | Int64Rep, Int64Rep => true
    | Word64Rep, Word64Rep => true
    | AddrRep, AddrRep => true
    | FloatRep, FloatRep => true
    | DoubleRep, DoubleRep => true
    | VecRep a1 a2, VecRep b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___PrimRep_op_zsze__ : PrimRep -> PrimRep -> bool :=
  fun x y => negb (Eq___PrimRep_op_zeze__ x y).

Program Instance Eq___PrimRep : GHC.Base.Eq_ PrimRep :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___PrimRep_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___PrimRep_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__PrimRep' *)

Local Definition Eq___TyConFlavour_op_zeze__
   : TyConFlavour -> TyConFlavour -> bool :=
  fun a b => false.

Local Definition Eq___TyConFlavour_op_zsze__
   : TyConFlavour -> TyConFlavour -> bool :=
  fun x y => negb (Eq___TyConFlavour_op_zeze__ x y).

Program Instance Eq___TyConFlavour : GHC.Base.Eq_ TyConFlavour :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TyConFlavour_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TyConFlavour_op_zsze__ |}.

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__TyConBndrVis' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyVarBndr__TyConBndrVis__11' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__Injectivity' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__FamTyConFlav' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__PrimElemRep' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__PrimRep' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyConFlavour' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__TyCon' *)

Local Definition NamedThing__TyCon_getName : TyCon -> Name.Name :=
  tyConName.

Local Definition NamedThing__TyCon_getOccName : TyCon -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__TyCon_getName n).

Program Instance NamedThing__TyCon : Name.NamedThing TyCon :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__TyCon_getName ;
           Name.getOccName__ := NamedThing__TyCon_getOccName |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TyCon' *)

Local Definition Uniquable__TyCon_getUnique : TyCon -> Unique.Unique :=
  fun tc => tyConUnique tc.

Program Instance Uniquable__TyCon : Unique.Uniquable TyCon :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__TyCon_getUnique |}.

Local Definition Eq___TyCon_op_zeze__ : TyCon -> TyCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

Local Definition Eq___TyCon_op_zsze__ : TyCon -> TyCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

Program Instance Eq___TyCon : GHC.Base.Eq_ TyCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TyCon_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TyCon_op_zsze__ |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__AlgTyConFlav' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__PatSyn' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `Core.OutputableBndr__PatSyn' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__PatSyn' *)

Local Definition NamedThing__PatSyn_getName : PatSyn -> Name.Name :=
  patSynName.

Local Definition NamedThing__PatSyn_getOccName : PatSyn -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__PatSyn_getName n).

Program Instance NamedThing__PatSyn : Name.NamedThing PatSyn :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__PatSyn_getName ;
           Name.getOccName__ := NamedThing__PatSyn_getOccName |}.

Local Definition Uniquable__PatSyn_getUnique : PatSyn -> Unique.Unique :=
  psUnique.

Program Instance Uniquable__PatSyn : Unique.Uniquable PatSyn :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__PatSyn_getUnique |}.

Local Definition Eq___PatSyn_op_zeze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base.==_ Unique.getUnique.

Local Definition Eq___PatSyn_op_zsze__ : PatSyn -> PatSyn -> bool :=
  Data.Function.on _GHC.Base./=_ Unique.getUnique.

Program Instance Eq___PatSyn : GHC.Base.Eq_ PatSyn :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___PatSyn_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___PatSyn_op_zsze__ |}.

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
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___RecSelParent_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___RecSelParent_op_zsze__ |}.

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
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___CafInfo_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___CafInfo_op_zsze__ |}.

Local Definition Ord__CafInfo_op_zl__ : CafInfo -> CafInfo -> bool :=
  fun a b =>
    match a with
    | MayHaveCafRefs => match b with | MayHaveCafRefs => false | _ => true end
    | NoCafRefs => match b with | NoCafRefs => false | _ => false end
    end.

Local Definition Ord__CafInfo_op_zlze__ : CafInfo -> CafInfo -> bool :=
  fun a b => negb (Ord__CafInfo_op_zl__ b a).

Local Definition Ord__CafInfo_op_zg__ : CafInfo -> CafInfo -> bool :=
  fun a b => Ord__CafInfo_op_zl__ b a.

Local Definition Ord__CafInfo_op_zgze__ : CafInfo -> CafInfo -> bool :=
  fun a b => negb (Ord__CafInfo_op_zl__ a b).

Local Definition Ord__CafInfo_compare : CafInfo -> CafInfo -> comparison :=
  fun a b =>
    match a with
    | MayHaveCafRefs => match b with | MayHaveCafRefs => Eq | _ => Lt end
    | NoCafRefs => match b with | NoCafRefs => Eq | _ => Gt end
    end.

Local Definition Ord__CafInfo_max : CafInfo -> CafInfo -> CafInfo :=
  fun x y => if Ord__CafInfo_op_zlze__ x y : bool then y else x.

Local Definition Ord__CafInfo_min : CafInfo -> CafInfo -> CafInfo :=
  fun x y => if Ord__CafInfo_op_zlze__ x y : bool then x else y.

Program Instance Ord__CafInfo : GHC.Base.Ord CafInfo :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__CafInfo_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__CafInfo_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__CafInfo_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__CafInfo_op_zgze__ ;
           GHC.Base.compare__ := Ord__CafInfo_compare ;
           GHC.Base.max__ := Ord__CafInfo_max ;
           GHC.Base.min__ := Ord__CafInfo_min |}.

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
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___LevityInfo_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___LevityInfo_op_zsze__ |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__RecSelParent' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__CafInfo' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TickBoxOp' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__IdDetails' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__LevityInfo' *)

Local Definition Eq___JointDmd_op_zeze__ {inst_s} {inst_u} `{GHC.Base.Eq_
  inst_s} `{GHC.Base.Eq_ inst_u}
   : JointDmd inst_s inst_u -> JointDmd inst_s inst_u -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | JD a1 a2, JD b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    end.

Local Definition Eq___JointDmd_op_zsze__ {inst_s} {inst_u} `{GHC.Base.Eq_
  inst_s} `{GHC.Base.Eq_ inst_u}
   : JointDmd inst_s inst_u -> JointDmd inst_s inst_u -> bool :=
  fun x y => negb (Eq___JointDmd_op_zeze__ x y).

Program Instance Eq___JointDmd {s} {u} `{GHC.Base.Eq_ s} `{GHC.Base.Eq_ u}
   : GHC.Base.Eq_ (JointDmd s u) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___JointDmd_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___JointDmd_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__JointDmd' *)

Local Definition Eq___ExnStr_op_zeze__ : ExnStr -> ExnStr -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | VanStr, VanStr => true
    | Mk_ExnStr, Mk_ExnStr => true
    | _, _ => false
    end.

Local Definition Eq___ExnStr_op_zsze__ : ExnStr -> ExnStr -> bool :=
  fun x y => negb (Eq___ExnStr_op_zeze__ x y).

Program Instance Eq___ExnStr : GHC.Base.Eq_ ExnStr :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___ExnStr_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___ExnStr_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__ExnStr' *)

Local Definition Eq___Str_op_zeze__ {inst_s} `{GHC.Base.Eq_ inst_s}
   : Str inst_s -> Str inst_s -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Lazy, Lazy => true
    | Mk_Str a1 a2, Mk_Str b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___Str_op_zsze__ {inst_s} `{GHC.Base.Eq_ inst_s}
   : Str inst_s -> Str inst_s -> bool :=
  fun x y => negb (Eq___Str_op_zeze__ x y).

Program Instance Eq___Str {s} `{GHC.Base.Eq_ s} : GHC.Base.Eq_ (Str s) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Str_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Str_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__Str' *)

Local Definition Eq___StrDmd_op_zeze__ : StrDmd -> StrDmd -> bool :=
  fix StrDmd_eq x y
        := let eq' : GHC.Base.Eq_ StrDmd := GHC.Base.eq_default StrDmd_eq in
           match x, y with
           | HyperStr, HyperStr => true
           | SCall a1, SCall b1 => a1 GHC.Base.== b1
           | SProd a1, SProd b1 => a1 GHC.Base.== b1
           | HeadStr, HeadStr => true
           | _, _ => false
           end.

Local Definition Eq___StrDmd_op_zsze__ : StrDmd -> StrDmd -> bool :=
  fun x y => negb (Eq___StrDmd_op_zeze__ x y).

Program Instance Eq___StrDmd : GHC.Base.Eq_ StrDmd :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___StrDmd_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___StrDmd_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__StrDmd' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__Count' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__Use' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__UseDmd' *)

Local Definition Eq___Termination_op_zeze__ {inst_r} `{GHC.Base.Eq_ inst_r}
   : Termination inst_r -> Termination inst_r -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Diverges, Diverges => true
    | ThrowsExn, ThrowsExn => true
    | Dunno a1, Dunno b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___Termination_op_zsze__ {inst_r} `{GHC.Base.Eq_ inst_r}
   : Termination inst_r -> Termination inst_r -> bool :=
  fun x y => negb (Eq___Termination_op_zeze__ x y).

Program Instance Eq___Termination {r} `{GHC.Base.Eq_ r}
   : GHC.Base.Eq_ (Termination r) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Termination_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Termination_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__Termination' *)

Local Definition Eq___CPRResult_op_zeze__ : CPRResult -> CPRResult -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoCPR, NoCPR => true
    | RetProd, RetProd => true
    | RetSum a1, RetSum b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___CPRResult_op_zsze__ : CPRResult -> CPRResult -> bool :=
  fun x y => negb (Eq___CPRResult_op_zeze__ x y).

Program Instance Eq___CPRResult : GHC.Base.Eq_ CPRResult :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___CPRResult_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___CPRResult_op_zsze__ |}.

(* Skipping all instances of class `GHC.Show.Show', including
   `Core.Show__CPRResult' *)

Local Definition Eq___DmdType_op_zeze__ : DmdType -> DmdType -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Mk_DmdType fv1 ds1 res1, Mk_DmdType fv2 ds2 res2 =>
        andb (UniqFM.nonDetUFMToList fv1 GHC.Base.== UniqFM.nonDetUFMToList fv2) (andb
              (ds1 GHC.Base.== ds2) (res1 GHC.Base.== res2))
    end.

Local Definition Eq___DmdType_op_zsze__ : DmdType -> DmdType -> bool :=
  fun x y => negb (Eq___DmdType_op_zeze__ x y).

Program Instance Eq___DmdType : GHC.Base.Eq_ DmdType :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___DmdType_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___DmdType_op_zsze__ |}.

Local Definition Eq___StrictSig_op_zeze__ : StrictSig -> StrictSig -> bool :=
  GHC.Prim.coerce _GHC.Base.==_.

Local Definition Eq___StrictSig_op_zsze__ : StrictSig -> StrictSig -> bool :=
  GHC.Prim.coerce _GHC.Base./=_.

Program Instance Eq___StrictSig : GHC.Base.Eq_ StrictSig :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___StrictSig_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___StrictSig_op_zsze__ |}.

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__JointDmd' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__JointDmd' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__ExnStr' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__ArgStr' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__StrDmd' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__ArgStr' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__StrDmd' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__Count' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Count' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__UseDmd' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__ArgUse' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__UseDmd' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__ArgUse' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TypeShape' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Termination' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__CPRResult' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__CPRResult' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__DmdResult' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__DmdType' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__DmdType' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__StrictSig' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__StrictSig' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__HsImplBang' *)

Local Definition Eq___SrcStrictness_op_zeze__
   : SrcStrictness -> SrcStrictness -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | SrcLazy, SrcLazy => true
    | SrcStrict, SrcStrict => true
    | NoSrcStrict, NoSrcStrict => true
    | _, _ => false
    end.

Local Definition Eq___SrcStrictness_op_zsze__
   : SrcStrictness -> SrcStrictness -> bool :=
  fun x y => negb (Eq___SrcStrictness_op_zeze__ x y).

Program Instance Eq___SrcStrictness : GHC.Base.Eq_ SrcStrictness :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___SrcStrictness_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___SrcStrictness_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__SrcStrictness' *)

Local Definition Eq___SrcUnpackedness_op_zeze__
   : SrcUnpackedness -> SrcUnpackedness -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | SrcUnpack, SrcUnpack => true
    | SrcNoUnpack, SrcNoUnpack => true
    | NoSrcUnpack, NoSrcUnpack => true
    | _, _ => false
    end.

Local Definition Eq___SrcUnpackedness_op_zsze__
   : SrcUnpackedness -> SrcUnpackedness -> bool :=
  fun x y => negb (Eq___SrcUnpackedness_op_zeze__ x y).

Program Instance Eq___SrcUnpackedness : GHC.Base.Eq_ SrcUnpackedness :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___SrcUnpackedness_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___SrcUnpackedness_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__SrcUnpackedness' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__HsSrcBang' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__HsImplBang' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__SrcStrictness' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__SrcStrictness' *)

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__SrcUnpackedness' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__SrcUnpackedness' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__HsSrcBang' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__StrictnessMark' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__EqSpec' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__DataCon' *)

(* Skipping all instances of class `Outputable.OutputableBndr', including
   `Core.OutputableBndr__DataCon' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__DataCon' *)

Local Definition NamedThing__DataCon_getName : DataCon -> Name.Name :=
  dcName.

Local Definition NamedThing__DataCon_getOccName : DataCon -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__DataCon_getName n).

Program Instance NamedThing__DataCon : Name.NamedThing DataCon :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__DataCon_getName ;
           Name.getOccName__ := NamedThing__DataCon_getOccName |}.

Local Definition Uniquable__DataCon_getUnique : DataCon -> Unique.Unique :=
  dcUnique.

Program Instance Uniquable__DataCon : Unique.Uniquable DataCon :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__DataCon_getUnique |}.

Local Definition Eq___DataCon_op_zsze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

Local Definition Eq___DataCon_op_zeze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

Program Instance Eq___DataCon : GHC.Base.Eq_ DataCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___DataCon_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___DataCon_op_zsze__ |}.

Local Definition Eq___AltCon_op_zeze__ : AltCon -> AltCon -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | DataAlt a1, DataAlt b1 => ((a1 GHC.Base.== b1))
    | LitAlt a1, LitAlt b1 => ((a1 GHC.Base.== b1))
    | DEFAULT, DEFAULT => true
    | _, _ => false
    end.

Local Definition Eq___AltCon_op_zsze__ : AltCon -> AltCon -> bool :=
  fun x y => negb (Eq___AltCon_op_zeze__ x y).

Program Instance Eq___AltCon : GHC.Base.Eq_ AltCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___AltCon_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___AltCon_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__AltCon' *)

Local Definition Eq___Tickish_op_zeze__ {inst_id} `{GHC.Base.Eq_ inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | ProfNote a1 a2 a3, ProfNote b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    | HpcTick a1 a2, HpcTick b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | Breakpoint a1 a2, Breakpoint b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | SourceNote a1 a2, SourceNote b1 b2 =>
        (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2)))
    | _, _ => false
    end.

Local Definition Eq___Tickish_op_zsze__ {inst_id} `{GHC.Base.Eq_ inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => negb (Eq___Tickish_op_zeze__ x y).

Program Instance Eq___Tickish {id} `{GHC.Base.Eq_ id}
   : GHC.Base.Eq_ (Tickish id) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Tickish_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Tickish_op_zsze__ |}.

Local Definition Ord__Tickish_compare {inst_id} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> comparison :=
  fun a b =>
    match a with
    | ProfNote a1 a2 a3 =>
        match b with
        | ProfNote b1 b2 b3 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => Lt
            | Eq =>
                match (GHC.Base.compare a2 b2) with
                | Lt => Lt
                | Eq => (GHC.Base.compare a3 b3)
                | Gt => Gt
                end
            | Gt => Gt
            end
        | _ => Lt
        end
    | HpcTick a1 a2 =>
        match b with
        | ProfNote _ _ _ => Gt
        | HpcTick b1 b2 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => Lt
            | Eq => (GHC.Base.compare a2 b2)
            | Gt => Gt
            end
        | _ => Lt
        end
    | Breakpoint a1 a2 =>
        match b with
        | SourceNote _ _ => Lt
        | Breakpoint b1 b2 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => Lt
            | Eq => (GHC.Base.compare a2 b2)
            | Gt => Gt
            end
        | _ => Gt
        end
    | SourceNote a1 a2 =>
        match b with
        | SourceNote b1 b2 =>
            match (GHC.Base.compare a1 b1) with
            | Lt => Lt
            | Eq => (GHC.Base.compare a2 b2)
            | Gt => Gt
            end
        | _ => Gt
        end
    end.

Local Definition Ord__Tickish_op_zl__ {inst_id} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => Ord__Tickish_compare x y GHC.Base.== Lt.

Local Definition Ord__Tickish_op_zlze__ {inst_id} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => Ord__Tickish_compare x y GHC.Base./= Gt.

Local Definition Ord__Tickish_op_zg__ {inst_id} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => Ord__Tickish_compare x y GHC.Base.== Gt.

Local Definition Ord__Tickish_op_zgze__ {inst_id} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => Ord__Tickish_compare x y GHC.Base./= Lt.

Local Definition Ord__Tickish_max {inst_id} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> Tickish inst_id :=
  fun x y => if Ord__Tickish_op_zlze__ x y : bool then y else x.

Local Definition Ord__Tickish_min {inst_id} `{GHC.Base.Ord inst_id}
   : Tickish inst_id -> Tickish inst_id -> Tickish inst_id :=
  fun x y => if Ord__Tickish_op_zlze__ x y : bool then x else y.

Program Instance Ord__Tickish {id} `{GHC.Base.Ord id}
   : GHC.Base.Ord (Tickish id) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Tickish_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Tickish_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Tickish_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Tickish_op_zgze__ ;
           GHC.Base.compare__ := Ord__Tickish_compare ;
           GHC.Base.max__ := Ord__Tickish_max ;
           GHC.Base.min__ := Ord__Tickish_min |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Tickish' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Expr' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Bind' *)

Local Definition Eq___TickishScoping_op_zeze__
   : TickishScoping -> TickishScoping -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NoScope, NoScope => true
    | SoftScope, SoftScope => true
    | CostCentreScope, CostCentreScope => true
    | _, _ => false
    end.

Local Definition Eq___TickishScoping_op_zsze__
   : TickishScoping -> TickishScoping -> bool :=
  fun x y => negb (Eq___TickishScoping_op_zeze__ x y).

Program Instance Eq___TickishScoping : GHC.Base.Eq_ TickishScoping :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TickishScoping_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TickishScoping_op_zsze__ |}.

Local Definition Eq___TickishPlacement_op_zeze__
   : TickishPlacement -> TickishPlacement -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | PlaceRuntime, PlaceRuntime => true
    | PlaceNonLam, PlaceNonLam => true
    | PlaceCostCentre, PlaceCostCentre => true
    | _, _ => false
    end.

Local Definition Eq___TickishPlacement_op_zsze__
   : TickishPlacement -> TickishPlacement -> bool :=
  fun x y => negb (Eq___TickishPlacement_op_zeze__ x y).

Program Instance Eq___TickishPlacement : GHC.Base.Eq_ TickishPlacement :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___TickishPlacement_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___TickishPlacement_op_zsze__ |}.

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__IsOrphan' *)

Local Definition Eq___UnfoldingGuidance_op_zeze__
   : UnfoldingGuidance -> UnfoldingGuidance -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | UnfWhen a1 a2 a3, UnfWhen b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    | UnfIfGoodArgs a1 a2 a3, UnfIfGoodArgs b1 b2 b3 =>
        (andb (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
    | UnfNever, UnfNever => true
    | _, _ => false
    end.

Local Definition Eq___UnfoldingGuidance_op_zsze__
   : UnfoldingGuidance -> UnfoldingGuidance -> bool :=
  fun x y => negb (Eq___UnfoldingGuidance_op_zeze__ x y).

Program Instance Eq___UnfoldingGuidance : GHC.Base.Eq_ UnfoldingGuidance :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___UnfoldingGuidance_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___UnfoldingGuidance_op_zsze__ |}.

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__AltCon' *)

Local Definition Ord__AltCon_compare : AltCon -> AltCon -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | DataAlt con1, DataAlt con2 =>
        if andb Util.debugIsOn (negb (dataConTyCon con1 GHC.Base.==
                                      dataConTyCon con2)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/coreSyn/CoreSyn.hs")
              #319)
        else GHC.Base.compare (dataConTag con1) (dataConTag con2)
    | DataAlt _, _ => Gt
    | _, DataAlt _ => Lt
    | LitAlt l1, LitAlt l2 => GHC.Base.compare l1 l2
    | LitAlt _, DEFAULT => Gt
    | DEFAULT, DEFAULT => Eq
    | DEFAULT, _ => Lt
    end.

Local Definition Ord__AltCon_op_zl__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base.== Lt.

Local Definition Ord__AltCon_op_zlze__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base./= Gt.

Local Definition Ord__AltCon_op_zg__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base.== Gt.

Local Definition Ord__AltCon_op_zgze__ : AltCon -> AltCon -> bool :=
  fun x y => Ord__AltCon_compare x y GHC.Base./= Lt.

Local Definition Ord__AltCon_max : AltCon -> AltCon -> AltCon :=
  fun x y => if Ord__AltCon_op_zlze__ x y : bool then y else x.

Local Definition Ord__AltCon_min : AltCon -> AltCon -> AltCon :=
  fun x y => if Ord__AltCon_op_zlze__ x y : bool then x else y.

Program Instance Ord__AltCon : GHC.Base.Ord AltCon :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__AltCon_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__AltCon_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__AltCon_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__AltCon_op_zgze__ ;
           GHC.Base.compare__ := Ord__AltCon_compare ;
           GHC.Base.max__ := Ord__AltCon_max ;
           GHC.Base.min__ := Ord__AltCon_min |}.

(* Skipping all instances of class `Binary.Binary', including
   `Core.Binary__IsOrphan' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__TaggedBndr' *)

(* Skipping all instances of class `Data.Data.Data', including
   `Core.Data__Class' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `Core.Outputable__Class' *)

Local Definition NamedThing__Class_getName : Class -> Name.Name :=
  fun clas => className clas.

Local Definition NamedThing__Class_getOccName : Class -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__Class_getName n).

Program Instance NamedThing__Class : Name.NamedThing Class :=
  fun _ k__ =>
    k__ {| Name.getName__ := NamedThing__Class_getName ;
           Name.getOccName__ := NamedThing__Class_getOccName |}.

Local Definition Uniquable__Class_getUnique : Class -> Unique.Unique :=
  fun c => classKey c.

Program Instance Uniquable__Class : Unique.Uniquable Class :=
  fun _ k__ => k__ {| Unique.getUnique__ := Uniquable__Class_getUnique |}.

Local Definition Eq___Class_op_zeze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.== classKey c2.

Local Definition Eq___Class_op_zsze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base./= classKey c2.

Program Instance Eq___Class : GHC.Base.Eq_ Class :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Class_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Class_op_zsze__ |}.

Axiom tidyTyCoVarBndr : TidyEnv -> TyCoVar -> TidyEnv * TyCoVar.

Axiom eqTypeX : RnEnv2 -> unit -> unit -> bool.

Axiom eqCoercionX : RnEnv2 -> unit -> unit -> bool.

Axiom splitPiTy_maybe : unit -> option (unit * unit).

Axiom isTypeLevPoly : unit -> bool.

Axiom isUnliftedType : unit -> bool.

Axiom isFunTy : unit -> bool.

Axiom isCoercionType : unit -> bool.

(* External variables:
     Bool.Sumbool.sumbool_of_bool Eq Gt Lt None Some Type andb app bool comparison
     cons false list nat negb nil op_zt__ option orb pair size_AnnExpr' snd true tt
     unit BasicTypes.Activation BasicTypes.AlwaysActive BasicTypes.Arity
     BasicTypes.Boxity BasicTypes.ConTag BasicTypes.ConTagZ BasicTypes.DefMethSpec
     BasicTypes.IAmALoopBreaker BasicTypes.IAmDead BasicTypes.InlinePragma
     BasicTypes.JoinArity BasicTypes.ManyOccs BasicTypes.NoOneShotInfo
     BasicTypes.NoTailCallInfo BasicTypes.OccInfo BasicTypes.OneOcc
     BasicTypes.OneShotInfo BasicTypes.OneShotLam BasicTypes.RuleName
     BasicTypes.SourceText BasicTypes.TupleSort BasicTypes.defaultInlinePragma
     BasicTypes.fIRST_TAG BasicTypes.isAlwaysTailCalled BasicTypes.isBoxed
     BasicTypes.noOccInfo BasicTypes.tupleSortBoxity BasicTypes.zapFragileOcc
     BinNat.N.of_nat BinNums.N BooleanFormula.BooleanFormula BooleanFormula.mkTrue
     Coq.Init.Datatypes.app Coq.Init.Peano.lt Coq.Lists.List.firstn
     Coq.Lists.List.flat_map Coq.Lists.List.length Coq.Lists.List.repeat
     Coq.Lists.List.skipn Data.Foldable.all Data.Foldable.any Data.Foldable.concatMap
     Data.Foldable.find Data.Foldable.foldl Data.Foldable.foldr Data.Foldable.null
     Data.Function.on Data.Maybe.isJust Data.Tuple.fst Datatypes.id DynFlags.DynFlags
     DynFlags.Opt_KillAbsence DynFlags.Opt_KillOneShot DynFlags.gopt
     FastStringEnv.dFsEnvElts FastStringEnv.emptyDFsEnv FastStringEnv.lookupDFsEnv
     FastStringEnv.mkDFsEnv FieldLabel.FieldLabel FieldLabel.FieldLabelEnv
     FieldLabel.FieldLabelString FieldLabel.flLabel GHC.Base.Eq_ GHC.Base.Monad
     GHC.Base.Ord GHC.Base.String GHC.Base.compare GHC.Base.compare__
     GHC.Base.eq_default GHC.Base.fmap GHC.Base.map GHC.Base.mappend GHC.Base.max
     GHC.Base.max__ GHC.Base.min GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg__ GHC.Base.op_zg____
     GHC.Base.op_zgze__ GHC.Base.op_zgze____ GHC.Base.op_zgzgze__ GHC.Base.op_zl__
     GHC.Base.op_zl____ GHC.Base.op_zlze__ GHC.Base.op_zlze____ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Base.return_ GHC.Char.Char GHC.DeferredFix.deferredFix1
     GHC.DeferredFix.deferredFix2 GHC.Err.Build_Default GHC.Err.Default
     GHC.Err.default GHC.Err.error GHC.List.filter GHC.List.reverse GHC.List.zip
     GHC.List.zipWith GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__
     GHC.Num.op_zt__ GHC.Prim.coerce GHC.Prim.seq GHC.Real.Rational GHC.Wf.wfFix1
     GHC.Wf.wfFix2 GHC.Wf.wfFix3 Literal.Literal Literal.mkMachChar
     Literal.mkMachDouble Literal.mkMachFloat Literal.mkMachString Maybes.orElse
     Module.Module Module.ModuleSet Module.emptyModuleSet Module.mkModuleSet
     Name.Name Name.NamedThing Name.getName__ Name.getOccName__ Name.isWiredInName
     Name.mkExternalName Name.nameModule Name.nameOccName Name.nameSrcSpan
     Name.nameUnique Name.setNameUnique NameEnv.NameEnv NameEnv.emptyNameEnv
     NameEnv.extendNameEnv NameEnv.lookupNameEnv OccName.HasOccName OccName.OccName
     OccName.TidyOccEnv OccName.emptyTidyOccEnv OccName.isTcOcc OccName.mkTyConRepOcc
     OccName.occName__ Panic.assertPanic Panic.panic Panic.panicStr Panic.someSDoc
     Panic.warnPprTrace PrelNames.gHC_PRIM PrelNames.gHC_TYPES SrcLoc.RealSrcSpan
     SrcLoc.SrcSpan UniqDFM.UniqDFM UniqDFM.addListToUDFM UniqDFM.addToUDFM
     UniqDFM.addToUDFM_C UniqDFM.allUDFM UniqDFM.alterUDFM UniqDFM.anyUDFM
     UniqDFM.delFromUDFM UniqDFM.delListFromUDFM UniqDFM.disjointUDFM
     UniqDFM.elemUDFM UniqDFM.eltsUDFM UniqDFM.emptyUDFM UniqDFM.filterUDFM
     UniqDFM.foldUDFM UniqDFM.isNullUDFM UniqDFM.listToUDFM UniqDFM.lookupUDFM
     UniqDFM.mapUDFM UniqDFM.minusUDFM UniqDFM.partitionUDFM UniqDFM.plusUDFM
     UniqDFM.plusUDFM_C UniqDFM.udfmToUfm UniqDFM.unitUDFM UniqDSet.UniqDSet
     UniqDSet.addListToUniqDSet UniqDSet.addOneToUniqDSet
     UniqDSet.delListFromUniqDSet UniqDSet.delOneFromUniqDSet
     UniqDSet.elementOfUniqDSet UniqDSet.emptyUniqDSet UniqDSet.filterUniqDSet
     UniqDSet.foldUniqDSet UniqDSet.intersectUniqDSets UniqDSet.isEmptyUniqDSet
     UniqDSet.minusUniqDSet UniqDSet.mkUniqDSet UniqDSet.partitionUniqDSet
     UniqDSet.sizeUniqDSet UniqDSet.unionManyUniqDSets UniqDSet.unionUniqDSets
     UniqDSet.uniqDSetIntersectUniqSet UniqDSet.uniqDSetMinusUniqSet
     UniqDSet.uniqDSetToList UniqDSet.unitUniqDSet UniqFM.UniqFM UniqFM.addListToUFM
     UniqFM.addToUFM UniqFM.addToUFM_Acc UniqFM.addToUFM_C UniqFM.addToUFM_Directly
     UniqFM.alterUFM UniqFM.delFromUFM UniqFM.delFromUFM_Directly
     UniqFM.delListFromUFM UniqFM.disjointUFM UniqFM.elemUFM UniqFM.elemUFM_Directly
     UniqFM.emptyUFM UniqFM.filterUFM UniqFM.filterUFM_Directly UniqFM.intersectUFM
     UniqFM.isNullUFM UniqFM.listToUFM UniqFM.listToUFM_Directly UniqFM.lookupUFM
     UniqFM.lookupUFM_Directly UniqFM.lookupWithDefaultUFM UniqFM.mapUFM
     UniqFM.minusUFM UniqFM.nonDetFoldUFM_Directly UniqFM.nonDetUFMToList
     UniqFM.partitionUFM UniqFM.plusMaybeUFM_C UniqFM.plusUFM UniqFM.plusUFMList
     UniqFM.plusUFM_C UniqFM.plusUFM_CD UniqFM.unitUFM UniqSet.UniqSet
     UniqSet.addListToUniqSet UniqSet.addOneToUniqSet UniqSet.delListFromUniqSet
     UniqSet.delOneFromUniqSet UniqSet.delOneFromUniqSet_Directly
     UniqSet.elemUniqSet_Directly UniqSet.elementOfUniqSet UniqSet.emptyUniqSet
     UniqSet.filterUniqSet UniqSet.getUniqSet UniqSet.intersectUniqSets
     UniqSet.isEmptyUniqSet UniqSet.lookupUniqSet UniqSet.lookupUniqSet_Directly
     UniqSet.minusUniqSet UniqSet.mkUniqSet UniqSet.sizeUniqSet
     UniqSet.unionManyUniqSets UniqSet.unionUniqSets UniqSet.uniqSetAll
     UniqSet.uniqSetAny UniqSet.unitUniqSet UniqSet.unsafeUFMToUniqSet
     Unique.Uniquable Unique.Unique Unique.dataConRepNameUnique Unique.deriveUnique
     Unique.getKey Unique.getUnique Unique.getUnique__ Unique.mkUniqueGrimily
     Unique.nonDetCmpUnique Unique.tyConRepNameUnique Util.HasDebugCallStack
     Util.count Util.debugIsOn Util.equalLength Util.foldl2 Util.lengthAtLeast
     Util.lengthAtMost Util.lengthExceeds Util.lengthIs Util.listLengthCmp
     Util.zipEqual Util.zipWithEqual
*)
