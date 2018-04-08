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
Require BooleanFormula.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Foldable.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Name.
Require Panic.
Require SrcLoc.
Require Unique.
Require Util.
Require Var.
Import GHC.Base.Notations.
Import GHC.List.Notations.
Import GHC.Num.Notations.
Require Data.Set.Internal.
Require Data.Traversable.
Require Data.Tuple.
Require FastString.
Require FieldLabel.
Require GHC.Real.
Require ListSetOps.
Require Module.
Require OccName.
Require PrelNames.
Require UniqSet.
Require Constants.
Require Data.Maybe.
Require DynFlags.
Require FastStringEnv.
Require GHC.Prim.
Require Maybes.
Require NameEnv.
Import GHC.Prim.Notations.
Import Util.Notations.

(* Converted type declarations: *)

Definition FunDep a :=
  (list a * list a)%type%type.

Definition DefMethInfo :=
  (option (Name.Name * BasicTypes.DefMethSpec unit)%type)%type.

Definition ClassOpItem :=
  (Var.Id * DefMethInfo)%type%type.

Definition ClassMinimalDef :=
  (BooleanFormula.BooleanFormula Name.Name)%type.

Inductive ClassATItem : Type
  := ATI : TyCon -> (option (unit * SrcLoc.SrcSpan)%type) -> ClassATItem.

Inductive ClassBody : Type
  := AbstractClass : ClassBody
  |  ConcreteClass
   : list unit ->
     list Var.Id ->
     list ClassATItem -> list ClassOpItem -> ClassMinimalDef -> ClassBody.

Inductive Class : Type
  := Class
   : TyCon ->
     Name.Name ->
     Unique.Unique ->
     list Var.TyVar -> list (FunDep Var.TyVar) -> ClassBody -> Class.

Instance Default__ClassBody : GHC.Err.Default ClassBody :=
  GHC.Err.Build_Default _ AbstractClass.

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

Definition classBody (arg_0__ : Class) :=
  let 'Class _ _ _ _ _ classBody := arg_0__ in
  classBody.

Definition classFunDeps (arg_0__ : Class) :=
  let 'Class _ _ _ _ classFunDeps _ := arg_0__ in
  classFunDeps.

Definition classKey (arg_0__ : Class) :=
  let 'Class _ _ classKey _ _ _ := arg_0__ in
  classKey.

Definition className (arg_0__ : Class) :=
  let 'Class _ className _ _ _ _ := arg_0__ in
  className.

Definition classTyCon (arg_0__ : Class) :=
  let 'Class classTyCon _ _ _ _ _ := arg_0__ in
  classTyCon.

Definition classTyVars (arg_0__ : Class) :=
  let 'Class _ _ _ classTyVars _ _ := arg_0__ in
  classTyVars.

Inductive StrictnessMark : Type
  := MarkedStrict : StrictnessMark
  |  NotMarkedStrict : StrictnessMark.

Inductive SrcUnpackedness : Type
  := SrcUnpack : SrcUnpackedness
  |  SrcNoUnpack : SrcUnpackedness
  |  NoSrcUnpack : SrcUnpackedness.

Inductive SrcStrictness : Type
  := SrcLazy : SrcStrictness
  |  SrcStrict : SrcStrictness
  |  NoSrcStrict : SrcStrictness.

Inductive HsSrcBang : Type
  := HsSrcBang
   : BasicTypes.SourceText -> SrcUnpackedness -> SrcStrictness -> HsSrcBang.

Inductive HsImplBang : Type
  := HsLazy : HsImplBang
  |  HsStrict : HsImplBang
  |  HsUnpack : (option unit) -> HsImplBang.

Inductive EqSpec : Type := EqSpec : Var.TyVar -> unit -> EqSpec.

Inductive DataConRep : Type
  := NoDataConRep : DataConRep
  |  DCR
   : Var.Id ->
     unit -> list unit -> list StrictnessMark -> list HsImplBang -> DataConRep.

Inductive DataCon : Type
  := MkData
   : Name.Name ->
     Unique.Unique ->
     BasicTypes.ConTag ->
     bool ->
     list Var.TyVar ->
     list Var.TyVar ->
     list Var.TyVarBinder ->
     list EqSpec ->
     unit ->
     unit ->
     list unit ->
     unit ->
     list HsSrcBang ->
     list FieldLabel.FieldLabel ->
     Var.Id ->
     DataConRep ->
     BasicTypes.Arity ->
     BasicTypes.Arity -> TyCon -> unit -> bool -> TyCon -> DataCon.

Instance Default__StrictnessMark : GHC.Err.Default StrictnessMark :=
  GHC.Err.Build_Default _ MarkedStrict.

Instance Default__SrcUnpackedness : GHC.Err.Default SrcUnpackedness :=
  GHC.Err.Build_Default _ SrcUnpack.

Instance Default__SrcStrictness : GHC.Err.Default SrcStrictness :=
  GHC.Err.Build_Default _ SrcLazy.

Instance Default__HsImplBang : GHC.Err.Default HsImplBang :=
  GHC.Err.Build_Default _ HsLazy.

Instance Default__DataConRep : GHC.Err.Default DataConRep :=
  GHC.Err.Build_Default _ NoDataConRep.

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

Definition dcr_wrap_id (arg_0__ : DataConRep) :=
  match arg_0__ with
  | NoDataConRep =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dcr_wrap_id' has no match in constructor `NoDataConRep' of type `DataConRep'")
  | DCR dcr_wrap_id _ _ _ _ => dcr_wrap_id
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

Definition TyConRepName :=
  Name.Name%type.

Inductive TyConFlavour : Type
  := ClassFlavour : TyConFlavour
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

Inductive TyConBndrVis : Type
  := NamedTCB : Var.ArgFlag -> TyConBndrVis
  |  AnonTCB : TyConBndrVis.

Definition TyConBinder :=
  (Var.TyVarBndr Var.TyVar TyConBndrVis)%type.

Inductive RecTcChecker : Type
  := RC : GHC.Num.Int -> (NameEnv.NameEnv GHC.Num.Int) -> RecTcChecker.

Inductive PrimElemRep : Type
  := Int8ElemRep : PrimElemRep
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
  := VoidRep : PrimRep
  |  LiftedRep : PrimRep
  |  UnliftedRep : PrimRep
  |  IntRep : PrimRep
  |  WordRep : PrimRep
  |  Int64Rep : PrimRep
  |  Word64Rep : PrimRep
  |  AddrRep : PrimRep
  |  FloatRep : PrimRep
  |  DoubleRep : PrimRep
  |  VecRep : GHC.Num.Int -> PrimElemRep -> PrimRep.

Inductive RuntimeRepInfo : Type
  := NoRRI : RuntimeRepInfo
  |  RuntimeRep : (list unit -> list PrimRep) -> RuntimeRepInfo
  |  VecCount : GHC.Num.Int -> RuntimeRepInfo
  |  VecElem : PrimElemRep -> RuntimeRepInfo.

Inductive Injectivity : Type
  := NotInjective : Injectivity
  |  Injective : list bool -> Injectivity.

Inductive FamTyConFlav : Type
  := DataFamilyTyCon : TyConRepName -> FamTyConFlav
  |  OpenSynFamilyTyCon : FamTyConFlav
  |  ClosedSynFamilyTyCon
   : (option (CoAxiom.CoAxiom CoAxiom.Branched)) -> FamTyConFlav
  |  AbstractClosedSynFamilyTyCon : FamTyConFlav
  |  BuiltInSynFamTyCon : CoAxiom.BuiltInSynFamily -> FamTyConFlav.

Inductive AlgTyConRhs : Type
  := AbstractTyCon : AlgTyConRhs
  |  DataTyCon : list DataCon -> bool -> AlgTyConRhs
  |  TupleTyCon : DataCon -> BasicTypes.TupleSort -> AlgTyConRhs
  |  SumTyCon : list DataCon -> AlgTyConRhs
  |  NewTyCon
   : DataCon ->
     unit ->
     (list Var.TyVar * unit)%type ->
     CoAxiom.CoAxiom CoAxiom.Unbranched -> AlgTyConRhs.

Inductive AlgTyConFlav : Type
  := VanillaAlgTyCon : TyConRepName -> AlgTyConFlav
  |  UnboxedAlgTyCon : (option TyConRepName) -> AlgTyConFlav
  |  ClassTyCon : Class -> TyConRepName -> AlgTyConFlav
  |  DataFamInstTyCon
   : (CoAxiom.CoAxiom CoAxiom.Unbranched) -> TyCon -> list unit -> AlgTyConFlav
with TyCon : Type
  := FunTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder -> unit -> unit -> BasicTypes.Arity -> TyConRepName -> TyCon
  |  AlgTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     list Var.TyVar ->
     unit ->
     unit ->
     BasicTypes.Arity ->
     list CoAxiom.Role ->
     option unit ->
     bool ->
     list unit -> AlgTyConRhs -> FieldLabel.FieldLabelEnv -> AlgTyConFlav -> TyCon
  |  SynonymTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     list Var.TyVar ->
     unit ->
     unit -> BasicTypes.Arity -> list CoAxiom.Role -> unit -> bool -> bool -> TyCon
  |  FamilyTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     list Var.TyVar ->
     unit ->
     unit ->
     BasicTypes.Arity ->
     option Name.Name -> FamTyConFlav -> option Class -> Injectivity -> TyCon
  |  PrimTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     unit ->
     unit ->
     BasicTypes.Arity -> list CoAxiom.Role -> bool -> option TyConRepName -> TyCon
  |  PromotedDataCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     unit ->
     unit ->
     BasicTypes.Arity ->
     list CoAxiom.Role -> DataCon -> TyConRepName -> RuntimeRepInfo -> TyCon
  |  TcTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     list Var.TyVar ->
     unit ->
     unit ->
     BasicTypes.Arity -> list (Name.Name * Var.TyVar)%type -> TyConFlavour -> TyCon.

Instance Default__TyConFlavour : GHC.Err.Default TyConFlavour :=
  GHC.Err.Build_Default _ ClassFlavour.

Instance Default__TyConBndrVis : GHC.Err.Default TyConBndrVis :=
  GHC.Err.Build_Default _ AnonTCB.

Instance Default__PrimElemRep : GHC.Err.Default PrimElemRep :=
  GHC.Err.Build_Default _ Int8ElemRep.

Instance Default__PrimRep : GHC.Err.Default PrimRep :=
  GHC.Err.Build_Default _ VoidRep.

Instance Default__RuntimeRepInfo : GHC.Err.Default RuntimeRepInfo :=
  GHC.Err.Build_Default _ NoRRI.

Instance Default__Injectivity : GHC.Err.Default Injectivity :=
  GHC.Err.Build_Default _ NotInjective.

Instance Default__FamTyConFlav : GHC.Err.Default FamTyConFlav :=
  GHC.Err.Build_Default _ OpenSynFamilyTyCon.

Instance Default__AlgTyConRhs : GHC.Err.Default AlgTyConRhs :=
  GHC.Err.Build_Default _ AbstractTyCon.

Definition data_con (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
  | AbstractTyCon =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_con' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
  | DataTyCon _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_con' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
  | TupleTyCon data_con _ => data_con
  | SumTyCon _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `data_con' has no match in constructor `SumTyCon' of type `AlgTyConRhs'")
  | NewTyCon data_con _ _ _ => data_con
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

Definition algTcParent (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcParent' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ algTcParent => algTcParent
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcParent' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcParent' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcParent' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcParent' has no match in constructor `PromotedDataCon' of type `TyCon'")
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `algTcParent' has no match in constructor `TcTyCon' of type `TyCon'")
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

Definition dataCon (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dataCon' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dataCon' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dataCon' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dataCon' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dataCon' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ dataCon _ _ => dataCon
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `dataCon' has no match in constructor `TcTyCon' of type `TyCon'")
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

Definition promDcRepInfo (arg_0__ : TyCon) :=
  match arg_0__ with
  | FunTyCon _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `promDcRepInfo' has no match in constructor `FunTyCon' of type `TyCon'")
  | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `promDcRepInfo' has no match in constructor `AlgTyCon' of type `TyCon'")
  | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `promDcRepInfo' has no match in constructor `SynonymTyCon' of type `TyCon'")
  | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `promDcRepInfo' has no match in constructor `FamilyTyCon' of type `TyCon'")
  | PrimTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `promDcRepInfo' has no match in constructor `PrimTyCon' of type `TyCon'")
  | PromotedDataCon _ _ _ _ _ _ _ _ _ promDcRepInfo => promDcRepInfo
  | TcTyCon _ _ _ _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `promDcRepInfo' has no match in constructor `TcTyCon' of type `TyCon'")
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
(* Midamble *)

(* --- TyCon ---- *)
Instance Default__AlgTyConFlav : Err.Default AlgTyConFlav :=
  Err.Build_Default _ (VanillaAlgTyCon Err.default).

Instance Default__RuntimRepInfo : Err.Default RuntimeRepInfo :=
  Err.Build_Default _ Mk_RuntimeRepInfo_Dummy.                                 

Instance Uniquable_Tycon : Unique.Uniquable TyCon. 
Admitted.

(* --- DataCon ---- *)

Import FieldLabel.

Require GHC.Err.
Instance Default__DataCon : GHC.Err.Default DataCon := {}.
Admitted.

Instance Uniqable_DataCon : Unique.Uniquable DataCon := {}.
Admitted.


(* Converted value declarations: *)

(* Translating `instance Outputable__AlgTyConFlav' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

Local Definition Eq___TyCon_op_zeze__ : TyCon -> TyCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

Local Definition Eq___TyCon_op_zsze__ : TyCon -> TyCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

Program Instance Eq___TyCon : GHC.Base.Eq_ TyCon :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TyCon_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TyCon_op_zsze__ |}.

(* Translating `instance Uniquable__TyCon' failed: OOPS! Cannot find information
   for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Outputable__TyCon' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance NamedThing__TyCon' failed: OOPS! Cannot find
   information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Data__TyCon' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Outputable__TyConFlavour' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__PrimRep' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__PrimElemRep' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__FamTyConFlav' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__Injectivity' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__TyVarBndr__TyConBndrVis__11' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Binary__TyConBndrVis' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

Local Definition Eq___TyConFlavour_op_zeze__
   : TyConFlavour -> TyConFlavour -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TupleFlavour a1, TupleFlavour b1 => ((a1 GHC.Base.== b1))
    | a, b =>
        let 'lop_azh__ := (_Deriving.$con2tag_GDTzQOFa1zUIKOcsSgCJHI_ a) in
        let 'lop_bzh__ := (_Deriving.$con2tag_GDTzQOFa1zUIKOcsSgCJHI_ b) in
        (_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.==# lop_bzh__))
    end.

Local Definition Eq___TyConFlavour_op_zsze__
   : TyConFlavour -> TyConFlavour -> bool :=
  fun x y => negb (Eq___TyConFlavour_op_zeze__ x y).

Program Instance Eq___TyConFlavour : GHC.Base.Eq_ TyConFlavour :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TyConFlavour_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TyConFlavour_op_zsze__ |}.

(* Translating `instance Show__PrimRep' failed: OOPS! Cannot find information
   for class Qualified "GHC.Show" "Show" unsupported *)

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
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___PrimRep_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___PrimRep_op_zsze__ |}.

(* Translating `instance Show__PrimElemRep' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

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
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___PrimElemRep_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___PrimElemRep_op_zsze__ |}.

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
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Injectivity_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Injectivity_op_zsze__ |}.

Local Definition Eq___DataCon_op_zeze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

Local Definition Eq___DataCon_op_zsze__ : DataCon -> DataCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

Program Instance Eq___DataCon : GHC.Base.Eq_ DataCon :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___DataCon_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___DataCon_op_zsze__ |}.

(* Translating `instance Uniquable__DataCon' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance NamedThing__DataCon' failed: OOPS! Cannot find
   information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Outputable__DataCon' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance OutputableBndr__DataCon' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "OutputableBndr" unsupported *)

(* Translating `instance Data__DataCon' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Outputable__EqSpec' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__StrictnessMark' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__HsSrcBang' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__SrcUnpackedness' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__SrcUnpackedness' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__SrcStrictness' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__SrcStrictness' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__HsImplBang' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Data__HsSrcBang' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__SrcUnpackedness' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

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
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___SrcUnpackedness_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___SrcUnpackedness_op_zsze__ |}.

(* Translating `instance Data__SrcStrictness' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

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
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___SrcStrictness_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___SrcStrictness_op_zsze__ |}.

(* Translating `instance Data__HsImplBang' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___Class_op_zeze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base.== classKey c2.

Local Definition Eq___Class_op_zsze__ : Class -> Class -> bool :=
  fun c1 c2 => classKey c1 GHC.Base./= classKey c2.

Program Instance Eq___Class : GHC.Base.Eq_ Class :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Class_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Class_op_zsze__ |}.

(* Translating `instance Uniquable__Class' failed: OOPS! Cannot find information
   for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance NamedThing__Class' failed: OOPS! Cannot find
   information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Outputable__Class' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Data__Class' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

Definition algTyConRhs : TyCon -> AlgTyConRhs :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ => rhs
    | other =>
        Panic.panicStr (GHC.Base.hs_string__ "algTyConRhs") (Panic.noString other)
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

Definition expandSynTyCon_maybe {tyco}
   : TyCon ->
     list tyco -> option (list (Var.TyVar * tyco)%type * unit * list tyco)%type :=
  fun tc tys =>
    match tc with
    | SynonymTyCon _ _ _ tvs _ _ arity _ rhs _ _ =>
        match Util.listLengthCmp tys arity with
        | Gt => Some (pair (pair (GHC.List.zip tvs tys) rhs) (GHC.List.drop arity tys))
        | Eq => Some (pair (pair (GHC.List.zip tvs tys) rhs) nil)
        | Lt => None
        end
    | _ => None
    end.

Definition famTyConFlav_maybe : TyCon -> option FamTyConFlav :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ flav _ _ => Some flav
    | _ => None
    end.

Definition initRecTc : RecTcChecker :=
  RC #100 NameEnv.emptyNameEnv.

Definition isAbstractTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ AbstractTyCon _ _ => true
    | _ => false
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

Definition isBuiltInSynFamTyCon_maybe
   : TyCon -> option CoAxiom.BuiltInSynFamily :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ (BuiltInSynFamTyCon ops) _ _ => Some ops
    | _ => None
    end.

Definition isClassTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (ClassTyCon _ _) => true
    | _ => false
    end.

Definition isClosedSynFamilyTyConWithAxiom_maybe
   : TyCon -> option (CoAxiom.CoAxiom CoAxiom.Branched) :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ (ClosedSynFamilyTyCon mb) _ _ => mb
    | _ => None
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

Definition isFamInstTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (DataFamInstTyCon _ _ _) => true
    | _ => false
    end.

Definition isFamilyTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isFunTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FunTyCon _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isGadtSyntaxTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ res _ _ _ _ => res
    | _ => false
    end.

Definition isGcPtrRep : PrimRep -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | LiftedRep => true
    | UnliftedRep => true
    | _ => false
    end.

Definition isGenInjAlgRhs : AlgTyConRhs -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | TupleTyCon _ _ => true
    | SumTyCon _ => true
    | DataTyCon _ _ => true
    | AbstractTyCon => false
    | NewTyCon _ _ _ _ => false
    end.

Definition isInjectiveTyCon : TyCon -> CoAxiom.Role -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, CoAxiom.Phantom => false
    | FunTyCon _ _ _ _ _ _ _, _ => true
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _, CoAxiom.Nominal => true
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _, CoAxiom.Representational =>
        isGenInjAlgRhs rhs
    | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _, _ => false
    | FamilyTyCon _ _ _ _ _ _ _ _ (DataFamilyTyCon _) _ _, CoAxiom.Nominal => true
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ (Injective inj), CoAxiom.Nominal =>
        Data.Foldable.and inj
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _, _ => false
    | PrimTyCon _ _ _ _ _ _ _ _ _, _ => true
    | PromotedDataCon _ _ _ _ _ _ _ _ _ _, _ => true
    | TcTyCon _ _ _ _ _ _ _ _ _, _ => true
    end.

Definition isGenerativeTyCon : TyCon -> CoAxiom.Role -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ (DataFamilyTyCon _) _ _, CoAxiom.Nominal => true
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _, _ => false
    | tc, r => isInjectiveTyCon tc r
    end.

Definition tyConInjectivityInfo : TyCon -> Injectivity :=
  fun tc =>
    match tc with
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ inj => inj
    | _ =>
        if isInjectiveTyCon tc CoAxiom.Nominal : bool
        then Injective (GHC.List.replicate (tyConArity tc) true) else
        NotInjective
    end.

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

Definition isLiftedTypeKindTyConName : Name.Name -> bool :=
  (fun arg_0__ => Unique.hasKey arg_0__ PrelNames.liftedTypeKindTyConKey)
  Util.<||>
  ((fun arg_1__ => Unique.hasKey arg_1__ PrelNames.starKindTyConKey) Util.<||>
   (fun arg_2__ => Unique.hasKey arg_2__ PrelNames.unicodeStarKindTyConKey)).

Definition isNamedTyConBinder : TyConBinder -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Var.TvBndr _ (NamedTCB _) => true
    | _ => false
    end.

Definition isNewTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ _ _) _ _ => true
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

Definition isOpenTypeFamilyTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ OpenSynFamilyTyCon _ _ => true
    | _ => false
    end.

Definition isPrimTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | PrimTyCon _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isPromotedDataCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | PromotedDataCon _ _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isPromotedDataCon_maybe : TyCon -> option DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | PromotedDataCon _ _ _ _ _ _ _ dc _ _ => Some dc
    | _ => None
    end.

Definition isTauTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | SynonymTyCon _ _ _ _ _ _ _ _ _ is_tau _ => is_tau
    | _ => true
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
        Panic.panicStr (GHC.Base.hs_string__ "isTcLevPoly datacon") (Panic.noString tc)
    end.

Definition isTcTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | TcTyCon _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isTupleTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (TupleTyCon _ _) _ _ => true
    | _ => false
    end.

Definition isTypeSynonymTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

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

Definition isVanillaAlgTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (VanillaAlgTyCon _) => true
    | _ => false
    end.

Definition isVisibleTcbVis : TyConBndrVis -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | NamedTCB vis => Var.isVisibleArgFlag vis
    | AnonTCB => true
    end.

Definition isVisibleTyConBinder {tv} : Var.TyVarBndr tv TyConBndrVis -> bool :=
  fun arg_0__ => let 'Var.TvBndr _ tcb_vis := arg_0__ in isVisibleTcbVis tcb_vis.

Definition isInvisibleTyConBinder {tv}
   : Var.TyVarBndr tv TyConBndrVis -> bool :=
  fun tcb => negb (isVisibleTyConBinder tcb).

Definition tyConVisibleTyVars : TyCon -> list Var.TyVar :=
  fun tc =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | Var.TvBndr tv vis => if isVisibleTcbVis vis : bool then cons tv nil else nil
      | _ => nil
      end in
    Coq.Lists.List.flat_map cont_0__ (tyConBinders tc).

Definition isVoidRep : PrimRep -> bool :=
  fun arg_0__ => match arg_0__ with | VoidRep => true | _other => false end.

Definition mkAnonTyConBinder : Var.TyVar -> TyConBinder :=
  fun tv => Var.TvBndr tv AnonTCB.

Definition mkAnonTyConBinders : list Var.TyVar -> list TyConBinder :=
  fun tvs => GHC.Base.map mkAnonTyConBinder tvs.

Definition mkNamedTyConBinder : Var.ArgFlag -> Var.TyVar -> TyConBinder :=
  fun vis tv => Var.TvBndr tv (NamedTCB vis).

Definition mkNamedTyConBinders
   : Var.ArgFlag -> list Var.TyVar -> list TyConBinder :=
  fun vis tvs => GHC.Base.map (mkNamedTyConBinder vis) tvs.

Definition mkTyConKind : list TyConBinder -> unit -> unit :=
  fun bndrs res_kind =>
    let mk : TyConBinder -> unit -> unit :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | Var.TvBndr tv AnonTCB, k => TysWiredIn.mkFunKind (Var.tyVarKind tv) k
        | Var.TvBndr tv (NamedTCB vis), k => TysWiredIn.mkForAllKind tv vis k
        end in
    Data.Foldable.foldr mk res_kind bndrs.

Definition mkTupleTyCon
   : Name.Name ->
     list TyConBinder ->
     unit ->
     BasicTypes.Arity -> DataCon -> BasicTypes.TupleSort -> AlgTyConFlav -> TyCon :=
  fun name binders res_kind arity con sort parent =>
    AlgTyCon (Name.nameUnique name) name binders (Var.binderVars binders) res_kind
             (mkTyConKind binders res_kind) arity (GHC.List.replicate arity
              CoAxiom.Representational) None false nil (TupleTyCon con sort)
             FastStringEnv.emptyDFsEnv parent.

Definition mkTcTyCon
   : Name.Name ->
     list TyConBinder ->
     unit -> list (Name.Name * Var.TyVar)%type -> TyConFlavour -> TyCon :=
  fun name binders res_kind scoped_tvs flav =>
    TcTyCon (Unique.getUnique name) name binders (Var.binderVars binders) res_kind
            (mkTyConKind binders res_kind) (Data.Foldable.length binders) scoped_tvs flav.

Definition mkSynonymTyCon
   : Name.Name ->
     list TyConBinder ->
     unit -> list CoAxiom.Role -> unit -> bool -> bool -> TyCon :=
  fun name binders res_kind roles rhs is_tau is_fam_free =>
    SynonymTyCon (Name.nameUnique name) name binders (Var.binderVars binders)
                 res_kind (mkTyConKind binders res_kind) (Data.Foldable.length binders) roles rhs
                 is_tau is_fam_free.

Definition mkSumTyCon
   : Name.Name ->
     list TyConBinder ->
     unit ->
     BasicTypes.Arity -> list Var.TyVar -> list DataCon -> AlgTyConFlav -> TyCon :=
  fun name binders res_kind arity tyvars cons_ parent =>
    AlgTyCon (Name.nameUnique name) name binders tyvars res_kind (mkTyConKind
              binders res_kind) arity (GHC.List.replicate arity CoAxiom.Representational) None
             false nil (SumTyCon cons_) FastStringEnv.emptyDFsEnv parent.

Definition mkPromotedDataCon
   : DataCon ->
     Name.Name ->
     TyConRepName ->
     list TyConBinder -> unit -> list CoAxiom.Role -> RuntimeRepInfo -> TyCon :=
  fun con name rep_name binders res_kind roles rep_info =>
    PromotedDataCon (Name.nameUnique name) name binders res_kind (mkTyConKind
                     binders res_kind) (Data.Foldable.length roles) roles con rep_name rep_info.

Definition mkPrimTyCon'
   : Name.Name ->
     list TyConBinder ->
     unit -> list CoAxiom.Role -> bool -> option TyConRepName -> TyCon :=
  fun name binders res_kind roles is_unlifted rep_nm =>
    PrimTyCon (Name.nameUnique name) name binders res_kind (mkTyConKind binders
               res_kind) (Data.Foldable.length roles) roles is_unlifted rep_nm.

Definition mkKindTyCon
   : Name.Name ->
     list TyConBinder -> unit -> list CoAxiom.Role -> Name.Name -> TyCon :=
  fun name binders res_kind roles rep_nm =>
    let tc := mkPrimTyCon' name binders res_kind roles false (Some rep_nm) in tc.

Definition mkFunTyCon : Name.Name -> list TyConBinder -> Name.Name -> TyCon :=
  fun name binders rep_nm =>
    FunTyCon (Name.nameUnique name) name binders TysWiredIn.liftedTypeKind
             (mkTyConKind binders TysWiredIn.liftedTypeKind) (Data.Foldable.length binders)
             rep_nm.

Definition mkFamilyTyCon
   : Name.Name ->
     list TyConBinder ->
     unit ->
     option Name.Name -> FamTyConFlav -> option Class -> Injectivity -> TyCon :=
  fun name binders res_kind resVar flav parent inj =>
    FamilyTyCon (Name.nameUnique name) name binders (Var.binderVars binders)
                res_kind (mkTyConKind binders res_kind) (Data.Foldable.length binders) resVar
                flav parent inj.

Definition newTyConCo_maybe
   : TyCon -> option (CoAxiom.CoAxiom CoAxiom.Unbranched) :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ _ co) _ _ => Some co
    | _ => None
    end.

Definition newTyConCo : TyCon -> CoAxiom.CoAxiom CoAxiom.Unbranched :=
  fun tc =>
    match newTyConCo_maybe tc with
    | Some co => co
    | None => Panic.panicStr (GHC.Base.hs_string__ "newTyConCo") (Panic.noString tc)
    end.

Definition newTyConDataCon_maybe : TyCon -> option DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon con _ _ _) _ _ => Some con
    | _ => None
    end.

Definition newTyConEtadArity : TyCon -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ tvs_rhs _) _ _ =>
        Data.Foldable.length (Data.Tuple.fst tvs_rhs)
    | tycon =>
        Panic.panicStr (GHC.Base.hs_string__ "newTyConEtadArity") (Panic.noString tycon)
    end.

Definition newTyConEtadRhs : TyCon -> (list Var.TyVar * unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ tvs_rhs _) _ _ => tvs_rhs
    | tycon =>
        Panic.panicStr (GHC.Base.hs_string__ "newTyConEtadRhs") (Panic.noString tycon)
    end.

Definition newTyConRhs : TyCon -> (list Var.TyVar * unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ tvs _ _ _ _ _ _ _ (NewTyCon _ rhs _ _) _ _ => pair tvs rhs
    | tycon =>
        Panic.panicStr (GHC.Base.hs_string__ "newTyConRhs") (Panic.noString tycon)
    end.

Definition okParent : Name.Name -> AlgTyConFlav -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, VanillaAlgTyCon _ => true
    | _, UnboxedAlgTyCon _ => true
    | tc_name, ClassTyCon cls _ => tc_name GHC.Base.== tyConName (classTyCon cls)
    | _, DataFamInstTyCon _ fam_tc tys => Util.lengthAtLeast tys (tyConArity fam_tc)
    end.

Definition pprPromotionQuote : TyCon -> GHC.Base.String :=
  fun tc =>
    match tc with
    | PromotedDataCon _ _ _ _ _ _ _ _ _ _ => Panic.noString (GHC.Char.hs_char__ "'")
    | _ => Panic.someSDoc
    end.

Definition primElemRepSizeB : PrimElemRep -> GHC.Num.Int :=
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

Definition primRepSizeB : DynFlags.DynFlags -> PrimRep -> GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | dflags, IntRep => DynFlags.wORD_SIZE dflags
    | dflags, WordRep => DynFlags.wORD_SIZE dflags
    | _, Int64Rep => Constants.wORD64_SIZE
    | _, Word64Rep => Constants.wORD64_SIZE
    | _, FloatRep => Constants.fLOAT_SIZE
    | dflags, DoubleRep => DynFlags.dOUBLE_SIZE dflags
    | dflags, AddrRep => DynFlags.wORD_SIZE dflags
    | dflags, LiftedRep => DynFlags.wORD_SIZE dflags
    | dflags, UnliftedRep => DynFlags.wORD_SIZE dflags
    | _, VoidRep => #0
    | _, VecRep len rep => len GHC.Num.* primElemRepSizeB rep
    end.

Definition primRepIsFloat : PrimRep -> option bool :=
  fun arg_0__ =>
    match arg_0__ with
    | FloatRep => Some true
    | DoubleRep => Some true
    | VecRep _ _ => None
    | _ => Some false
    end.

Definition synTyConDefn_maybe : TyCon -> option (list Var.TyVar * unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | SynonymTyCon _ _ _ tyvars _ _ _ _ ty _ _ => Some (pair tyvars ty)
    | _ => None
    end.

Definition synTyConRhs_maybe : TyCon -> option unit :=
  fun arg_0__ =>
    match arg_0__ with
    | SynonymTyCon _ _ _ _ _ _ _ _ rhs _ _ => Some rhs
    | _ => None
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

Definition tyConAssoc_maybe : TyCon -> option Class :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ _ mb_cls _ => mb_cls
    | _ => None
    end.

Definition isTyConAssoc : TyCon -> bool :=
  fun tc => Data.Maybe.isJust (tyConAssoc_maybe tc).

Definition tyConBinderArgFlag : TyConBinder -> Var.ArgFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | Var.TvBndr _ (NamedTCB vis) => vis
    | Var.TvBndr _ AnonTCB => Var.Required
    end.

Definition tyConCType_maybe : TyCon -> option unit :=
  fun arg_0__ =>
    match arg_0__ with
    | (AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ as tc) => tyConCType tc
    | _ => None
    end.

Definition tyConClass_maybe : TyCon -> option Class :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (ClassTyCon clas _) => Some clas
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

Definition kindTyConKeys : UniqSet.UniqSet Unique.Unique :=
  let tycon_with_datacons :=
    fun tc =>
      cons (Unique.getUnique tc) (GHC.Base.map Unique.getUnique (tyConDataCons tc)) in
  UniqSet.unionManyUniqSets (cons (UniqSet.mkUniqSet (cons
                                                      PrelNames.liftedTypeKindTyConKey (cons PrelNames.starKindTyConKey
                                                                                             (cons
                                                                                              PrelNames.unicodeStarKindTyConKey
                                                                                              (cons
                                                                                               PrelNames.constraintKindTyConKey
                                                                                               (cons
                                                                                                PrelNames.tYPETyConKey
                                                                                                nil)))))) (GHC.Base.map
                                   (UniqSet.mkUniqSet GHC.Base.∘ tycon_with_datacons) (cons
                                                                                       TysWiredIn.runtimeRepTyCon (cons
                                                                                        TysWiredIn.vecCountTyCon (cons
                                                                                         TysWiredIn.vecElemTyCon
                                                                                         nil))))).

Definition isKindTyCon : TyCon -> bool :=
  fun tc => UniqSet.elementOfUniqSet (Unique.getUnique tc) kindTyConKeys.

Definition tyConFamInstSig_maybe
   : TyCon ->
     option (TyCon * list unit * CoAxiom.CoAxiom CoAxiom.Unbranched)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (DataFamInstTyCon ax f ts) =>
        Some (pair (pair f ts) ax)
    | _ => None
    end.

Definition tyConFamInst_maybe : TyCon -> option (TyCon * list unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (DataFamInstTyCon _ f ts) =>
        Some (pair f ts)
    | _ => None
    end.

Definition tyConFamilyCoercion_maybe
   : TyCon -> option (CoAxiom.CoAxiom CoAxiom.Unbranched) :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (DataFamInstTyCon ax _ _) => Some ax
    | _ => None
    end.

Definition tyConFamilyResVar_maybe : TyCon -> option Name.Name :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ res _ _ _ => res
    | _ => None
    end.

Definition tyConFamilySize : TyCon -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
    | (AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ as tc) =>
        match rhs with
        | DataTyCon cons_ _ => Data.Foldable.length cons_
        | NewTyCon _ _ _ _ => #1
        | TupleTyCon _ _ => #1
        | SumTyCon cons_ => Data.Foldable.length cons_
        | _ =>
            Panic.panicStr (GHC.Base.hs_string__ "tyConFamilySize 1") (Panic.noString tc)
        end
    | tc =>
        Panic.panicStr (GHC.Base.hs_string__ "tyConFamilySize 2") (Panic.noString tc)
    end.

Definition tyConFamilySizeAtMost : TyCon -> GHC.Num.Int -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ as tc), n =>
        match rhs with
        | DataTyCon cons_ _ => Util.lengthAtMost cons_ n
        | NewTyCon _ _ _ _ => #1 GHC.Base.<= n
        | TupleTyCon _ _ => #1 GHC.Base.<= n
        | SumTyCon cons_ => Util.lengthAtMost cons_ n
        | _ =>
            Panic.panicStr (GHC.Base.hs_string__ "tyConFamilySizeAtMost 1") (Panic.noString
                                                                             tc)
        end
    | tc, _ =>
        Panic.panicStr (GHC.Base.hs_string__ "tyConFamilySizeAtMost 2") (Panic.noString
                                                                         tc)
    end.

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

Definition mightBeUnsaturatedTyCon : TyCon -> bool :=
  tcFlavourCanBeUnsaturated GHC.Base.∘ tyConFlavour.

Definition makeRecoveryTyCon : TyCon -> TyCon :=
  fun tc =>
    mkTcTyCon (tyConName tc) (tyConBinders tc) (tyConResKind tc) nil (tyConFlavour
                                                                      tc).

Definition tyConRepModOcc
   : Module.Module -> OccName.OccName -> (Module.Module * OccName.OccName)%type :=
  fun tc_module tc_occ =>
    let rep_module :=
      if tc_module GHC.Base.== PrelNames.gHC_PRIM : bool then PrelNames.gHC_TYPES else
      tc_module in
    pair rep_module (OccName.mkTyConRepOcc tc_occ).

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
   : Name.Name -> list TyConBinder -> unit -> list CoAxiom.Role -> TyCon :=
  fun name binders res_kind roles =>
    mkPrimTyCon' name binders res_kind roles true (Some (mkPrelTyConRepName name)).

Definition mkLiftedPrimTyCon
   : Name.Name -> list TyConBinder -> unit -> list CoAxiom.Role -> TyCon :=
  fun name binders res_kind roles =>
    let rep_nm := mkPrelTyConRepName name in
    mkPrimTyCon' name binders res_kind roles false (Some rep_nm).

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

Definition tyConRoles : TyCon -> list CoAxiom.Role :=
  fun tc =>
    let const_role := fun r => GHC.List.replicate (tyConArity tc) r in
    match tc with
    | FunTyCon _ _ _ _ _ _ _ => const_role CoAxiom.Representational
    | AlgTyCon _ _ _ _ _ _ _ roles _ _ _ _ _ _ => roles
    | SynonymTyCon _ _ _ _ _ _ _ roles _ _ _ => roles
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ => const_role CoAxiom.Nominal
    | PrimTyCon _ _ _ _ _ _ roles _ _ => roles
    | PromotedDataCon _ _ _ _ _ _ roles _ _ _ => roles
    | TcTyCon _ _ _ _ _ _ _ _ _ => const_role CoAxiom.Nominal
    end.

Definition tyConRuntimeRepInfo : TyCon -> RuntimeRepInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | PromotedDataCon _ _ _ _ _ _ _ _ _ rri => rri
    | _ => NoRRI
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
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "tyConDataCon") (Panic.noString tc)
    end.

Definition tyConSkolem : TyCon -> bool :=
  Name.isHoleName GHC.Base.∘ tyConName.

Definition tyConStupidTheta : TyCon -> list unit :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ stupid _ _ _ => stupid
    | tycon =>
        Panic.panicStr (GHC.Base.hs_string__ "tyConStupidTheta") (Panic.noString tycon)
    end.

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

Definition tyConTyVarBinders : list TyConBinder -> list Var.TyVarBinder :=
  fun tc_bndrs =>
    let mk_binder :=
      fun arg_0__ =>
        let 'Var.TvBndr tv tc_vis := arg_0__ in
        let vis :=
          match tc_vis with
          | AnonTCB => Var.Specified
          | NamedTCB Var.Required => Var.Specified
          | NamedTCB vis => vis
          end in
        Var.mkTyVarBinder vis tv in
    GHC.Base.map mk_binder tc_bndrs.

Definition unwrapNewTyConEtad_maybe
   : TyCon ->
     option (list Var.TyVar * unit * CoAxiom.CoAxiom CoAxiom.Unbranched)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ (pair tvs rhs) co) _ _ =>
        Some (pair (pair tvs rhs) co)
    | _ => None
    end.

Definition unwrapNewTyCon_maybe
   : TyCon ->
     option (list Var.TyVar * unit * CoAxiom.CoAxiom CoAxiom.Unbranched)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ tvs _ _ _ _ _ _ _ (NewTyCon _ rhs _ co) _ _ =>
        Some (pair (pair tvs rhs) co)
    | _ => None
    end.

Definition visibleDataCons : AlgTyConRhs -> list DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AbstractTyCon => nil
    | DataTyCon cs _ => cs
    | NewTyCon c _ _ _ => cons c nil
    | TupleTyCon c _ => cons c nil
    | SumTyCon cs => cs
    end.

Definition buildSynTyCon
   : Name.Name ->
     list TyConBinder -> unit -> list CoAxiom.Role -> unit -> TyCon :=
  fun name binders res_kind roles rhs =>
    let is_fam_free := Type.isFamFreeTy rhs in
    let is_tau := Type.isTauTy rhs in
    mkSynonymTyCon name binders res_kind roles rhs is_tau is_fam_free.

Definition classDataCon : Class -> DataCon :=
  fun clas =>
    match tyConDataCons (classTyCon clas) with
    | cons dict_constr no_more =>
        if andb Util.debugIsOn (negb (Data.Foldable.null no_more)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/basicTypes/DataCon.hs") #1346)
        else dict_constr
    | nil => Panic.panic (GHC.Base.hs_string__ "classDataCon")
    end.

Definition dataConBoxer : DataCon -> option unit :=
  fun arg_0__ =>
    match arg_0__ with
    | MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (DCR _ boxer _ _ _) _ _ _ _ _ _ =>
        Some boxer
    | _ => None
    end.

Definition dataConExTyVars : DataCon -> list Var.TyVar :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ tvbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
    tvbs.

Definition isProductTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | (AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ as tc) =>
        match algTcRhs tc with
        | TupleTyCon _ _ => true
        | DataTyCon (cons data_con nil) _ =>
            Data.Foldable.null (dataConExTyVars data_con)
        | NewTyCon _ _ _ _ => true
        | _ => false
        end
    | _ => false
    end.

Definition isDataSumTyCon_maybe : TyCon -> option (list DataCon) :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | DataTyCon cons_ _ =>
            if andb (Util.lengthExceeds cons_ #1) (Data.Foldable.all (Data.Foldable.null
                                                                      GHC.Base.∘
                                                                      dataConExTyVars) cons_) : bool
            then Some cons_ else
            None
        | SumTyCon cons_ =>
            if Data.Foldable.all (Data.Foldable.null GHC.Base.∘ dataConExTyVars)
               cons_ : bool
            then Some cons_ else
            None
        | _ => None
        end
    | _ => None
    end.

Definition isDataProductTyCon_maybe : TyCon -> option DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        let j_2__ := match rhs with | TupleTyCon con _ => Some con | _ => None end in
        match rhs with
        | DataTyCon (cons con nil) _ =>
            if Data.Foldable.null (dataConExTyVars con) : bool then Some con else
            j_2__
        | _ => j_2__
        end
    | _ => None
    end.

Definition dataConFieldLabels : DataCon -> list FieldLabel.FieldLabel :=
  dcFields.

Definition fieldsOfAlgTcRhs : AlgTyConRhs -> FieldLabel.FieldLabelEnv :=
  fun rhs =>
    let dataConsFields :=
      fun dcs => Data.Foldable.concatMap dataConFieldLabels dcs in
    FastStringEnv.mkDFsEnv (Coq.Lists.List.flat_map (fun fl =>
                                                       cons (pair (FieldLabel.flLabel fl) fl) nil) (dataConsFields
                                                     (visibleDataCons rhs))).

Definition mkAlgTyCon
   : Name.Name ->
     list TyConBinder ->
     unit ->
     list CoAxiom.Role ->
     option unit -> list unit -> AlgTyConRhs -> AlgTyConFlav -> bool -> TyCon :=
  fun name binders res_kind roles cType stupid rhs parent gadt_syn =>
    AlgTyCon (Name.nameUnique name) name binders (Var.binderVars binders) res_kind
             (mkTyConKind binders res_kind) (Data.Foldable.length binders) roles cType
             gadt_syn stupid rhs (fieldsOfAlgTcRhs rhs) (if andb Util.debugIsOn (negb
                                                                  (okParent name parent)) : bool
              then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                               "ghc/compiler/types/TyCon.hs") #1433 (Panic.noString name Outputable.$$
                                                                                     Panic.noString parent))
              else parent).

Definition buildAlgTyCon
   : Name.Name ->
     list Var.TyVar ->
     list CoAxiom.Role ->
     option unit -> unit -> AlgTyConRhs -> bool -> AlgTyConFlav -> TyCon :=
  fun tc_name ktvs roles cType stupid_theta rhs gadt_syn parent =>
    let binders := Type.mkTyConBindersPreferAnon ktvs TysWiredIn.liftedTypeKind in
    mkAlgTyCon tc_name binders TysWiredIn.liftedTypeKind roles cType stupid_theta
    rhs parent gadt_syn.

Definition mkClassTyCon
   : Name.Name ->
     list TyConBinder ->
     list CoAxiom.Role -> AlgTyConRhs -> Class -> Name.Name -> TyCon :=
  fun name binders roles rhs clas tc_rep_name =>
    mkAlgTyCon name binders TysWiredIn.constraintKind roles None nil rhs (ClassTyCon
                                                                          clas tc_rep_name) false.

Definition dataConFieldType_maybe
   : DataCon ->
     FieldLabel.FieldLabelString -> option (FieldLabel.FieldLabel * unit)%type :=
  fun con label =>
    Data.Foldable.find ((fun arg_0__ => arg_0__ GHC.Base.== label) GHC.Base.∘
                        (FieldLabel.flLabel GHC.Base.∘ Data.Tuple.fst)) (GHC.List.zip (dcFields con)
                                                                                      (dcOrigArgTys con)).

Definition dataConFieldType : DataCon -> FieldLabel.FieldLabelString -> unit :=
  fun con label =>
    match dataConFieldType_maybe con label with
    | Some (pair _ ty) => ty
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "dataConFieldType") (GHC.Base.mappend
                                                                  (Panic.noString con) (Panic.noString label))
    end.

Definition dataConFullSig
   : DataCon ->
     (list Var.TyVar * list Var.TyVar * list EqSpec * unit * list unit *
      unit)%type :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ univ_tvs ex_tvs _ eq_spec theta _ arg_tys res_ty _ _ _ _ _ _
       _ _ _ _ := arg_0__ in
    pair (pair (pair (pair (pair univ_tvs ex_tvs) eq_spec) theta) arg_tys) res_ty.

Definition dataConImplBangs : DataCon -> list HsImplBang :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep => GHC.List.replicate (dcSourceArity dc) HsLazy
    | DCR _ _ _ _ bangs => bangs
    end.

Definition dataConImplicitTyThings : DataCon -> list unit :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ work rep _ _ _ _ _ _ := arg_0__ in
    let wrap_ids :=
      match rep with
      | NoDataConRep => nil
      | DCR wrap _ _ _ _ => cons (TyCoRep.AnId wrap) nil
      end in
    Coq.Init.Datatypes.app (cons (TyCoRep.AnId work) nil) wrap_ids.

Definition dataConInstOrigArgTys : DataCon -> list unit -> list unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (MkData _ _ _ _ univ_tvs ex_tvs _ _ _ _ arg_tys _ _ _ _ _ _ _ _ _ _ _ as dc)
    , inst_tys =>
        let tyvars := Coq.Init.Datatypes.app univ_tvs ex_tvs in
        if andb Util.debugIsOn (negb (Util.equalLength tyvars inst_tys)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/basicTypes/DataCon.hs") #1274 ((GHC.Base.mappend (id
                                                                                                         (GHC.Base.hs_string__
                                                                                                          "dataConInstOrigArgTys"))
                                                                                                        (Panic.noString
                                                                                                         dc)
                                                                                       Outputable.$$
                                                                                       Panic.noString tyvars)
                                                                                      Outputable.$$
                                                                                      Panic.noString inst_tys))
        else GHC.Base.map (TyCoRep.substTyWith tyvars inst_tys) arg_tys
    end.

Definition dataConIsInfix : DataCon -> bool :=
  dcInfix.

Definition dataConName : DataCon -> Name.Name :=
  dcName.

Definition dataConIdentity : DataCon -> list GHC.Word.Word8 :=
  fun dc =>
    let name := dataConName dc in
    let mod_ :=
      if andb Util.debugIsOn (negb (Name.isExternalName name)) : bool
      then (Panic.assertPanic (GHC.Base.hs_string__
                               "ghc/compiler/basicTypes/DataCon.hs") #1304)
      else Name.nameModule name in
    Coq.Init.Datatypes.app (FastString.bytesFS (Module.unitIdFS (Module.moduleUnitId
                                                                 mod_))) (cons (GHC.Real.fromIntegral (GHC.Base.ord
                                                                                                       (GHC.Char.hs_char__
                                                                                                        ":")))
                                                                               (Coq.Init.Datatypes.app
                                                                                (FastString.bytesFS (Module.moduleNameFS
                                                                                                     (Module.moduleName
                                                                                                      mod_))) (cons
                                                                                 (GHC.Real.fromIntegral (GHC.Base.ord
                                                                                                         (GHC.Char.hs_char__
                                                                                                          ".")))
                                                                                 (FastString.bytesFS (OccName.occNameFS
                                                                                                      (Name.nameOccName
                                                                                                       name)))))).

Definition dataConOrigArgTys : DataCon -> list unit :=
  fun dc => dcOrigArgTys dc.

Definition dataConOrigResTy : DataCon -> unit :=
  fun dc => dcOrigResTy dc.

Definition dataConOrigTyCon : DataCon -> TyCon :=
  fun dc =>
    match tyConFamInst_maybe (dcRepTyCon dc) with
    | Some (pair tc _) => tc
    | _ => dcRepTyCon dc
    end.

Definition dataConRepArgTys : DataCon -> list unit :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ eq_spec theta _ orig_arg_tys _ _ _ _ rep _ _ _ _ _
       _ := arg_0__ in
    match rep with
    | NoDataConRep =>
        if andb Util.debugIsOn (negb (Data.Foldable.null eq_spec)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/basicTypes/DataCon.hs") #1293)
        else Coq.Init.Datatypes.app theta orig_arg_tys
    | DCR _ _ arg_tys _ _ => arg_tys
    end.

Definition dataConRepStrictness : DataCon -> list StrictnessMark :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep =>
        Coq.Lists.List.flat_map (fun _ => cons NotMarkedStrict nil) (dataConRepArgTys
                                 dc)
    | DCR _ _ _ strs _ => strs
    end.

Definition dataConInstArgTys : DataCon -> list unit -> list unit :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (MkData _ _ _ _ univ_tvs ex_tvs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ as dc)
    , inst_tys =>
        if andb Util.debugIsOn (negb (Util.equalLength univ_tvs inst_tys)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/basicTypes/DataCon.hs") #1257 ((GHC.Base.mappend (id
                                                                                                         (GHC.Base.hs_string__
                                                                                                          "dataConInstArgTys"))
                                                                                                        (Panic.noString
                                                                                                         dc)
                                                                                       Outputable.$$
                                                                                       Panic.noString univ_tvs)
                                                                                      Outputable.$$
                                                                                      Panic.noString inst_tys))
        else if andb Util.debugIsOn (negb (Data.Foldable.null ex_tvs)) : bool
             then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                              "ghc/compiler/basicTypes/DataCon.hs") #1258 (Panic.noString dc))
             else GHC.Base.map (TyCoRep.substTyWith univ_tvs inst_tys) (dataConRepArgTys dc)
    end.

Definition splitDataProductType_maybe
   : unit -> option (TyCon * list unit * DataCon * list unit)%type :=
  fun ty =>
    match Type.splitTyConApp_maybe ty with
    | Some (pair tycon ty_args) =>
        match isDataProductTyCon_maybe tycon with
        | Some con =>
            Some (pair (pair (pair tycon ty_args) con) (dataConInstArgTys con ty_args))
        | _ => None
        end
    | _ => None
    end.

Definition dataConRepArity : DataCon -> BasicTypes.Arity :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arity _ _ _ _ _ := arg_0__ in
    arity.

Definition isNullaryRepDataCon : DataCon -> bool :=
  fun dc => dataConRepArity dc GHC.Base.== #0.

Definition dataConRepType : DataCon -> unit :=
  dcRepType.

Definition dataConSourceArity : DataCon -> BasicTypes.Arity :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ arity _ _ _ _ := arg_0__ in
    arity.

Definition isNullarySrcDataCon : DataCon -> bool :=
  fun dc => dataConSourceArity dc GHC.Base.== #0.

Definition dataConSrcBangs : DataCon -> list HsSrcBang :=
  dcSrcBangs.

Definition dataConStupidTheta : DataCon -> unit :=
  fun dc => dcStupidTheta dc.

Definition dataConTag : DataCon -> BasicTypes.ConTag :=
  dcTag.

Definition dataConTagZ : DataCon -> BasicTypes.ConTagZ :=
  fun con => dataConTag con GHC.Num.- BasicTypes.fIRST_TAG.

Definition dataConTyCon : DataCon -> TyCon :=
  dcRepTyCon.

Definition specialPromotedDc : DataCon -> bool :=
  isKindTyCon GHC.Base.∘ dataConTyCon.

Definition isPromotedTupleTyCon : TyCon -> bool :=
  fun tyCon =>
    match isPromotedDataCon_maybe tyCon with
    | Some dataCon =>
        if isTupleTyCon (dataConTyCon dataCon) : bool then true else
        false
    | _ => false
    end.

Definition dataConUnivAndExTyVars : DataCon -> list Var.TyVar :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ univ_tvs ex_tvs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ :=
      arg_0__ in
    Coq.Init.Datatypes.app univ_tvs ex_tvs.

Definition dataConUnivTyVars : DataCon -> list Var.TyVar :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ tvbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
    tvbs.

Definition dataConUserTyVarBinders : DataCon -> list Var.TyVarBinder :=
  dcUserTyVarBinders.

Definition dataConUserTyVars : DataCon -> list Var.TyVar :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ tvbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
    Var.binderVars tvbs.

Definition dataConUserType : DataCon -> unit :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ user_tvbs _ theta _ arg_tys res_ty _ _ _ _ _ _ _ _ _
       _ := arg_0__ in
    TyCoRep.mkForAllTys user_tvbs (TyCoRep.mkFunTys theta (TyCoRep.mkFunTys arg_tys
                                                                            res_ty)).

Definition dataConWorkId : DataCon -> Var.Id :=
  fun dc => dcWorkId dc.

Definition dataConWrapId : DataCon -> Var.Id :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep => dcWorkId dc
    | DCR wrap_id _ _ _ _ => wrap_id
    end.

Definition dataConWrapId_maybe : DataCon -> option Var.Id :=
  fun dc =>
    match dcRep dc with
    | NoDataConRep => None
    | DCR wrap_id _ _ _ _ => Some wrap_id
    end.

Definition eqHsBang : HsImplBang -> HsImplBang -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | HsLazy, HsLazy => true
    | HsStrict, HsStrict => true
    | HsUnpack None, HsUnpack None => true
    | HsUnpack (Some c1), HsUnpack (Some c2) =>
        Type.eqType (Coercion.coercionType c1) (Coercion.coercionType c2)
    | _, _ => false
    end.

Definition eqSpecPair : EqSpec -> (Var.TyVar * unit)%type :=
  fun arg_0__ => let 'EqSpec tv ty := arg_0__ in pair tv ty.

Definition eqSpecPreds : list EqSpec -> unit :=
  fun spec =>
    let cont_0__ arg_1__ :=
      let 'EqSpec tv ty := arg_1__ in
      cons (Type.mkPrimEqPred (TyCoRep.mkTyVarTy tv) ty) nil in
    Coq.Lists.List.flat_map cont_0__ spec.

Definition dataConTheta : DataCon -> unit :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ eq_spec theta _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
    Coq.Init.Datatypes.app (eqSpecPreds eq_spec) theta.

Definition dataConSig
   : DataCon -> (list Var.TyVar * unit * list unit * unit)%type :=
  fun arg_0__ =>
    let '(MkData _ _ _ _ _ _ _ _ _ _ arg_tys res_ty _ _ _ _ _ _ _ _ _ _ as con) :=
      arg_0__ in
    pair (pair (pair (dataConUnivAndExTyVars con) (dataConTheta con)) arg_tys)
         res_ty.

Definition dataConInstSig
   : DataCon -> list unit -> (list Var.TyVar * unit * list unit)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkData _ _ _ _ univ_tvs ex_tvs _ eq_spec theta _ arg_tys _ _ _ _ _ _ _ _ _ _ _
    , univ_tys =>
        let univ_subst := TyCoRep.zipTvSubst univ_tvs univ_tys in
        let 'pair subst ex_tvs' := Data.Traversable.mapAccumL TyCoRep.substTyVarBndr
                                     univ_subst ex_tvs in
        pair (pair ex_tvs' (TyCoRep.substTheta subst (Coq.Init.Datatypes.app
                                                      (eqSpecPreds eq_spec) theta))) (TyCoRep.substTys subst arg_tys)
    end.

Definition dataConCannotMatch : list unit -> DataCon -> bool :=
  fun tys con =>
    let predEqs :=
      fun pred =>
        match Type.classifyPredType pred with
        | Type.EqPred Type.NomEq ty1 ty2 => cons (pair ty1 ty2) nil
        | Type.ClassPred eq (cons _ (cons ty1 (cons ty2 nil))) =>
            if Unique.hasKey eq PrelNames.eqTyConKey : bool
            then cons (pair ty1 ty2) nil else
            nil
        end in
    let 'pair (pair _ inst_theta) _ := dataConInstSig con tys in
    if Data.Foldable.null inst_theta : bool then false else
    if Data.Foldable.all Type.isTyVarTy tys : bool then false else
    Unify.typesCantMatch (Data.Foldable.concatMap predEqs inst_theta).

Definition eqSpecTyVar : EqSpec -> Var.TyVar :=
  fun arg_0__ => let 'EqSpec tv _ := arg_0__ in tv.

Definition filterEqSpec : list EqSpec -> list Var.TyVar -> list Var.TyVar :=
  fun eq_spec =>
    let not_in_eq_spec :=
      fun var =>
        Data.Foldable.all (negb GHC.Base.∘
                           ((fun arg_0__ => arg_0__ GHC.Base.== var) GHC.Base.∘ eqSpecTyVar)) eq_spec in
    GHC.List.filter not_in_eq_spec.

Definition dataConUserTyVarsArePermuted : DataCon -> bool :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ univ_tvs ex_tvs user_tvbs eq_spec _ _ _ _ _ _ _ _ _ _ _ _ _
       _ := arg_0__ in
    (Coq.Init.Datatypes.app (filterEqSpec eq_spec univ_tvs) ex_tvs) GHC.Base./=
    Var.binderVars user_tvbs.

Definition eqSpecType : EqSpec -> unit :=
  fun arg_0__ => let 'EqSpec _ ty := arg_0__ in ty.

Definition freshNames : list Name.Name -> list Name.Name :=
  fun avoids =>
    let avoid_occs : OccName.OccSet :=
      OccName.mkOccSet (GHC.Base.map Name.getOccName avoids) in
    let avoid_uniqs : UniqSet.UniqSet Unique.Unique :=
      UniqSet.mkUniqSet (GHC.Base.map Unique.getUnique avoids) in
    Coq.Lists.List.flat_map (fun n =>
                               let occ :=
                                 OccName.mkTyVarOccFS (FastString.mkFastString (cons (GHC.Char.hs_char__ "x")
                                                                                     (GHC.Show.show n))) in
                               let uniq := Unique.mkAlphaTyVarUnique n in
                               if negb (UniqSet.elementOfUniqSet uniq avoid_uniqs) : bool
                               then if negb (OccName.elemOccSet occ avoid_occs) : bool
                                    then cons (Name.mkSystemName uniq occ) nil else
                                    nil else
                               nil) (enumFrom #0).

Definition mkCleanAnonTyConBinders
   : list TyConBinder -> list unit -> list TyConBinder :=
  fun tc_bndrs tys =>
    let fresh_names :=
      freshNames (GHC.Base.map Name.getName (Var.binderVars tc_bndrs)) in
    let cont_1__ arg_2__ :=
      let 'pair name ty := arg_2__ in
      cons (mkAnonTyConBinder (Var.mkTyVar name ty)) nil in
    Coq.Lists.List.flat_map cont_1__ (GHC.List.zip fresh_names tys).

Definition mkDataCon
   : Name.Name ->
     bool ->
     TyConRepName ->
     list HsSrcBang ->
     list FieldLabel.FieldLabel ->
     list Var.TyVar ->
     list Var.TyVar ->
     list Var.TyVarBinder ->
     list EqSpec ->
     unit ->
     list unit ->
     unit -> RuntimeRepInfo -> TyCon -> unit -> Var.Id -> DataConRep -> DataCon :=
  fun name
  declared_infix
  prom_info
  arg_stricts
  fields
  univ_tvs
  ex_tvs
  user_tvbs
  eq_spec
  theta
  orig_arg_tys
  orig_res_ty
  rep_info
  rep_tycon
  stupid_theta
  work_id
  rep =>
    let roles :=
      Coq.Init.Datatypes.app (GHC.Base.map (GHC.Base.const CoAxiom.Nominal)
                              (Coq.Init.Datatypes.app univ_tvs ex_tvs)) (GHC.Base.map (GHC.Base.const
                                                                                       CoAxiom.Representational)
                              orig_arg_tys) in
    let prom_res_kind := orig_res_ty in
    let user_tvbs_invariant :=
      Data.Set.Internal.fromList (Coq.Init.Datatypes.app (filterEqSpec eq_spec
                                                          univ_tvs) ex_tvs) GHC.Base.==
      Data.Set.Internal.fromList (Var.binderVars user_tvbs) in
    let user_tvbs' :=
      if andb Util.debugIsOn (negb (user_tvbs_invariant)) : bool
      then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                       "ghc/compiler/basicTypes/DataCon.hs") #897 ((Panic.noString univ_tvs
                                                                                    Outputable.$$
                                                                                    Panic.noString ex_tvs) Outputable.$$
                                                                                   Panic.noString user_tvbs))
      else user_tvbs in
    let prom_tv_bndrs :=
      let cont_3__ arg_4__ :=
        match arg_4__ with
        | Var.TvBndr tv vis => cons (mkNamedTyConBinder vis tv) nil
        | _ => nil
        end in
      Coq.Lists.List.flat_map cont_3__ user_tvbs' in
    let prom_arg_bndrs :=
      mkCleanAnonTyConBinders prom_tv_bndrs (Coq.Init.Datatypes.app theta
                                                                    orig_arg_tys) in
    let is_vanilla :=
      andb (Data.Foldable.null ex_tvs) (andb (Data.Foldable.null eq_spec)
                                             (Data.Foldable.null theta)) in
    let con :=
      MkData name (Name.nameUnique name) tag is_vanilla univ_tvs ex_tvs user_tvbs'
             eq_spec theta stupid_theta orig_arg_tys orig_res_ty arg_stricts fields work_id
             rep (Data.Foldable.length rep_arg_tys) (Data.Foldable.length orig_arg_tys)
             rep_tycon rep_ty declared_infix promoted in
    let tag :=
      ListSetOps.assoc (GHC.Base.hs_string__ "mkDataCon") (GHC.List.zip (tyConDataCons
                                                                         rep_tycon) (enumFrom BasicTypes.fIRST_TAG))
      con in
    let rep_arg_tys := dataConRepArgTys con in
    let rep_ty :=
      match rep with
      | NoDataConRep => dataConUserType con
      | DCR _ _ _ _ _ =>
          Type.mkInvForAllTys univ_tvs (Type.mkInvForAllTys ex_tvs (TyCoRep.mkFunTys
                                                             rep_arg_tys (Type.mkTyConApp rep_tycon (TyCoRep.mkTyVarTys
                                                                                           univ_tvs))))
      end in
    let promoted :=
      mkPromotedDataCon con name prom_info (Coq.Init.Datatypes.app prom_tv_bndrs
                                                                   prom_arg_bndrs) prom_res_kind roles rep_info in
    con.

Definition isBanged : HsImplBang -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | HsUnpack _ => true
    | HsStrict => true
    | HsLazy => false
    end.

Definition isLegacyPromotableTyCon : TyCon -> bool :=
  fun tc => orb (isVanillaAlgTyCon tc) (orb (isFunTyCon tc) (isKindTyCon tc)).

Definition isMarkedStrict : StrictnessMark -> bool :=
  fun arg_0__ => match arg_0__ with | NotMarkedStrict => false | _ => true end.

Definition isSrcStrict : SrcStrictness -> bool :=
  fun arg_0__ => match arg_0__ with | SrcStrict => true | _ => false end.

Definition isSrcUnpacked : SrcUnpackedness -> bool :=
  fun arg_0__ => match arg_0__ with | SrcUnpack => true | _ => false end.

Definition isTupleDataCon : DataCon -> bool :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _ := arg_0__ in
    isTupleTyCon tc.

Definition isUnboxedSumCon : DataCon -> bool :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _ := arg_0__ in
    isUnboxedSumTyCon tc.

Definition isUnboxedTupleCon : DataCon -> bool :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc _ _ _ := arg_0__ in
    isUnboxedTupleTyCon tc.

Definition isVanillaDataCon : DataCon -> bool :=
  fun dc => dcVanilla dc.

Definition mkEqSpec : Var.TyVar -> unit -> EqSpec :=
  fun tv ty => EqSpec tv ty.

Definition dataConEqSpec : DataCon -> list EqSpec :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ eq_spec theta _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
    Coq.Init.Datatypes.app eq_spec (Coq.Init.Datatypes.app (let cont_1__ arg_2__ :=
                                                              match arg_2__ with
                                                              | Some (pair tc (cons _k1 (cons _k2 (cons ty1 (cons ty2
                                                                   nil))))) =>
                                                                  if Unique.hasKey tc PrelNames.heqTyConKey : bool
                                                                  then Coq.Lists.List.flat_map (fun spec =>
                                                                                                  cons spec nil)
                                                                                               (match pair
                                                                                                        (Type.getTyVar_maybe
                                                                                                         ty1)
                                                                                                        (Type.getTyVar_maybe
                                                                                                         ty2) with
                                                                                                | pair (Some tv1) _ =>
                                                                                                    cons (mkEqSpec tv1
                                                                                                          ty2) nil
                                                                                                | pair _ (Some tv2) =>
                                                                                                    cons (mkEqSpec tv2
                                                                                                          ty1) nil
                                                                                                | _ => nil
                                                                                                end) else
                                                                  nil
                                                              | _ => nil
                                                              end in
                                                            Coq.Lists.List.flat_map cont_1__ (GHC.Base.map
                                                                                     Type.splitTyConApp_maybe theta))
                                                           (let cont_7__ arg_8__ :=
                                                              match arg_8__ with
                                                              | Some (pair tc (cons _k (cons ty1 (cons ty2 nil)))) =>
                                                                  if Unique.hasKey tc PrelNames.eqTyConKey : bool
                                                                  then Coq.Lists.List.flat_map (fun spec =>
                                                                                                  cons spec nil)
                                                                                               (match pair
                                                                                                        (Type.getTyVar_maybe
                                                                                                         ty1)
                                                                                                        (Type.getTyVar_maybe
                                                                                                         ty2) with
                                                                                                | pair (Some tv1) _ =>
                                                                                                    cons (mkEqSpec tv1
                                                                                                          ty2) nil
                                                                                                | pair _ (Some tv2) =>
                                                                                                    cons (mkEqSpec tv2
                                                                                                          ty1) nil
                                                                                                | _ => nil
                                                                                                end) else
                                                                  nil
                                                              | _ => nil
                                                              end in
                                                            Coq.Lists.List.flat_map cont_7__ (GHC.Base.map
                                                                                     Type.splitTyConApp_maybe theta))).

Definition isLegacyPromotableDataCon : DataCon -> bool :=
  fun dc =>
    andb (Data.Foldable.null (dataConEqSpec dc)) (andb (Data.Foldable.null
                                                        (dataConTheta dc)) (andb (negb (isFamInstTyCon (dataConTyCon
                                                                                                        dc)))
                                                                                 (UniqSet.uniqSetAll
                                                                                  isLegacyPromotableTyCon
                                                                                  (Type.tyConsOfType (dataConUserType
                                                                                                      dc))))).

Definition promoteDataCon : DataCon -> TyCon :=
  fun arg_0__ =>
    let 'MkData _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tc := arg_0__ in
    tc.

Definition substEqSpec : TyCoRep.TCvSubst -> EqSpec -> EqSpec :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | subst, EqSpec tv ty =>
        let tv' :=
          Type.getTyVar (GHC.Base.hs_string__ "substEqSpec") (TyCoRep.substTyVar subst
                                                              tv) in
        EqSpec tv' (TyCoRep.substTy subst ty)
    end.

Definition classATItems : Class -> list ClassATItem :=
  fun arg_0__ =>
    match arg_0__ with
    | Class _ _ _ _ _ (ConcreteClass _ _ at_stuff _ _) => at_stuff
    | _ => nil
    end.

Definition classATs : Class -> list TyCon :=
  fun arg_0__ =>
    match arg_0__ with
    | Class _ _ _ _ _ (ConcreteClass _ _ at_stuff _ _) =>
        let cont_1__ arg_2__ := let 'ATI tc _ := arg_2__ in cons tc nil in
        Coq.Lists.List.flat_map cont_1__ at_stuff
    | _ => nil
    end.

Definition tyConATs : TyCon -> list TyCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (ClassTyCon clas _) => classATs clas
    | _ => nil
    end.

Definition classArity : Class -> BasicTypes.Arity :=
  fun clas => Data.Foldable.length (classTyVars clas).

Definition classBigSig
   : Class ->
     (list Var.TyVar * list unit * list Var.Id * list ClassOpItem)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Class _ _ _ tyvars _ AbstractClass => pair (pair (pair tyvars nil) nil) nil
    | Class _ _ _ tyvars _ (ConcreteClass sc_theta sc_sels _ op_stuff _) =>
        pair (pair (pair tyvars sc_theta) sc_sels) op_stuff
    end.

Definition classExtraBigSig
   : Class ->
     (list Var.TyVar * list (FunDep Var.TyVar) * list unit * list Var.Id *
      list ClassATItem *
      list ClassOpItem)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Class _ _ _ tyvars fundeps AbstractClass =>
        pair (pair (pair (pair (pair tyvars fundeps) nil) nil) nil) nil
    | Class _ _ _ tyvars fundeps (ConcreteClass sc_theta sc_sels ats op_stuff _) =>
        pair (pair (pair (pair (pair tyvars fundeps) sc_theta) sc_sels) ats) op_stuff
    end.

Definition classHasFds : Class -> bool :=
  fun arg_0__ =>
    let 'Class _ _ _ _ fds _ := arg_0__ in
    negb (Data.Foldable.null fds).

Definition classMethods : Class -> list Var.Id :=
  fun arg_0__ =>
    match arg_0__ with
    | Class _ _ _ _ _ (ConcreteClass _ _ _ op_stuff _) =>
        let cont_1__ arg_2__ := let 'pair op_sel _ := arg_2__ in cons op_sel nil in
        Coq.Lists.List.flat_map cont_1__ op_stuff
    | _ => nil
    end.

Definition classAllSelIds : Class -> list Var.Id :=
  fun arg_0__ =>
    match arg_0__ with
    | (Class _ _ _ _ _ (ConcreteClass _ sc_sels _ _ _) as c) =>
        Coq.Init.Datatypes.app sc_sels (classMethods c)
    | c =>
        if andb Util.debugIsOn (negb (Data.Foldable.null (classMethods c))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Class.hs")
              #244)
        else nil
    end.

Definition classMinimalDef : Class -> ClassMinimalDef :=
  fun arg_0__ =>
    match arg_0__ with
    | Class _ _ _ _ _ (ConcreteClass _ _ _ _ d) => d
    | _ => BooleanFormula.mkTrue
    end.

Definition classOpItems : Class -> list ClassOpItem :=
  fun arg_0__ =>
    match arg_0__ with
    | Class _ _ _ _ _ (ConcreteClass _ _ _ op_stuff _) => op_stuff
    | _ => nil
    end.

Definition classSCSelId : Class -> GHC.Num.Int -> Var.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Class _ _ _ _ _ (ConcreteClass _ sc_sels _ _ _), n =>
        if andb Util.debugIsOn (negb (andb (n GHC.Base.>= #0) (Util.lengthExceeds
                                            sc_sels n))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Class.hs")
              #251)
        else sc_sels GHC.List.!! n
    | c, n =>
        Panic.panicStr (GHC.Base.hs_string__ "classSCSelId") (GHC.Base.mappend
                                                              (Panic.noString c) (Panic.noString n))
    end.

Definition classSCTheta : Class -> list unit :=
  fun arg_0__ =>
    match arg_0__ with
    | Class _ _ _ _ _ (ConcreteClass theta_stuff _ _ _ _) => theta_stuff
    | _ => nil
    end.

Definition classTvsFds
   : Class -> (list Var.TyVar * list (FunDep Var.TyVar))%type :=
  fun c => pair (classTyVars c) (classFunDeps c).

Definition isAbstractClass : Class -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Class _ _ _ _ _ AbstractClass => true
    | _ => false
    end.

Definition mkAbstractClass
   : Name.Name -> list Var.TyVar -> list (FunDep Var.TyVar) -> TyCon -> Class :=
  fun cls_name tyvars fds tycon =>
    Class tycon cls_name (Name.nameUnique cls_name) tyvars fds AbstractClass.

Definition mkClass
   : Name.Name ->
     list Var.TyVar ->
     list (FunDep Var.TyVar) ->
     list unit ->
     list Var.Id ->
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
    Class tycon cls_name (Name.nameUnique cls_name) tyvars fds (ConcreteClass
           super_classes superdict_sels at_stuff op_stuff mindef).

Definition pprDefMethInfo : DefMethInfo -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | None => Panic.someSDoc
    | Some (pair n BasicTypes.VanillaDM) =>
        GHC.Base.mappend (id (GHC.Base.hs_string__ "Default method")) (Panic.noString n)
    | Some (pair n (BasicTypes.GenericDM ty)) =>
        GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend (id (GHC.Base.hs_string__
                                                                  "Generic default method")) (Panic.noString n))
                                           Outputable.dcolon) (TyCoRep.pprType ty)
    end.

Definition pprFunDep {a} `{Outputable.Outputable a}
   : FunDep a -> GHC.Base.String :=
  fun arg_0__ =>
    let 'pair us vs := arg_0__ in
    Outputable.hsep (cons (Outputable.interppSP us) (cons Outputable.arrow (cons
                                                           (Outputable.interppSP vs) nil))).

Definition pprFundeps {a} `{Outputable.Outputable a}
   : list (FunDep a) -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => Panic.someSDoc
    | fds => Outputable.hsep (cons Panic.someSDoc Panic.someSDoc)
    end.

(* External variables:
     Eq Gt Lt None Some TyCon andb bool cons enumFrom false id list negb nil op_zt__
     option orb pair promoted rep_arg_tys rep_ty tag true unit BasicTypes.Arity
     BasicTypes.Boxity BasicTypes.ConTag BasicTypes.ConTagZ BasicTypes.DefMethSpec
     BasicTypes.GenericDM BasicTypes.SourceText BasicTypes.TupleSort
     BasicTypes.VanillaDM BasicTypes.fIRST_TAG BasicTypes.isBoxed
     BasicTypes.tupleSortBoxity BooleanFormula.BooleanFormula BooleanFormula.mkTrue
     CoAxiom.Branched CoAxiom.BuiltInSynFamily CoAxiom.CoAxiom CoAxiom.Nominal
     CoAxiom.Phantom CoAxiom.Representational CoAxiom.Role CoAxiom.Unbranched
     Coercion.coercionType Constants.fLOAT_SIZE Constants.wORD64_SIZE
     Coq.Init.Datatypes.app Coq.Lists.List.flat_map Data.Foldable.all
     Data.Foldable.and Data.Foldable.concatMap Data.Foldable.find Data.Foldable.foldr
     Data.Foldable.length Data.Foldable.null Data.Maybe.isJust
     Data.Set.Internal.fromList Data.Traversable.mapAccumL Data.Tuple.fst
     Deriving.op_zdcon2tagzuGDTzzQOFa1zzUIKOcsSgCJHI__ DynFlags.DynFlags
     DynFlags.dOUBLE_SIZE DynFlags.wORD_SIZE FastString.bytesFS
     FastString.mkFastString FastStringEnv.dFsEnvElts FastStringEnv.emptyDFsEnv
     FastStringEnv.lookupDFsEnv FastStringEnv.mkDFsEnv FieldLabel.FieldLabel
     FieldLabel.FieldLabelEnv FieldLabel.FieldLabelString FieldLabel.flLabel
     GHC.Base.Eq_ GHC.Base.String GHC.Base.const GHC.Base.map GHC.Base.mappend
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zgze__ GHC.Base.op_zlze__
     GHC.Base.op_zsze__ GHC.Base.ord GHC.Err.Build_Default GHC.Err.Default
     GHC.Err.error GHC.List.drop GHC.List.filter GHC.List.op_znzn__
     GHC.List.replicate GHC.List.zip GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zm__
     GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Prim.op_tagToEnumzh__ GHC.Prim.op_zezezh__
     GHC.Real.fromIntegral GHC.Show.show GHC.Word.Word8 ListSetOps.assoc
     Maybes.orElse Module.Module Module.moduleName Module.moduleNameFS
     Module.moduleUnitId Module.unitIdFS Name.Name Name.getName Name.getOccName
     Name.isExternalName Name.isHoleName Name.isWiredInName Name.mkExternalName
     Name.mkSystemName Name.nameModule Name.nameOccName Name.nameSrcSpan
     Name.nameUnique NameEnv.NameEnv NameEnv.emptyNameEnv NameEnv.extendNameEnv
     NameEnv.lookupNameEnv OccName.OccName OccName.OccSet OccName.elemOccSet
     OccName.isTcOcc OccName.mkOccSet OccName.mkTyConRepOcc OccName.mkTyVarOccFS
     OccName.occNameFS Outputable.Outputable Outputable.arrow
     Outputable.assertPprPanic Outputable.dcolon Outputable.hsep Outputable.interppSP
     Outputable.op_zdzd__ Panic.assertPanic Panic.noString Panic.panic Panic.panicStr
     Panic.someSDoc PrelNames.constraintKindTyConKey PrelNames.eqTyConKey
     PrelNames.gHC_PRIM PrelNames.gHC_TYPES PrelNames.heqTyConKey
     PrelNames.liftedTypeKindTyConKey PrelNames.starKindTyConKey
     PrelNames.tYPETyConKey PrelNames.unicodeStarKindTyConKey SrcLoc.SrcSpan
     TyCoRep.AnId TyCoRep.TCvSubst TyCoRep.mkForAllTys TyCoRep.mkFunTys
     TyCoRep.mkTyVarTy TyCoRep.mkTyVarTys TyCoRep.pprType TyCoRep.substTheta
     TyCoRep.substTy TyCoRep.substTyVar TyCoRep.substTyVarBndr TyCoRep.substTyWith
     TyCoRep.substTys TyCoRep.zipTvSubst Type.ClassPred Type.EqPred Type.NomEq
     Type.classifyPredType Type.eqType Type.getTyVar Type.getTyVar_maybe
     Type.isFamFreeTy Type.isTauTy Type.isTyVarTy Type.mkInvForAllTys
     Type.mkPrimEqPred Type.mkTyConApp Type.mkTyConBindersPreferAnon
     Type.splitTyConApp_maybe Type.tyConsOfType TysWiredIn.constraintKind
     TysWiredIn.liftedTypeKind TysWiredIn.mkForAllKind TysWiredIn.mkFunKind
     TysWiredIn.runtimeRepTyCon TysWiredIn.vecCountTyCon TysWiredIn.vecElemTyCon
     Unify.typesCantMatch UniqSet.UniqSet UniqSet.elementOfUniqSet UniqSet.mkUniqSet
     UniqSet.unionManyUniqSets UniqSet.uniqSetAll Unique.Unique
     Unique.dataConRepNameUnique Unique.getUnique Unique.hasKey
     Unique.mkAlphaTyVarUnique Unique.tyConRepNameUnique Util.debugIsOn
     Util.equalLength Util.lengthAtLeast Util.lengthAtMost Util.lengthExceeds
     Util.listLengthCmp Util.op_zlzbzbzg__ Var.ArgFlag Var.Id Var.Required
     Var.Specified Var.TvBndr Var.TyVar Var.TyVarBinder Var.TyVarBndr Var.binderVars
     Var.isVisibleArgFlag Var.mkTyVar Var.mkTyVarBinder Var.tyVarKind
*)
