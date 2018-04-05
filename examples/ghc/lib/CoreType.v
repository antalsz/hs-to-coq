(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Parameter TcTyVarDetails : Type.  (* From TcType *)
Parameter CoercionHole : Type.
Parameter CType : Type.
Parameter RuntimeRepInfo : Type.

(* From Var *)
Inductive ExportFlag : Type := NotExported : ExportFlag
                            |  Exported : ExportFlag.
Inductive IdScope : Type := GlobalId : IdScope
                         |  LocalId : ExportFlag -> IdScope.


(* From TyCon *)
Require Name.
Definition TyConRepName := Name.Name%type.

Inductive Injectivity : Type := NotInjective : Injectivity
                             |  Injective : list bool -> Injectivity.

(* Converted imports: *)

Require BasicTypes.
Require Data.Foldable.
Require Data.Traversable.
Require Data.Tuple.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require Name.
Require Pair.
Require Panic.
Require SrcLoc.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Require Control.Monad.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Data.Either.
Require Data.Function.
Require Data.Functor.
Require Data.Maybe.
Require GHC.List.
Require ListSetOps.
Require PrelNames.
Require UniqFM.
Import Data.Functor.Notations.
Require Class.
Require ConLike.
Require DataCon.
Require DynFlags.
Require OccName.
Require UniqSet.
Require UniqSupply.
Require Constants.
Require Core.
Require FastStringEnv.
Require FieldLabel.
Require Maybes.
Require Module.
Require NameEnv.
Require TysWiredIn.
Import Util.Notations.
Require Control.Arrow.
Require Digraph.
Require IdInfo.
Require UniqDFM.
Require UniqDSet.

(* Converted type declarations: *)

Definition Unbranched :=
  Unbranched%type.

Definition TypeEqn :=
  (Pair.Pair Type_)%type.

Inductive Role : Type
  := Nominal : Role
  |  Representational : Role
  |  Phantom : Role.

Inductive CoAxiomRule : Type
  := Mk_CoAxiomRule
   : FastString.FastString ->
     list Role -> Role -> (list TypeEqn -> option TypeEqn) -> CoAxiomRule.

Inductive CoAxBranch : Type
  := Mk_CoAxBranch
   : SrcLoc.SrcSpan ->
     list TyVar ->
     list CoVar -> list Role -> list Type_ -> Type_ -> list CoAxBranch -> CoAxBranch.

Inductive BuiltInSynFamily : Type
  := Mk_BuiltInSynFamily
   : (list Type_ -> option (CoAxiomRule * list Type_ * Type_)%type) ->
     (list Type_ -> Type_ -> list TypeEqn) ->
     (list Type_ -> Type_ -> list Type_ -> Type_ -> list TypeEqn) ->
     BuiltInSynFamily.

Definition Branched :=
  Branched%type.

Definition BranchIndex :=
  GHC.Num.Int%type.

Inductive Branches br : Type
  := MkBranches : GHC.Arr.Array BranchIndex CoAxBranch -> Branches br.

Inductive CoAxiom br : Type
  := CoAxiom
   : Unique.Unique ->
     Name.Name -> Role -> TyCon -> Branches br -> bool -> CoAxiom br.

Inductive BranchFlag : Type
  := Mk_Branched : BranchFlag
  |  Mk_Unbranched : BranchFlag.

Arguments MkBranches {_} _.

Arguments CoAxiom {_} _ _ _ _ _ _.

Instance Default__Role : GHC.Err.Default Role :=
  GHC.Err.Build_Default _ Nominal.

Instance Default__BranchFlag : GHC.Err.Default BranchFlag :=
  GHC.Err.Build_Default _ Mk_Branched.

Definition coaxrAsmpRoles (arg_0__ : CoAxiomRule) :=
  let 'Mk_CoAxiomRule _ coaxrAsmpRoles _ _ := arg_0__ in
  coaxrAsmpRoles.

Definition coaxrName (arg_0__ : CoAxiomRule) :=
  let 'Mk_CoAxiomRule coaxrName _ _ _ := arg_0__ in
  coaxrName.

Definition coaxrProves (arg_0__ : CoAxiomRule) :=
  let 'Mk_CoAxiomRule _ _ _ coaxrProves := arg_0__ in
  coaxrProves.

Definition coaxrRole (arg_0__ : CoAxiomRule) :=
  let 'Mk_CoAxiomRule _ _ coaxrRole _ := arg_0__ in
  coaxrRole.

Definition cab_cvs (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ _ cab_cvs _ _ _ _ := arg_0__ in
  cab_cvs.

Definition cab_incomps (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ _ _ _ _ _ cab_incomps := arg_0__ in
  cab_incomps.

Definition cab_lhs (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ _ _ _ cab_lhs _ _ := arg_0__ in
  cab_lhs.

Definition cab_loc (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch cab_loc _ _ _ _ _ _ := arg_0__ in
  cab_loc.

Definition cab_rhs (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ _ _ _ _ cab_rhs _ := arg_0__ in
  cab_rhs.

Definition cab_roles (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ _ _ cab_roles _ _ _ := arg_0__ in
  cab_roles.

Definition cab_tvs (arg_0__ : CoAxBranch) :=
  let 'Mk_CoAxBranch _ cab_tvs _ _ _ _ _ := arg_0__ in
  cab_tvs.

Definition sfInteractInert (arg_0__ : BuiltInSynFamily) :=
  let 'Mk_BuiltInSynFamily _ _ sfInteractInert := arg_0__ in
  sfInteractInert.

Definition sfInteractTop (arg_0__ : BuiltInSynFamily) :=
  let 'Mk_BuiltInSynFamily _ sfInteractTop _ := arg_0__ in
  sfInteractTop.

Definition sfMatchFam (arg_0__ : BuiltInSynFamily) :=
  let 'Mk_BuiltInSynFamily sfMatchFam _ _ := arg_0__ in
  sfMatchFam.

Definition unMkBranches {br} (arg_0__ : Branches br) :=
  let 'MkBranches unMkBranches := arg_0__ in
  unMkBranches.

Definition co_ax_branches {br} (arg_0__ : CoAxiom br) :=
  let 'CoAxiom _ _ _ _ co_ax_branches _ := arg_0__ in
  co_ax_branches.

Definition co_ax_implicit {br} (arg_0__ : CoAxiom br) :=
  let 'CoAxiom _ _ _ _ _ co_ax_implicit := arg_0__ in
  co_ax_implicit.

Definition co_ax_name {br} (arg_0__ : CoAxiom br) :=
  let 'CoAxiom _ co_ax_name _ _ _ _ := arg_0__ in
  co_ax_name.

Definition co_ax_role {br} (arg_0__ : CoAxiom br) :=
  let 'CoAxiom _ _ co_ax_role _ _ _ := arg_0__ in
  co_ax_role.

Definition co_ax_tc {br} (arg_0__ : CoAxiom br) :=
  let 'CoAxiom _ _ _ co_ax_tc _ _ := arg_0__ in
  co_ax_tc.

Definition co_ax_unique {br} (arg_0__ : CoAxiom br) :=
  let 'CoAxiom co_ax_unique _ _ _ _ _ := arg_0__ in
  co_ax_unique.

Inductive NormaliseStepResult ev : Type
  := NS_Done : NormaliseStepResult ev
  |  NS_Abort : NormaliseStepResult ev
  |  NS_Step : RecTcChecker -> Type_ -> ev -> NormaliseStepResult ev.

Definition NormaliseStepper ev :=
  (RecTcChecker -> TyCon -> list Type_ -> NormaliseStepResult ev)%type.

Definition LiftCoEnv :=
  (VarEnv Coercion)%type.

Inductive LiftingContext : Type := LC : TCvSubst -> LiftCoEnv -> LiftingContext.

Arguments NS_Done {_}.

Arguments NS_Abort {_}.

Arguments NS_Step {_} _ _ _.

Definition InterestingVarFun :=
  (Var -> bool)%type.

Definition FV :=
  (InterestingVarFun ->
   VarSet -> (list Var * VarSet)%type -> (list Var * VarSet)%type)%type.

Inductive TyThing : Type
  := AnId : Id -> TyThing
  |  AConLike : ConLike.ConLike -> TyThing
  |  ATyCon : TyCon -> TyThing
  |  ACoAxiom : (CoAxiom Branched) -> TyThing.

Inductive TyLit : Type
  := NumTyLit : GHC.Num.Integer -> TyLit
  |  StrTyLit : FastString.FastString -> TyLit.

Inductive CoercionN__raw : Type :=.

Reserved Notation "'CoercionN'".

Inductive KindCoercion__raw : Type :=.

Reserved Notation "'KindCoercion'".

Inductive KindOrType__raw : Type :=.

Reserved Notation "'KindOrType'".

Inductive Coercion : Type
  := Refl : Role -> Type_ -> Coercion
  |  TyConAppCo : Role -> TyCon -> list Coercion -> Coercion
  |  AppCo : Coercion -> CoercionN -> Coercion
  |  ForAllCo : TyVar -> KindCoercion -> Coercion -> Coercion
  |  FunCo : Role -> Coercion -> Coercion -> Coercion
  |  CoVarCo : CoVar -> Coercion
  |  AxiomInstCo : (CoAxiom Branched) -> BranchIndex -> list Coercion -> Coercion
  |  UnivCo : UnivCoProvenance -> Role -> Type_ -> Type_ -> Coercion
  |  SymCo : Coercion -> Coercion
  |  TransCo : Coercion -> Coercion -> Coercion
  |  AxiomRuleCo : CoAxiomRule -> list Coercion -> Coercion
  |  NthCo : GHC.Num.Int -> Coercion -> Coercion
  |  LRCo : BasicTypes.LeftOrRight -> CoercionN -> Coercion
  |  InstCo : Coercion -> CoercionN -> Coercion
  |  CoherenceCo : Coercion -> KindCoercion -> Coercion
  |  KindCo : Coercion -> Coercion
  |  SubCo : CoercionN -> Coercion
  |  HoleCo : CoercionHole -> Coercion
with CoercionHole : Type
  := CoercionHole : CoVar -> GHC.IORef.IORef (option Coercion) -> CoercionHole
with Type_ : Type
  := TyVarTy : Var -> Type_
  |  AppTy : Type_ -> Type_ -> Type_
  |  TyConApp : TyCon -> list KindOrType -> Type_
  |  ForAllTy : TyVarBinder -> Type_ -> Type_
  |  FunTy : Type_ -> Type_ -> Type_
  |  LitTy : TyLit -> Type_
  |  CastTy : Type_ -> KindCoercion -> Type_
  |  CoercionTy : Coercion -> Type_
with UnivCoProvenance : Type
  := UnsafeCoerceProv : UnivCoProvenance
  |  PhantomProv : KindCoercion -> UnivCoProvenance
  |  ProofIrrelProv : KindCoercion -> UnivCoProvenance
  |  PluginProv : GHC.Base.String -> UnivCoProvenance
where "'KindOrType'" := (GHC.Base.Synonym KindOrType__raw Type_%type)
and   "'CoercionN'" := (GHC.Base.Synonym CoercionN__raw Coercion%type)
and   "'KindCoercion'" := (GHC.Base.Synonym KindCoercion__raw CoercionN%type).

Definition CoercionP :=
  Coercion%type.

Definition CoercionR :=
  Coercion%type.

Definition CvSubstEnv :=
  (CoVarEnv Coercion)%type.

Definition Kind :=
  Type_%type.

Definition PredType :=
  Type_%type.

Definition ThetaType :=
  (list PredType)%type.

Definition TvSubstEnv :=
  (TyVarEnv Type_)%type.

Inductive TCvSubst : Type
  := TCvSubst : InScopeSet -> TvSubstEnv -> CvSubstEnv -> TCvSubst.

Inductive TyBinder : Type
  := Named : TyVarBinder -> TyBinder
  |  Anon : Type_ -> TyBinder.

Instance Default__UnivCoProvenance : GHC.Err.Default UnivCoProvenance :=
  GHC.Err.Build_Default _ UnsafeCoerceProv.

Definition ch_co_var (arg_0__ : CoercionHole) :=
  let 'CoercionHole ch_co_var _ := arg_0__ in
  ch_co_var.

Definition ch_ref (arg_0__ : CoercionHole) :=
  let 'CoercionHole _ ch_ref := arg_0__ in
  ch_ref.

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
  := NamedTCB : ArgFlag -> TyConBndrVis
  |  AnonTCB : TyConBndrVis.

Definition TyConBinder :=
  (TyVarBndr TyVar TyConBndrVis)%type.

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
  |  RuntimeRep : (list Type_ -> list PrimRep) -> RuntimeRepInfo
  |  VecCount : GHC.Num.Int -> RuntimeRepInfo
  |  VecElem : PrimElemRep -> RuntimeRepInfo.

Inductive Injectivity : Type
  := NotInjective : Injectivity
  |  Injective : list bool -> Injectivity.

Inductive FamTyConFlav : Type
  := DataFamilyTyCon : TyConRepName -> FamTyConFlav
  |  OpenSynFamilyTyCon : FamTyConFlav
  |  ClosedSynFamilyTyCon : (option (CoAxiom Branched)) -> FamTyConFlav
  |  AbstractClosedSynFamilyTyCon : FamTyConFlav
  |  BuiltInSynFamTyCon : BuiltInSynFamily -> FamTyConFlav.

Inductive AlgTyConRhs : Type
  := AbstractTyCon : AlgTyConRhs
  |  DataTyCon : list DataCon.DataCon -> bool -> AlgTyConRhs
  |  TupleTyCon : DataCon.DataCon -> BasicTypes.TupleSort -> AlgTyConRhs
  |  SumTyCon : list DataCon.DataCon -> AlgTyConRhs
  |  NewTyCon
   : DataCon.DataCon ->
     Type_ -> (list TyVar * Type_)%type -> CoAxiom Unbranched -> AlgTyConRhs.

Inductive AlgTyConFlav : Type
  := VanillaAlgTyCon : TyConRepName -> AlgTyConFlav
  |  UnboxedAlgTyCon : (option TyConRepName) -> AlgTyConFlav
  |  ClassTyCon : Class.Class -> TyConRepName -> AlgTyConFlav
  |  DataFamInstTyCon
   : (CoAxiom Unbranched) -> TyCon -> list Type_ -> AlgTyConFlav
with TyCon : Type
  := FunTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder -> Kind -> Kind -> BasicTypes.Arity -> TyConRepName -> TyCon
  |  AlgTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     list TyVar ->
     Kind ->
     Kind ->
     BasicTypes.Arity ->
     list Role ->
     option Core.CType ->
     bool ->
     list PredType ->
     AlgTyConRhs -> FieldLabel.FieldLabelEnv -> AlgTyConFlav -> TyCon
  |  SynonymTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     list TyVar ->
     Kind -> Kind -> BasicTypes.Arity -> list Role -> Type_ -> bool -> bool -> TyCon
  |  FamilyTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     list TyVar ->
     Kind ->
     Kind ->
     BasicTypes.Arity ->
     option Name.Name -> FamTyConFlav -> option Class.Class -> Injectivity -> TyCon
  |  PrimTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     Kind ->
     Kind -> BasicTypes.Arity -> list Role -> bool -> option TyConRepName -> TyCon
  |  PromotedDataCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     Kind ->
     Kind ->
     BasicTypes.Arity ->
     list Role -> DataCon.DataCon -> TyConRepName -> RuntimeRepInfo -> TyCon
  |  TcTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     list TyVar ->
     Kind ->
     Kind ->
     BasicTypes.Arity -> list (Name.Name * TyVar)%type -> TyConFlavour -> TyCon.

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

Inductive TypeOrdering : Type
  := TLT : TypeOrdering
  |  TEQ : TypeOrdering
  |  TEQX : TypeOrdering
  |  TGT : TypeOrdering.

Inductive TyCoMapper env m : Type
  := TyCoMapper
   : bool ->
     (env -> TyVar -> m Type_) ->
     (env -> CoVar -> m Coercion) ->
     (env -> CoercionHole -> m Coercion) ->
     (env -> TyVar -> ArgFlag -> m (env * TyVar)%type) -> TyCoMapper env m.

Inductive EqRel : Type := NomEq : EqRel |  ReprEq : EqRel.

Inductive PredTree : Type
  := ClassPred : Class.Class -> list Type_ -> PredTree
  |  EqPred : EqRel -> Type_ -> Type_ -> PredTree
  |  IrredPred : PredType -> PredTree.

Arguments TyCoMapper {_} {_} _ _ _ _ _.

Instance Default__TypeOrdering : GHC.Err.Default TypeOrdering :=
  GHC.Err.Build_Default _ TLT.

Instance Default__EqRel : GHC.Err.Default EqRel :=
  GHC.Err.Build_Default _ NomEq.

Definition tcm_covar {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'TyCoMapper _ _ tcm_covar _ _ := arg_0__ in
  tcm_covar.

Definition tcm_hole {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'TyCoMapper _ _ _ tcm_hole _ := arg_0__ in
  tcm_hole.

Definition tcm_smart {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'TyCoMapper tcm_smart _ _ _ _ := arg_0__ in
  tcm_smart.

Definition tcm_tybinder {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'TyCoMapper _ _ _ _ tcm_tybinder := arg_0__ in
  tcm_tybinder.

Definition tcm_tyvar {env} {m} (arg_0__ : TyCoMapper env m) :=
  let 'TyCoMapper _ tcm_tyvar _ _ _ := arg_0__ in
  tcm_tyvar.

Inductive TyVarBndr tyvar argf : Type
  := TvBndr : tyvar -> argf -> TyVarBndr tyvar argf.

Inductive ExportFlag : Type
  := NotExported : ExportFlag
  |  Exported : ExportFlag.

Inductive IdScope : Type
  := GlobalId : IdScope
  |  LocalId : ExportFlag -> IdScope.

Inductive Var : Type
  := TyVar : Name.Name -> GHC.Num.Int -> Kind -> Var
  |  TcTyVar : Name.Name -> GHC.Num.Int -> Kind -> Core.TcTyVarDetails -> Var
  |  Id
   : Name.Name ->
     GHC.Num.Int -> Type_ -> IdScope -> IdInfo.IdDetails -> IdInfo.IdInfo -> Var.

Definition Id :=
  Var%type.

Definition InId :=
  Id%type.

Definition InVar :=
  Var%type.

Definition JoinId :=
  Id%type.

Definition KindVar :=
  Var%type.

Definition NcId :=
  Id%type.

Definition OutId :=
  Id%type.

Definition OutVar :=
  Var%type.

Definition TKVar :=
  Var%type.

Definition TyCoVar :=
  Id%type.

Definition TyVar :=
  Var%type.

Definition InTyVar :=
  TyVar%type.

Definition OutTyVar :=
  TyVar%type.

Definition TypeVar :=
  Var%type.

Definition EvId :=
  Id%type.

Definition EvVar :=
  EvId%type.

Definition IpId :=
  EvId%type.

Definition EqVar :=
  EvId%type.

Definition DictId :=
  EvId%type.

Definition DFunId :=
  Id%type.

Definition CoVar :=
  Id%type.

Definition InCoVar :=
  CoVar%type.

Definition OutCoVar :=
  CoVar%type.

Inductive ArgFlag : Type
  := Required : ArgFlag
  |  Specified : ArgFlag
  |  Inferred : ArgFlag.

Definition TyVarBinder :=
  (TyVarBndr TyVar ArgFlag)%type.

Arguments TvBndr {_} {_} _ _.

Instance Default__ExportFlag : GHC.Err.Default ExportFlag :=
  GHC.Err.Build_Default _ NotExported.

Instance Default__IdScope : GHC.Err.Default IdScope :=
  GHC.Err.Build_Default _ GlobalId.

Instance Default__ArgFlag : GHC.Err.Default ArgFlag :=
  GHC.Err.Build_Default _ Required.

Definition idScope (arg_0__ : Var) :=
  match arg_0__ with
  | TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `idScope' has no match in constructor `TyVar' of type `Var'")
  | TcTyVar _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `idScope' has no match in constructor `TcTyVar' of type `Var'")
  | Id _ _ _ idScope _ _ => idScope
  end.

Definition id_details (arg_0__ : Var) :=
  match arg_0__ with
  | TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_details' has no match in constructor `TyVar' of type `Var'")
  | TcTyVar _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_details' has no match in constructor `TcTyVar' of type `Var'")
  | Id _ _ _ _ id_details _ => id_details
  end.

Definition id_info (arg_0__ : Var) :=
  match arg_0__ with
  | TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_info' has no match in constructor `TyVar' of type `Var'")
  | TcTyVar _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_info' has no match in constructor `TcTyVar' of type `Var'")
  | Id _ _ _ _ _ id_info => id_info
  end.

Definition realUnique (arg_0__ : Var) :=
  match arg_0__ with
  | TyVar _ realUnique _ => realUnique
  | TcTyVar _ realUnique _ _ => realUnique
  | Id _ realUnique _ _ _ _ => realUnique
  end.

Definition tc_tv_details (arg_0__ : Var) :=
  match arg_0__ with
  | TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tc_tv_details' has no match in constructor `TyVar' of type `Var'")
  | TcTyVar _ _ _ tc_tv_details => tc_tv_details
  | Id _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tc_tv_details' has no match in constructor `Id' of type `Var'")
  end.

Definition varName (arg_0__ : Var) :=
  match arg_0__ with
  | TyVar varName _ _ => varName
  | TcTyVar varName _ _ _ => varName
  | Id varName _ _ _ _ _ => varName
  end.

Definition varType (arg_0__ : Var) :=
  match arg_0__ with
  | TyVar _ _ varType => varType
  | TcTyVar _ _ varType _ => varType
  | Id _ _ varType _ _ _ => varType
  end.

Definition VarEnv :=
  UniqFM.UniqFM%type.

Definition TyVarEnv :=
  VarEnv%type.

Definition TyCoVarEnv :=
  VarEnv%type.

Definition TidyEnv :=
  (OccName.TidyOccEnv * VarEnv Var)%type%type.

Inductive InScopeSet : Type := InScope : VarSet -> GHC.Num.Int -> InScopeSet.

Inductive RnEnv2 : Type
  := RV2 : VarEnv Var -> VarEnv Var -> InScopeSet -> RnEnv2.

Definition IdEnv :=
  VarEnv%type.

Definition DVarEnv :=
  UniqDFM.UniqDFM%type.

Definition DTyVarEnv :=
  DVarEnv%type.

Definition DIdEnv :=
  DVarEnv%type.

Definition CoVarEnv :=
  VarEnv%type.

Definition envL (arg_0__ : RnEnv2) :=
  let 'RV2 envL _ _ := arg_0__ in
  envL.

Definition envR (arg_0__ : RnEnv2) :=
  let 'RV2 _ envR _ := arg_0__ in
  envR.

Definition in_scope (arg_0__ : RnEnv2) :=
  let 'RV2 _ _ in_scope := arg_0__ in
  in_scope.

Definition VarSet :=
  (UniqSet.UniqSet Var)%type.

Definition TyVarSet :=
  (UniqSet.UniqSet TyVar)%type.

Definition TyCoVarSet :=
  (UniqSet.UniqSet TyCoVar)%type.

Definition IdSet :=
  (UniqSet.UniqSet Id)%type.

Definition DVarSet :=
  (UniqDSet.UniqDSet Var)%type.

Definition DTyVarSet :=
  (UniqDSet.UniqDSet TyVar)%type.

Definition DTyCoVarSet :=
  (UniqDSet.UniqDSet TyCoVar)%type.

Definition DIdSet :=
  (UniqDSet.UniqDSet Id)%type.

Definition CoVarSet :=
  (UniqSet.UniqSet CoVar)%type.

(* The Haskell code containes partial or untranslateable code, which needs the
   following *)

Axiom missingValue : forall {a}, a.
(* Midamble *)

(* Primitive types *)
(* From TysPrim *)
Parameter addrPrimTy   : Type_.
Parameter charPrimTy   : Type_.
Parameter intPrimTy    : Type_.
Parameter wordPrimTy   : Type_.
Parameter int64PrimTy  : Type_.
Parameter word64PrimTy : Type_.
Parameter floatPrimTy  : Type_.
Parameter doublePrimTy : Type_.

(* From DataCon *)
Parameter dataConWorkId       : DataCon.DataCon -> Var.
Parameter dataConExTyVars     : DataCon.DataCon -> list TyVar.

(* From PatSyn *)
Parameter patSynExTyVars     : PatSyn.PatSyn -> list TyVar.

(* From ConLike *)
Definition conLikeExTyVars : ConLike.ConLike -> list TyVar :=
  fun arg_0__ =>
    match arg_0__ with
      | ConLike.RealDataCon dcon1 => dataConExTyVars dcon1
      | ConLike.PatSynCon psyn1 => patSynExTyVars psyn1
    end.

(* From Class *)
Parameter classTyVars : Class.Class -> list TyVar.
Parameter classMethods : Class.Class -> list Var.
Parameter classAllSelIds : Class.Class -> list Var.
Definition classArity : Class.Class -> BasicTypes.Arity :=
  fun clas => Data.Foldable.length (classTyVars clas).

(* Converted value declarations: *)

(* Translating `instance Outputable__InScopeSet' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__TyVarBndr__ArgFlag__11' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Binary__TyVarBndr' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__ArgFlag' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__ArgFlag' failed: OOPS! Cannot find information
   for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__Var' failed: OOPS! Cannot find information
   for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance NamedThing__Var' failed: OOPS! Cannot find information
   for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Uniquable__Var' failed: OOPS! Cannot find information
   for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition Eq___Var_op_zeze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.== realUnique b.

Local Definition Eq___Var_op_zsze__ : Var -> Var -> bool :=
  fun x y => negb (Eq___Var_op_zeze__ x y).

Program Instance Eq___Var : GHC.Base.Eq_ Var :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Var_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Var_op_zsze__ |}.

Local Definition Ord__Var_op_zg__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.> realUnique b.

Local Definition Ord__Var_op_zgze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.>= realUnique b.

Local Definition Ord__Var_op_zl__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.< realUnique b.

Local Definition Ord__Var_op_zlze__ : Var -> Var -> bool :=
  fun a b => realUnique a GHC.Base.<= realUnique b.

Local Definition Ord__Var_min : Var -> Var -> Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then x else y.

Local Definition Ord__Var_max : Var -> Var -> Var :=
  fun x y => if Ord__Var_op_zlze__ x y : bool then y else x.

(* Translating `instance Data__Var' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance HasOccName__Var' failed: OOPS! Cannot find information
   for class Qualified "OccName" "HasOccName" unsupported *)

(* Translating `instance Data__TyVarBndr' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__ArgFlag' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

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
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___ArgFlag_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___ArgFlag_op_zsze__ |}.

(* Translating `instance Outputable__EqRel' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Bounded__TypeOrdering' failed: OOPS! Cannot find
   information for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance Enum__TypeOrdering' failed: negative `Integer' literals
   unsupported *)

(* Skipping instance Ord__TypeOrdering *)

Local Definition Eq___TypeOrdering_op_zeze__
   : TypeOrdering -> TypeOrdering -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TLT, TLT => true
    | TEQ, TEQ => true
    | TEQX, TEQX => true
    | TGT, TGT => true
    | _, _ => false
    end.

Local Definition Eq___TypeOrdering_op_zsze__
   : TypeOrdering -> TypeOrdering -> bool :=
  fun x y => negb (Eq___TypeOrdering_op_zeze__ x y).

Program Instance Eq___TypeOrdering : GHC.Base.Eq_ TypeOrdering :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TypeOrdering_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TypeOrdering_op_zsze__ |}.

Local Definition Ord__EqRel_compare : EqRel -> EqRel -> comparison :=
  fun a b =>
    match a with
    | NomEq => match b with | NomEq => Eq | _ => Lt end
    | ReprEq => match b with | ReprEq => Eq | _ => Gt end
    end.

Local Definition Ord__EqRel_op_zl__ : EqRel -> EqRel -> bool :=
  fun a b =>
    match a with
    | NomEq => match b with | NomEq => false | _ => true end
    | ReprEq => match b with | ReprEq => false | _ => false end
    end.

Local Definition Ord__EqRel_op_zlze__ : EqRel -> EqRel -> bool :=
  fun a b => negb (Ord__EqRel_op_zl__ b a).

Local Definition Ord__EqRel_min : EqRel -> EqRel -> EqRel :=
  fun x y => if Ord__EqRel_op_zlze__ x y : bool then x else y.

Local Definition Ord__EqRel_max : EqRel -> EqRel -> EqRel :=
  fun x y => if Ord__EqRel_op_zlze__ x y : bool then y else x.

Local Definition Ord__EqRel_op_zgze__ : EqRel -> EqRel -> bool :=
  fun a b => negb (Ord__EqRel_op_zl__ a b).

Local Definition Ord__EqRel_op_zg__ : EqRel -> EqRel -> bool :=
  fun a b => Ord__EqRel_op_zl__ b a.

Program Instance Ord__EqRel : GHC.Base.Ord EqRel :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__EqRel_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__EqRel_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__EqRel_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__EqRel_op_zgze__ ;
         GHC.Base.compare__ := Ord__EqRel_compare ;
         GHC.Base.max__ := Ord__EqRel_max ;
         GHC.Base.min__ := Ord__EqRel_min |}.

Local Definition Eq___EqRel_op_zeze__ : EqRel -> EqRel -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NomEq, NomEq => true
    | ReprEq, ReprEq => true
    | _, _ => false
    end.

Local Definition Eq___EqRel_op_zsze__ : EqRel -> EqRel -> bool :=
  fun x y => negb (Eq___EqRel_op_zeze__ x y).

Program Instance Eq___EqRel : GHC.Base.Eq_ EqRel :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___EqRel_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___EqRel_op_zsze__ |}.

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

(* Skipping instance Eq___TyConFlavour *)

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

(* Translating `instance Outputable__TCvSubst' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__TyBinder' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__UnivCoProvenance' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Data__CoercionHole' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Outputable__CoercionHole' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__Type_' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__Coercion' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__TyLit' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__TyThing' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance NamedThing__TyThing' failed: OOPS! Cannot find
   information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Data__TyBinder' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__Type_' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__UnivCoProvenance' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__Coercion' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__TyLit' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

Local Definition Ord__TyLit_compare : TyLit -> TyLit -> comparison :=
  fun a b =>
    match a with
    | NumTyLit a1 =>
        match b with
        | NumTyLit b1 => (GHC.Base.compare a1 b1)
        | _ => Lt
        end
    | StrTyLit a1 =>
        match b with
        | StrTyLit b1 => (GHC.Base.compare a1 b1)
        | _ => Gt
        end
    end.

Local Definition Ord__TyLit_op_zl__ : TyLit -> TyLit -> bool :=
  fun a b =>
    match a with
    | NumTyLit a1 =>
        match b with
        | NumTyLit b1 => (a1 GHC.Base.< b1)
        | _ => true
        end
    | StrTyLit a1 =>
        match b with
        | StrTyLit b1 => (a1 GHC.Base.< b1)
        | _ => false
        end
    end.

Local Definition Ord__TyLit_op_zlze__ : TyLit -> TyLit -> bool :=
  fun a b => negb (Ord__TyLit_op_zl__ b a).

Local Definition Ord__TyLit_min : TyLit -> TyLit -> TyLit :=
  fun x y => if Ord__TyLit_op_zlze__ x y : bool then x else y.

Local Definition Ord__TyLit_max : TyLit -> TyLit -> TyLit :=
  fun x y => if Ord__TyLit_op_zlze__ x y : bool then y else x.

Local Definition Ord__TyLit_op_zgze__ : TyLit -> TyLit -> bool :=
  fun a b => negb (Ord__TyLit_op_zl__ a b).

Local Definition Ord__TyLit_op_zg__ : TyLit -> TyLit -> bool :=
  fun a b => Ord__TyLit_op_zl__ b a.

Program Instance Ord__TyLit : GHC.Base.Ord TyLit :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__TyLit_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__TyLit_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__TyLit_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__TyLit_op_zgze__ ;
         GHC.Base.compare__ := Ord__TyLit_compare ;
         GHC.Base.max__ := Ord__TyLit_max ;
         GHC.Base.min__ := Ord__TyLit_min |}.

Local Definition Eq___TyLit_op_zeze__ : TyLit -> TyLit -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NumTyLit a1, NumTyLit b1 => ((a1 GHC.Base.== b1))
    | StrTyLit a1, StrTyLit b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___TyLit_op_zsze__ : TyLit -> TyLit -> bool :=
  fun x y => negb (Eq___TyLit_op_zeze__ x y).

Program Instance Eq___TyLit : GHC.Base.Eq_ TyLit :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TyLit_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TyLit_op_zsze__ |}.

(* Translating `instance Outputable__LiftingContext' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Data__CoAxiomRule' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Uniquable__CoAxiomRule' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

Local Definition Eq___CoAxiomRule_op_zeze__
   : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => coaxrName x GHC.Base.== coaxrName y.

Local Definition Eq___CoAxiomRule_op_zsze__
   : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => negb (Eq___CoAxiomRule_op_zeze__ x y).

Program Instance Eq___CoAxiomRule : GHC.Base.Eq_ CoAxiomRule :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___CoAxiomRule_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___CoAxiomRule_op_zsze__ |}.

Local Definition Ord__CoAxiomRule_compare
   : CoAxiomRule -> CoAxiomRule -> comparison :=
  fun x y => GHC.Base.compare (coaxrName x) (coaxrName y).

Local Definition Ord__CoAxiomRule_op_zg__
   : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => Ord__CoAxiomRule_compare x y GHC.Base.== Gt.

Local Definition Ord__CoAxiomRule_op_zgze__
   : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => Ord__CoAxiomRule_compare x y GHC.Base./= Lt.

Local Definition Ord__CoAxiomRule_op_zl__
   : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => Ord__CoAxiomRule_compare x y GHC.Base.== Lt.

Local Definition Ord__CoAxiomRule_op_zlze__
   : CoAxiomRule -> CoAxiomRule -> bool :=
  fun x y => Ord__CoAxiomRule_compare x y GHC.Base./= Gt.

Local Definition Ord__CoAxiomRule_max
   : CoAxiomRule -> CoAxiomRule -> CoAxiomRule :=
  fun x y => if Ord__CoAxiomRule_op_zlze__ x y : bool then y else x.

Local Definition Ord__CoAxiomRule_min
   : CoAxiomRule -> CoAxiomRule -> CoAxiomRule :=
  fun x y => if Ord__CoAxiomRule_op_zlze__ x y : bool then x else y.

Program Instance Ord__CoAxiomRule : GHC.Base.Ord CoAxiomRule :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__CoAxiomRule_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__CoAxiomRule_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__CoAxiomRule_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__CoAxiomRule_op_zgze__ ;
         GHC.Base.compare__ := Ord__CoAxiomRule_compare ;
         GHC.Base.max__ := Ord__CoAxiomRule_max ;
         GHC.Base.min__ := Ord__CoAxiomRule_min |}.

(* Translating `instance Outputable__CoAxiomRule' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

Local Definition Eq___CoAxiom_op_zeze__ {inst_br}
   : (CoAxiom inst_br) -> (CoAxiom inst_br) -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

Local Definition Eq___CoAxiom_op_zsze__ {inst_br}
   : (CoAxiom inst_br) -> (CoAxiom inst_br) -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

Program Instance Eq___CoAxiom {br} : GHC.Base.Eq_ (CoAxiom br) :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___CoAxiom_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___CoAxiom_op_zsze__ |}.

(* Translating `instance Uniquable__CoAxiom' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Outputable__CoAxiom' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance NamedThing__CoAxiom' failed: OOPS! Cannot find
   information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Data__CoAxiom' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Outputable__CoAxBranch' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__Role' failed: OOPS! Cannot find information
   for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Binary__Role' failed: OOPS! Cannot find information for
   class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Data__CoAxBranch' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__Role' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Skipping instance Ord__Role *)

Local Definition Eq___Role_op_zeze__ : Role -> Role -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Nominal, Nominal => true
    | Representational, Representational => true
    | Phantom, Phantom => true
    | _, _ => false
    end.

Local Definition Eq___Role_op_zsze__ : Role -> Role -> bool :=
  fun x y => negb (Eq___Role_op_zeze__ x y).

Program Instance Eq___Role : GHC.Base.Eq_ Role :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Role_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Role_op_zsze__ |}.

Definition allDVarSet : (Var -> bool) -> DVarSet -> bool :=
  UniqDFM.allUDFM.

Definition allVarSet : (Var -> bool) -> VarSet -> bool :=
  UniqSet.uniqSetAll.

Definition anyDVarSet : (Var -> bool) -> DVarSet -> bool :=
  UniqDFM.anyUDFM.

Definition anyVarSet : (Var -> bool) -> VarSet -> bool :=
  UniqSet.uniqSetAny.

Definition dVarSetElems : DVarSet -> list Var :=
  UniqDSet.uniqDSetToList.

Definition dVarSetIntersectVarSet : DVarSet -> VarSet -> DVarSet :=
  UniqDSet.uniqDSetIntersectUniqSet.

Definition dVarSetMinusVarSet : DVarSet -> VarSet -> DVarSet :=
  UniqDSet.uniqDSetMinusUniqSet.

Definition dVarSetToVarSet : DVarSet -> VarSet :=
  UniqSet.unsafeUFMToUniqSet GHC.Base.∘ UniqDFM.udfmToUfm.

Definition delDVarSet : DVarSet -> Var -> DVarSet :=
  UniqDSet.delOneFromUniqDSet.

Definition delDVarSetList : DVarSet -> list Var -> DVarSet :=
  UniqDSet.delListFromUniqDSet.

Definition delVarSet : VarSet -> Var -> VarSet :=
  UniqSet.delOneFromUniqSet.

Definition delVarSetByKey : VarSet -> Unique.Unique -> VarSet :=
  UniqSet.delOneFromUniqSet_Directly.

Definition delVarSetList : VarSet -> list Var -> VarSet :=
  UniqSet.delListFromUniqSet.

Definition disjointDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => UniqDFM.disjointUDFM s1 s2.

Definition intersectsDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => negb (disjointDVarSet s1 s2).

Definition disjointVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => UniqFM.disjointUFM (UniqSet.getUniqSet s1) (UniqSet.getUniqSet s2).

Definition intersectsVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => negb (disjointVarSet s1 s2).

Definition elemDVarSet : Var -> DVarSet -> bool :=
  UniqDSet.elementOfUniqDSet.

Definition elemVarSet : Var -> VarSet -> bool :=
  UniqSet.elementOfUniqSet.

Definition elemVarSetByKey : Unique.Unique -> VarSet -> bool :=
  UniqSet.elemUniqSet_Directly.

Definition emptyDVarSet : DVarSet :=
  UniqDSet.emptyUniqDSet.

Definition emptyVarSet : VarSet :=
  UniqSet.emptyUniqSet.

Definition extendDVarSet : DVarSet -> Var -> DVarSet :=
  UniqDSet.addOneToUniqDSet.

Definition extendDVarSetList : DVarSet -> list Var -> DVarSet :=
  UniqDSet.addListToUniqDSet.

Definition extendVarSet : VarSet -> Var -> VarSet :=
  UniqSet.addOneToUniqSet.

Definition extendVarSetList : VarSet -> list Var -> VarSet :=
  UniqSet.addListToUniqSet.

Definition filterDVarSet : (Var -> bool) -> DVarSet -> DVarSet :=
  UniqDSet.filterUniqDSet.

Definition filterVarSet : (Var -> bool) -> VarSet -> VarSet :=
  UniqSet.filterUniqSet.

Definition foldDVarSet {a} : (Var -> a -> a) -> a -> DVarSet -> a :=
  UniqDSet.foldUniqDSet.

Definition intersectDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.intersectUniqDSets.

Definition intersectVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.intersectUniqSets.

Definition isEmptyDVarSet : DVarSet -> bool :=
  UniqDSet.isEmptyUniqDSet.

Definition isEmptyVarSet : VarSet -> bool :=
  UniqSet.isEmptyUniqSet.

Definition lookupVarSet : VarSet -> Var -> option Var :=
  UniqSet.lookupUniqSet.

Definition lookupVarSetByName : VarSet -> Name.Name -> option Var :=
  UniqSet.lookupUniqSet.

Definition lookupVarSet_Directly : VarSet -> Unique.Unique -> option Var :=
  UniqSet.lookupUniqSet_Directly.

Definition mapVarSet {b} {a} `{Unique.Uniquable b}
   : (a -> b) -> UniqSet.UniqSet a -> UniqSet.UniqSet b :=
  UniqSet.mapUniqSet.

Definition minusDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.minusUniqDSet.

Definition subDVarSet : DVarSet -> DVarSet -> bool :=
  fun s1 s2 => isEmptyDVarSet (minusDVarSet s1 s2).

Definition minusVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.minusUniqSet.

Definition subVarSet : VarSet -> VarSet -> bool :=
  fun s1 s2 => isEmptyVarSet (minusVarSet s1 s2).

Definition fixVarSet : (VarSet -> VarSet) -> VarSet -> VarSet :=
  fix fixVarSet fn vars
        := let new_vars := fn vars in
           if subVarSet new_vars vars : bool then vars else
           fixVarSet fn new_vars.

Definition mkDVarSet : list Var -> DVarSet :=
  UniqDSet.mkUniqDSet.

Definition mkVarSet : list Var -> VarSet :=
  UniqSet.mkUniqSet.

Definition partitionDVarSet
   : (Var -> bool) -> DVarSet -> (DVarSet * DVarSet)%type :=
  UniqDSet.partitionUniqDSet.

Definition partitionVarSet
   : (Var -> bool) -> VarSet -> (VarSet * VarSet)%type :=
  UniqSet.partitionUniqSet.

Definition pluralVarSet : VarSet -> GHC.Base.String :=
  UniqFM.pluralUFM GHC.Base.∘ UniqSet.getUniqSet.

Definition pprVarSet
   : VarSet -> (list Var -> GHC.Base.String) -> GHC.Base.String :=
  UniqFM.pprUFM GHC.Base.∘ UniqSet.getUniqSet.

Definition seqDVarSet : DVarSet -> unit :=
  fun s => tt.

Definition seqVarSet : VarSet -> unit :=
  fun s => tt.

Definition sizeDVarSet : DVarSet -> GHC.Num.Int :=
  UniqDSet.sizeUniqDSet.

Definition sizeVarSet : VarSet -> GHC.Num.Int :=
  UniqSet.sizeUniqSet.

Definition unionDVarSet : DVarSet -> DVarSet -> DVarSet :=
  UniqDSet.unionUniqDSets.

Definition transCloDVarSet : (DVarSet -> DVarSet) -> DVarSet -> DVarSet :=
  fun fn seeds =>
    let go : DVarSet -> DVarSet -> DVarSet :=
      fix go acc candidates
            := let new_vs := minusDVarSet (fn candidates) acc in
               if isEmptyDVarSet new_vs : bool then acc else
               go (unionDVarSet acc new_vs) new_vs in
    go seeds seeds.

Definition mapUnionDVarSet {a} : (a -> DVarSet) -> list a -> DVarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionDVarSet GHC.Base.∘ get_set) emptyDVarSet xs.

Definition unionDVarSets : list DVarSet -> DVarSet :=
  UniqDSet.unionManyUniqDSets.

Definition unionVarSet : VarSet -> VarSet -> VarSet :=
  UniqSet.unionUniqSets.

Definition transCloVarSet : (VarSet -> VarSet) -> VarSet -> VarSet :=
  fun fn seeds =>
    let go : VarSet -> VarSet -> VarSet :=
      fix go acc candidates
            := let new_vs := minusVarSet (fn candidates) acc in
               if isEmptyVarSet new_vs : bool then acc else
               go (unionVarSet acc new_vs) new_vs in
    go seeds seeds.

Definition mapUnionVarSet {a} : (a -> VarSet) -> list a -> VarSet :=
  fun get_set xs =>
    Data.Foldable.foldr (unionVarSet GHC.Base.∘ get_set) emptyVarSet xs.

Definition unionVarSets : list VarSet -> VarSet :=
  UniqSet.unionManyUniqSets.

Definition unitDVarSet : Var -> DVarSet :=
  UniqDSet.unitUniqDSet.

Definition unitVarSet : Var -> VarSet :=
  UniqSet.unitUniqSet.

Definition alterDVarEnv {a}
   : (option a -> option a) -> DVarEnv a -> Var -> DVarEnv a :=
  UniqDFM.alterUDFM.

Definition alterVarEnv {a}
   : (option a -> option a) -> VarEnv a -> Var -> VarEnv a :=
  UniqFM.alterUFM.

Definition anyDVarEnv {a} : (a -> bool) -> DVarEnv a -> bool :=
  UniqDFM.anyUDFM.

Definition dVarEnvElts {a} : DVarEnv a -> list a :=
  UniqDFM.eltsUDFM.

Definition delDVarEnv {a} : DVarEnv a -> Var -> DVarEnv a :=
  UniqDFM.delFromUDFM.

Definition delDVarEnvList {a} : DVarEnv a -> list Var -> DVarEnv a :=
  UniqDFM.delListFromUDFM.

Definition delInScopeSet : InScopeSet -> Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, v => InScope (delVarSet in_scope v) n
    end.

Definition delVarEnv {a} : VarEnv a -> Var -> VarEnv a :=
  UniqFM.delFromUFM.

Definition delVarEnvList {a} : VarEnv a -> list Var -> VarEnv a :=
  UniqFM.delListFromUFM.

Definition delVarEnv_Directly {a} : VarEnv a -> Unique.Unique -> VarEnv a :=
  UniqFM.delFromUFM_Directly.

Definition disjointVarEnv {a} : VarEnv a -> VarEnv a -> bool :=
  UniqFM.disjointUFM.

Definition elemDVarEnv {a} : Var -> DVarEnv a -> bool :=
  UniqDFM.elemUDFM.

Definition elemInScopeSet : Var -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, InScope in_scope _ => elemVarSet v in_scope
    end.

Definition rnInScope : Var -> RnEnv2 -> bool :=
  fun x env => elemInScopeSet x (in_scope env).

Definition elemVarEnv {a} : Var -> VarEnv a -> bool :=
  UniqFM.elemUFM.

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

Definition elemVarEnvByKey {a} : Unique.Unique -> VarEnv a -> bool :=
  UniqFM.elemUFM_Directly.

Definition emptyDVarEnv {a} : DVarEnv a :=
  UniqDFM.emptyUDFM.

Definition emptyInScopeSet : InScopeSet :=
  InScope emptyVarSet #1.

Definition emptyVarEnv {a} : VarEnv a :=
  UniqFM.emptyUFM.

Definition mkRnEnv2 : InScopeSet -> RnEnv2 :=
  fun vars => RV2 emptyVarEnv emptyVarEnv vars.

Definition nukeRnEnvL : RnEnv2 -> RnEnv2 :=
  fun env =>
    let 'RV2 envL_0__ envR_1__ in_scope_2__ := env in
    RV2 emptyVarEnv envR_1__ in_scope_2__.

Definition nukeRnEnvR : RnEnv2 -> RnEnv2 :=
  fun env =>
    let 'RV2 envL_0__ envR_1__ in_scope_2__ := env in
    RV2 envL_0__ emptyVarEnv in_scope_2__.

Definition emptyTidyEnv : TidyEnv :=
  pair OccName.emptyTidyOccEnv emptyVarEnv.

Definition extendDVarEnv {a} : DVarEnv a -> Var -> a -> DVarEnv a :=
  UniqDFM.addToUDFM.

Definition extendDVarEnvList {a}
   : DVarEnv a -> list (Var * a)%type -> DVarEnv a :=
  UniqDFM.addListToUDFM.

Definition extendDVarEnv_C {a}
   : (a -> a -> a) -> DVarEnv a -> Var -> a -> DVarEnv a :=
  UniqDFM.addToUDFM_C.

Definition extendInScopeSet : InScopeSet -> Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, v => InScope (extendVarSet in_scope v) (n GHC.Num.+ #1)
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

Definition extendInScopeSetList : InScopeSet -> list Var -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, vs =>
        InScope (Data.Foldable.foldl (fun s v => extendVarSet s v) in_scope vs) (n
                                                                                 GHC.Num.+
                                                                                 Data.Foldable.length vs)
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

Definition extendInScopeSetSet : InScopeSet -> VarSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope n, vs =>
        InScope (unionVarSet in_scope vs) (n GHC.Num.+ UniqSet.sizeUniqSet vs)
    end.

Definition addRnInScopeSet : RnEnv2 -> VarSet -> RnEnv2 :=
  fun env vs =>
    if isEmptyVarSet vs : bool then env else
    let 'RV2 envL_0__ envR_1__ in_scope_2__ := env in
    RV2 envL_0__ envR_1__ (extendInScopeSetSet (in_scope env) vs).

Definition extendVarEnv {a} : VarEnv a -> Var -> a -> VarEnv a :=
  UniqFM.addToUFM.

Definition extendVarEnvList {a} : VarEnv a -> list (Var * a)%type -> VarEnv a :=
  UniqFM.addListToUFM.

Definition extendVarEnv_Acc {a} {b}
   : (a -> b -> b) -> (a -> b) -> VarEnv b -> Var -> a -> VarEnv b :=
  UniqFM.addToUFM_Acc.

Definition extendVarEnv_C {a}
   : (a -> a -> a) -> VarEnv a -> Var -> a -> VarEnv a :=
  UniqFM.addToUFM_C.

Definition extendVarEnv_Directly {a}
   : VarEnv a -> Unique.Unique -> a -> VarEnv a :=
  UniqFM.addToUFM_Directly.

Definition filterDVarEnv {a} : (a -> bool) -> DVarEnv a -> DVarEnv a :=
  UniqDFM.filterUDFM.

Definition filterVarEnv {a} : (a -> bool) -> VarEnv a -> VarEnv a :=
  UniqFM.filterUFM.

Definition filterVarEnv_Directly {a}
   : (Unique.Unique -> a -> bool) -> VarEnv a -> VarEnv a :=
  UniqFM.filterUFM_Directly.

Definition restrictVarEnv {a} : VarEnv a -> VarSet -> VarEnv a :=
  fun env vs =>
    let keep :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | u, _ => elemVarSetByKey u vs
        end in
    filterVarEnv_Directly keep env.

Definition foldDVarEnv {a} {b} : (a -> b -> b) -> b -> DVarEnv a -> b :=
  UniqDFM.foldUDFM.

Definition getInScopeVars : InScopeSet -> VarSet :=
  fun arg_0__ => let 'InScope vs _ := arg_0__ in vs.

Definition isEmptyDVarEnv {a} : DVarEnv a -> bool :=
  UniqDFM.isNullUDFM.

Definition isEmptyVarEnv {a} : VarEnv a -> bool :=
  UniqFM.isNullUFM.

Definition intersectsVarEnv {a} : VarEnv a -> VarEnv a -> bool :=
  fun e1 e2 => negb (isEmptyVarEnv (UniqFM.intersectUFM e1 e2)).

Definition lookupDVarEnv {a} : DVarEnv a -> Var -> option a :=
  UniqDFM.lookupUDFM.

Definition modifyDVarEnv {a} : (a -> a) -> DVarEnv a -> Var -> DVarEnv a :=
  fun mangle_fn env key =>
    match (lookupDVarEnv env key) with
    | None => env
    | Some xx => extendDVarEnv env key (mangle_fn xx)
    end.

Definition lookupInScope : InScopeSet -> Var -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope _, v => lookupVarSet in_scope v
    end.

Definition lookupRnInScope : RnEnv2 -> Var -> Var :=
  fun env v => Maybes.orElse (lookupInScope (in_scope env) v) v.

Definition lookupInScope_Directly : InScopeSet -> Unique.Unique -> option Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope in_scope _, uniq => lookupVarSet_Directly in_scope uniq
    end.

Definition lookupVarEnv {a} : VarEnv a -> Var -> option a :=
  UniqFM.lookupUFM.

Definition lookupVarEnv_NF {a} : VarEnv a -> Var -> a :=
  fun env id =>
    match lookupVarEnv env id with
    | Some xx => xx
    | None => Panic.panic (GHC.Base.hs_string__ "lookupVarEnv_NF: Nothing")
    end.

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

Definition modifyVarEnv {a} : (a -> a) -> VarEnv a -> Var -> VarEnv a :=
  fun mangle_fn env key =>
    match (lookupVarEnv env key) with
    | None => env
    | Some xx => extendVarEnv env key (mangle_fn xx)
    end.

Definition lookupVarEnv_Directly {a} : VarEnv a -> Unique.Unique -> option a :=
  UniqFM.lookupUFM_Directly.

Definition lookupWithDefaultVarEnv {a} : VarEnv a -> a -> Var -> a :=
  UniqFM.lookupWithDefaultUFM.

Definition mapDVarEnv {a} {b} : (a -> b) -> DVarEnv a -> DVarEnv b :=
  UniqDFM.mapUDFM.

Definition mapVarEnv {a} {b} : (a -> b) -> VarEnv a -> VarEnv b :=
  UniqFM.mapUFM.

Definition minusDVarEnv {a} {a'} : DVarEnv a -> DVarEnv a' -> DVarEnv a :=
  UniqDFM.minusUDFM.

Definition minusVarEnv {a} {b} : VarEnv a -> VarEnv b -> VarEnv a :=
  UniqFM.minusUFM.

Definition mkDVarEnv {a} : list (Var * a)%type -> DVarEnv a :=
  UniqDFM.listToUDFM.

Definition mkInScopeSet : VarSet -> InScopeSet :=
  fun in_scope => InScope in_scope #1.

Definition mkVarEnv {a} : list (Var * a)%type -> VarEnv a :=
  UniqFM.listToUFM.

Definition zipVarEnv {a} : list Var -> list a -> VarEnv a :=
  fun tyvars tys =>
    mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipVarEnv") tyvars tys).

Definition mkVarEnv_Directly {a} : list (Unique.Unique * a)%type -> VarEnv a :=
  UniqFM.listToUFM_Directly.

Definition modifyVarEnv_Directly {a}
   : (a -> a) -> UniqFM.UniqFM a -> Unique.Unique -> UniqFM.UniqFM a :=
  fun mangle_fn env key =>
    match (UniqFM.lookupUFM_Directly env key) with
    | None => env
    | Some xx => UniqFM.addToUFM_Directly env key (mangle_fn xx)
    end.

Definition partitionDVarEnv {a}
   : (a -> bool) -> DVarEnv a -> (DVarEnv a * DVarEnv a)%type :=
  UniqDFM.partitionUDFM.

Definition partitionVarEnv {a}
   : (a -> bool) -> VarEnv a -> (VarEnv a * VarEnv a)%type :=
  UniqFM.partitionUFM.

Definition plusDVarEnv {a} : DVarEnv a -> DVarEnv a -> DVarEnv a :=
  UniqDFM.plusUDFM.

Definition plusDVarEnv_C {a}
   : (a -> a -> a) -> DVarEnv a -> DVarEnv a -> DVarEnv a :=
  UniqDFM.plusUDFM_C.

Definition plusMaybeVarEnv_C {a}
   : (a -> a -> option a) -> VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusMaybeUFM_C.

Definition plusVarEnv {a} : VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM.

Definition plusVarEnvList {a} : list (VarEnv a) -> VarEnv a :=
  UniqFM.plusUFMList.

Definition plusVarEnv_C {a}
   : (a -> a -> a) -> VarEnv a -> VarEnv a -> VarEnv a :=
  UniqFM.plusUFM_C.

Definition plusVarEnv_CD {a}
   : (a -> a -> a) -> VarEnv a -> a -> VarEnv a -> a -> VarEnv a :=
  UniqFM.plusUFM_CD.

Definition rnEnvL : RnEnv2 -> VarEnv Var :=
  envL.

Definition rnEnvR : RnEnv2 -> VarEnv Var :=
  envR.

Definition rnInScopeSet : RnEnv2 -> InScopeSet :=
  in_scope.

Definition rnSwap : RnEnv2 -> RnEnv2 :=
  fun arg_0__ => let 'RV2 envL envR in_scope := arg_0__ in RV2 envR envL in_scope.

Definition unionInScope : InScopeSet -> InScopeSet -> InScopeSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope s1 _, InScope s2 n2 => InScope (unionVarSet s1 s2) n2
    end.

Definition unitDVarEnv {a} : Var -> a -> DVarEnv a :=
  UniqDFM.unitUDFM.

Definition unitVarEnv {a} : Var -> a -> VarEnv a :=
  UniqFM.unitUFM.

Definition varSetInScope : VarSet -> InScopeSet -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | vars, InScope s1 _ => subVarSet vars s1
    end.

Definition binderArgFlag {tv} {argf} : TyVarBndr tv argf -> argf :=
  fun arg_0__ => let 'TvBndr _ argf := arg_0__ in argf.

Definition binderVar {tv} {argf} : TyVarBndr tv argf -> tv :=
  fun arg_0__ => let 'TvBndr v _ := arg_0__ in v.

Definition binderVars {tv} {argf} : list (TyVarBndr tv argf) -> list tv :=
  fun tvbs => GHC.Base.map binderVar tvbs.

Definition globaliseId : Id -> Id :=
  fun id =>
    match id with
    | TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | TcTyVar _ _ _ _ =>
        GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
    id_info_5__ =>
        Id varName_0__ realUnique_1__ varType_2__ GlobalId id_details_4__ id_info_5__
    end.

Definition idDetails : Id -> IdInfo.IdDetails :=
  fun arg_0__ =>
    match arg_0__ with
    | Id _ _ _ _ details _ => details
    | other =>
        Panic.panicStr (GHC.Base.hs_string__ "idDetails") (Panic.noString other)
    end.

Definition idInfo `{Util.HasDebugCallStack} : Id -> IdInfo.IdInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | Id _ _ _ _ _ info => info
    | other => Panic.panicStr (GHC.Base.hs_string__ "idInfo") (Panic.noString other)
    end.

Definition isCoVar : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Id _ _ _ _ details _ => IdInfo.isCoVarDetails details
    | _ => false
    end.

Definition isExportedId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Id _ _ _ GlobalId _ _ => true
    | Id _ _ _ (LocalId Exported) _ _ => true
    | _ => false
    end.

Definition isGlobalId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Id _ _ _ GlobalId _ _ => true
    | _ => false
    end.

Definition isLocalVar : Var -> bool :=
  fun v => negb (isGlobalId v).

Definition mustHaveLocalBinding : Var -> bool :=
  fun var => isLocalVar var.

Definition isId : Var -> bool :=
  fun arg_0__ => match arg_0__ with | Id _ _ _ _ _ _ => true | _ => false end.

Definition isLocalId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Id _ _ _ (LocalId _) _ _ => true
    | _ => false
    end.

Definition setIdNotExported : Id -> Id :=
  fun id =>
    if andb Util.debugIsOn (negb (isLocalId id)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Var.hs")
          #591)
    else match id with
         | TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
         | TcTyVar _ _ _ _ =>
             GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
         | Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
         id_info_5__ =>
             Id varName_0__ realUnique_1__ varType_2__ (LocalId NotExported) id_details_4__
                id_info_5__
         end.

Definition isNonCoVarId : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Id _ _ _ _ details _ => negb (IdInfo.isCoVarDetails details)
    | _ => false
    end.

Definition isTcTyVar : Var -> bool :=
  fun arg_0__ => match arg_0__ with | TcTyVar _ _ _ _ => true | _ => false end.

Definition isTyVar : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | TyVar _ _ _ => true
    | TcTyVar _ _ _ _ => true
    | _ => false
    end.

Definition isTyCoVar : Var -> bool :=
  fun v => orb (isTyVar v) (isCoVar v).

Definition isVisibleArgFlag : ArgFlag -> bool :=
  fun arg_0__ => match arg_0__ with | Required => true | _ => false end.

Definition isInvisibleArgFlag : ArgFlag -> bool :=
  negb GHC.Base.∘ isVisibleArgFlag.

Definition lazySetIdInfo : Id -> IdInfo.IdInfo -> Var :=
  fun id info =>
    match id with
    | TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | TcTyVar _ _ _ _ =>
        GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
    id_info_5__ =>
        Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__ info
    end.

Definition mkTcTyVar : Name.Name -> Kind -> Core.TcTyVarDetails -> TyVar :=
  fun name kind details =>
    TcTyVar name (Unique.getKey (Name.nameUnique name)) kind details.

Definition mkTyVar : Name.Name -> Kind -> TyVar :=
  fun name kind => TyVar name (Unique.getKey (Name.nameUnique name)) kind.

Definition mkTyVarBinder : ArgFlag -> Var -> TyVarBinder :=
  fun vis var => TvBndr var vis.

Definition mkTyVarBinders : ArgFlag -> list TyVar -> list TyVarBinder :=
  fun vis => GHC.Base.map (mkTyVarBinder vis).

Definition mk_id
   : Name.Name -> Type_ -> IdScope -> IdInfo.IdDetails -> IdInfo.IdInfo -> Id :=
  fun name ty scope details info =>
    Id name (Unique.getKey (Name.nameUnique name)) ty scope details info.

Definition mkLocalVar
   : IdInfo.IdDetails -> Name.Name -> Type_ -> IdInfo.IdInfo -> Id :=
  fun details name ty info => mk_id name ty (LocalId NotExported) details info.

Definition mkGlobalVar
   : IdInfo.IdDetails -> Name.Name -> Type_ -> IdInfo.IdInfo -> Id :=
  fun details name ty info => mk_id name ty GlobalId details info.

Definition mkExportedLocalVar
   : IdInfo.IdDetails -> Name.Name -> Type_ -> IdInfo.IdInfo -> Id :=
  fun details name ty info => mk_id name ty (LocalId Exported) details info.

Definition mkCoVar : Name.Name -> Type_ -> CoVar :=
  fun name ty =>
    mk_id name ty (LocalId NotExported) IdInfo.coVarDetails IdInfo.vanillaIdInfo.

Definition ppr_id_scope : IdScope -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | GlobalId => id (GHC.Base.hs_string__ "gid")
    | LocalId Exported => id (GHC.Base.hs_string__ "lidx")
    | LocalId NotExported => id (GHC.Base.hs_string__ "lid")
    end.

Definition ppr_debug : Var -> Outputable.PprStyle -> GHC.Base.String :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TyVar _ _ _, sty =>
        if Outputable.debugStyle sty : bool
        then id (id (GHC.Base.hs_string__ "tv")) else
        Panic.someSDoc
    | TcTyVar _ _ _ d, sty =>
        if orb (Outputable.dumpStyle sty) (Outputable.debugStyle sty) : bool
        then id (TcType.pprTcTyVarDetails d) else
        Panic.someSDoc
    | Id _ _ _ s d _, sty =>
        if Outputable.debugStyle sty : bool
        then id (GHC.Base.mappend (ppr_id_scope s) (IdInfo.pprIdDetails d)) else
        Panic.someSDoc
    end.

Definition sameVis : ArgFlag -> ArgFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Required, Required => true
    | Required, _ => false
    | _, Required => false
    | _, _ => true
    end.

Definition setIdDetails : Id -> IdInfo.IdDetails -> Id :=
  fun id details =>
    match id with
    | TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | TcTyVar _ _ _ _ =>
        GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
    id_info_5__ =>
        Id varName_0__ realUnique_1__ varType_2__ idScope_3__ details id_info_5__
    end.

Definition setIdExported : Id -> Id :=
  fun arg_0__ =>
    match arg_0__ with
    | (Id _ _ _ (LocalId _) _ _ as id) =>
        match id with
        | TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | TcTyVar _ _ _ _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | Id varName_1__ realUnique_2__ varType_3__ idScope_4__ id_details_5__
        id_info_6__ =>
            Id varName_1__ realUnique_2__ varType_3__ (LocalId Exported) id_details_5__
               id_info_6__
        end
    | (Id _ _ _ GlobalId _ _ as id) => id
    | tv =>
        Panic.panicStr (GHC.Base.hs_string__ "setIdExported") (Panic.noString tv)
    end.

Definition setTcTyVarDetails : TyVar -> Core.TcTyVarDetails -> TyVar :=
  fun tv details =>
    match tv with
    | TyVar _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    | TcTyVar varName_0__ realUnique_1__ varType_2__ tc_tv_details_3__ =>
        TcTyVar varName_0__ realUnique_1__ varType_2__ details
    | Id _ _ _ _ _ _ => GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
    end.

Definition setTyVarKind : TyVar -> Kind -> TyVar :=
  fun tv k =>
    match tv with
    | TyVar varName_0__ realUnique_1__ varType_2__ =>
        TyVar varName_0__ realUnique_1__ k
    | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        TcTyVar varName_3__ realUnique_4__ k tc_tv_details_6__
    | Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Id varName_7__ realUnique_8__ k idScope_10__ id_details_11__ id_info_12__
    end.

Definition setVarName : Var -> Name.Name -> Var :=
  fun var new_name =>
    match var with
    | TyVar varName_0__ realUnique_1__ varType_2__ =>
        TyVar new_name (Unique.getKey (Unique.getUnique new_name)) varType_2__
    | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        TcTyVar new_name (Unique.getKey (Unique.getUnique new_name)) varType_5__
                tc_tv_details_6__
    | Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Id new_name (Unique.getKey (Unique.getUnique new_name)) varType_9__ idScope_10__
           id_details_11__ id_info_12__
    end.

Definition setTyVarName : TyVar -> Name.Name -> TyVar :=
  setVarName.

Definition setVarType : Id -> Type_ -> Id :=
  fun id ty =>
    match id with
    | TyVar varName_0__ realUnique_1__ varType_2__ =>
        TyVar varName_0__ realUnique_1__ ty
    | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        TcTyVar varName_3__ realUnique_4__ ty tc_tv_details_6__
    | Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Id varName_7__ realUnique_8__ ty idScope_10__ id_details_11__ id_info_12__
    end.

Definition setVarUnique : Var -> Unique.Unique -> Var :=
  fun var uniq =>
    match var with
    | TyVar varName_0__ realUnique_1__ varType_2__ =>
        TyVar (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq) varType_2__
    | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        TcTyVar (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq) varType_5__
                tc_tv_details_6__
    | Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Id (Name.setNameUnique (varName var) uniq) (Unique.getKey uniq) varType_9__
           idScope_10__ id_details_11__ id_info_12__
    end.

Definition setTyVarUnique : TyVar -> Unique.Unique -> TyVar :=
  setVarUnique.

Definition uniqAway' : InScopeSet -> Var -> Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | InScope set n, var =>
        let orig_unique := Unique.getUnique var in
        let fix try k
                  := let uniq := Unique.deriveUnique orig_unique (n GHC.Num.* k) in
                     let msg :=
                       GHC.Base.mappend (GHC.Base.mappend (GHC.Base.mappend (Panic.noString k) (id
                                                                             (GHC.Base.hs_string__ "tries")))
                                                          (Panic.noString var)) (Panic.noString n) in
                     if andb Util.debugIsOn (k GHC.Base.> #1000) : bool
                     then Panic.panicStr (GHC.Base.hs_string__ "uniqAway loop:") msg else
                     if elemVarSetByKey uniq set : bool then try (k GHC.Num.+ #1) else
                     if k GHC.Base.> #3 : bool
                     then Outputable.pprTraceDebug (GHC.Base.hs_string__ "uniqAway:") msg
                          setVarUnique var uniq else
                     setVarUnique var uniq in
        try #1
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

Definition tyVarKind : TyVar -> Kind :=
  varType.

Definition updateTyVarKind : (Kind -> Kind) -> TyVar -> TyVar :=
  fun update tv =>
    match tv with
    | TyVar varName_0__ realUnique_1__ varType_2__ =>
        TyVar varName_0__ realUnique_1__ (update (tyVarKind tv))
    | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        TcTyVar varName_3__ realUnique_4__ (update (tyVarKind tv)) tc_tv_details_6__
    | Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Id varName_7__ realUnique_8__ (update (tyVarKind tv)) idScope_10__
           id_details_11__ id_info_12__
    end.

Definition updateTyVarKindM {m} `{(GHC.Base.Monad m)}
   : (Kind -> m Kind) -> TyVar -> m TyVar :=
  fun update tv =>
    update (tyVarKind tv) GHC.Base.>>=
    (fun k' =>
       GHC.Base.return_ (match tv with
                         | TyVar varName_0__ realUnique_1__ varType_2__ =>
                             TyVar varName_0__ realUnique_1__ k'
                         | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
                             TcTyVar varName_3__ realUnique_4__ k' tc_tv_details_6__
                         | Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
                         id_info_12__ =>
                             Id varName_7__ realUnique_8__ k' idScope_10__ id_details_11__ id_info_12__
                         end)).

Definition binderKind {argf} : TyVarBndr TyVar argf -> Kind :=
  fun arg_0__ => let 'TvBndr tv _ := arg_0__ in tyVarKind tv.

Definition tyVarName : TyVar -> Name.Name :=
  varName.

Definition updateVarType : (Type_ -> Type_) -> Id -> Id :=
  fun f id =>
    match id with
    | TyVar varName_0__ realUnique_1__ varType_2__ =>
        TyVar varName_0__ realUnique_1__ (f (varType id))
    | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
        TcTyVar varName_3__ realUnique_4__ (f (varType id)) tc_tv_details_6__
    | Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
    id_info_12__ =>
        Id varName_7__ realUnique_8__ (f (varType id)) idScope_10__ id_details_11__
           id_info_12__
    end.

Definition updateVarTypeM {m} `{GHC.Base.Monad m}
   : (Type_ -> m Type_) -> Id -> m Id :=
  fun f id =>
    f (varType id) GHC.Base.>>=
    (fun ty' =>
       GHC.Base.return_ (match id with
                         | TyVar varName_0__ realUnique_1__ varType_2__ =>
                             TyVar varName_0__ realUnique_1__ ty'
                         | TcTyVar varName_3__ realUnique_4__ varType_5__ tc_tv_details_6__ =>
                             TcTyVar varName_3__ realUnique_4__ ty' tc_tv_details_6__
                         | Id varName_7__ realUnique_8__ varType_9__ idScope_10__ id_details_11__
                         id_info_12__ =>
                             Id varName_7__ realUnique_8__ ty' idScope_10__ id_details_11__ id_info_12__
                         end)).

Definition varUnique : Var -> Unique.Unique :=
  fun var => Unique.mkUniqueGrimily (realUnique var).

Definition nonDetCmpVar : Var -> Var -> comparison :=
  fun a b => Unique.nonDetCmpUnique (varUnique a) (varUnique b).

Local Definition Ord__Var_compare : Var -> Var -> comparison :=
  fun a b => nonDetCmpVar a b.

Program Instance Ord__Var : GHC.Base.Ord Var :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__Var_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__Var_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__Var_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__Var_op_zgze__ ;
         GHC.Base.compare__ := Ord__Var_compare ;
         GHC.Base.max__ := Ord__Var_max ;
         GHC.Base.min__ := Ord__Var_min |}.

Definition binderRelevantType_maybe : TyBinder -> option Type_ :=
  fun arg_0__ => match arg_0__ with | Named _ => None | Anon ty => Some ty end.

Definition caseBinder {a}
   : TyBinder -> (TyVarBinder -> a) -> (Type_ -> a) -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Named v, f, _ => f v
    | Anon t, _, d => d t
    end.

Definition eqRelRole : EqRel -> Role :=
  fun arg_0__ =>
    match arg_0__ with
    | NomEq => Nominal
    | ReprEq => Representational
    end.

Definition equalityTyCon : Role -> TyCon :=
  fun arg_0__ =>
    match arg_0__ with
    | Nominal => TysPrim.eqPrimTyCon
    | Representational => TysPrim.eqReprPrimTyCon
    | Phantom => TysPrim.eqPhantPrimTyCon
    end.

Definition isAnonTyBinder : TyBinder -> bool :=
  fun arg_0__ => match arg_0__ with | Named _ => false | Anon _ => true end.

Definition isCoercionTy : Type_ -> bool :=
  fun arg_0__ => match arg_0__ with | CoercionTy _ => true | _ => false end.

Definition isCoercionTy_maybe : Type_ -> option Coercion :=
  fun arg_0__ => match arg_0__ with | CoercionTy co => Some co | _ => None end.

Definition isIPClass : Class.Class -> bool :=
  fun cls => Unique.hasKey cls PrelNames.ipClassKey.

Definition isIPTyCon : TyCon -> bool :=
  fun tc => Unique.hasKey tc PrelNames.ipClassKey.

Definition isNamedTyBinder : TyBinder -> bool :=
  fun arg_0__ => match arg_0__ with | Named _ => true | Anon _ => false end.

Definition mkAnonBinder : Type_ -> TyBinder :=
  Anon.

Definition mkClassPred : Class.Class -> list Type_ -> PredType :=
  fun clas tys => TyConApp (Class.classTyCon clas) tys.

Definition mkCoercionTy : Coercion -> Type_ :=
  CoercionTy.

Definition mkHeteroPrimEqPred : Kind -> Kind -> Type_ -> Type_ -> Type_ :=
  fun k1 k2 ty1 ty2 =>
    TyConApp TysPrim.eqPrimTyCon (cons k1 (cons k2 (cons ty1 (cons ty2 nil)))).

Definition mkHeteroReprPrimEqPred : Kind -> Kind -> Type_ -> Type_ -> Type_ :=
  fun k1 k2 ty1 ty2 =>
    TyConApp TysPrim.eqReprPrimTyCon (cons k1 (cons k2 (cons ty1 (cons ty2 nil)))).

Definition mkInvForAllTy : TyVar -> Type_ -> Type_ :=
  fun tv ty =>
    if andb Util.debugIsOn (negb (isTyVar tv)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
          #1282)
    else ForAllTy (TvBndr tv Inferred) ty.

Definition mkInvForAllTys : list TyVar -> Type_ -> Type_ :=
  fun tvs ty =>
    if andb Util.debugIsOn (negb (Data.Foldable.all isTyVar tvs)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
          #1288)
    else Data.Foldable.foldr mkInvForAllTy ty tvs.

Definition mkLamType : Var -> Type_ -> Type_ :=
  fun v ty =>
    if isTyVar v : bool then ForAllTy (TvBndr v Inferred) ty else
    FunTy (varType v) ty.

Definition mkLamTypes : list Var -> Type_ -> Type_ :=
  fun vs ty => Data.Foldable.foldr mkLamType ty vs.

Definition mkNumLitTy : GHC.Num.Integer -> Type_ :=
  fun n => LitTy (NumTyLit n).

Definition mkStrLitTy : FastString.FastString -> Type_ :=
  fun s => LitTy (StrTyLit s).

Definition mkTyBinderTyConBinder
   : TyBinder ->
     SrcLoc.SrcSpan -> Unique.Unique -> OccName.OccName -> TyConBinder :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | Named (TvBndr tv argf), _, _, _ => TvBndr tv (NamedTCB argf)
    | Anon kind, loc, uniq, occ =>
        TvBndr (mkTyVar (Name.mkInternalName uniq occ loc) kind) AnonTCB
    end.

Definition nonDetCmpTc : TyCon -> TyCon -> comparison :=
  fun tc1 tc2 =>
    let u2 := tyConUnique tc2 in
    let u1 := tyConUnique tc1 in
    if andb Util.debugIsOn (negb (andb (negb (Kind.isStarKindSynonymTyCon tc1))
                                       (negb (Kind.isStarKindSynonymTyCon tc2)))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
          #2292)
    else Unique.nonDetCmpUnique u1 u2.

Definition repGetTyVar_maybe : Type_ -> option TyVar :=
  fun arg_0__ => match arg_0__ with | TyVarTy tv => Some tv | _ => None end.

Definition seqTypes : list Type_ -> unit :=
  fix seqTypes arg_0__
        := match arg_0__ with
           | nil => tt
           | cons ty tys => seqTypes tys
           end.

Definition stripCoercionTy : Type_ -> Coercion :=
  fun arg_0__ =>
    match arg_0__ with
    | CoercionTy co => co
    | ty =>
        Panic.panicStr (GHC.Base.hs_string__ "stripCoercionTy") (Panic.noString ty)
    end.

Definition tyBinderType : TyBinder -> Type_ :=
  fun arg_0__ =>
    match arg_0__ with
    | Named tvb => binderKind tvb
    | Anon ty => ty
    end.

Definition tyConAppTyConPicky_maybe : Type_ -> option TyCon :=
  fun arg_0__ =>
    match arg_0__ with
    | TyConApp tc _ => Some tc
    | FunTy _ _ => Some TysPrim.funTyCon
    | _ => None
    end.

Definition tyConBindersTyBinders : list TyConBinder -> list TyBinder :=
  let to_tyb :=
    fun arg_0__ =>
      match arg_0__ with
      | TvBndr tv (NamedTCB vis) => Named (TvBndr tv vis)
      | TvBndr tv AnonTCB => Anon (tyVarKind tv)
      end in
  GHC.Base.map to_tyb.

Definition typeLiteralKind : TyLit -> Kind :=
  fun l =>
    match l with
    | NumTyLit _ => TysWiredIn.typeNatKind
    | StrTyLit _ => TysWiredIn.typeSymbolKind
    end.

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
     list tyco -> option (list (TyVar * tyco)%type * Type_ * list tyco)%type :=
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

Definition isBuiltInSynFamTyCon_maybe : TyCon -> option BuiltInSynFamily :=
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
   : TyCon -> option (CoAxiom Branched) :=
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

Definition isDataProductTyCon_maybe : TyCon -> option DataCon.DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        let j_2__ := match rhs with | TupleTyCon con _ => Some con | _ => None end in
        match rhs with
        | DataTyCon (cons con nil) _ =>
            if Data.Foldable.null (Core.dataConExTyVars con) : bool then Some con else
            j_2__
        | _ => j_2__
        end
    | _ => None
    end.

Definition isDataSumTyCon_maybe : TyCon -> option (list DataCon.DataCon) :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _ =>
        match rhs with
        | DataTyCon cons_ _ =>
            if andb (Util.lengthExceeds cons_ #1) (Data.Foldable.all (Data.Foldable.null
                                                                      GHC.Base.∘
                                                                      Core.dataConExTyVars) cons_) : bool
            then Some cons_ else
            None
        | SumTyCon cons_ =>
            if Data.Foldable.all (Data.Foldable.null GHC.Base.∘ Core.dataConExTyVars)
               cons_ : bool
            then Some cons_ else
            None
        | _ => None
        end
    | _ => None
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

Definition mkTyConApp : TyCon -> list Type_ -> Type_ :=
  fun tycon tys =>
    let j_0__ := TyConApp tycon tys in
    if isFunTyCon tycon : bool
    then match tys with
         | cons _rep1 (cons _rep2 (cons ty1 (cons ty2 nil))) => FunTy ty1 ty2
         | _ => j_0__
         end else
    j_0__.

Definition mkAppTys : Type_ -> list Type_ -> Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | ty1, nil => ty1
    | TyConApp tc tys1, tys2 => mkTyConApp tc (Coq.Init.Datatypes.app tys1 tys2)
    | ty1, tys2 => Data.Foldable.foldl AppTy ty1 tys2
    end.

Definition mkAppTy : Type_ -> Type_ -> Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TyConApp tc tys, ty2 =>
        mkTyConApp tc (Coq.Init.Datatypes.app tys (cons ty2 nil))
    | ty1, ty2 => AppTy ty1 ty2
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

Definition isInjectiveTyCon : TyCon -> Role -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Phantom => false
    | FunTyCon _ _ _ _ _ _ _, _ => true
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _, Nominal => true
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ rhs _ _, Representational => isGenInjAlgRhs rhs
    | SynonymTyCon _ _ _ _ _ _ _ _ _ _ _, _ => false
    | FamilyTyCon _ _ _ _ _ _ _ _ (DataFamilyTyCon _) _ _, Nominal => true
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ (Injective inj), Nominal =>
        Data.Foldable.and inj
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _, _ => false
    | PrimTyCon _ _ _ _ _ _ _ _ _, _ => true
    | PromotedDataCon _ _ _ _ _ _ _ _ _ _, _ => true
    | TcTyCon _ _ _ _ _ _ _ _ _, _ => true
    end.

Definition isGenerativeTyCon : TyCon -> Role -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ (DataFamilyTyCon _) _ _, Nominal => true
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _, _ => false
    | tc, r => isInjectiveTyCon tc r
    end.

Definition tyConInjectivityInfo : TyCon -> Injectivity :=
  fun tc =>
    match tc with
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ inj => inj
    | _ =>
        if isInjectiveTyCon tc Nominal : bool
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
    | TvBndr _ (NamedTCB _) => true
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

Definition isProductTyCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | (AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ as tc) =>
        match algTcRhs tc with
        | TupleTyCon _ _ => true
        | DataTyCon (cons data_con nil) _ =>
            Data.Foldable.null (Core.dataConExTyVars data_con)
        | NewTyCon _ _ _ _ => true
        | _ => false
        end
    | _ => false
    end.

Definition isPromotedDataCon : TyCon -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | PromotedDataCon _ _ _ _ _ _ _ _ _ _ => true
    | _ => false
    end.

Definition isPromotedDataCon_maybe : TyCon -> option DataCon.DataCon :=
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

Definition isPromotedTupleTyCon : TyCon -> bool :=
  fun tyCon =>
    match isPromotedDataCon_maybe tyCon with
    | Some dataCon =>
        if isTupleTyCon (DataCon.dataConTyCon dataCon) : bool then true else
        false
    | _ => false
    end.

Definition isCTupleClass : Class.Class -> bool :=
  fun cls => isTupleTyCon (Class.classTyCon cls).

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
    | NamedTCB vis => isVisibleArgFlag vis
    | AnonTCB => true
    end.

Definition isVisibleTyConBinder {tv} : TyVarBndr tv TyConBndrVis -> bool :=
  fun arg_0__ => let 'TvBndr _ tcb_vis := arg_0__ in isVisibleTcbVis tcb_vis.

Definition isInvisibleTyConBinder {tv} : TyVarBndr tv TyConBndrVis -> bool :=
  fun tcb => negb (isVisibleTyConBinder tcb).

Definition tyConVisibleTyVars : TyCon -> list TyVar :=
  fun tc =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | TvBndr tv vis => if isVisibleTcbVis vis : bool then cons tv nil else nil
      | _ => nil
      end in
    Coq.Lists.List.flat_map cont_0__ (tyConBinders tc).

Definition isVoidRep : PrimRep -> bool :=
  fun arg_0__ => match arg_0__ with | VoidRep => true | _other => false end.

Definition mkAnonTyConBinder : TyVar -> TyConBinder :=
  fun tv => TvBndr tv AnonTCB.

Definition mkAnonTyConBinders : list TyVar -> list TyConBinder :=
  fun tvs => GHC.Base.map mkAnonTyConBinder tvs.

Definition mkNamedTyConBinder : ArgFlag -> TyVar -> TyConBinder :=
  fun vis tv => TvBndr tv (NamedTCB vis).

Definition mkNamedTyConBinders : ArgFlag -> list TyVar -> list TyConBinder :=
  fun vis tvs => GHC.Base.map (mkNamedTyConBinder vis) tvs.

Definition mkTyConKind : list TyConBinder -> Kind -> Kind :=
  fun bndrs res_kind =>
    let mk : TyConBinder -> Kind -> Kind :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | TvBndr tv AnonTCB, k => TysWiredIn.mkFunKind (tyVarKind tv) k
        | TvBndr tv (NamedTCB vis), k => TysWiredIn.mkForAllKind tv vis k
        end in
    Data.Foldable.foldr mk res_kind bndrs.

Definition mkTupleTyCon
   : Name.Name ->
     list TyConBinder ->
     Kind ->
     BasicTypes.Arity ->
     DataCon.DataCon -> BasicTypes.TupleSort -> AlgTyConFlav -> TyCon :=
  fun name binders res_kind arity con sort parent =>
    AlgTyCon (Name.nameUnique name) name binders (binderVars binders) res_kind
             (mkTyConKind binders res_kind) arity (GHC.List.replicate arity Representational)
             None false nil (TupleTyCon con sort) FastStringEnv.emptyDFsEnv parent.

Definition mkTcTyCon
   : Name.Name ->
     list TyConBinder ->
     Kind -> list (Name.Name * TyVar)%type -> TyConFlavour -> TyCon :=
  fun name binders res_kind scoped_tvs flav =>
    TcTyCon (Unique.getUnique name) name binders (binderVars binders) res_kind
            (mkTyConKind binders res_kind) (Data.Foldable.length binders) scoped_tvs flav.

Definition mkSynonymTyCon
   : Name.Name ->
     list TyConBinder -> Kind -> list Role -> Type_ -> bool -> bool -> TyCon :=
  fun name binders res_kind roles rhs is_tau is_fam_free =>
    SynonymTyCon (Name.nameUnique name) name binders (binderVars binders) res_kind
                 (mkTyConKind binders res_kind) (Data.Foldable.length binders) roles rhs is_tau
                 is_fam_free.

Definition mkSumTyCon
   : Name.Name ->
     list TyConBinder ->
     Kind ->
     BasicTypes.Arity ->
     list TyVar -> list DataCon.DataCon -> AlgTyConFlav -> TyCon :=
  fun name binders res_kind arity tyvars cons_ parent =>
    AlgTyCon (Name.nameUnique name) name binders tyvars res_kind (mkTyConKind
              binders res_kind) arity (GHC.List.replicate arity Representational) None false
             nil (SumTyCon cons_) FastStringEnv.emptyDFsEnv parent.

Definition mkPromotedDataCon
   : DataCon.DataCon ->
     Name.Name ->
     TyConRepName ->
     list TyConBinder -> Kind -> list Role -> RuntimeRepInfo -> TyCon :=
  fun con name rep_name binders res_kind roles rep_info =>
    PromotedDataCon (Name.nameUnique name) name binders res_kind (mkTyConKind
                     binders res_kind) (Data.Foldable.length roles) roles con rep_name rep_info.

Definition mkPrimTyCon'
   : Name.Name ->
     list TyConBinder -> Kind -> list Role -> bool -> option TyConRepName -> TyCon :=
  fun name binders res_kind roles is_unlifted rep_nm =>
    PrimTyCon (Name.nameUnique name) name binders res_kind (mkTyConKind binders
               res_kind) (Data.Foldable.length roles) roles is_unlifted rep_nm.

Definition mkKindTyCon
   : Name.Name -> list TyConBinder -> Kind -> list Role -> Name.Name -> TyCon :=
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
     Kind ->
     option Name.Name ->
     FamTyConFlav -> option Class.Class -> Injectivity -> TyCon :=
  fun name binders res_kind resVar flav parent inj =>
    FamilyTyCon (Name.nameUnique name) name binders (binderVars binders) res_kind
                (mkTyConKind binders res_kind) (Data.Foldable.length binders) resVar flav parent
                inj.

Definition newTyConCo_maybe : TyCon -> option (CoAxiom Unbranched) :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ _ co) _ _ => Some co
    | _ => None
    end.

Definition newTyConCo : TyCon -> CoAxiom Unbranched :=
  fun tc =>
    match newTyConCo_maybe tc with
    | Some co => co
    | None => Panic.panicStr (GHC.Base.hs_string__ "newTyConCo") (Panic.noString tc)
    end.

Definition newTyConDataCon_maybe : TyCon -> option DataCon.DataCon :=
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

Definition newTyConEtadRhs : TyCon -> (list TyVar * Type_)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ tvs_rhs _) _ _ => tvs_rhs
    | tycon =>
        Panic.panicStr (GHC.Base.hs_string__ "newTyConEtadRhs") (Panic.noString tycon)
    end.

Definition newTyConRhs : TyCon -> (list TyVar * Type_)%type :=
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
    | tc_name, ClassTyCon cls _ =>
        tc_name GHC.Base.== tyConName (Class.classTyCon cls)
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

Definition synTyConDefn_maybe : TyCon -> option (list TyVar * Type_)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | SynonymTyCon _ _ _ tyvars _ _ _ _ ty _ _ => Some (pair tyvars ty)
    | _ => None
    end.

Definition synTyConRhs_maybe : TyCon -> option Type_ :=
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

Definition tyConATs : TyCon -> list TyCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (ClassTyCon clas _) => Class.classATs clas
    | _ => nil
    end.

Definition tyConAssoc_maybe : TyCon -> option Class.Class :=
  fun arg_0__ =>
    match arg_0__ with
    | FamilyTyCon _ _ _ _ _ _ _ _ _ mb_cls _ => mb_cls
    | _ => None
    end.

Definition isTyConAssoc : TyCon -> bool :=
  fun tc => Data.Maybe.isJust (tyConAssoc_maybe tc).

Definition tyConBinderArgFlag : TyConBinder -> ArgFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | TvBndr _ (NamedTCB vis) => vis
    | TvBndr _ AnonTCB => Required
    end.

Definition tyConCType_maybe : TyCon -> option Core.CType :=
  fun arg_0__ =>
    match arg_0__ with
    | (AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ _ as tc) => tyConCType tc
    | _ => None
    end.

Definition tyConClass_maybe : TyCon -> option Class.Class :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (ClassTyCon clas _) => Some clas
    | _ => None
    end.

Definition tyConDataCons_maybe : TyCon -> option (list DataCon.DataCon) :=
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

Definition tyConDataCons : TyCon -> list DataCon.DataCon :=
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
   : TyCon -> option (TyCon * list Type_ * CoAxiom Unbranched)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (DataFamInstTyCon ax f ts) =>
        Some (pair (pair f ts) ax)
    | _ => None
    end.

Definition tyConFamInst_maybe : TyCon -> option (TyCon * list Type_)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (DataFamInstTyCon _ f ts) =>
        Some (pair f ts)
    | _ => None
    end.

Definition pprSourceTyCon : TyCon -> GHC.Base.String :=
  fun tycon =>
    match tyConFamInst_maybe tycon with
    | Some (pair fam_tc tys) => Panic.noString (TyConApp fam_tc tys)
    | _ => Panic.noString tycon
    end.

Definition tyConFamilyCoercion_maybe : TyCon -> option (CoAxiom Unbranched) :=
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
   : Name.Name -> list TyConBinder -> Kind -> list Role -> TyCon :=
  fun name binders res_kind roles =>
    mkPrimTyCon' name binders res_kind roles true (Some (mkPrelTyConRepName name)).

Definition mkLiftedPrimTyCon
   : Name.Name -> list TyConBinder -> Kind -> list Role -> TyCon :=
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

Definition tyConRoles : TyCon -> list Role :=
  fun tc =>
    let const_role := fun r => GHC.List.replicate (tyConArity tc) r in
    match tc with
    | FunTyCon _ _ _ _ _ _ _ => const_role Representational
    | AlgTyCon _ _ _ _ _ _ _ roles _ _ _ _ _ _ => roles
    | SynonymTyCon _ _ _ _ _ _ _ roles _ _ _ => roles
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ => const_role Nominal
    | PrimTyCon _ _ _ _ _ _ roles _ _ => roles
    | PromotedDataCon _ _ _ _ _ _ roles _ _ _ => roles
    | TcTyCon _ _ _ _ _ _ _ _ _ => const_role Nominal
    end.

Definition tyConRuntimeRepInfo : TyCon -> RuntimeRepInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | PromotedDataCon _ _ _ _ _ _ _ _ _ rri => rri
    | _ => NoRRI
    end.

Definition tyConSingleAlgDataCon_maybe : TyCon -> option DataCon.DataCon :=
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

Definition tyConSingleDataCon_maybe : TyCon -> option DataCon.DataCon :=
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

Definition tyConSingleDataCon : TyCon -> DataCon.DataCon :=
  fun tc =>
    match tyConSingleDataCon_maybe tc with
    | Some c => c
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "tyConDataCon") (Panic.noString tc)
    end.

Definition tyConSkolem : TyCon -> bool :=
  Name.isHoleName GHC.Base.∘ tyConName.

Definition tyConStupidTheta : TyCon -> list PredType :=
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

Definition tyConTyVarBinders : list TyConBinder -> list TyVarBinder :=
  fun tc_bndrs =>
    let mk_binder :=
      fun arg_0__ =>
        let 'TvBndr tv tc_vis := arg_0__ in
        let vis :=
          match tc_vis with
          | AnonTCB => Specified
          | NamedTCB Required => Specified
          | NamedTCB vis => vis
          end in
        mkTyVarBinder vis tv in
    GHC.Base.map mk_binder tc_bndrs.

Definition unwrapNewTyConEtad_maybe
   : TyCon -> option (list TyVar * Type_ * CoAxiom Unbranched)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ (pair tvs rhs) co) _ _ =>
        Some (pair (pair tvs rhs) co)
    | _ => None
    end.

Definition unwrapNewTyCon_maybe
   : TyCon -> option (list TyVar * Type_ * CoAxiom Unbranched)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ tvs _ _ _ _ _ _ _ (NewTyCon _ rhs _ co) _ _ =>
        Some (pair (pair tvs rhs) co)
    | _ => None
    end.

Definition visibleDataCons : AlgTyConRhs -> list DataCon.DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AbstractTyCon => nil
    | DataTyCon cs _ => cs
    | NewTyCon c _ _ _ => cons c nil
    | TupleTyCon c _ => cons c nil
    | SumTyCon cs => cs
    end.

Definition fieldsOfAlgTcRhs : AlgTyConRhs -> FieldLabel.FieldLabelEnv :=
  fun rhs =>
    let dataConsFields :=
      fun dcs => Data.Foldable.concatMap DataCon.dataConFieldLabels dcs in
    FastStringEnv.mkDFsEnv (Coq.Lists.List.flat_map (fun fl =>
                                                       cons (pair (FieldLabel.flLabel fl) fl) nil) (dataConsFields
                                                     (visibleDataCons rhs))).

Definition mkAlgTyCon
   : Name.Name ->
     list TyConBinder ->
     Kind ->
     list Role ->
     option Core.CType ->
     list PredType -> AlgTyConRhs -> AlgTyConFlav -> bool -> TyCon :=
  fun name binders res_kind roles cType stupid rhs parent gadt_syn =>
    AlgTyCon (Name.nameUnique name) name binders (binderVars binders) res_kind
             (mkTyConKind binders res_kind) (Data.Foldable.length binders) roles cType
             gadt_syn stupid rhs (fieldsOfAlgTcRhs rhs) (if andb Util.debugIsOn (negb
                                                                  (okParent name parent)) : bool
              then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                               "ghc/compiler/types/TyCon.hs") #1433 (Panic.noString name Outputable.$$
                                                                                     Panic.noString parent))
              else parent).

Definition mkClassTyCon
   : Name.Name ->
     list TyConBinder ->
     list Role -> AlgTyConRhs -> Class.Class -> Name.Name -> TyCon :=
  fun name binders roles rhs clas tc_rep_name =>
    mkAlgTyCon name binders TysWiredIn.constraintKind roles None nil rhs (ClassTyCon
                                                                          clas tc_rep_name) false.

Definition coHoleCoVar : CoercionHole -> CoVar :=
  ch_co_var.

Definition coVarsOfCo : Coercion -> CoVarSet :=
  fix coVarsOfCo arg_0__
        := match arg_0__ with
           | Refl _ ty => coVarsOfType ty
           | TyConAppCo _ _ args => coVarsOfCos args
           | AppCo co arg => unionVarSet (coVarsOfCo co) (coVarsOfCo arg)
           | ForAllCo tv kind_co co =>
               unionVarSet (delVarSet (coVarsOfCo co) tv) (coVarsOfCo kind_co)
           | FunCo _ co1 co2 => unionVarSet (coVarsOfCo co1) (coVarsOfCo co2)
           | CoVarCo v => coVarsOfCoVar v
           | HoleCo h => coVarsOfCoVar (coHoleCoVar h)
           | AxiomInstCo _ _ as_ => coVarsOfCos as_
           | UnivCo p _ t1 t2 =>
               unionVarSet (coVarsOfProv p) (coVarsOfTypes (cons t1 (cons t2 nil)))
           | SymCo co => coVarsOfCo co
           | TransCo co1 co2 => unionVarSet (coVarsOfCo co1) (coVarsOfCo co2)
           | NthCo _ co => coVarsOfCo co
           | LRCo _ co => coVarsOfCo co
           | InstCo co arg => unionVarSet (coVarsOfCo co) (coVarsOfCo arg)
           | CoherenceCo c1 c2 => coVarsOfCos (cons c1 (cons c2 nil))
           | KindCo co => coVarsOfCo co
           | SubCo co => coVarsOfCo co
           | AxiomRuleCo _ cs => coVarsOfCos cs
           end.

Definition coVarsOfCoVar : CoVar -> CoVarSet :=
  fun v => unionVarSet (unitVarSet v) (coVarsOfType (varType v)).

Definition coVarsOfType : Type_ -> CoVarSet :=
  fix coVarsOfType arg_0__
        := match arg_0__ with
           | TyVarTy v => coVarsOfType (tyVarKind v)
           | TyConApp _ tys => coVarsOfTypes tys
           | LitTy _ => emptyVarSet
           | AppTy fun_ arg => unionVarSet (coVarsOfType fun_) (coVarsOfType arg)
           | FunTy arg res => unionVarSet (coVarsOfType arg) (coVarsOfType res)
           | ForAllTy (TvBndr tv _) ty =>
               unionVarSet (delVarSet (coVarsOfType ty) tv) (coVarsOfType (tyVarKind tv))
           | CastTy ty co => unionVarSet (coVarsOfType ty) (coVarsOfCo co)
           | CoercionTy co => coVarsOfCo co
           end.

Definition coVarsOfTypes : list Type_ -> TyCoVarSet :=
  fun tys => mapUnionVarSet coVarsOfType tys.

Definition coVarsOfCos : list Coercion -> CoVarSet :=
  fun cos => mapUnionVarSet coVarsOfCo cos.

Definition coVarsOfProv : UnivCoProvenance -> CoVarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | UnsafeCoerceProv => emptyVarSet
    | PhantomProv co => coVarsOfCo co
    | ProofIrrelProv co => coVarsOfCo co
    | PluginProv _ => emptyVarSet
    end.

Definition coercionSize : Coercion -> GHC.Num.Int :=
  fix coercionSize arg_0__
        := match arg_0__ with
           | Refl _ ty => typeSize ty
           | TyConAppCo _ _ args =>
               #1 GHC.Num.+ Data.Foldable.sum (GHC.Base.map coercionSize args)
           | AppCo co arg => coercionSize co GHC.Num.+ coercionSize arg
           | ForAllCo _ h co => (#1 GHC.Num.+ coercionSize co) GHC.Num.+ coercionSize h
           | FunCo _ co1 co2 => (#1 GHC.Num.+ coercionSize co1) GHC.Num.+ coercionSize co2
           | CoVarCo _ => #1
           | HoleCo _ => #1
           | AxiomInstCo _ _ args =>
               #1 GHC.Num.+ Data.Foldable.sum (GHC.Base.map coercionSize args)
           | UnivCo p _ t1 t2 =>
               ((#1 GHC.Num.+ provSize p) GHC.Num.+ typeSize t1) GHC.Num.+ typeSize t2
           | SymCo co => #1 GHC.Num.+ coercionSize co
           | TransCo co1 co2 => (#1 GHC.Num.+ coercionSize co1) GHC.Num.+ coercionSize co2
           | NthCo _ co => #1 GHC.Num.+ coercionSize co
           | LRCo _ co => #1 GHC.Num.+ coercionSize co
           | InstCo co arg => (#1 GHC.Num.+ coercionSize co) GHC.Num.+ coercionSize arg
           | CoherenceCo c1 c2 => (#1 GHC.Num.+ coercionSize c1) GHC.Num.+ coercionSize c2
           | KindCo co => #1 GHC.Num.+ coercionSize co
           | SubCo co => #1 GHC.Num.+ coercionSize co
           | AxiomRuleCo _ cs =>
               #1 GHC.Num.+ Data.Foldable.sum (GHC.Base.map coercionSize cs)
           end.

Definition provSize : UnivCoProvenance -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
    | UnsafeCoerceProv => #1
    | PhantomProv co => #1 GHC.Num.+ coercionSize co
    | ProofIrrelProv co => #1 GHC.Num.+ coercionSize co
    | PluginProv _ => #1
    end.

Definition typeSize : Type_ -> GHC.Num.Int :=
  fix typeSize arg_0__
        := match arg_0__ with
           | LitTy _ => #1
           | TyVarTy _ => #1
           | AppTy t1 t2 => typeSize t1 GHC.Num.+ typeSize t2
           | FunTy t1 t2 => typeSize t1 GHC.Num.+ typeSize t2
           | ForAllTy (TvBndr tv _) t => typeSize (tyVarKind tv) GHC.Num.+ typeSize t
           | TyConApp _ ts => #1 GHC.Num.+ Data.Foldable.sum (GHC.Base.map typeSize ts)
           | CastTy ty co => typeSize ty GHC.Num.+ coercionSize co
           | CoercionTy co => coercionSize co
           end.

Definition debug_ppr_ty : BasicTypes.TyPrec -> Type_ -> GHC.Base.String :=
  fix debug_ppr_ty arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, LitTy l => Panic.noString l
           | _, TyVarTy tv => Panic.noString tv
           | prec, FunTy arg res =>
               BasicTypes.maybeParen prec BasicTypes.FunPrec (Outputable.sep (cons
                                                                              (debug_ppr_ty BasicTypes.FunPrec arg)
                                                                              (cons (GHC.Base.mappend Outputable.arrow
                                                                                                      (debug_ppr_ty prec
                                                                                                       res)) nil)))
           | prec, TyConApp tc tys =>
               if Data.Foldable.null tys : bool then Panic.noString tc else
               BasicTypes.maybeParen prec BasicTypes.TyConPrec (Outputable.hang (Panic.noString
                                                                                 tc) #2 (Outputable.sep (GHC.Base.map
                                                                                                         (debug_ppr_ty
                                                                                                          BasicTypes.TyConPrec)
                                                                                                         tys)))
           | prec, AppTy t1 t2 =>
               Outputable.hang (debug_ppr_ty prec t1) #2 (debug_ppr_ty BasicTypes.TyConPrec t2)
           | prec, CastTy ty co =>
               BasicTypes.maybeParen prec BasicTypes.TopPrec (Outputable.hang (debug_ppr_ty
                                                                               BasicTypes.TopPrec ty) #2
                                                                              (GHC.Base.mappend (id
                                                                                                 (GHC.Base.hs_string__
                                                                                                  "|>")) (Panic.noString
                                                                                                 co)))
           | _, CoercionTy co =>
               id (GHC.Base.mappend (id (GHC.Base.hs_string__ "CO")) (Panic.noString co))
           | prec, (ForAllTy _ _ as ty) =>
               let fix split ty
                         := match ty with
                            | ForAllTy tv ty' => let 'pair tvs body := split ty' in pair (cons tv tvs) body
                            | _ => pair nil ty
                            end in
               let 'pair tvs body := split ty in
               BasicTypes.maybeParen prec BasicTypes.FunPrec (Outputable.hang (GHC.Base.mappend
                                                                               (GHC.Base.mappend (id
                                                                                                  (GHC.Base.hs_string__
                                                                                                   "forall"))
                                                                                                 (Panic.noString
                                                                                                  (GHC.Base.map
                                                                                                   Panic.noString tvs)))
                                                                               Outputable.dot) #2 (Panic.noString body))
           end.

Definition debugPprType : Type_ -> GHC.Base.String :=
  fun ty => debug_ppr_ty BasicTypes.TopPrec ty.

Definition delBinderVar : VarSet -> TyVarBinder -> VarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | vars, TvBndr tv _ => delVarSet vars tv
    end.

Definition emptyCvSubstEnv : CvSubstEnv :=
  emptyVarEnv.

Definition mkTvSubst : InScopeSet -> TvSubstEnv -> TCvSubst :=
  fun in_scope tenv => TCvSubst in_scope tenv emptyCvSubstEnv.

Definition emptyTvSubstEnv : TvSubstEnv :=
  emptyVarEnv.

Definition emptyTCvSubst : TCvSubst :=
  TCvSubst emptyInScopeSet emptyTvSubstEnv emptyCvSubstEnv.

Definition mkEmptyTCvSubst : InScopeSet -> TCvSubst :=
  fun is_ => TCvSubst is_ emptyTvSubstEnv emptyCvSubstEnv.

Definition extendCvSubst : TCvSubst -> CoVar -> Coercion -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | TCvSubst in_scope tenv cenv, v, co =>
        TCvSubst in_scope tenv (extendVarEnv cenv v co)
    end.

Definition extendTCvInScope : TCvSubst -> Var -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst in_scope tenv cenv, var =>
        TCvSubst (extendInScopeSet in_scope var) tenv cenv
    end.

Definition extendTCvInScopeList : TCvSubst -> list Var -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst in_scope tenv cenv, vars =>
        TCvSubst (extendInScopeSetList in_scope vars) tenv cenv
    end.

Definition extendTCvInScopeSet : TCvSubst -> VarSet -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst in_scope tenv cenv, vars =>
        TCvSubst (extendInScopeSetSet in_scope vars) tenv cenv
    end.

Definition extendTvSubst : TCvSubst -> TyVar -> Type_ -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | TCvSubst in_scope tenv cenv, tv, ty =>
        TCvSubst in_scope (extendVarEnv tenv tv ty) cenv
    end.

Definition extendTvSubstList : TCvSubst -> list Var -> list Type_ -> TCvSubst :=
  fun subst tvs tys => Util.foldl2 extendTvSubst subst tvs tys.

Definition extendTCvSubst : TCvSubst -> TyCoVar -> Type_ -> TCvSubst :=
  fun subst v ty =>
    if isTyVar v : bool then extendTvSubst subst v ty else
    match ty with
    | CoercionTy co => extendCvSubst subst v co
    | _ =>
        Panic.panicStr (GHC.Base.hs_string__ "extendTCvSubst") (GHC.Base.mappend
                                                                (GHC.Base.mappend (Panic.noString v) (id
                                                                                   (GHC.Base.hs_string__ "|->")))
                                                                (Panic.noString ty))
    end.

Definition getCvSubstEnv : TCvSubst -> CvSubstEnv :=
  fun arg_0__ => let 'TCvSubst _ _ env := arg_0__ in env.

Definition getHelpfulOccName : TyCoVar -> OccName.OccName :=
  fun tyvar =>
    let name := tyVarName tyvar in
    let occ := Name.getOccName name in
    let occ1 :=
      if andb (Name.isSystemName name) (isTcTyVar tyvar) : bool
      then OccName.mkTyVarOcc (Coq.Init.Datatypes.app (OccName.occNameString occ)
                                                      (GHC.Base.hs_string__ "0")) else
      occ in
    occ1.

Definition getTCvInScope : TCvSubst -> InScopeSet :=
  fun arg_0__ => let 'TCvSubst in_scope _ _ := arg_0__ in in_scope.

Definition getTvSubstEnv : TCvSubst -> TvSubstEnv :=
  fun arg_0__ => let 'TCvSubst _ env _ := arg_0__ in env.

Definition isCoercionType : Type_ -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | TyConApp tc tys =>
        if andb (orb (Unique.hasKey tc PrelNames.eqPrimTyConKey) (Unique.hasKey tc
                                                                                PrelNames.eqReprPrimTyConKey))
                (Util.lengthIs tys #4) : bool
        then true else
        false
    | _ => false
    end.

Definition isEmptyTCvSubst : TCvSubst -> bool :=
  fun arg_0__ =>
    let 'TCvSubst _ tenv cenv := arg_0__ in
    andb (isEmptyVarEnv tenv) (isEmptyVarEnv cenv).

Definition isInScope : Var -> TCvSubst -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, TCvSubst in_scope _ _ => elemInScopeSet v in_scope
    end.

Definition lookupCoVar : TCvSubst -> Var -> option Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst _ _ cenv, v => lookupVarEnv cenv v
    end.

Definition lookupTyVar : TCvSubst -> TyVar -> option Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst _ tenv _, tv =>
        if andb Util.debugIsOn (negb (isTyVar tv)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
              #2255)
        else lookupVarEnv tenv tv
    end.

Definition partitionInvisibles {a}
   : TyCon -> (a -> Type_) -> list a -> (list a * list a)%type :=
  fun tc get_ty =>
    let fix go arg_0__ arg_1__ arg_2__
              := let j_4__ :=
                   match arg_0__, arg_1__, arg_2__ with
                   | _, _, xs => pair nil xs
                   end in
                 match arg_0__, arg_1__, arg_2__ with
                 | _, _, nil => pair nil nil
                 | subst, ForAllTy (TvBndr tv vis) res_ki, cons x xs =>
                     let subst' := extendTvSubst subst tv (get_ty x) in
                     if isVisibleArgFlag vis : bool
                     then Control.Arrow.second (fun arg_9__ => cons x arg_9__) (go subst' res_ki
                                                                                xs) else
                     Control.Arrow.first (fun arg_7__ => cons x arg_7__) (go subst' res_ki xs)
                 | subst, TyVarTy tv, xs =>
                     match lookupTyVar subst tv with
                     | Some ki => go subst ki xs
                     | _ => j_4__
                     end
                 | _, _, _ => j_4__
                 end in
    go emptyTCvSubst (tyConKind tc).

Definition filterOutInvisibleTypes : TyCon -> list Type_ -> list Type_ :=
  fun tc tys => Data.Tuple.snd (partitionInvisibles tc GHC.Base.id tys).

Definition mkForAllTy : TyVar -> ArgFlag -> Type_ -> Type_ :=
  fun tv vis ty => ForAllTy (TvBndr tv vis) ty.

Definition mkForAllTys : list TyVarBinder -> Type_ -> Type_ :=
  fun tyvars ty => Data.Foldable.foldr ForAllTy ty tyvars.

Definition mkVisForAllTys : list TyVar -> Type_ -> Type_ :=
  fun tvs =>
    if andb Util.debugIsOn (negb (Data.Foldable.all isTyVar tvs)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
          #1299)
    else mkForAllTys (Coq.Lists.List.flat_map (fun tv =>
                                                 cons (TvBndr tv Required) nil) tvs).

Definition mkSpecForAllTys : list TyVar -> Type_ -> Type_ :=
  fun tvs =>
    if andb Util.debugIsOn (negb (Data.Foldable.all isTyVar tvs)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
          #1294)
    else mkForAllTys (Coq.Lists.List.flat_map (fun tv =>
                                                 cons (TvBndr tv Specified) nil) tvs).

Definition mkForAllTys' : list (TyVar * ArgFlag)%type -> Type_ -> Type_ :=
  fun tvvs ty =>
    let strictMkForAllTy :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair tv vis, ty => ForAllTy (TvBndr tv vis) ty
        end in
    Data.Foldable.foldr strictMkForAllTy ty tvvs.

Definition mkFunTy : Type_ -> Type_ -> Type_ :=
  fun arg res => FunTy arg res.

Definition mkFunTys : list Type_ -> Type_ -> Type_ :=
  fun tys ty => Data.Foldable.foldr mkFunTy ty tys.

Definition mkPiTy : TyBinder -> Type_ -> Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Anon ty1, ty2 => FunTy ty1 ty2
    | Named tvb, ty => ForAllTy tvb ty
    end.

Definition mkPiTys : list TyBinder -> Type_ -> Type_ :=
  fun tbs ty => Data.Foldable.foldr mkPiTy ty tbs.

Definition mkTCvSubst
   : InScopeSet -> (TvSubstEnv * CvSubstEnv)%type -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | in_scope, pair tenv cenv => TCvSubst in_scope tenv cenv
    end.

Definition mkTyConTy : TyCon -> Type_ :=
  fun tycon => TyConApp tycon nil.

Definition mkTyVarTy : TyVar -> Type_ :=
  fun v =>
    if andb Util.debugIsOn (negb (isTyVar v)) : bool
    then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                     "ghc/compiler/types/TyCoRep.hs") #660 (GHC.Base.mappend (GHC.Base.mappend
                                                                                              (Panic.noString v)
                                                                                              Outputable.dcolon)
                                                                                             (Panic.noString (tyVarKind
                                                                                                              v))))
    else TyVarTy v.

Definition mkTyVarTys : list TyVar -> list Type_ :=
  GHC.Base.map mkTyVarTy.

Definition notElemTCvSubst : Var -> TCvSubst -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, TCvSubst _ tenv cenv =>
        if isTyVar v : bool then negb (elemVarEnv v tenv) else
        negb (elemVarEnv v cenv)
    end.

Definition ppSuggestExplicitKinds : GHC.Base.String :=
  Outputable.sdocWithDynFlags (fun dflags =>
                                 Outputable.ppUnless (DynFlags.gopt DynFlags.Opt_PrintExplicitKinds dflags) (id
                                                                                                             (GHC.Base.hs_string__
                                                                                                              "Use -fprint-explicit-kinds to see the kind arguments"))).

Definition pprForAll : list TyVarBinder -> GHC.Base.String :=
  fun tvs =>
    IfaceType.pprIfaceForAll (GHC.Base.map ToIface.toIfaceForAllBndr tvs).

Definition pprTyLit : TyLit -> GHC.Base.String :=
  IfaceType.pprIfaceTyLit GHC.Base.∘ ToIface.toIfaceTyLit.

Definition pprTypeApp : TyCon -> list Type_ -> GHC.Base.String :=
  fun tc tys =>
    IfaceType.pprIfaceTypeApp BasicTypes.TopPrec (ToIface.toIfaceTyCon tc)
    (ToIface.toIfaceTcArgs tc tys).

Definition pprClassPred : Class.Class -> list Type_ -> GHC.Base.String :=
  fun clas tys => pprTypeApp (Class.classTyCon clas) tys.

Definition pprUserForAll : list TyVarBinder -> GHC.Base.String :=
  IfaceType.pprUserIfaceForAll GHC.Base.∘ GHC.Base.map ToIface.toIfaceForAllBndr.

Definition setCvSubstEnv : TCvSubst -> CvSubstEnv -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst in_scope tenv _, cenv => TCvSubst in_scope tenv cenv
    end.

Definition setTvSubstEnv : TCvSubst -> TvSubstEnv -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst in_scope _ cenv, tenv => TCvSubst in_scope tenv cenv
    end.

Definition splitForAllTys'
   : Type_ -> (list TyVar * list ArgFlag * Type_)%type :=
  fun ty =>
    let fix go arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | ForAllTy (TvBndr tv vis) ty, tvs, viss => go ty (cons tv tvs) (cons vis viss)
                 | ty, tvs, viss => pair (pair (GHC.List.reverse tvs) (GHC.List.reverse viss)) ty
                 end in
    go ty nil nil.

Definition tidyType : TidyEnv -> Type_ -> Type_ :=
  fix tidyType arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, LitTy n => LitTy n
           | env, TyVarTy tv => TyVarTy (tidyTyVarOcc env tv)
           | env, TyConApp tycon tys =>
               let args := tidyTypes env tys in Util.seqList args (TyConApp tycon args)
           | env, AppTy fun_ arg => AppTy (tidyType env fun_) (tidyType env arg)
           | env, FunTy fun_ arg => FunTy (tidyType env fun_) (tidyType env arg)
           | env, (ForAllTy _ _ as ty) =>
               let 'pair (pair tvs vis) body_ty := splitForAllTys' ty in
               let 'pair env' tvs' := tidyTyCoVarBndrs env tvs in
               mkForAllTys' (GHC.List.zip tvs' vis) (tidyType env' body_ty)
           | env, CastTy ty co => CastTy (tidyType env ty) (tidyCo env co)
           | env, CoercionTy co => CoercionTy (tidyCo env co)
           end.

Definition tidyTyCoVarBndrs
   : TidyEnv -> list TyCoVar -> (TidyEnv * list TyCoVar)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair occ_env subst, tvs =>
        let occs := GHC.Base.map getHelpfulOccName tvs in
        let tidy_env' := pair (OccName.avoidClashesOccEnv occ_env occs) subst in
        Data.Traversable.mapAccumL tidyTyCoVarBndr tidy_env' tvs
    end.

Definition tidyTyCoVarBndr : TidyEnv -> TyCoVar -> (TidyEnv * TyCoVar)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (pair occ_env subst as tidy_env), tyvar =>
        let 'pair occ_env' occ' := OccName.tidyOccName occ_env (getHelpfulOccName
                                                                tyvar) in
        let name := tyVarName tyvar in
        let name' := Name.tidyNameOcc name occ' in
        let kind' := tidyKind tidy_env (tyVarKind tyvar) in
        let tyvar' := setTyVarKind (setTyVarName tyvar name') kind' in
        let subst' := extendVarEnv subst tyvar tyvar' in
        pair (pair occ_env' subst') tyvar'
    end.

Definition tidyKind : TidyEnv -> Kind -> Kind :=
  tidyType.

Definition tidyCo : TidyEnv -> Coercion -> Coercion :=
  fix tidyCo arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | (pair _ subst as env), co =>
               let fix go arg_2__
                         := match arg_2__ with
                            | Refl r ty => Refl r (tidyType env ty)
                            | TyConAppCo r tc cos =>
                                let args := GHC.Base.map go cos in Util.seqList args (TyConAppCo r tc args)
                            | AppCo co1 co2 => AppCo (go co1) (go co2)
                            | ForAllCo tv h co =>
                                let 'pair envp tvp := tidyTyCoVarBndr env tv in
                                ForAllCo tvp (go h) (tidyCo envp co)
                            | FunCo r co1 co2 => FunCo r (go co1) (go co2)
                            | CoVarCo cv =>
                                match lookupVarEnv subst cv with
                                | None => CoVarCo cv
                                | Some cv' => CoVarCo cv'
                                end
                            | HoleCo h => HoleCo h
                            | AxiomInstCo con ind cos =>
                                let args := GHC.Base.map go cos in Util.seqList args (AxiomInstCo con ind args)
                            | UnivCo p r t1 t2 => UnivCo (go_prov p) r (tidyType env t1) (tidyType env t2)
                            | SymCo co => SymCo (go co)
                            | TransCo co1 co2 => TransCo (go co1) (go co2)
                            | NthCo d co => NthCo d (go co)
                            | LRCo lr co => LRCo lr (go co)
                            | InstCo co ty => InstCo (go co) (go ty)
                            | CoherenceCo co1 co2 => CoherenceCo (go co1) (go co2)
                            | KindCo co => KindCo (go co)
                            | SubCo co => SubCo (go co)
                            | AxiomRuleCo ax cos =>
                                let cos1 := tidyCos env cos in Util.seqList cos1 (AxiomRuleCo ax cos1)
                            end in
               let go_prov :=
                 fun arg_30__ =>
                   match arg_30__ with
                   | UnsafeCoerceProv => UnsafeCoerceProv
                   | PhantomProv co => PhantomProv (go co)
                   | ProofIrrelProv co => ProofIrrelProv (go co)
                   | (PluginProv _ as p) => p
                   end in
               go co
           end.

Definition tidyCos : TidyEnv -> list Coercion -> list Coercion :=
  fun env => GHC.Base.map (tidyCo env).

Definition tidyTyVarOcc : TidyEnv -> TyVar -> TyVar :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (pair _ subst as env), tv =>
        match lookupVarEnv subst tv with
        | None => updateTyVarKind (tidyType env) tv
        | Some tv' => tv'
        end
    end.

Definition tidyTypes : TidyEnv -> list Type_ -> list Type_ :=
  fun env tys => GHC.Base.map (tidyType env) tys.

Definition tidyTyVarBinder {vis}
   : TidyEnv -> TyVarBndr TyVar vis -> (TidyEnv * TyVarBndr TyVar vis)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | tidy_env, TvBndr tv vis =>
        let 'pair tidy_env' tv' := tidyTyCoVarBndr tidy_env tv in
        pair tidy_env' (TvBndr tv' vis)
    end.

Definition tidyTyVarBinders {vis}
   : TidyEnv ->
     list (TyVarBndr TyVar vis) -> (TidyEnv * list (TyVarBndr TyVar vis))%type :=
  Data.Traversable.mapAccumL tidyTyVarBinder.

Definition tidyTopType : Type_ -> Type_ :=
  fun ty => tidyType emptyTidyEnv ty.

Definition substCoVar : TCvSubst -> CoVar -> Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst _ _ cenv, cv =>
        match lookupVarEnv cenv cv with
        | Some co => co
        | None => CoVarCo cv
        end
    end.

Definition substCoVars : TCvSubst -> list CoVar -> list Coercion :=
  fun subst cvs => GHC.Base.map (substCoVar subst) cvs.

Definition substTyVar : TCvSubst -> TyVar -> Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst _ tenv _, tv =>
        if andb Util.debugIsOn (negb (isTyVar tv)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
              #2244)
        else match lookupVarEnv tenv tv with
             | Some ty => ty
             | None => TyVarTy tv
             end
    end.

Definition substTyVars : TCvSubst -> list TyVar -> list Type_ :=
  fun subst => GHC.Base.map (substTyVar subst).

Definition tyThingCategory : TyThing -> GHC.Base.String :=
  fun arg_0__ =>
    match arg_0__ with
    | ATyCon tc =>
        if isClassTyCon tc : bool then GHC.Base.hs_string__ "class" else
        GHC.Base.hs_string__ "type constructor"
    | ACoAxiom _ => GHC.Base.hs_string__ "coercion axiom"
    | AnId _ => GHC.Base.hs_string__ "identifier"
    | AConLike (ConLike.RealDataCon _) => GHC.Base.hs_string__ "data constructor"
    | AConLike (ConLike.PatSynCon _) => GHC.Base.hs_string__ "pattern synonym"
    end.

Definition pprTyThingCategory : TyThing -> GHC.Base.String :=
  id GHC.Base.∘ (Util.capitalise GHC.Base.∘ tyThingCategory).

Definition pprShortTyThing : TyThing -> GHC.Base.String :=
  fun thing =>
    GHC.Base.mappend (pprTyThingCategory thing) (Outputable.quotes (Panic.noString
                                                                    (Name.getName thing))).

Definition unionTCvSubst : TCvSubst -> TCvSubst -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst in_scope1 tenv1 cenv1, TCvSubst in_scope2 tenv2 cenv2 =>
        if andb Util.debugIsOn (negb (andb (negb (intersectsVarEnv tenv1 tenv2)) (negb
                                            (intersectsVarEnv cenv1 cenv2)))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
              #1929)
        else TCvSubst (unionInScope in_scope1 in_scope2) (plusVarEnv tenv1 tenv2)
             (plusVarEnv cenv1 cenv2)
    end.

Definition zapTCvSubst : TCvSubst -> TCvSubst :=
  fun arg_0__ =>
    let 'TCvSubst in_scope _ _ := arg_0__ in
    TCvSubst in_scope emptyVarEnv emptyVarEnv.

Definition zipCoEnv : list CoVar -> list Coercion -> CvSubstEnv :=
  fun cvs cos =>
    mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipCoEnv") cvs cos).

Definition zipTyEnv : list TyVar -> list Type_ -> TvSubstEnv :=
  fun tyvars tys =>
    if andb Util.debugIsOn (negb (Data.Foldable.all (negb GHC.Base.∘ isCoercionTy)
                                  tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #1982)
    else mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipTyEnv") tyvars tys).

Definition delFV : Var -> FV -> FV :=
  fun var fv fv_cand in_scope acc => fv fv_cand (extendVarSet in_scope var) acc.

Definition delFVs : VarSet -> FV -> FV :=
  fun vars fv fv_cand in_scope acc => fv fv_cand (unionVarSet in_scope vars) acc.

Definition emptyFV : FV :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | _, _, acc => acc
    end.

Definition filterFV : InterestingVarFun -> FV -> FV :=
  fun fv_cand2 fv fv_cand1 in_scope acc =>
    fv (fun v => andb (fv_cand1 v) (fv_cand2 v)) in_scope acc.

Definition fvVarListVarSet : FV -> (list Var * VarSet)%type :=
  fun fv => fv (GHC.Base.const true) emptyVarSet (pair nil emptyVarSet).

Definition fvVarSet : FV -> VarSet :=
  Data.Tuple.snd GHC.Base.∘ fvVarListVarSet.

Definition fvVarList : FV -> list Var :=
  Data.Tuple.fst GHC.Base.∘ fvVarListVarSet.

Definition fvDVarSet : FV -> DVarSet :=
  mkDVarSet GHC.Base.∘ (Data.Tuple.fst GHC.Base.∘ fvVarListVarSet).

Definition mapUnionFV {a} : (a -> FV) -> list a -> FV :=
  fix mapUnionFV arg_0__ arg_1__ arg_2__ arg_3__ arg_4__
        := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
           | _f, nil, _fv_cand, _in_scope, acc => acc
           | f, cons a as_, fv_cand, in_scope, acc =>
               mapUnionFV f as_ fv_cand in_scope (f a fv_cand in_scope acc)
           end.

Definition unionsFV : list FV -> FV :=
  fun fvs fv_cand in_scope acc => mapUnionFV GHC.Base.id fvs fv_cand in_scope acc.

Definition unionFV : FV -> FV -> FV :=
  fun fv1 fv2 fv_cand in_scope acc =>
    fv1 fv_cand in_scope (fv2 fv_cand in_scope acc).

Definition unitFV : Id -> FV :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | var, fv_cand, in_scope, (pair have haveSet as acc) =>
        if elemVarSet var in_scope : bool then acc else
        if elemVarSet var haveSet : bool then acc else
        if fv_cand var : bool then pair (cons var have) (extendVarSet haveSet var) else
        acc
    end.

Definition mkFVs : list Var -> FV :=
  fun vars fv_cand in_scope acc => mapUnionFV unitFV vars fv_cand in_scope acc.

Definition tyCoFVsOfType : Type_ -> FV :=
  fix tyCoFVsOfType arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | TyVarTy v, a, b, c => (unionFV (unitFV v) (tyCoFVsOfType (tyVarKind v))) a b c
           | TyConApp _ tys, a, b, c => tyCoFVsOfTypes tys a b c
           | LitTy _, a, b, c => emptyFV a b c
           | AppTy fun_ arg, a, b, c =>
               (unionFV (tyCoFVsOfType fun_) (tyCoFVsOfType arg)) a b c
           | FunTy arg res, a, b, c =>
               (unionFV (tyCoFVsOfType arg) (tyCoFVsOfType res)) a b c
           | ForAllTy bndr ty, a, b, c => tyCoFVsBndr bndr (tyCoFVsOfType ty) a b c
           | CastTy ty co, a, b, c => (unionFV (tyCoFVsOfType ty) (tyCoFVsOfCo co)) a b c
           | CoercionTy co, a, b, c => tyCoFVsOfCo co a b c
           end.

Definition tyCoFVsOfCo : Coercion -> FV :=
  fix tyCoFVsOfCo arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | Refl _ ty, fv_cand, in_scope, acc => tyCoFVsOfType ty fv_cand in_scope acc
           | TyConAppCo _ _ cos, fv_cand, in_scope, acc =>
               tyCoFVsOfCos cos fv_cand in_scope acc
           | AppCo co arg, fv_cand, in_scope, acc =>
               (unionFV (tyCoFVsOfCo co) (tyCoFVsOfCo arg)) fv_cand in_scope acc
           | ForAllCo tv kind_co co, fv_cand, in_scope, acc =>
               (unionFV (delFV tv (tyCoFVsOfCo co)) (tyCoFVsOfCo kind_co)) fv_cand in_scope acc
           | FunCo _ co1 co2, fv_cand, in_scope, acc =>
               (unionFV (tyCoFVsOfCo co1) (tyCoFVsOfCo co2)) fv_cand in_scope acc
           | CoVarCo v, fv_cand, in_scope, acc => tyCoFVsOfCoVar v fv_cand in_scope acc
           | HoleCo h, fv_cand, in_scope, acc =>
               tyCoFVsOfCoVar (coHoleCoVar h) fv_cand in_scope acc
           | AxiomInstCo _ _ cos, fv_cand, in_scope, acc =>
               tyCoFVsOfCos cos fv_cand in_scope acc
           | UnivCo p _ t1 t2, fv_cand, in_scope, acc =>
               (unionFV (unionFV (tyCoFVsOfProv p) (tyCoFVsOfType t1)) (tyCoFVsOfType t2))
               fv_cand in_scope acc
           | SymCo co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
           | TransCo co1 co2, fv_cand, in_scope, acc =>
               (unionFV (tyCoFVsOfCo co1) (tyCoFVsOfCo co2)) fv_cand in_scope acc
           | NthCo _ co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
           | LRCo _ co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
           | InstCo co arg, fv_cand, in_scope, acc =>
               (unionFV (tyCoFVsOfCo co) (tyCoFVsOfCo arg)) fv_cand in_scope acc
           | CoherenceCo c1 c2, fv_cand, in_scope, acc =>
               (unionFV (tyCoFVsOfCo c1) (tyCoFVsOfCo c2)) fv_cand in_scope acc
           | KindCo co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
           | SubCo co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
           | AxiomRuleCo _ cs, fv_cand, in_scope, acc =>
               tyCoFVsOfCos cs fv_cand in_scope acc
           end.

Definition tyCoFVsOfCoVar : CoVar -> FV :=
  fun v fv_cand in_scope acc =>
    (unionFV (unitFV v) (tyCoFVsOfType (varType v))) fv_cand in_scope acc.

Definition tyCoFVsOfCos : list Coercion -> FV :=
  fix tyCoFVsOfCos arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | nil, fv_cand, in_scope, acc => emptyFV fv_cand in_scope acc
           | cons co cos, fv_cand, in_scope, acc =>
               (unionFV (tyCoFVsOfCo co) (tyCoFVsOfCos cos)) fv_cand in_scope acc
           end.

Definition tyCoFVsOfProv : UnivCoProvenance -> FV :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | UnsafeCoerceProv, fv_cand, in_scope, acc => emptyFV fv_cand in_scope acc
    | PhantomProv co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
    | ProofIrrelProv co, fv_cand, in_scope, acc =>
        tyCoFVsOfCo co fv_cand in_scope acc
    | PluginProv _, fv_cand, in_scope, acc => emptyFV fv_cand in_scope acc
    end.

Definition tyCoFVsBndr : TyVarBinder -> FV -> FV :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TvBndr tv _, fvs => unionFV (delFV tv fvs) (tyCoFVsOfType (tyVarKind tv))
    end.

Definition tyCoFVsOfTypes : list Type_ -> FV :=
  fix tyCoFVsOfTypes arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | cons ty tys, fv_cand, in_scope, acc =>
               (unionFV (tyCoFVsOfType ty) (tyCoFVsOfTypes tys)) fv_cand in_scope acc
           | nil, fv_cand, in_scope, acc => emptyFV fv_cand in_scope acc
           end.

Definition tyCoVarsOfCos : list Coercion -> TyCoVarSet :=
  fun cos => fvVarSet (tyCoFVsOfCos cos).

Definition zipCvSubst : list CoVar -> list Coercion -> TCvSubst :=
  fun cvs cos =>
    let cenv := zipCoEnv cvs cos in
    if andb Util.debugIsOn (orb (negb (Data.Foldable.all isCoVar cvs))
                                (Util.neLength cvs cos)) : bool
    then Outputable.pprTrace (GHC.Base.hs_string__ "zipCvSubst") (Panic.noString cvs
                                                                  Outputable.$$
                                                                  Panic.noString cos) emptyTCvSubst else
    TCvSubst (mkInScopeSet (tyCoVarsOfCos cos)) emptyTvSubstEnv cenv.

Definition tyCoVarsOfCosSet : CoVarEnv Coercion -> TyCoVarSet :=
  fun cos => fvVarSet (tyCoFVsOfCos (UniqFM.nonDetEltsUFM cos)).

Definition tyCoVarsOfProv : UnivCoProvenance -> TyCoVarSet :=
  fun prov => fvVarSet (tyCoFVsOfProv prov).

Definition tyCoVarsOfCo : Coercion -> TyCoVarSet :=
  fun co => fvVarSet (tyCoFVsOfCo co).

Definition tyCoVarsOfCoDSet : Coercion -> DTyCoVarSet :=
  fun co => fvDVarSet (tyCoFVsOfCo co).

Definition tyCoVarsOfCoList : Coercion -> list TyCoVar :=
  fun co => fvVarList (tyCoFVsOfCo co).

Definition tyCoVarsOfTypes : list Type_ -> TyCoVarSet :=
  fun tys => fvVarSet (tyCoFVsOfTypes tys).

Definition mkTvSubstPrs : list (TyVar * Type_)%type -> TCvSubst :=
  fun prs =>
    let onlyTyVarsAndNoCoercionTy :=
      Data.Foldable.and (let cont_0__ arg_1__ :=
                           let 'pair tv ty := arg_1__ in
                           cons (andb (isTyVar tv) (negb (isCoercionTy ty))) nil in
                         Coq.Lists.List.flat_map cont_0__ prs) in
    let in_scope :=
      mkInScopeSet (tyCoVarsOfTypes (GHC.Base.map Data.Tuple.snd prs)) in
    let tenv := mkVarEnv prs in
    if andb Util.debugIsOn (negb (onlyTyVarsAndNoCoercionTy)) : bool
    then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                     "ghc/compiler/types/TyCoRep.hs") #1972 (GHC.Base.mappend (id
                                                                                               (GHC.Base.hs_string__
                                                                                                "prs")) (Panic.noString
                                                                                               prs)))
    else mkTvSubst in_scope tenv.

Definition mkTyCoInScopeSet : list Type_ -> list Coercion -> InScopeSet :=
  fun tys cos =>
    mkInScopeSet (unionVarSet (tyCoVarsOfTypes tys) (tyCoVarsOfCos cos)).

Definition zipTvSubst : list TyVar -> list Type_ -> TCvSubst :=
  fun tvs tys =>
    let tenv := zipTyEnv tvs tys in
    if andb Util.debugIsOn (orb (negb (Data.Foldable.all isTyVar tvs))
                                (Util.neLength tvs tys)) : bool
    then Outputable.pprTrace (GHC.Base.hs_string__ "zipTvSubst") (Panic.noString tvs
                                                                  Outputable.$$
                                                                  Panic.noString tys) emptyTCvSubst else
    mkTvSubst (mkInScopeSet (tyCoVarsOfTypes tys)) tenv.

Definition tyCoVarsOfTypesDSet : list Type_ -> DTyCoVarSet :=
  fun tys => fvDVarSet (tyCoFVsOfTypes tys).

Definition tyCoVarsOfTypesList : list Type_ -> list TyCoVar :=
  fun tys => fvVarList (tyCoFVsOfTypes tys).

Definition tyCoVarsOfTypesSet : TyVarEnv Type_ -> TyCoVarSet :=
  fun tys => fvVarSet (tyCoFVsOfTypes (UniqFM.nonDetEltsUFM tys)).

Definition getTCvSubstRangeFVs : TCvSubst -> VarSet :=
  fun arg_0__ =>
    let 'TCvSubst _ tenv cenv := arg_0__ in
    let cenvFVs := tyCoVarsOfCosSet cenv in
    let tenvFVs := tyCoVarsOfTypesSet tenv in unionVarSet tenvFVs cenvFVs.

Definition isValidTCvSubst : TCvSubst -> bool :=
  fun arg_0__ =>
    let 'TCvSubst in_scope tenv cenv := arg_0__ in
    let cenvFVs := tyCoVarsOfCosSet cenv in
    let tenvFVs := tyCoVarsOfTypesSet tenv in
    andb (varSetInScope tenvFVs in_scope) (varSetInScope cenvFVs in_scope).

Definition checkValidSubst {a} `{GHC.Stack.Types.HasCallStack}
   : TCvSubst -> list Type_ -> list Coercion -> a -> a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | (TCvSubst in_scope tenv cenv as subst), tys, cos, a =>
        let substDomain :=
          Coq.Init.Datatypes.app (UniqFM.nonDetKeysUFM tenv) (UniqFM.nonDetKeysUFM
                                  cenv) in
        let needInScope :=
          UniqSet.delListFromUniqSet_Directly (unionVarSet (tyCoVarsOfTypes tys)
                                                           (tyCoVarsOfCos cos)) substDomain in
        let tysCosFVsInScope := varSetInScope needInScope in_scope in
        Panic.warnPprTrace (negb (isValidTCvSubst subst)) (GHC.Base.hs_string__
                            "ghc/compiler/types/TyCoRep.hs") #2147 (GHC.Base.mappend (GHC.Base.mappend
                                                                                      (GHC.Base.mappend
                                                                                       (GHC.Base.mappend
                                                                                        (GHC.Base.mappend
                                                                                         (GHC.Base.mappend
                                                                                          (GHC.Base.mappend (id
                                                                                                             (GHC.Base.hs_string__
                                                                                                              "in_scope"))
                                                                                                            (Panic.noString
                                                                                                             in_scope)
                                                                                           Outputable.$$
                                                                                           id (GHC.Base.hs_string__
                                                                                               "tenv")) (Panic.noString
                                                                                           tenv) Outputable.$$
                                                                                          id (GHC.Base.hs_string__
                                                                                              "tenvFVs"))
                                                                                         (Panic.noString
                                                                                          (tyCoVarsOfTypesSet tenv))
                                                                                         Outputable.$$
                                                                                         id (GHC.Base.hs_string__
                                                                                             "cenv")) (Panic.noString
                                                                                         cenv) Outputable.$$
                                                                                        id (GHC.Base.hs_string__
                                                                                            "cenvFVs")) (Panic.noString
                                                                                        (tyCoVarsOfCosSet cenv))
                                                                                       Outputable.$$
                                                                                       id (GHC.Base.hs_string__ "tys"))
                                                                                      (Panic.noString tys) Outputable.$$
                                                                                      id (GHC.Base.hs_string__ "cos"))
                                                                                     (Panic.noString cos))
        (Panic.warnPprTrace (negb tysCosFVsInScope) (GHC.Base.hs_string__
                             "ghc/compiler/types/TyCoRep.hs") #2154 (GHC.Base.mappend (GHC.Base.mappend
                                                                                       (GHC.Base.mappend
                                                                                        (GHC.Base.mappend
                                                                                         (GHC.Base.mappend
                                                                                          (GHC.Base.mappend (id
                                                                                                             (GHC.Base.hs_string__
                                                                                                              "in_scope"))
                                                                                                            (Panic.noString
                                                                                                             in_scope)
                                                                                           Outputable.$$
                                                                                           id (GHC.Base.hs_string__
                                                                                               "tenv")) (Panic.noString
                                                                                           tenv) Outputable.$$
                                                                                          id (GHC.Base.hs_string__
                                                                                              "cenv")) (Panic.noString
                                                                                          cenv) Outputable.$$
                                                                                         id (GHC.Base.hs_string__
                                                                                             "tys")) (Panic.noString
                                                                                         tys) Outputable.$$
                                                                                        id (GHC.Base.hs_string__ "cos"))
                                                                                       (Panic.noString cos)
                                                                                       Outputable.$$
                                                                                       id (GHC.Base.hs_string__
                                                                                           "needInScope"))
                                                                                      (Panic.noString needInScope)) a)
    end.

Definition tyCoVarsOfType : Type_ -> TyCoVarSet :=
  fun ty => fvVarSet (tyCoFVsOfType ty).

Definition extendTvSubstAndInScope : TCvSubst -> TyVar -> Type_ -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | TCvSubst in_scope tenv cenv, tv, ty =>
        TCvSubst (extendInScopeSetSet in_scope (tyCoVarsOfType ty)) (extendVarEnv tenv
                                                                     tv ty) cenv
    end.

Definition extendTvSubstBinderAndInScope
   : TCvSubst -> TyBinder -> Type_ -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | subst, Named bndr, ty => extendTvSubstAndInScope subst (binderVar bndr) ty
    | subst, Anon _, _ => subst
    end.

Definition extendTvSubstWithClone : TCvSubst -> TyVar -> TyVar -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | TCvSubst in_scope tenv cenv, tv, tv' =>
        let new_in_scope := extendVarSet (tyCoVarsOfType (tyVarKind tv')) tv' in
        TCvSubst (extendInScopeSetSet in_scope new_in_scope) (extendVarEnv tenv tv
                                                              (mkTyVarTy tv')) cenv
    end.

Definition noFreeVarsOfType : Type_ -> bool :=
  fix noFreeVarsOfType arg_0__
        := match arg_0__ with
           | TyVarTy _ => false
           | AppTy t1 t2 => andb (noFreeVarsOfType t1) (noFreeVarsOfType t2)
           | TyConApp _ tys => Data.Foldable.all noFreeVarsOfType tys
           | (ForAllTy _ _ as ty) => isEmptyVarSet (tyCoVarsOfType ty)
           | FunTy t1 t2 => andb (noFreeVarsOfType t1) (noFreeVarsOfType t2)
           | LitTy _ => true
           | CastTy ty co => andb (noFreeVarsOfType ty) (noFreeVarsOfCo co)
           | CoercionTy co => noFreeVarsOfCo co
           end.

Definition noFreeVarsOfCo : Coercion -> bool :=
  fix noFreeVarsOfCo arg_0__
        := match arg_0__ with
           | Refl _ ty => noFreeVarsOfType ty
           | TyConAppCo _ _ args => Data.Foldable.all noFreeVarsOfCo args
           | AppCo c1 c2 => andb (noFreeVarsOfCo c1) (noFreeVarsOfCo c2)
           | (ForAllCo _ _ _ as co) => isEmptyVarSet (tyCoVarsOfCo co)
           | FunCo _ c1 c2 => andb (noFreeVarsOfCo c1) (noFreeVarsOfCo c2)
           | CoVarCo _ => false
           | HoleCo _ => true
           | AxiomInstCo _ _ args => Data.Foldable.all noFreeVarsOfCo args
           | UnivCo p _ t1 t2 =>
               andb (noFreeVarsOfProv p) (andb (noFreeVarsOfType t1) (noFreeVarsOfType t2))
           | SymCo co => noFreeVarsOfCo co
           | TransCo co1 co2 => andb (noFreeVarsOfCo co1) (noFreeVarsOfCo co2)
           | NthCo _ co => noFreeVarsOfCo co
           | LRCo _ co => noFreeVarsOfCo co
           | InstCo co1 co2 => andb (noFreeVarsOfCo co1) (noFreeVarsOfCo co2)
           | CoherenceCo co1 co2 => andb (noFreeVarsOfCo co1) (noFreeVarsOfCo co2)
           | KindCo co => noFreeVarsOfCo co
           | SubCo co => noFreeVarsOfCo co
           | AxiomRuleCo _ cs => Data.Foldable.all noFreeVarsOfCo cs
           end.

Definition noFreeVarsOfProv : UnivCoProvenance -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | UnsafeCoerceProv => true
    | PhantomProv co => noFreeVarsOfCo co
    | ProofIrrelProv co => noFreeVarsOfCo co
    | PluginProv _ => true
    end.

Definition splitVisVarsOfType : Type_ -> Pair.Pair TyCoVarSet :=
  fun orig_ty =>
    let invisible := fun vs => Pair.Mk_Pair vs emptyVarSet in
    let fix go arg_1__
              := match arg_1__ with
                 | TyVarTy tv => Pair.Mk_Pair (tyCoVarsOfType (tyVarKind tv)) (unitVarSet tv)
                 | AppTy t1 t2 => GHC.Base.mappend (go t1) (go t2)
                 | TyConApp tc tys => go_tc tc tys
                 | FunTy t1 t2 => GHC.Base.mappend (go t1) (go t2)
                 | ForAllTy (TvBndr tv _) ty =>
                     GHC.Base.mappend ((fun arg_6__ => delVarSet arg_6__ tv) Data.Functor.<$> go ty)
                                      (invisible (tyCoVarsOfType (tyVarKind tv)))
                 | LitTy _ => GHC.Base.mempty
                 | CastTy ty co => GHC.Base.mappend (go ty) (invisible (tyCoVarsOfCo co))
                 | CoercionTy co => invisible (tyCoVarsOfCo co)
                 end in
    let go_tc :=
      fun tc tys =>
        let 'pair invis vis := partitionInvisibles tc GHC.Base.id tys in
        GHC.Base.mappend (invisible (tyCoVarsOfTypes invis)) (Data.Foldable.foldMap go
                          vis) in
    let 'Pair.Mk_Pair invis_vars1 vis_vars := go orig_ty in
    let invis_vars := minusVarSet invis_vars1 vis_vars in
    Pair.Mk_Pair invis_vars vis_vars.

Definition splitVisVarsOfTypes : list Type_ -> Pair.Pair TyCoVarSet :=
  Data.Foldable.foldMap splitVisVarsOfType.

Definition mkTyConBindersPreferAnon : list TyVar -> Type_ -> list TyConBinder :=
  fun vars inner_ty =>
    let go : list TyVar -> (list TyConBinder * VarSet)%type :=
      fix go arg_0__
            := match arg_0__ with
               | nil => pair nil (tyCoVarsOfType inner_ty)
               | cons v vs =>
                   let kind_vars := tyCoVarsOfType (tyVarKind v) in
                   let 'pair binders fvs := go vs in
                   if elemVarSet v fvs : bool
                   then pair (cons (TvBndr v (NamedTCB Required)) binders) (unionVarSet (delVarSet
                                                                                         fvs v) kind_vars) else
                   pair (cons (TvBndr v AnonTCB) binders) (unionVarSet fvs kind_vars)
               end in
    Data.Tuple.fst (go vars).

Definition tyCoVarsOfTypeDSet : Type_ -> DTyCoVarSet :=
  fun ty => fvDVarSet (tyCoFVsOfType ty).

Definition tyCoVarsOfTypeList : Type_ -> list TyCoVar :=
  fun ty => fvVarList (tyCoFVsOfType ty).

Definition tidyOpenTyCoVar : TidyEnv -> TyCoVar -> (TidyEnv * TyCoVar)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (pair _ subst as env), tyvar =>
        match lookupVarEnv subst tyvar with
        | Some tyvar' => pair env tyvar'
        | None =>
            let env' := tidyFreeTyCoVars env (tyCoVarsOfTypeList (tyVarKind tyvar)) in
            tidyTyCoVarBndr env' tyvar
        end
    end.

Definition tidyFreeTyCoVars : TidyEnv -> list TyCoVar -> TidyEnv :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair full_occ_env var_env, tyvars =>
        Data.Tuple.fst (tidyOpenTyCoVars (pair full_occ_env var_env) tyvars)
    end.

Definition tidyOpenTyCoVars
   : TidyEnv -> list TyCoVar -> (TidyEnv * list TyCoVar)%type :=
  fun env tyvars => Data.Traversable.mapAccumL tidyOpenTyCoVar env tyvars.

Definition toposortTyVars : list TyCoVar -> list TyCoVar :=
  fun tvs =>
    let var_ids : VarEnv GHC.Num.Int := mkVarEnv (GHC.List.zip tvs (enumFrom #1)) in
    let nodes : list (Digraph.Node GHC.Num.Int TyVar) :=
      Coq.Lists.List.flat_map (fun tv =>
                                 cons (Digraph.DigraphNode tv (lookupVarEnv_NF var_ids tv) (Data.Maybe.mapMaybe
                                                                                            (lookupVarEnv var_ids)
                                                                                            (tyCoVarsOfTypeList
                                                                                             (tyVarKind tv)))) nil)
                              tvs in
    GHC.List.reverse (Coq.Lists.List.flat_map (fun node =>
                                                 cons (Digraph.node_payload node) nil) (Digraph.topologicalSortG
                                               (Digraph.graphFromEdgedVerticesOrd nodes))).

Definition tidyToIfaceCo : Coercion -> IfaceType.IfaceCoercion :=
  fun co =>
    let free_tcvs := toposortTyVars (tyCoVarsOfCoList co) in
    let env := tidyFreeTyCoVars emptyTidyEnv free_tcvs in
    ToIface.toIfaceCoercionX (mkVarSet free_tcvs) (tidyCo env co).

Definition tidyToIfaceCoSty
   : Coercion -> Outputable.PprStyle -> IfaceType.IfaceCoercion :=
  fun co sty =>
    if Outputable.userStyle sty : bool then tidyToIfaceCo co else
    ToIface.toIfaceCoercionX (tyCoVarsOfCo co) co.

Definition pprCo : Coercion -> GHC.Base.String :=
  fun co =>
    Outputable.getPprStyle (fun sty =>
                              IfaceType.pprIfaceCoercion (tidyToIfaceCoSty co sty)).

Definition pprParendCo : Coercion -> GHC.Base.String :=
  fun co =>
    Outputable.getPprStyle (fun sty =>
                              IfaceType.pprParendIfaceCoercion (tidyToIfaceCoSty co sty)).

Definition tyCoVarsOfTypesWellScoped : list Type_ -> list TyVar :=
  toposortTyVars GHC.Base.∘ tyCoVarsOfTypesList.

Definition tidyOpenTypes
   : TidyEnv -> list Type_ -> (TidyEnv * list Type_)%type :=
  fun env tys =>
    let 'pair (pair _ var_env as env') tvs' := tidyOpenTyCoVars env
                                                 (tyCoVarsOfTypesWellScoped tys) in
    let trimmed_occ_env :=
      OccName.initTidyOccEnv (GHC.Base.map Name.getOccName tvs') in
    pair env' (tidyTypes (pair trimmed_occ_env var_env) tys).

Definition tidyOpenType : TidyEnv -> Type_ -> (TidyEnv * Type_)%type :=
  fun env ty =>
    let 'pair env' (cons ty' nil) := tidyOpenTypes env (cons ty nil) in
    pair env' ty'.

Definition tidyOpenKind : TidyEnv -> Kind -> (TidyEnv * Kind)%type :=
  tidyOpenType.

Definition dVarSetElemsWellScoped : DVarSet -> list Var :=
  toposortTyVars GHC.Base.∘ dVarSetElems.

Definition tyCoVarsOfTypeWellScoped : Type_ -> list TyVar :=
  toposortTyVars GHC.Base.∘ tyCoVarsOfTypeList.

Definition tidyToIfaceType : Type_ -> IfaceType.IfaceType :=
  fun ty =>
    let free_tcvs := tyCoVarsOfTypeWellScoped ty in
    let env := tidyFreeTyCoVars emptyTidyEnv free_tcvs in
    ToIface.toIfaceTypeX (mkVarSet free_tcvs) (tidyType env ty).

Definition pprParendTheta : ThetaType -> GHC.Base.String :=
  IfaceType.pprIfaceContext BasicTypes.TyConPrec GHC.Base.∘
  GHC.Base.map tidyToIfaceType.

Definition pprSigmaType : Type_ -> GHC.Base.String :=
  IfaceType.pprIfaceSigmaType IfaceType.ShowForAllWhen GHC.Base.∘ tidyToIfaceType.

Definition pprTheta : ThetaType -> GHC.Base.String :=
  IfaceType.pprIfaceContext BasicTypes.TopPrec GHC.Base.∘
  GHC.Base.map tidyToIfaceType.

Definition pprThetaArrowTy : ThetaType -> GHC.Base.String :=
  IfaceType.pprIfaceContextArr GHC.Base.∘ GHC.Base.map tidyToIfaceType.

Definition tidyToIfaceTypeSty
   : Type_ -> Outputable.PprStyle -> IfaceType.IfaceType :=
  fun ty sty =>
    if Outputable.userStyle sty : bool then tidyToIfaceType ty else
    ToIface.toIfaceTypeX (tyCoVarsOfType ty) ty.

Definition pprPrecType : BasicTypes.TyPrec -> Type_ -> GHC.Base.String :=
  fun prec ty =>
    Outputable.getPprStyle (fun sty =>
                              if Outputable.debugStyle sty : bool
                              then debug_ppr_ty prec ty
                              else IfaceType.pprPrecIfaceType prec (tidyToIfaceTypeSty ty sty)).

Definition pprParendType : Type_ -> GHC.Base.String :=
  pprPrecType BasicTypes.TyConPrec.

Definition pprDataConWithArgs : DataCon.DataCon -> GHC.Base.String :=
  fun dc =>
    let user_bndrs := DataCon.dataConUserTyVarBinders dc in
    let forAllDoc := pprUserForAll user_bndrs in
    let 'pair (pair (pair (pair (pair _univ_tvs _ex_tvs) _eq_spec) theta) arg_tys)
       _res_ty := DataCon.dataConFullSig dc in
    let thetaDoc := pprThetaArrowTy theta in
    let argsDoc := Outputable.hsep (GHC.Base.fmap pprParendType arg_tys) in
    Outputable.sep (cons forAllDoc (cons thetaDoc (cons (GHC.Base.mappend
                                                         (Panic.noString dc) argsDoc) nil))).

Definition pprDataCons : TyCon -> GHC.Base.String :=
  let sepWithVBars :=
    fun arg_0__ =>
      match arg_0__ with
      | nil => Panic.someSDoc
      | docs => Outputable.sep (Panic.someSDoc)
      end in
  sepWithVBars GHC.Base.∘
  (GHC.Base.fmap pprDataConWithArgs GHC.Base.∘ tyConDataCons).

Definition pprParendKind : Kind -> GHC.Base.String :=
  pprParendType.

Definition pprType : Type_ -> GHC.Base.String :=
  pprPrecType BasicTypes.TopPrec.

Definition pprKind : Kind -> GHC.Base.String :=
  pprType.

Definition tcTyVarDetails : TyVar -> Core.TcTyVarDetails :=
  fun arg_0__ =>
    match arg_0__ with
    | TcTyVar _ _ _ details => details
    | TyVar _ _ _ => TcType.vanillaSkolemTv
    | var =>
        Panic.panicStr (GHC.Base.hs_string__ "tcTyVarDetails") (GHC.Base.mappend
                                                                (GHC.Base.mappend (Panic.noString var)
                                                                                  Outputable.dcolon) (pprKind (tyVarKind
                                                                                                               var)))
    end.

Definition closeOverKindsFV : list TyVar -> FV :=
  fun tvs =>
    unionFV (mapUnionFV (tyCoFVsOfType GHC.Base.∘ tyVarKind) tvs) (mkFVs tvs).

Definition closeOverKindsList : list TyVar -> list TyVar :=
  fun tvs => fvVarList (closeOverKindsFV tvs).

Definition closeOverKindsDSet : DTyVarSet -> DTyVarSet :=
  fvDVarSet GHC.Base.∘ (closeOverKindsFV GHC.Base.∘ dVarSetElems).

Definition closeOverKinds : TyVarSet -> TyVarSet :=
  fvVarSet GHC.Base.∘ (closeOverKindsFV GHC.Base.∘ UniqSet.nonDetEltsUniqSet).

Definition coVarKind : CoVar -> Type_ :=
  fun cv =>
    if andb Util.debugIsOn (negb (isCoVar cv)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #311)
    else varType cv.

Definition coVarName : CoVar -> Name.Name :=
  varName.

Axiom coercionKind : forall {A : Type}, A.

Definition coercionKinds : list Coercion -> Pair.Pair (list Type_) :=
  fun tys => Data.Traversable.sequenceA (GHC.Base.map coercionKind tys).

Definition liftCoSubstVarBndrCallback {a}
   : (LiftingContext -> Type_ -> (Coercion * a)%type) ->
     LiftingContext -> TyVar -> (LiftingContext * TyVar * Coercion * a)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | fun_, (LC subst cenv as lc), old_var =>
        let old_kind := tyVarKind old_var in
        let 'pair eta stuff := fun_ lc old_kind in
        let 'Pair.Mk_Pair k1 _ := coercionKind eta in
        let new_var := uniqAway (getTCvInScope subst) (setVarType old_var k1) in
        let lifted := Refl Nominal (TyVarTy new_var) in
        let new_cenv := extendVarEnv cenv old_var lifted in
        pair (pair (pair (LC (extendTCvInScope subst new_var) new_cenv) new_var) eta)
             stuff
    end.

Definition substForAllCoBndrCallback
   : bool ->
     (Coercion -> Coercion) ->
     TCvSubst -> TyVar -> Coercion -> (TCvSubst * TyVar * Coercion)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | sym, sco, TCvSubst in_scope tenv cenv, old_var, old_kind_co =>
        let no_kind_change := noFreeVarsOfCo old_kind_co in
        let new_kind_co :=
          if no_kind_change : bool then old_kind_co else
          sco old_kind_co in
        let 'Pair.Mk_Pair new_ki1 _ := coercionKind new_kind_co in
        let new_var := uniqAway in_scope (setTyVarKind old_var new_ki1) in
        let no_change := andb no_kind_change (new_var GHC.Base.== old_var) in
        let new_env :=
          if andb no_change (negb sym) : bool then delVarEnv tenv old_var else
          if sym : bool
          then extendVarEnv tenv old_var (CastTy (TyVarTy new_var) new_kind_co) else
          extendVarEnv tenv old_var (TyVarTy new_var) in
        pair (pair (TCvSubst (extendInScopeSet in_scope new_var) new_env cenv) new_var)
             new_kind_co
    end.

(* Translating `coercionKind' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Axiom coercionKindRole : forall {A : Type}, A.

Definition coercionRole : Coercion -> Role :=
  Data.Tuple.snd GHC.Base.∘ coercionKindRole.

Definition setNominalRole_maybe : Coercion -> option Coercion :=
  fix setNominalRole_maybe arg_0__
        := let 'co := arg_0__ in
           match coercionRole co with
           | Nominal => Some co
           | _ =>
               match arg_0__ with
               | SubCo co => Some co
               | Refl _ ty => Some (Refl Nominal ty)
               | TyConAppCo Representational tc cos =>
                   Data.Traversable.mapM setNominalRole_maybe cos GHC.Base.>>=
                   (fun cos' => GHC.Base.return_ (TyConAppCo Nominal tc cos'))
               | FunCo Representational co1 co2 =>
                   setNominalRole_maybe co1 GHC.Base.>>=
                   (fun co1' =>
                      setNominalRole_maybe co2 GHC.Base.>>=
                      (fun co2' => GHC.Base.return_ (FunCo Nominal co1' co2')))
               | SymCo co => SymCo Data.Functor.<$> setNominalRole_maybe co
               | TransCo co1 co2 =>
                   (TransCo Data.Functor.<$> setNominalRole_maybe co1) GHC.Base.<*>
                   setNominalRole_maybe co2
               | AppCo co1 co2 =>
                   (AppCo Data.Functor.<$> setNominalRole_maybe co1) GHC.Base.<*> GHC.Base.pure co2
               | ForAllCo tv kind_co co =>
                   ForAllCo tv kind_co Data.Functor.<$> setNominalRole_maybe co
               | NthCo n co => NthCo n Data.Functor.<$> setNominalRole_maybe co
               | InstCo co arg =>
                   (InstCo Data.Functor.<$> setNominalRole_maybe co) GHC.Base.<*> GHC.Base.pure arg
               | CoherenceCo co1 co2 =>
                   (CoherenceCo Data.Functor.<$> setNominalRole_maybe co1) GHC.Base.<*>
                   GHC.Base.pure co2
               | UnivCo prov _ co1 co2 =>
                   if (match prov with
                       | UnsafeCoerceProv => true
                       | PhantomProv _ => false
                       | ProofIrrelProv _ => true
                       | PluginProv _ => false
                       end) : bool
                   then Some (UnivCo prov Nominal co1 co2) else
                   None
               end
           end.

(* Translating `coercionKindRole' failed: using a record pattern for the unknown
   constructor `LRCo' unsupported *)

Definition composeSteppers {ev}
   : NormaliseStepper ev -> NormaliseStepper ev -> NormaliseStepper ev :=
  fun step1 step2 rec_nts tc tys =>
    match step1 rec_nts tc tys with
    | (NS_Step _ _ _ as success) => success
    | NS_Done => step2 rec_nts tc tys
    | NS_Abort => NS_Abort
    end.

Definition emptyLiftingContext : InScopeSet -> LiftingContext :=
  fun in_scope => LC (mkEmptyTCvSubst in_scope) emptyVarEnv.

Definition extendLiftingContext
   : LiftingContext -> TyVar -> Coercion -> LiftingContext :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | LC subst env, tv, arg =>
        if andb Util.debugIsOn (negb (isTyVar tv)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
              #1460)
        else LC subst (extendVarEnv env tv arg)
    end.

Definition getCoVar_maybe : Coercion -> option CoVar :=
  fun arg_0__ => match arg_0__ with | CoVarCo cv => Some cv | _ => None end.

Definition isCoVar_maybe : Coercion -> option CoVar :=
  fun arg_0__ => match arg_0__ with | CoVarCo cv => Some cv | _ => None end.

Definition isMappedByLC : TyCoVar -> LiftingContext -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | tv, LC _ env => elemVarEnv tv env
    end.

Axiom isReflCo : forall {A : Type}, A.

Definition mkForAllCos : list (TyVar * Coercion)%type -> Coercion -> Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | bndrs, Refl r ty =>
        let 'pair refls_rev'd non_refls_rev'd := GHC.List.span (isReflCo GHC.Base.∘
                                                                Data.Tuple.snd) (GHC.List.reverse bndrs) in
        Data.Foldable.foldl (GHC.Base.flip (Data.Tuple.uncurry ForAllCo)) (Refl r
                                                                           (mkInvForAllTys (GHC.List.reverse
                                                                                            (GHC.Base.map Data.Tuple.fst
                                                                                             refls_rev'd)) ty))
        non_refls_rev'd
    | bndrs, co => Data.Foldable.foldr (Data.Tuple.uncurry ForAllCo) co bndrs
    end.

(* Translating `isReflCo' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Definition isReflCo_maybe : Coercion -> option (Type_ * Role)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Refl r ty => Some (pair ty r)
    | _ => None
    end.

Definition mkFunCo : Role -> Coercion -> Coercion -> Coercion :=
  fun r co1 co2 =>
    let j_0__ := FunCo r co1 co2 in
    match isReflCo_maybe co1 with
    | Some (pair ty1 _) =>
        match isReflCo_maybe co2 with
        | Some (pair ty2 _) => Refl r (mkFunTy ty1 ty2)
        | _ => j_0__
        end
    | _ => j_0__
    end.

Definition mkFunCos : Role -> list Coercion -> Coercion -> Coercion :=
  fun r cos res_co => Data.Foldable.foldr (mkFunCo r) res_co cos.

Definition lcInScopeSet : LiftingContext -> InScopeSet :=
  fun arg_0__ => let 'LC subst _ := arg_0__ in getTCvInScope subst.

Definition lcTCvSubst : LiftingContext -> TCvSubst :=
  fun arg_0__ => let 'LC subst _ := arg_0__ in subst.

Definition ltRole : Role -> Role -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Phantom, _ => false
    | Representational, Phantom => true
    | Representational, _ => false
    | Nominal, Nominal => false
    | Nominal, _ => true
    end.

Definition mapStepResult {ev1} {ev2}
   : (ev1 -> ev2) -> NormaliseStepResult ev1 -> NormaliseStepResult ev2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, NS_Step rec_nts ty ev => NS_Step rec_nts ty (f ev)
    | _, NS_Done => NS_Done
    | _, NS_Abort => NS_Abort
    end.

Definition mkAppCos : Coercion -> list Coercion -> Coercion :=
  fun co1 cos => Data.Foldable.foldl mkAppCo co1 cos.

Definition mkAxiomRuleCo : CoAxiomRule -> list Coercion -> Coercion :=
  AxiomRuleCo.

Definition mkCoVarCo : CoVar -> Coercion :=
  fun cv => CoVarCo cv.

Definition mkCoVarCos : list CoVar -> list Coercion :=
  GHC.Base.map mkCoVarCo.

Definition extendCvSubstWithClone : TCvSubst -> CoVar -> CoVar -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | TCvSubst in_scope tenv cenv, cv, cv' =>
        let new_in_scope := extendVarSet (tyCoVarsOfType (varType cv')) cv' in
        TCvSubst (extendInScopeSetSet in_scope new_in_scope) tenv (extendVarEnv cenv cv
                                                                   (mkCoVarCo cv'))
    end.

Axiom mkCoherenceCo : forall {A : Type}, A.

Definition mkCoherenceLeftCo : Coercion -> Coercion -> Coercion :=
  mkCoherenceCo.

(* Translating `mkCoherenceCo' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Axiom mkForAllCo : forall {A : Type}, A.

(* Translating `mkForAllCo' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Definition mkHeteroCoercionType
   : Role -> Kind -> Kind -> Type_ -> Type_ -> Type_ :=
  fun arg_0__ =>
    match arg_0__ with
    | Nominal => mkHeteroPrimEqPred
    | Representational => mkHeteroReprPrimEqPred
    | Phantom => Panic.panic (GHC.Base.hs_string__ "mkHeteroCoercionType")
    end.

Definition mkHoleCo : CoercionHole -> Coercion :=
  fun h => HoleCo h.

Definition mkLiftingContext
   : list (TyCoVar * Coercion)%type -> LiftingContext :=
  fun pairs =>
    LC (mkEmptyTCvSubst (mkInScopeSet (tyCoVarsOfCos (GHC.Base.map Data.Tuple.snd
                                                      pairs)))) (mkVarEnv pairs).

Axiom mkProofIrrelCo : forall {A : Type}, A.

(* Translating `mkProofIrrelCo' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Definition mkReflCo : Role -> Type_ -> Coercion :=
  fun r ty => Refl r ty.

Definition mkRepReflCo : Type_ -> Coercion :=
  mkReflCo Representational.

Definition mkNomReflCo : Type_ -> Coercion :=
  mkReflCo Nominal.

Definition mkHomoForAllCos_NoRefl : list TyVar -> Coercion -> Coercion :=
  fun tvs orig_co =>
    let go := fun tv co => ForAllCo tv (mkNomReflCo (tyVarKind tv)) co in
    Data.Foldable.foldr go orig_co tvs.

Definition mkHomoForAllCos : list TyVar -> Coercion -> Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | tvs, Refl r ty => Refl r (mkInvForAllTys tvs ty)
    | tvs, ty => mkHomoForAllCos_NoRefl tvs ty
    end.

Definition mkPiCo : Role -> Var -> Coercion -> Coercion :=
  fun r v co =>
    if isTyVar v : bool then mkHomoForAllCos (cons v nil) co else
    mkFunCo r (mkReflCo r (varType v)) co.

Definition mkPiCos : Role -> list Var -> Coercion -> Coercion :=
  fun r vs co => Data.Foldable.foldr (mkPiCo r) co vs.

Definition mkSubstLiftingContext : TCvSubst -> LiftingContext :=
  fun subst => LC subst emptyVarEnv.

Axiom mkSymCo : forall {A : Type}, A.

Definition swapLiftCoEnv : LiftCoEnv -> LiftCoEnv :=
  mapVarEnv mkSymCo.

Definition mkCoherenceRightCo : Coercion -> Coercion -> Coercion :=
  fun c1 c2 => mkSymCo (mkCoherenceCo (mkSymCo c1) c2).

Definition castCoercionKind : Coercion -> Coercion -> Coercion -> Coercion :=
  fun g h1 h2 => mkCoherenceRightCo (mkCoherenceLeftCo g h1) h2.

(* Translating `mkSymCo' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Axiom mkTransCo : forall {A : Type}, A.

(* Translating `mkTransCo' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Definition ppr_co_ax_branch {br}
   : (TyCon -> Type_ -> GHC.Base.String) ->
     CoAxiom br -> CoAxBranch -> GHC.Base.String :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | ppr_rhs, CoAxiom _ name _ fam_tc _ _, Mk_CoAxBranch loc tvs cvs _ lhs rhs _ =>
        let pprLoc :=
          fun loc =>
            if SrcLoc.isGoodSrcSpan loc : bool
            then GHC.Base.mappend (id (GHC.Base.hs_string__ "at")) (Panic.noString
                                   (SrcLoc.srcSpanStart loc)) else
            GHC.Base.mappend (id (GHC.Base.hs_string__ "in")) (Outputable.quotes
                              (Panic.noString (Name.nameModule name))) in
        Data.Foldable.foldr1 (GHC.Base.flip Outputable.hangNotEmpty #2) (cons
                                                                         (pprUserForAll (mkTyVarBinders Inferred
                                                                                         (Coq.Init.Datatypes.app tvs
                                                                                                                 cvs)))
                                                                         (cons (GHC.Base.mappend (GHC.Base.mappend
                                                                                                  (pprTypeApp fam_tc
                                                                                                   lhs)
                                                                                                  Outputable.equals)
                                                                                                 (ppr_rhs fam_tc rhs))
                                                                               (cons (GHC.Base.mappend (id
                                                                                                        (GHC.Base.hs_string__
                                                                                                         "-- Defined"))
                                                                                                       (pprLoc loc))
                                                                                     nil)))
    end.

Axiom promoteCoercion : forall {A : Type}, A.

(* Translating `promoteCoercion' failed: using a record pattern for the unknown
   constructor `CoVarCo' unsupported *)

Definition seqCos : list Coercion -> unit :=
  fix seqCos arg_0__
        := match arg_0__ with
           | nil => tt
           | cons co cos => seqCos cos
           end.

Definition seqCo : Coercion -> unit :=
  fix seqCo arg_0__
        := match arg_0__ with
           | Refl r ty => seqType ty
           | TyConAppCo r tc cos => seqCos cos
           | AppCo co1 co2 => seqCo co2
           | ForAllCo tv k co => seqCo co
           | FunCo r co1 co2 => seqCo co2
           | CoVarCo cv => tt
           | HoleCo h => tt
           | AxiomInstCo con ind cos => seqCos cos
           | UnivCo p r t1 t2 => seqType t2
           | SymCo co => seqCo co
           | TransCo co1 co2 => seqCo co2
           | NthCo n co => seqCo co
           | LRCo lr co => seqCo co
           | InstCo co arg => seqCo arg
           | CoherenceCo co1 co2 => seqCo co2
           | KindCo co => seqCo co
           | SubCo co => seqCo co
           | AxiomRuleCo _ cs => seqCos cs
           end.

Definition seqType : Type_ -> unit :=
  fix seqType arg_0__
        := match arg_0__ with
           | LitTy n => tt
           | TyVarTy tv => tt
           | AppTy t1 t2 => seqType t2
           | FunTy t1 t2 => seqType t2
           | TyConApp tc tys => seqTypes tys
           | ForAllTy (TvBndr tv _) ty => seqType ty
           | CastTy ty co => seqCo co
           | CoercionTy co => seqCo co
           end.

Definition seqProv : UnivCoProvenance -> unit :=
  fun arg_0__ =>
    match arg_0__ with
    | UnsafeCoerceProv => tt
    | PhantomProv co => seqCo co
    | ProofIrrelProv co => seqCo co
    | PluginProv _ => tt
    end.

Definition setCoVarName : CoVar -> Name.Name -> CoVar :=
  setVarName.

Definition setCoVarUnique : CoVar -> Unique.Unique -> CoVar :=
  setVarUnique.

Definition splitForAllCo_maybe
   : Coercion -> option (TyVar * Coercion * Coercion)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | ForAllCo tv k_co co => Some (pair (pair tv k_co) co)
    | _ => None
    end.

Definition splitFunCo_maybe : Coercion -> option (Coercion * Coercion)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | FunCo _ arg res => Some (pair arg res)
    | _ => None
    end.

Definition substForAllCoBndrCallbackLC
   : bool ->
     (Coercion -> Coercion) ->
     LiftingContext ->
     TyVar -> Coercion -> (LiftingContext * TyVar * Coercion)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | sym, sco, LC subst lc_env, tv, co =>
        let 'pair (pair subst' tv') co' := substForAllCoBndrCallback sym sco subst tv
                                             co in
        pair (pair (LC subst' lc_env) tv') co'
    end.

Definition tyConRolesRepresentational : TyCon -> list Role :=
  fun tc => Coq.Init.Datatypes.app (tyConRoles tc) (GHC.List.repeat Nominal).

Definition tyConRolesX : Role -> TyCon -> list Role :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Representational, tc => tyConRolesRepresentational tc
    | role, _ => GHC.List.repeat role
    end.

Definition nthRole : Role -> TyCon -> GHC.Num.Int -> Role :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Nominal, _, _ => Nominal
    | Phantom, _, _ => Phantom
    | Representational, tc, n => ListSetOps.getNth (tyConRolesRepresentational tc) n
    end.

Axiom ty_co_subst : forall {A : Type}, A.

Definition extendLiftingContextEx
   : LiftingContext -> list (TyVar * Type_)%type -> LiftingContext :=
  fix extendLiftingContextEx arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | lc, nil => lc
           | (LC subst env as lc), cons (pair v ty) rest =>
               let lc' :=
                 LC (extendTCvInScopeSet subst (tyCoVarsOfType ty)) (extendVarEnv env v (mkSymCo
                                                                                         (mkCoherenceCo (mkNomReflCo ty)
                                                                                                        (ty_co_subst lc
                                                                                                         Nominal
                                                                                                         (tyVarKind
                                                                                                          v))))) in
               extendLiftingContextEx lc' rest
           end.

Definition liftCoSubstVarBndr
   : LiftingContext -> TyVar -> (LiftingContext * TyVar * Coercion)%type :=
  fun lc tv =>
    let callback := fun lc' ty' => pair (ty_co_subst lc' Nominal ty') tt in
    let 'pair (pair (pair lc' tv') h) _ := liftCoSubstVarBndrCallback callback lc
                                             tv in
    pair (pair lc' tv') h.

(* Translating `ty_co_subst' failed: using a record pattern for the unknown
   constructor `LitTy' unsupported *)

Definition zapLiftingContext : LiftingContext -> LiftingContext :=
  fun arg_0__ => let 'LC subst _ := arg_0__ in LC (zapTCvSubst subst) emptyVarEnv.

Definition branchesNth {br} : Branches br -> BranchIndex -> CoAxBranch :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkBranches arr, n => arr GHC.Arr.! n
    end.

Definition coAxiomNthBranch {br} : CoAxiom br -> BranchIndex -> CoAxBranch :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CoAxiom _ _ _ _ bs _, index => branchesNth bs index
    end.

Definition coAxiomArity {br} : CoAxiom br -> BranchIndex -> BasicTypes.Arity :=
  fun ax index =>
    let 'Mk_CoAxBranch _ tvs cvs _ _ _ _ := coAxiomNthBranch ax index in
    Data.Foldable.length tvs GHC.Num.+ Data.Foldable.length cvs.

Definition mkAxiomInstCo
   : CoAxiom Branched -> BranchIndex -> list Coercion -> Coercion :=
  fun ax index args =>
    if andb Util.debugIsOn (negb (Util.lengthIs args (coAxiomArity ax
                                                 index))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #717)
    else AxiomInstCo ax index args.

Definition subst_co : TCvSubst -> Coercion -> Coercion :=
  fix subst_co subst co
        := let go_ty : Type_ -> Type_ := subst_ty subst in
           let go : Coercion -> Coercion :=
             fix go arg_1__
                   := match arg_1__ with
                      | Refl r ty => mkReflCo r (go_ty ty)
                      | TyConAppCo r tc args =>
                          let args' := GHC.Base.map go args in
                          Util.seqList args' (mkTyConAppCo r tc args')
                      | AppCo co arg => mkAppCo (go co) (go arg)
                      | ForAllCo tv kind_co co =>
                          let 'pair (pair subst' tv') kind_co' := substForAllCoBndrUnchecked subst tv
                                                                    kind_co in
                          mkForAllCo tv' kind_co' (subst_co subst' co)
                      | FunCo r co1 co2 => mkFunCo r (go co1) (go co2)
                      | CoVarCo cv => substCoVar subst cv
                      | AxiomInstCo con ind cos => mkAxiomInstCo con ind (GHC.Base.map go cos)
                      | UnivCo p r t1 t2 => mkUnivCo (go_prov p) r (go_ty t1) (go_ty t2)
                      | SymCo co => mkSymCo (go co)
                      | TransCo co1 co2 => mkTransCo (go co1) (go co2)
                      | NthCo d co => mkNthCo d (go co)
                      | LRCo lr co => mkLRCo lr (go co)
                      | InstCo co arg => mkInstCo (go co) (go arg)
                      | CoherenceCo co1 co2 => mkCoherenceCo (go co1) (go co2)
                      | KindCo co => mkKindCo (go co)
                      | SubCo co => mkSubCo (go co)
                      | AxiomRuleCo c cs =>
                          let cs1 := GHC.Base.map go cs in Util.seqList cs1 (AxiomRuleCo c cs1)
                      | HoleCo h => HoleCo h
                      end in
           let go_prov :=
             fun arg_26__ =>
               match arg_26__ with
               | UnsafeCoerceProv => UnsafeCoerceProv
               | PhantomProv kco => PhantomProv (go kco)
               | ProofIrrelProv kco => ProofIrrelProv (go kco)
               | (PluginProv _ as p) => p
               end in
           go co.

Definition mkUnivCo : UnivCoProvenance -> Role -> Type_ -> Type_ -> Coercion :=
  fun prov role ty1 ty2 =>
    if eqType ty1 ty2 : bool then Refl role ty1 else
    UnivCo prov role ty1 ty2.

Definition eqType : Type_ -> Type_ -> bool :=
  fun t1 t2 => Util.isEqual (nonDetCmpType t1 t2).

Definition nonDetCmpType : Type_ -> Type_ -> comparison :=
  fun t1 t2 =>
    let rn_env :=
      mkRnEnv2 (mkInScopeSet (tyCoVarsOfTypes (cons t1 (cons t2 nil)))) in
    nonDetCmpTypeX rn_env t1 t2.

Definition nonDetCmpTypeX : RnEnv2 -> Type_ -> Type_ -> comparison :=
  fun env orig_t1 orig_t2 =>
    let hasCast : TypeOrdering -> TypeOrdering :=
      fun arg_0__ => match arg_0__ with | TEQ => TEQX | rel => rel end in
    let thenCmpTy : TypeOrdering -> TypeOrdering -> TypeOrdering :=
      fun arg_2__ arg_3__ =>
        match arg_2__, arg_3__ with
        | TEQ, rel => rel
        | TEQX, rel => hasCast rel
        | rel, _ => rel
        end in
    let liftOrdering : comparison -> TypeOrdering :=
      fun arg_6__ => match arg_6__ with | Lt => TLT | Eq => TEQ | Gt => TGT end in
    let go : RnEnv2 -> Type_ -> Type_ -> TypeOrdering :=
      fix go arg_8__ arg_9__ arg_10__
            := match arg_8__, arg_9__, arg_10__ with
               | env, t1, t2 =>
                   match coreView t1 with
                   | Some t1' => go env t1' t2
                   | _ =>
                       match coreView t2 with
                       | Some t2' => go env t1 t2'
                       | _ =>
                           let j_27__ :=
                             match arg_8__, arg_9__, arg_10__ with
                             | env, FunTy s1 t1, FunTy s2 t2 => thenCmpTy (go env s1 s2) (go env t1 t2)
                             | env, TyConApp tc1 tys1, TyConApp tc2 tys2 =>
                                 thenCmpTy (liftOrdering (nonDetCmpTc tc1 tc2)) (gos env tys1 tys2)
                             | _, LitTy l1, LitTy l2 => liftOrdering (GHC.Base.compare l1 l2)
                             | env, CastTy t1 _, t2 => hasCast (go env t1 t2)
                             | env, t1, CastTy t2 _ => hasCast (go env t1 t2)
                             | _, CoercionTy _, CoercionTy _ => TEQ
                             | _, ty1, ty2 =>
                                 let get_rank : Type_ -> GHC.Num.Int :=
                                   fun arg_16__ =>
                                     match arg_16__ with
                                     | CastTy _ _ =>
                                         Panic.panicStr (GHC.Base.hs_string__ "nonDetCmpTypeX.get_rank") (Panic.noString
                                                                                                          (cons ty1
                                                                                                                (cons
                                                                                                                 ty2
                                                                                                                 nil)))
                                     | TyVarTy _ => #0
                                     | CoercionTy _ => #1
                                     | AppTy _ _ => #3
                                     | LitTy _ => #4
                                     | TyConApp _ _ => #5
                                     | FunTy _ _ => #6
                                     | ForAllTy _ _ => #7
                                     end in
                                 liftOrdering (GHC.Base.compare (get_rank ty1) (get_rank ty2))
                             end in
                           let j_29__ :=
                             match arg_8__, arg_9__, arg_10__ with
                             | env, ty1, AppTy s2 t2 =>
                                 match repSplitAppTy_maybe ty1 with
                                 | Some (pair s1 t1) => thenCmpTy (go env s1 s2) (go env t1 t2)
                                 | _ => j_27__
                                 end
                             | _, _, _ => j_27__
                             end in
                           match arg_8__, arg_9__, arg_10__ with
                           | env, TyVarTy tv1, TyVarTy tv2 =>
                               liftOrdering (nonDetCmpVar (rnOccL env tv1) (rnOccR env tv2))
                           | env, ForAllTy (TvBndr tv1 _) t1, ForAllTy (TvBndr tv2 _) t2 =>
                               thenCmpTy (go env (tyVarKind tv1) (tyVarKind tv2)) (go (rnBndr2 env tv1 tv2) t1
                                          t2)
                           | env, AppTy s1 t1, ty2 =>
                               match repSplitAppTy_maybe ty2 with
                               | Some (pair s2 t2) => thenCmpTy (go env s1 s2) (go env t1 t2)
                               | _ => j_29__
                               end
                           | _, _, _ => j_29__
                           end
                       end
                   end
               end in
    let gos : RnEnv2 -> list Type_ -> list Type_ -> TypeOrdering :=
      fix gos arg_37__ arg_38__ arg_39__
            := match arg_37__, arg_38__, arg_39__ with
               | _, nil, nil => TEQ
               | _, nil, _ => TLT
               | _, _, nil => TGT
               | env, cons ty1 tys1, cons ty2 tys2 =>
                   thenCmpTy (go env ty1 ty2) (gos env tys1 tys2)
               end in
    let toOrdering : TypeOrdering -> comparison :=
      fun arg_42__ =>
        match arg_42__ with
        | TLT => Lt
        | TEQ => Eq
        | TEQX => Eq
        | TGT => Gt
        end in
    let k2 := typeKind orig_t2 in
    let k1 := typeKind orig_t1 in
    match go env orig_t1 orig_t2 with
    | TEQX => toOrdering (go env k1 k2)
    | ty_ordering => toOrdering ty_ordering
    end.

Definition coreView : Type_ -> option Type_ :=
  fun arg_0__ =>
    let j_2__ :=
      match arg_0__ with
      | TyConApp tc nil =>
          if Kind.isStarKindSynonymTyCon tc : bool
          then Some TysWiredIn.liftedTypeKind else
          None
      | _ => None
      end in
    match arg_0__ with
    | TyConApp tc tys =>
        match expandSynTyCon_maybe tc tys with
        | Some (pair (pair tenv rhs) tys') =>
            Some (mkAppTys (substTy (mkTvSubstPrs tenv) rhs) tys')
        | _ => j_2__
        end
    | _ => j_2__
    end.

Definition substTy `{GHC.Stack.Types.HasCallStack}
   : TCvSubst -> Type_ -> Type_ :=
  fun subst ty =>
    if isEmptyTCvSubst subst : bool then ty else
    checkValidSubst subst (cons ty nil) nil (subst_ty subst ty).

Definition subst_ty : TCvSubst -> Type_ -> Type_ :=
  fix subst_ty subst ty
        := let fix go arg_0__
                     := match arg_0__ with
                        | TyVarTy tv => substTyVar subst tv
                        | AppTy fun_ arg => mkAppTy (go fun_) (go arg)
                        | TyConApp tc tys =>
                            let args := GHC.Base.map go tys in Util.seqList args (TyConApp tc args)
                        | FunTy arg res => FunTy (go arg) (go res)
                        | ForAllTy (TvBndr tv vis) ty =>
                            let 'pair subst' tv' := substTyVarBndrUnchecked subst tv in
                            ForAllTy (TvBndr tv' vis) (subst_ty subst' ty)
                        | LitTy n => LitTy n
                        | CastTy ty co => mkCastTy (go ty) (subst_co subst co)
                        | CoercionTy co => CoercionTy (subst_co subst co)
                        end in
           go ty.

Definition substTyVarBndrUnchecked
   : TCvSubst -> TyVar -> (TCvSubst * TyVar)%type :=
  substTyVarBndrCallback substTyUnchecked.

Definition substTyVarBndrCallback
   : (TCvSubst -> Type_ -> Type_) ->
     TCvSubst -> TyVar -> (TCvSubst * TyVar)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | subst_fn, (TCvSubst in_scope tenv cenv as subst), old_var =>
        let old_ki := tyVarKind old_var in
        let no_kind_change := noFreeVarsOfType old_ki in
        let new_var :=
          if no_kind_change : bool then uniqAway in_scope old_var else
          uniqAway in_scope (setTyVarKind old_var (subst_fn subst old_ki)) in
        let no_change := andb no_kind_change (new_var GHC.Base.== old_var) in
        let _no_capture := negb (elemVarSet new_var (tyCoVarsOfTypesSet tenv)) in
        let new_env :=
          if no_change : bool then delVarEnv tenv old_var else
          extendVarEnv tenv old_var (TyVarTy new_var) in
        if andb Util.debugIsOn (negb (_no_capture)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/types/TyCoRep.hs") #2393 ((pprTyVar old_var Outputable.$$
                                                                                  pprTyVar new_var) Outputable.$$
                                                                                 Panic.noString subst))
        else if andb Util.debugIsOn (negb (isTyVar old_var)) : bool
             then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
                   #2394)
             else pair (TCvSubst (extendInScopeSet in_scope new_var) new_env cenv) new_var
    end.

Definition pprTyVar : TyVar -> GHC.Base.String :=
  fun tv =>
    let kind := tyVarKind tv in
    if isLiftedTypeKind kind : bool then Panic.noString tv else
    id (GHC.Base.mappend (GHC.Base.mappend (Panic.noString tv) Outputable.dcolon)
                         (Panic.noString kind)).

Definition isLiftedTypeKind : Kind -> bool :=
  let is_lifted :=
    fun arg_0__ =>
      match arg_0__ with
      | TyConApp lifted_rep nil =>
          Unique.hasKey lifted_rep PrelNames.liftedRepDataConKey
      | _ => false
      end in
  is_TYPE is_lifted.

Definition is_TYPE : (Type_ -> bool) -> Kind -> bool :=
  fix is_TYPE arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | f, ki =>
               match coreView ki with
               | Some ki' => is_TYPE f ki'
               | _ =>
                   match arg_0__, arg_1__ with
                   | f, TyConApp tc (cons arg nil) =>
                       let fix go arg_2__
                                 := let 'ty := arg_2__ in
                                    match coreView ty with
                                    | Some ty' => go ty'
                                    | _ => let 'ty := arg_2__ in f ty
                                    end in
                       if Unique.hasKey tc PrelNames.tYPETyConKey : bool then go arg else
                       false
                   | _, _ => false
                   end
               end
           end.

Definition substTyUnchecked : TCvSubst -> Type_ -> Type_ :=
  fun subst ty => if isEmptyTCvSubst subst : bool then ty else subst_ty subst ty.

Definition mkCastTy : Type_ -> Coercion -> Type_ :=
  fix mkCastTy arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | ty, co =>
               if isReflexiveCo co : bool then ty else
               match arg_0__, arg_1__ with
               | CastTy ty co1, co2 => mkCastTy ty (mkTransCo co1 co2)
               | ty, co => CastTy ty co
               end
           end.

Definition isReflexiveCo : Coercion -> bool :=
  Data.Maybe.isJust GHC.Base.∘ isReflexiveCo_maybe.

Definition isReflexiveCo_maybe : Coercion -> option (Type_ * Role)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Refl r ty => Some (pair ty r)
    | co =>
        let 'pair (Pair.Mk_Pair ty1 ty2) r := coercionKindRole co in
        if eqType ty1 ty2 : bool then Some (pair ty1 r) else
        None
    end.

Definition typeKind `{Util.HasDebugCallStack} : Type_ -> Kind :=
  fix typeKind arg_0__
        := match arg_0__ with
           | TyConApp tc tys => piResultTys (tyConKind tc) tys
           | AppTy fun_ arg => piResultTy (typeKind fun_) arg
           | LitTy l => typeLiteralKind l
           | FunTy _ _ => TysWiredIn.liftedTypeKind
           | ForAllTy _ ty => typeKind ty
           | TyVarTy tyvar => tyVarKind tyvar
           | CastTy _ty co => Pair.pSnd (coercionKind co)
           | CoercionTy co => coercionType co
           end.

Definition coercionType : Coercion -> Type_ :=
  fun co =>
    let 'pair (Pair.Mk_Pair ty1 ty2) r := coercionKindRole co in
    mkCoercionType r ty1 ty2.

Definition mkCoercionType : Role -> Type_ -> Type_ -> Type_ :=
  fun arg_0__ =>
    match arg_0__ with
    | Nominal => mkPrimEqPred
    | Representational => mkReprPrimEqPred
    | Phantom =>
        fun ty1 ty2 =>
          let ki2 := typeKind ty2 in
          let ki1 := typeKind ty1 in
          TyConApp TysPrim.eqPhantPrimTyCon (cons ki1 (cons ki2 (cons ty1 (cons ty2
                                                                                nil))))
    end.

Definition mkPrimEqPred : Type_ -> Type_ -> Type_ :=
  fun ty1 ty2 =>
    let k2 := typeKind ty2 in
    let k1 := typeKind ty1 in
    TyConApp TysPrim.eqPrimTyCon (cons k1 (cons k2 (cons ty1 (cons ty2 nil)))).

Definition mkReprPrimEqPred : Type_ -> Type_ -> Type_ :=
  fun ty1 ty2 =>
    let k2 := typeKind ty2 in
    let k1 := typeKind ty1 in
    TyConApp TysPrim.eqReprPrimTyCon (cons k1 (cons k2 (cons ty1 (cons ty2 nil)))).

Definition piResultTy `{Util.HasDebugCallStack} : Type_ -> Type_ -> Type_ :=
  fun ty arg =>
    match piResultTy_maybe ty arg with
    | Some res => res
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "piResultTy") (Panic.noString ty
                                                            Outputable.$$
                                                            Panic.noString arg)
    end.

Definition piResultTy_maybe : Type_ -> Type_ -> option Type_ :=
  fix piResultTy_maybe ty arg
        := match coreView ty with
           | Some ty' => piResultTy_maybe ty' arg
           | _ =>
               match ty with
               | FunTy _ res => Some res
               | _ =>
                   match ty with
                   | ForAllTy (TvBndr tv _) res =>
                       let empty_subst :=
                         mkEmptyTCvSubst (mkInScopeSet (tyCoVarsOfTypes (cons arg (cons res nil)))) in
                       Some (substTy (extendTvSubst empty_subst tv arg) res)
                   | _ => None
                   end
               end
           end.

Definition piResultTys `{Util.HasDebugCallStack}
   : Type_ -> list Type_ -> Type_ :=
  fix piResultTys arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | ty, nil => ty
           | ty, (cons arg args as orig_args) =>
               let in_scope := mkInScopeSet (tyCoVarsOfTypes (cons ty orig_args)) in
               let go : TvSubstEnv -> Type_ -> list Type_ -> Type_ :=
                 fix go arg_3__ arg_4__ arg_5__
                       := match arg_3__, arg_4__, arg_5__ with
                          | tv_env, ty, nil => substTy (mkTvSubst in_scope tv_env) ty
                          | tv_env, ty, (cons arg args as all_args) =>
                              match coreView ty with
                              | Some ty' => go tv_env ty' all_args
                              | _ =>
                                  match ty with
                                  | FunTy _ res => go tv_env res args
                                  | _ =>
                                      match ty with
                                      | ForAllTy (TvBndr tv _) res => go (extendVarEnv tv_env tv arg) res args
                                      | _ =>
                                          let j_7__ :=
                                            Panic.panicStr (GHC.Base.hs_string__ "piResultTys2") ((Panic.noString ty
                                                                                                   Outputable.$$
                                                                                                   Panic.noString
                                                                                                   orig_args)
                                                                                                  Outputable.$$
                                                                                                  Panic.noString
                                                                                                  all_args) in
                                          match ty with
                                          | TyVarTy tv =>
                                              match lookupVarEnv tv_env tv with
                                              | Some ty' => piResultTys ty' all_args
                                              | _ => j_7__
                                              end
                                          | _ => j_7__
                                          end
                                      end
                                  end
                              end
                          end in
               match coreView ty with
               | Some ty' => piResultTys ty' orig_args
               | _ =>
                   match ty with
                   | FunTy _ res => piResultTys res args
                   | _ =>
                       match ty with
                       | ForAllTy (TvBndr tv _) res =>
                           go (extendVarEnv emptyTvSubstEnv tv arg) res args
                       | _ =>
                           Panic.panicStr (GHC.Base.hs_string__ "piResultTys1") (Panic.noString ty
                                                                                 Outputable.$$
                                                                                 Panic.noString orig_args)
                       end
                   end
               end
           end.

Definition repSplitAppTy_maybe `{Util.HasDebugCallStack}
   : Type_ -> option (Type_ * Type_)%type :=
  fun arg_0__ =>
    let j_1__ := let '_other := arg_0__ in None in
    match arg_0__ with
    | FunTy ty1 ty2 =>
        let rep2 := getRuntimeRep ty2 in
        let rep1 := getRuntimeRep ty1 in
        Some (pair (TyConApp TysPrim.funTyCon (cons rep1 (cons rep2 (cons ty1 nil))))
                   ty2)
    | AppTy ty1 ty2 => Some (pair ty1 ty2)
    | TyConApp tc tys =>
        if orb (mightBeUnsaturatedTyCon tc) (Util.lengthExceeds tys (tyConArity
                                                                 tc)) : bool
        then match Util.snocView tys with
             | Some (pair tys' ty') => Some (pair (TyConApp tc tys') ty')
             | _ => j_1__
             end else
        j_1__
    | _ => j_1__
    end.

Definition getRuntimeRep `{Util.HasDebugCallStack} : Type_ -> Type_ :=
  fun ty =>
    match getRuntimeRep_maybe ty with
    | Some r => r
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "getRuntimeRep") (GHC.Base.mappend
                                                               (GHC.Base.mappend (Panic.noString ty) Outputable.dcolon)
                                                               (Panic.noString (typeKind ty)))
    end.

Definition getRuntimeRep_maybe `{Util.HasDebugCallStack}
   : Type_ -> option Type_ :=
  getRuntimeRepFromKind_maybe GHC.Base.∘ typeKind.

Definition getRuntimeRepFromKind_maybe `{Util.HasDebugCallStack}
   : Type_ -> option Type_ :=
  let fix go arg_0__
            := let 'k := arg_0__ in
               match coreView k with
               | Some k' => go k'
               | _ =>
                   let 'k := arg_0__ in
                   match splitTyConApp_maybe k with
                   | Some (pair _tc (cons arg nil)) =>
                       if andb Util.debugIsOn (negb (Unique.hasKey _tc PrelNames.tYPETyConKey)) : bool
                       then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                                        "ghc/compiler/types/Type.hs") #2001 (Panic.noString k))
                       else Some arg
                   | _ => None
                   end
               end in
  go.

Definition splitTyConApp_maybe `{Util.HasDebugCallStack}
   : Type_ -> option (TyCon * list Type_)%type :=
  fix splitTyConApp_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => splitTyConApp_maybe ty'
           | _ => let 'ty := arg_0__ in repSplitTyConApp_maybe ty
           end.

Definition repSplitTyConApp_maybe `{Util.HasDebugCallStack}
   : Type_ -> option (TyCon * list Type_)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | TyConApp tc tys => Some (pair tc tys)
    | FunTy arg res =>
        match getRuntimeRep_maybe arg with
        | Some arg_rep =>
            match getRuntimeRep_maybe res with
            | Some res_rep =>
                Some (pair TysPrim.funTyCon (cons arg_rep (cons res_rep (cons arg (cons res
                                                                                        nil)))))
            | _ => None
            end
        | _ => None
        end
    | _ => None
    end.

Definition mkLRCo : BasicTypes.LeftOrRight -> Coercion -> Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | lr, Refl eq ty => Refl eq (BasicTypes.pickLR lr (splitAppTy ty))
    | lr, co => LRCo lr co
    end.

Definition splitAppTy : Type_ -> (Type_ * Type_)%type :=
  fun ty =>
    match splitAppTy_maybe ty with
    | Some pr => pr
    | None => Panic.panic (GHC.Base.hs_string__ "splitAppTy")
    end.

Definition splitAppTy_maybe : Type_ -> option (Type_ * Type_)%type :=
  fix splitAppTy_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => splitAppTy_maybe ty'
           | _ => let 'ty := arg_0__ in repSplitAppTy_maybe ty
           end.

Definition mkInstCo : Coercion -> Coercion -> Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | ForAllCo tv _kind_co body_co, Refl _ arg =>
        substCoWithUnchecked (cons tv nil) (cons arg nil) body_co
    | co, arg => InstCo co arg
    end.

Definition substCoWithUnchecked
   : list TyVar -> list Type_ -> Coercion -> Coercion :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Util.equalLength tvs tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #2095)
    else substCoUnchecked (zipTvSubst tvs tys).

Definition substCoUnchecked : TCvSubst -> Coercion -> Coercion :=
  fun subst co => if isEmptyTCvSubst subst : bool then co else subst_co subst co.

Definition mkTyConAppCo `{Util.HasDebugCallStack}
   : Role -> TyCon -> list Coercion -> Coercion :=
  fun r tc cos =>
    let j_0__ := TyConAppCo r tc cos in
    let j_1__ :=
      match Data.Traversable.traverse isReflCo_maybe cos with
      | Some tys_roles =>
          Refl r (mkTyConApp tc (GHC.Base.map Data.Tuple.fst tys_roles))
      | _ => j_0__
      end in
    let j_2__ :=
      match expandSynTyCon_maybe tc cos with
      | Some (pair (pair tv_co_prs rhs_ty) leftover_cos) =>
          mkAppCos (liftCoSubst r (mkLiftingContext tv_co_prs) rhs_ty) leftover_cos
      | _ => j_1__
      end in
    if Unique.hasKey tc PrelNames.funTyConKey : bool
    then match cos with
         | cons _rep1 (cons _rep2 (cons co1 (cons co2 nil))) => mkFunCo r co1 co2
         | _ => j_2__
         end else
    j_2__.

Definition liftCoSubst `{Util.HasDebugCallStack}
   : Role -> LiftingContext -> Type_ -> Coercion :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | r, (LC subst env as lc), ty =>
        if isEmptyVarEnv env : bool then Refl r (substTy subst ty) else
        ty_co_subst lc r ty
    end.

Definition mkKindCo : Coercion -> Coercion :=
  fun arg_0__ =>
    match arg_0__ with
    | Refl _ ty => Refl Nominal (typeKind ty)
    | UnivCo (PhantomProv h) _ _ _ => h
    | UnivCo (ProofIrrelProv h) _ _ _ => h
    | co =>
        let j_2__ := KindCo co in
        match coercionKind co with
        | Pair.Mk_Pair ty1 ty2 =>
            let tk2 := typeKind ty2 in
            let tk1 := typeKind ty1 in
            if eqType tk1 tk2 : bool then Refl Nominal tk1 else
            j_2__
        | _ => j_2__
        end
    end.

Definition mkNthCo : GHC.Num.Int -> Coercion -> Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | num_2__, Refl _ ty =>
        let j_21__ :=
          match arg_0__, arg_1__ with
          | n, (FunCo _ arg res as co) =>
              let 'num_4__ := n in
              if num_4__ GHC.Base.== #0 : bool then mkRuntimeRepCo arg else
              let 'num_5__ := n in
              if num_5__ GHC.Base.== #1 : bool then mkRuntimeRepCo res else
              let 'num_6__ := n in
              if num_6__ GHC.Base.== #2 : bool then arg else
              let 'num_7__ := n in
              if num_7__ GHC.Base.== #3 : bool then res else
              Panic.panicStr (GHC.Base.hs_string__ "mkNthCo(FunCo)") (Panic.noString n
                                                                      Outputable.$$
                                                                      Panic.noString co)
          | n, TyConAppCo _ _ arg_cos => ListSetOps.getNth arg_cos n
          | n, co => NthCo n co
          end in
        let j_28__ :=
          match arg_0__, arg_1__ with
          | n, Refl r ty =>
              let ok_tc_app : Type_ -> GHC.Num.Int -> bool :=
                fun ty n =>
                  match splitTyConApp_maybe ty with
                  | Some (pair _ tys) => Util.lengthExceeds tys n
                  | _ => if isForAllTy ty : bool then n GHC.Base.== #0 else false
                  end in
              let tc := tyConAppTyCon ty in
              let r' := nthRole r tc n in
              if andb Util.debugIsOn (negb (ok_tc_app ty n)) : bool
              then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                               "ghc/compiler/types/Coercion.hs") #821 (Panic.noString n Outputable.$$
                                                                                       Panic.noString ty))
              else mkReflCo r' (tyConAppArgN n ty)
          | num_3__, ForAllCo _ kind_co _ =>
              if num_3__ GHC.Base.== #0 : bool then kind_co else
              j_21__
          end in
        if num_2__ GHC.Base.== #0 : bool
        then match splitForAllTy_maybe ty with
             | Some (pair tv _) => Refl Nominal (tyVarKind tv)
             | _ => j_28__
             end else
        j_28__
    end.

Definition mkRuntimeRepCo `{Util.HasDebugCallStack} : Coercion -> Coercion :=
  fun co => let kind_co := mkKindCo co in mkNthCo #0 kind_co.

Definition isForAllTy : Type_ -> bool :=
  fix isForAllTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => isForAllTy ty'
           | _ => match arg_0__ with | ForAllTy _ _ => true | _ => false end
           end.

Definition splitForAllTy_maybe : Type_ -> option (TyVar * Type_)%type :=
  fun ty =>
    let fix go arg_0__
              := let 'ty := arg_0__ in
                 match coreView ty with
                 | Some ty' => go ty'
                 | _ =>
                     match arg_0__ with
                     | ForAllTy (TvBndr tv _) ty => Some (pair tv ty)
                     | _ => None
                     end
                 end in
    go ty.

Definition tyConAppArgN : GHC.Num.Int -> Type_ -> Type_ :=
  fun n ty =>
    match tyConAppArgs_maybe ty with
    | Some tys =>
        if andb Util.debugIsOn (negb (Util.lengthExceeds tys n)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/types/Type.hs") #1098 (GHC.Base.mappend (Panic.noString n)
                                                                                               (Panic.noString tys)))
        else ListSetOps.getNth tys n
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "tyConAppArgN") (GHC.Base.mappend
                                                              (Panic.noString n) (Panic.noString ty))
    end.

Definition tyConAppArgs_maybe : Type_ -> option (list Type_) :=
  fix tyConAppArgs_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => tyConAppArgs_maybe ty'
           | _ =>
               match arg_0__ with
               | TyConApp _ tys => Some tys
               | FunTy arg res =>
                   match getRuntimeRep_maybe arg with
                   | Some rep1 =>
                       match getRuntimeRep_maybe res with
                       | Some rep2 => Some (cons rep1 (cons rep2 (cons arg (cons res nil))))
                       | _ => None
                       end
                   | _ => None
                   end
               | _ => None
               end
           end.

Definition tyConAppTyCon : Type_ -> TyCon :=
  fun ty =>
    Maybes.orElse (tyConAppTyCon_maybe ty) (Panic.panicStr (GHC.Base.hs_string__
                                                            "tyConAppTyCon") (Panic.noString ty)).

Definition tyConAppTyCon_maybe : Type_ -> option TyCon :=
  fix tyConAppTyCon_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => tyConAppTyCon_maybe ty'
           | _ =>
               match arg_0__ with
               | TyConApp tc _ => Some tc
               | FunTy _ _ => Some TysPrim.funTyCon
               | _ => None
               end
           end.

Definition mkSubCo : Coercion -> Coercion :=
  fun arg_0__ =>
    match arg_0__ with
    | Refl Nominal ty => Refl Representational ty
    | TyConAppCo Nominal tc cos =>
        TyConAppCo Representational tc (applyRoles tc cos)
    | FunCo Nominal arg res =>
        FunCo Representational (downgradeRole Representational Nominal arg)
        (downgradeRole Representational Nominal res)
    | co =>
        if andb Util.debugIsOn (negb (coercionRole co GHC.Base.== Nominal)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/types/Coercion.hs") #921 (GHC.Base.mappend (Panic.noString co)
                                                                                                  (Panic.noString
                                                                                                   (coercionRole co))))
        else SubCo co
    end.

Definition applyRoles : TyCon -> list Coercion -> list Coercion :=
  fun tc cos =>
    GHC.List.zipWith (fun r => downgradeRole r Nominal) (tyConRolesRepresentational
                                                         tc) cos.

Definition downgradeRole : Role -> Role -> Coercion -> Coercion :=
  fun r1 r2 co =>
    match downgradeRole_maybe r1 r2 co with
    | Some co' => co'
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "downgradeRole") (Panic.noString co)
    end.

Definition downgradeRole_maybe : Role -> Role -> Coercion -> option Coercion :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Representational, Nominal, co => Some (mkSubCo co)
    | Nominal, Representational, _ => None
    | Phantom, Phantom, co => Some co
    | Phantom, _, co => Some (toPhantomCo co)
    | _, Phantom, _ => None
    | _, _, co => Some co
    end.

Definition toPhantomCo : Coercion -> Coercion :=
  fun co =>
    let 'Pair.Mk_Pair ty1 ty2 := coercionKind co in
    mkPhantomCo (mkKindCo co) ty1 ty2.

Definition mkPhantomCo : Coercion -> Type_ -> Type_ -> Coercion :=
  fun h t1 t2 => mkUnivCo (PhantomProv h) Phantom t1 t2.

Definition substForAllCoBndrUnchecked
   : TCvSubst -> TyVar -> Coercion -> (TCvSubst * TyVar * Coercion)%type :=
  fun subst => substForAllCoBndrCallback false (substCoUnchecked subst) subst.

Definition substTyWithUnchecked : list TyVar -> list Type_ -> Type_ -> Type_ :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Util.equalLength tvs tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #2070)
    else substTyUnchecked (zipTvSubst tvs tys).

Definition substTysUnchecked : TCvSubst -> list Type_ -> list Type_ :=
  fun subst tys =>
    if isEmptyTCvSubst subst : bool then tys else
    GHC.Base.map (subst_ty subst) tys.

Definition substThetaUnchecked : TCvSubst -> ThetaType -> ThetaType :=
  substTysUnchecked.

Definition liftCoSubstWith
   : Role -> list TyCoVar -> list Coercion -> Type_ -> Coercion :=
  fun r tvs cos ty =>
    liftCoSubst r (mkLiftingContext (Util.zipEqual (GHC.Base.hs_string__
                                                    "liftCoSubstWith") tvs cos)) ty.

Definition cloneTyVarBndr
   : TCvSubst -> TyVar -> Unique.Unique -> (TCvSubst * TyVar)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | (TCvSubst in_scope tv_env cv_env as subst), tv, uniq =>
        let old_ki := tyVarKind tv in
        let no_kind_change := noFreeVarsOfType old_ki in
        let tv1 :=
          if no_kind_change : bool then tv else
          setTyVarKind tv (substTy subst old_ki) in
        let tv' := setVarUnique tv1 uniq in
        if andb Util.debugIsOn (negb (isTyVar tv)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/types/TyCoRep.hs") #2445 (Panic.noString tv))
        else pair (TCvSubst (extendInScopeSet in_scope tv') (extendVarEnv tv_env tv
                                                             (mkTyVarTy tv')) cv_env) tv'
    end.

Definition cloneTyVarBndrs
   : TCvSubst ->
     list TyVar -> UniqSupply.UniqSupply -> (TCvSubst * list TyVar)%type :=
  fix cloneTyVarBndrs arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | subst, nil, _usupply => pair subst nil
           | subst, cons t ts, usupply =>
               let 'pair uniq usupply' := UniqSupply.takeUniqFromSupply usupply in
               let 'pair subst' tv := cloneTyVarBndr subst t uniq in
               let 'pair subst'' tvs := cloneTyVarBndrs subst' ts usupply' in
               pair subst'' (cons tv tvs)
           end.

Definition substTyAddInScope : TCvSubst -> Type_ -> Type_ :=
  fun subst ty => substTy (extendTCvInScopeSet subst (tyCoVarsOfType ty)) ty.

Definition substTyWith `{GHC.Stack.Types.HasCallStack}
   : list TyVar -> list Type_ -> Type_ -> Type_ :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Util.equalLength tvs tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #2060)
    else substTy (zipTvSubst tvs tys).

Definition applyTysX : list TyVar -> Type_ -> list Type_ -> Type_ :=
  fun tvs body_ty arg_tys =>
    let n_tvs := Data.Foldable.length tvs in
    let pp_stuff :=
      Panic.noString (cons (Panic.noString tvs) (cons (Panic.noString body_ty) (cons
                                                       (Panic.noString arg_tys) nil))) in
    if andb Util.debugIsOn (negb (Util.lengthAtLeast arg_tys n_tvs)) : bool
    then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                     "ghc/compiler/types/Type.hs") #1034 (pp_stuff))
    else if andb Util.debugIsOn (negb (subVarSet (tyCoVarsOfType body_ty) (mkVarSet
                                                  tvs))) : bool
         then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                          "ghc/compiler/types/Type.hs") #1035 (pp_stuff))
         else mkAppTys (substTyWith tvs (GHC.List.take n_tvs arg_tys) body_ty)
              (GHC.List.drop n_tvs arg_tys).

Definition newTyConInstRhs : TyCon -> list Type_ -> Type_ :=
  fun tycon tys =>
    let 'pair tvs rhs := newTyConEtadRhs tycon in
    if andb Util.debugIsOn (negb (Util.leLength tvs tys)) : bool
    then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                     "ghc/compiler/types/Type.hs") #1151 ((Panic.noString tycon Outputable.$$
                                                                           Panic.noString tys) Outputable.$$
                                                                          Panic.noString tvs))
    else applyTysX tvs rhs tys.

Definition substTyWithCoVars : list CoVar -> list Coercion -> Type_ -> Type_ :=
  fun cvs cos => substTy (zipCvSubst cvs cos).

Definition substTyWithInScope
   : InScopeSet -> list TyVar -> list Type_ -> Type_ -> Type_ :=
  fun in_scope tvs tys ty =>
    let tenv := zipTyEnv tvs tys in
    if andb Util.debugIsOn (negb (Util.equalLength tvs tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #2079)
    else substTy (mkTvSubst in_scope tenv) ty.

Definition tcView : Type_ -> option Type_ :=
  fun arg_0__ =>
    match arg_0__ with
    | TyConApp tc tys =>
        match expandSynTyCon_maybe tc tys with
        | Some (pair (pair tenv rhs) tys') =>
            Some (mkAppTys (substTy (mkTvSubstPrs tenv) rhs) tys')
        | _ => None
        end
    | _ => None
    end.

Definition isUnliftedTypeKind : Kind -> bool :=
  let is_unlifted :=
    fun arg_0__ =>
      match arg_0__ with
      | TyConApp rr _args => negb (Unique.hasKey rr PrelNames.liftedRepDataConKey)
      | _ => false
      end in
  is_TYPE is_unlifted.

Definition pprTvBndr : TyVarBinder -> GHC.Base.String :=
  pprTyVar GHC.Base.∘ binderVar.

Definition pprTvBndrs : list TyVarBinder -> GHC.Base.String :=
  fun tvs => Outputable.sep (GHC.Base.map pprTvBndr tvs).

Definition pprTyVars : list TyVar -> GHC.Base.String :=
  fun tvs => Outputable.sep (GHC.Base.map pprTyVar tvs).

Definition substTyVarBndr `{GHC.Stack.Types.HasCallStack}
   : TCvSubst -> TyVar -> (TCvSubst * TyVar)%type :=
  substTyVarBndrCallback substTy.

Definition isRuntimeRepTy : Type_ -> bool :=
  fix isRuntimeRepTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => isRuntimeRepTy ty'
           | _ =>
               match arg_0__ with
               | TyConApp tc nil => Unique.hasKey tc PrelNames.runtimeRepTyConKey
               | _ => false
               end
           end.

Definition isRuntimeRepVar : TyVar -> bool :=
  isRuntimeRepTy GHC.Base.∘ tyVarKind.

Definition injectiveVarsOfType : Type_ -> FV :=
  let fix go arg_0__
            := let 'ty := arg_0__ in
               match coreView ty with
               | Some ty' => go ty'
               | _ =>
                   match arg_0__ with
                   | TyVarTy v => unionFV (unitFV v) (go (tyVarKind v))
                   | AppTy f a => unionFV (go f) (go a)
                   | FunTy ty1 ty2 => unionFV (go ty1) (go ty2)
                   | TyConApp tc tys =>
                       match tyConInjectivityInfo tc with
                       | NotInjective => emptyFV
                       | Injective inj =>
                           mapUnionFV go (Util.filterByList (Coq.Init.Datatypes.app inj (GHC.List.repeat
                                                                                     true)) tys)
                       end
                   | ForAllTy tvb ty =>
                       tyCoFVsBndr tvb (unionFV (go (tyVarKind (binderVar tvb))) (go ty))
                   | LitTy _ => emptyFV
                   | CastTy ty _ => go ty
                   | CoercionTy _ => emptyFV
                   end
               end in
  go.

Definition injectiveVarsOfBinder : TyConBinder -> FV :=
  fun arg_0__ =>
    let 'TvBndr tv vis := arg_0__ in
    match vis with
    | AnonTCB => injectiveVarsOfType (tyVarKind tv)
    | NamedTCB Required => unionFV (unitFV tv) (injectiveVarsOfType (tyVarKind tv))
    | NamedTCB _ => emptyFV
    end.

Definition dropForAlls : Type_ -> Type_ :=
  fun ty =>
    let fix go arg_0__
              := let 'ty := arg_0__ in
                 match coreView ty with
                 | Some ty' => go ty'
                 | _ => match arg_0__ with | ForAllTy _ res => go res | res => res end
                 end in
    go ty.

Definition funArgTy : Type_ -> Type_ :=
  fix funArgTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => funArgTy ty'
           | _ =>
               match arg_0__ with
               | FunTy arg _res => arg
               | ty => Panic.panicStr (GHC.Base.hs_string__ "funArgTy") (Panic.noString ty)
               end
           end.

Definition funResultTy : Type_ -> Type_ :=
  fix funResultTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => funResultTy ty'
           | _ =>
               match arg_0__ with
               | FunTy _ res => res
               | ty => Panic.panicStr (GHC.Base.hs_string__ "funResultTy") (Panic.noString ty)
               end
           end.

Definition getCastedTyVar_maybe : Type_ -> option (TyVar * CoercionN)%type :=
  fix getCastedTyVar_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => getCastedTyVar_maybe ty'
           | _ =>
               match arg_0__ with
               | CastTy (TyVarTy tv) co => Some (pair tv co)
               | TyVarTy tv => Some (pair tv (mkReflCo Nominal (tyVarKind tv)))
               | _ => None
               end
           end.

Definition getTyVar_maybe : Type_ -> option TyVar :=
  fix getTyVar_maybe ty
        := match coreView ty with
           | Some ty' => getTyVar_maybe ty'
           | _ => repGetTyVar_maybe ty
           end.

Definition getTyVar : GHC.Base.String -> Type_ -> TyVar :=
  fun msg ty =>
    match getTyVar_maybe ty with
    | Some tv => tv
    | None =>
        Panic.panic (Coq.Init.Datatypes.app (GHC.Base.hs_string__ "getTyVar: ") msg)
    end.

Definition isTyVarTy : Type_ -> bool :=
  fun ty => Data.Maybe.isJust (getTyVar_maybe ty).

Definition isFamFreeTy : Type_ -> bool :=
  fix isFamFreeTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => isFamFreeTy ty'
           | _ =>
               match arg_0__ with
               | TyVarTy _ => true
               | LitTy _ => true
               | TyConApp tc tys =>
                   andb (Data.Foldable.all isFamFreeTy tys) (isFamFreeTyCon tc)
               | AppTy a b => andb (isFamFreeTy a) (isFamFreeTy b)
               | FunTy a b => andb (isFamFreeTy a) (isFamFreeTy b)
               | ForAllTy _ ty => isFamFreeTy ty
               | CastTy ty _ => isFamFreeTy ty
               | CoercionTy _ => false
               end
           end.

Definition isNumLitTy : Type_ -> option GHC.Num.Integer :=
  fix isNumLitTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty1 => isNumLitTy ty1
           | _ => match arg_0__ with | LitTy (NumTyLit n) => Some n | _ => None end
           end.

Definition isPiTy : Type_ -> bool :=
  fun arg_0__ =>
    let 'ty := arg_0__ in
    match coreView ty with
    | Some ty' => isForAllTy ty'
    | _ =>
        match arg_0__ with
        | ForAllTy _ _ => true
        | FunTy _ _ => true
        | _ => false
        end
    end.

Definition isStrLitTy : Type_ -> option FastString.FastString :=
  fix isStrLitTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty1 => isStrLitTy ty1
           | _ => match arg_0__ with | LitTy (StrTyLit s) => Some s | _ => None end
           end.

Definition isTauTy : Type_ -> bool :=
  fix isTauTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => isTauTy ty'
           | _ =>
               match arg_0__ with
               | TyVarTy _ => true
               | LitTy _ => true
               | TyConApp tc tys => andb (Data.Foldable.all isTauTy tys) (isTauTyCon tc)
               | AppTy a b => andb (isTauTy a) (isTauTy b)
               | FunTy a b => andb (isTauTy a) (isTauTy b)
               | ForAllTy _ _ => false
               | CastTy ty _ => isTauTy ty
               | CoercionTy _ => false
               end
           end.

Definition splitCastTy_maybe : Type_ -> option (Type_ * Coercion)%type :=
  fix splitCastTy_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => splitCastTy_maybe ty'
           | _ => match arg_0__ with | CastTy ty co => Some (pair ty co) | _ => None end
           end.

Definition splitForAllTyVarBndrs : Type_ -> (list TyVarBinder * Type_)%type :=
  fun ty =>
    let fix split arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | orig_ty, ty, bs =>
                     match coreView ty with
                     | Some ty' => split orig_ty ty' bs
                     | _ =>
                         match arg_0__, arg_1__, arg_2__ with
                         | _, ForAllTy b res, bs => split res res (cons b bs)
                         | orig_ty, _, bs => pair (GHC.List.reverse bs) orig_ty
                         end
                     end
                 end in
    split ty ty nil.

Definition splitForAllTy : Type_ -> (TyVar * Type_)%type :=
  fun ty =>
    match splitForAllTy_maybe ty with
    | Some answer => answer
    | _ => Panic.panicStr (GHC.Base.hs_string__ "splitForAllTy") (Panic.noString ty)
    end.

Definition splitForAllTys : Type_ -> (list TyVar * Type_)%type :=
  fun ty =>
    let fix split arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | orig_ty, ty, tvs =>
                     match coreView ty with
                     | Some ty' => split orig_ty ty' tvs
                     | _ =>
                         match arg_0__, arg_1__, arg_2__ with
                         | _, ForAllTy (TvBndr tv _) ty, tvs => split ty ty (cons tv tvs)
                         | orig_ty, _, tvs => pair (GHC.List.reverse tvs) orig_ty
                         end
                     end
                 end in
    split ty ty nil.

Definition splitFunTy : Type_ -> (Type_ * Type_)%type :=
  fix splitFunTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => splitFunTy ty'
           | _ =>
               match arg_0__ with
               | FunTy arg res => pair arg res
               | other =>
                   Panic.panicStr (GHC.Base.hs_string__ "splitFunTy") (Panic.noString other)
               end
           end.

Definition splitFunTy_maybe : Type_ -> option (Type_ * Type_)%type :=
  fix splitFunTy_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => splitFunTy_maybe ty'
           | _ => match arg_0__ with | FunTy arg res => Some (pair arg res) | _ => None end
           end.

Definition isFunTy : Type_ -> bool :=
  fun ty => Data.Maybe.isJust (splitFunTy_maybe ty).

Definition isValidJoinPointType : BasicTypes.JoinArity -> Type_ -> bool :=
  fun arity ty =>
    let fix valid_under tvs arity ty
              := if arity GHC.Base.== #0 : bool
                 then isEmptyVarSet (intersectVarSet tvs (tyCoVarsOfType ty)) else
                 match splitForAllTy_maybe ty with
                 | Some (pair t ty') => valid_under (extendVarSet tvs t) (arity GHC.Num.- #1) ty'
                 | _ =>
                     match splitFunTy_maybe ty with
                     | Some (pair _ res_ty) => valid_under tvs (arity GHC.Num.- #1) res_ty
                     | _ => false
                     end
                 end in
    valid_under emptyVarSet arity ty.

Definition splitFunTys : Type_ -> (list Type_ * Type_)%type :=
  fun ty =>
    let fix split arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | args, orig_ty, ty =>
                     match coreView ty with
                     | Some ty' => split args orig_ty ty'
                     | _ =>
                         match arg_0__, arg_1__, arg_2__ with
                         | args, _, FunTy arg res => split (cons arg args) res res
                         | args, orig_ty, _ => pair (GHC.List.reverse args) orig_ty
                         end
                     end
                 end in
    split nil ty ty.

Definition splitPiTy_maybe : Type_ -> option (TyBinder * Type_)%type :=
  fun ty =>
    let fix go arg_0__
              := let 'ty := arg_0__ in
                 match coreView ty with
                 | Some ty' => go ty'
                 | _ =>
                     match arg_0__ with
                     | ForAllTy bndr ty => Some (pair (Named bndr) ty)
                     | FunTy arg res => Some (pair (Anon arg) res)
                     | _ => None
                     end
                 end in
    go ty.

Definition modifyJoinResTy
   : GHC.Num.Int -> (Type_ -> Type_) -> Type_ -> Type_ :=
  fun orig_ar f orig_ty =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | num_2__, ty =>
                     if num_2__ GHC.Base.== #0 : bool then f ty else
                     match arg_0__, arg_1__ with
                     | n, ty =>
                         match splitPiTy_maybe ty with
                         | Some (pair arg_bndr res_ty) => mkPiTy arg_bndr (go (n GHC.Num.- #1) res_ty)
                         | _ =>
                             Panic.panicStr (GHC.Base.hs_string__ "modifyJoinResTy") (GHC.Base.mappend
                                                                                      (Panic.noString orig_ar)
                                                                                      (Panic.noString orig_ty))
                         end
                     end
                 end in
    go orig_ar orig_ty.

Definition setJoinResTy : GHC.Num.Int -> Type_ -> Type_ -> Type_ :=
  fun ar new_res_ty ty => modifyJoinResTy ar (GHC.Base.const new_res_ty) ty.

Definition splitPiTy : Type_ -> (TyBinder * Type_)%type :=
  fun ty =>
    match splitPiTy_maybe ty with
    | Some answer => answer
    | _ => Panic.panicStr (GHC.Base.hs_string__ "splitPiTy") (Panic.noString ty)
    end.

Definition splitPiTys : Type_ -> (list TyBinder * Type_)%type :=
  fun ty =>
    let fix split arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | orig_ty, ty, bs =>
                     match coreView ty with
                     | Some ty' => split orig_ty ty' bs
                     | _ =>
                         match arg_0__, arg_1__, arg_2__ with
                         | _, ForAllTy b res, bs => split res res (cons (Named b) bs)
                         | _, FunTy arg res, bs => split res res (cons (Anon arg) bs)
                         | orig_ty, _, bs => pair (GHC.List.reverse bs) orig_ty
                         end
                     end
                 end in
    split ty ty nil.

Definition coVarRole : CoVar -> Role :=
  fun cv =>
    let tc :=
      match tyConAppTyCon_maybe (varType cv) with
      | Some tc0 => tc0
      | None =>
          Panic.panicStr (GHC.Base.hs_string__ "coVarRole: not tyconapp") (Panic.noString
                                                                           cv)
      end in
    if Unique.hasKey tc PrelNames.eqPrimTyConKey : bool then Nominal else
    if Unique.hasKey tc PrelNames.eqReprPrimTyConKey : bool
    then Representational else
    Panic.panicStr (GHC.Base.hs_string__ "coVarRole: unknown tycon")
    (GHC.Base.mappend (GHC.Base.mappend (Panic.noString cv) Outputable.dcolon)
                      (Panic.noString (varType cv))).

Definition isClassPred : PredType -> bool :=
  fun ty =>
    match tyConAppTyCon_maybe ty with
    | Some tyCon => if isClassTyCon tyCon : bool then true else false
    | _ => false
    end.

Definition isDictTy : Type_ -> bool :=
  isClassPred.

Definition isDataFamilyAppType : Type_ -> bool :=
  fun ty =>
    match tyConAppTyCon_maybe ty with
    | Some tc => isDataFamilyTyCon tc
    | _ => false
    end.

Definition isEqPred : PredType -> bool :=
  fun ty =>
    match tyConAppTyCon_maybe ty with
    | Some tyCon =>
        orb (Unique.hasKey tyCon PrelNames.eqPrimTyConKey) (Unique.hasKey tyCon
                                                                          PrelNames.eqReprPrimTyConKey)
    | _ => false
    end.

Definition isIPPred : PredType -> bool :=
  fun ty =>
    match tyConAppTyCon_maybe ty with
    | Some tc => isIPTyCon tc
    | _ => false
    end.

Definition isNomEqPred : PredType -> bool :=
  fun ty =>
    match tyConAppTyCon_maybe ty with
    | Some tyCon => Unique.hasKey tyCon PrelNames.eqPrimTyConKey
    | _ => false
    end.

Definition isPredTy : Type_ -> bool :=
  fix isPredTy ty
        := let go_k : Kind -> list KindOrType -> bool :=
             fix go_k arg_0__ arg_1__
                   := match arg_0__, arg_1__ with
                      | k, nil => Kind.isConstraintKind k
                      | k, cons arg args =>
                          match piResultTy_maybe k arg with
                          | Some k' => go_k k' args
                          | None =>
                              Panic.warnPprTrace (true) (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
                                                 #1590 (GHC.Base.mappend (id (GHC.Base.hs_string__ "isPredTy"))
                                                                         (Panic.noString ty)) false
                          end
                      end in
           let go_tc : TyCon -> list KindOrType -> bool :=
             fun tc args =>
               if orb (Unique.hasKey tc PrelNames.eqPrimTyConKey) (Unique.hasKey tc
                                                                                 PrelNames.eqReprPrimTyConKey) : bool
               then Util.lengthIs args #4 else
               go_k (tyConKind tc) args in
           let go : Type_ -> list KindOrType -> bool :=
             fix go arg_11__ arg_12__
                   := match arg_11__, arg_12__ with
                      | AppTy ty1 ty2, args => go ty1 (cons ty2 args)
                      | TyVarTy tv, args => go_k (tyVarKind tv) args
                      | TyConApp tc tys, args =>
                          if andb Util.debugIsOn (negb (Data.Foldable.null args)) : bool
                          then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
                                #1568)
                          else go_tc tc tys
                      | FunTy arg res, nil => if isPredTy arg : bool then isPredTy res else false
                      | _, _ =>
                          match arg_11__, arg_12__ with
                          | ForAllTy _ ty, nil => go ty nil
                          | CastTy _ co, args => go_k (Pair.pSnd (coercionKind co)) args
                          | _, _ => false
                          end
                      end in
           go ty nil.

Definition isInvisibleBinder : TyBinder -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Named (TvBndr _ vis) => isInvisibleArgFlag vis
    | Anon ty => isPredTy ty
    end.

Definition isVisibleBinder : TyBinder -> bool :=
  negb GHC.Base.∘ isInvisibleBinder.

Definition splitPiTysInvisible : Type_ -> (list TyBinder * Type_)%type :=
  fun ty =>
    let fix split arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | orig_ty, ty, bs =>
                     match coreView ty with
                     | Some ty' => split orig_ty ty' bs
                     | _ =>
                         let j_4__ :=
                           match arg_0__, arg_1__, arg_2__ with
                           | orig_ty, _, bs => pair (GHC.List.reverse bs) orig_ty
                           end in
                         match arg_0__, arg_1__, arg_2__ with
                         | _, ForAllTy (TvBndr _ vis as b) res, bs =>
                             if isInvisibleArgFlag vis : bool then split res res (cons (Named b) bs) else
                             j_4__
                         | _, FunTy arg res, bs =>
                             if isPredTy arg : bool then split res res (cons (Anon arg) bs) else
                             j_4__
                         | _, _, _ => j_4__
                         end
                     end
                 end in
    split ty ty nil.

Definition synTyConResKind : TyCon -> Kind :=
  fun tycon => piResultTys (tyConKind tycon) (mkTyVarTys (tyConTyVars tycon)).

Definition isRuntimeRepKindedTy : Type_ -> bool :=
  isRuntimeRepTy GHC.Base.∘ typeKind.

Definition dropRuntimeRepArgs : list Type_ -> list Type_ :=
  GHC.List.dropWhile isRuntimeRepKindedTy.

Definition isTypeLevPoly : Type_ -> bool :=
  let check_kind := Kind.isKindLevPoly GHC.Base.∘ typeKind in
  let fix go arg_1__
            := match arg_1__ with
               | (TyVarTy _ as ty) => check_kind ty
               | (AppTy _ _ as ty) => check_kind ty
               | (TyConApp tc _ as ty) =>
                   if negb (isTcLevPoly tc) : bool then false else
                   check_kind ty
               | ForAllTy _ ty => go ty
               | FunTy _ _ => false
               | LitTy _ => false
               | (CastTy _ _ as ty) => check_kind ty
               | (CoercionTy _ as ty) =>
                   Panic.panicStr (GHC.Base.hs_string__ "isTypeLevPoly co") (Panic.noString ty)
               end in
  go.

Definition resultIsLevPoly : Type_ -> bool :=
  isTypeLevPoly GHC.Base.∘ (Data.Tuple.snd GHC.Base.∘ splitPiTys).

Definition mkPrimEqPredRole : Role -> Type_ -> Type_ -> PredType :=
  fun arg_0__ =>
    match arg_0__ with
    | Nominal => mkPrimEqPred
    | Representational => mkReprPrimEqPred
    | Phantom => Panic.panic (GHC.Base.hs_string__ "mkPrimEqPredRole phantom")
    end.

Definition topNormaliseTypeX {ev}
   : NormaliseStepper ev ->
     (ev -> ev -> ev) -> Type_ -> option (ev * Type_)%type :=
  fun stepper plus ty =>
    let fix go rec_nts ev ty
              := match splitTyConApp_maybe ty with
                 | Some (pair tc tys) =>
                     match stepper rec_nts tc tys with
                     | NS_Step rec_nts' ty' ev' => go rec_nts' (plus ev ev') ty'
                     | NS_Done => Some (pair ev ty)
                     | NS_Abort => None
                     end
                 | _ => Some (pair ev ty)
                 end in
    match splitTyConApp_maybe ty with
    | Some (pair tc tys) =>
        match stepper initRecTc tc tys with
        | NS_Step rec_nts ty' ev => go rec_nts ev ty'
        | _ => None
        end
    | _ => None
    end.

Definition pprCoAxBranch {br} : CoAxiom br -> CoAxBranch -> GHC.Base.String :=
  let pprRhs :=
    fun fam_tc rhs =>
      let j_0__ := Panic.noString rhs in
      match splitTyConApp_maybe rhs with
      | Some (pair tycon _) =>
          if isDataFamilyTyCon fam_tc : bool then pprDataCons tycon else
          j_0__
      | _ => j_0__
      end in
  ppr_co_ax_branch pprRhs.

Definition coVarKindsTypesRole
   : CoVar -> (Kind * Kind * Type_ * Type_ * Role)%type :=
  fun cv =>
    match splitTyConApp_maybe (varType cv) with
    | Some (pair tc (cons k1 (cons k2 (cons ty1 (cons ty2 nil))))) =>
        let role :=
          if Unique.hasKey tc PrelNames.eqPrimTyConKey : bool then Nominal else
          if Unique.hasKey tc PrelNames.eqReprPrimTyConKey : bool
          then Representational else
          Panic.panic (GHC.Base.hs_string__ "coVarKindsTypesRole") in
        pair (pair (pair (pair k1 k2) ty1) ty2) role
    | _ =>
        Panic.panicStr (GHC.Base.hs_string__
                        "coVarKindsTypesRole, non coercion variable") (Panic.noString cv Outputable.$$
                                                                       Panic.noString (varType cv))
    end.

Definition coVarTypes : CoVar -> Pair.Pair Type_ :=
  fun cv =>
    let 'pair (pair (pair (pair _ _) ty1) ty2) _ := coVarKindsTypesRole cv in
    Pair.Mk_Pair ty1 ty2.

Definition substCoVarBndr : TCvSubst -> CoVar -> (TCvSubst * CoVar)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (TCvSubst in_scope tenv cenv as subst), old_var =>
        let 'pair (pair (pair (pair _ _) t1) t2) role := coVarKindsTypesRole old_var in
        let t1' := substTy subst t1 in
        let t2' := substTy subst t2 in
        let new_var_type := mkCoercionType role t1' t2' in
        let subst_old_var := mkCoVar (varName old_var) new_var_type in
        let new_var := uniqAway in_scope subst_old_var in
        let no_kind_change :=
          Data.Foldable.all noFreeVarsOfType (cons t1 (cons t2 nil)) in
        let no_change := andb (new_var GHC.Base.== old_var) no_kind_change in
        let new_co := mkCoVarCo new_var in
        let new_cenv :=
          if no_change : bool then delVarEnv cenv old_var else
          extendVarEnv cenv old_var new_co in
        if andb Util.debugIsOn (negb (isCoVar old_var)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
              #2423)
        else pair (TCvSubst (extendInScopeSet in_scope new_var) tenv new_cenv) new_var
    end.

Definition getClassPredTys_maybe
   : PredType -> option (Class.Class * list Type_)%type :=
  fun ty =>
    match splitTyConApp_maybe ty with
    | Some (pair tc tys) =>
        match tyConClass_maybe tc with
        | Some clas => Some (pair clas tys)
        | _ => None
        end
    | _ => None
    end.

Definition getClassPredTys : PredType -> (Class.Class * list Type_)%type :=
  fun ty =>
    match getClassPredTys_maybe ty with
    | Some (pair clas tys) => pair clas tys
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "getClassPredTys") (Panic.noString ty)
    end.

Definition getEqPredTys : PredType -> (Type_ * Type_)%type :=
  fun ty =>
    let scrut_0__ := splitTyConApp_maybe ty in
    let j_2__ :=
      Panic.panicStr (GHC.Base.hs_string__ "getEqPredTys") (Panic.noString ty) in
    match scrut_0__ with
    | Some (pair tc (cons _ (cons _ (cons ty1 (cons ty2 nil))))) =>
        if orb (Unique.hasKey tc PrelNames.eqPrimTyConKey) (Unique.hasKey tc
                                                                          PrelNames.eqReprPrimTyConKey) : bool
        then pair ty1 ty2 else
        j_2__
    | _ => j_2__
    end.

Definition getEqPredTys_maybe
   : PredType -> option (Role * Type_ * Type_)%type :=
  fun ty =>
    match splitTyConApp_maybe ty with
    | Some (pair tc (cons _ (cons _ (cons ty1 (cons ty2 nil))))) =>
        if Unique.hasKey tc PrelNames.eqPrimTyConKey : bool
        then Some (pair (pair Nominal ty1) ty2) else
        if Unique.hasKey tc PrelNames.eqReprPrimTyConKey : bool
        then Some (pair (pair Representational ty1) ty2) else
        None
    | _ => None
    end.

Definition isAlgType : Type_ -> bool :=
  fun ty =>
    match splitTyConApp_maybe ty with
    | Some (pair tc ty_args) =>
        if andb Util.debugIsOn (negb (Util.lengthIs ty_args (tyConArity tc))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
              #2022)
        else isAlgTyCon tc
    | _other => false
    end.

Definition isDictLikeTy : Type_ -> bool :=
  fix isDictLikeTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => isDictLikeTy ty'
           | _ =>
               let 'ty := arg_0__ in
               let scrut_1__ := splitTyConApp_maybe ty in
               let j_2__ := let '_other := scrut_1__ in false in
               match scrut_1__ with
               | Some (pair tc tys) =>
                   if isClassTyCon tc : bool then true else
                   if isTupleTyCon tc : bool then Data.Foldable.all isDictLikeTy tys else
                   j_2__
               | _ => j_2__
               end
           end.

Definition isIPPred_maybe
   : Type_ -> option (FastString.FastString * Type_)%type :=
  fun ty =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | pair tc (cons t1 (cons t2 nil)) =>
          Control.Monad.guard (isIPTyCon tc) GHC.Base.>>
          (isStrLitTy t1 GHC.Base.>>= (fun x => GHC.Base.return_ (pair x t2)))
      | _ =>
          missingValue (GHC.Base.hs_string__ "Partial pattern match in `do' notation")
      end in
    splitTyConApp_maybe ty GHC.Base.>>= cont_0__.

Definition isPrimitiveType : Type_ -> bool :=
  fun ty =>
    match splitTyConApp_maybe ty with
    | Some (pair tc ty_args) =>
        if andb Util.debugIsOn (negb (Util.lengthIs ty_args (tyConArity tc))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
              #2041)
        else isPrimTyCon tc
    | _ => false
    end.

Definition nextRole : Type_ -> Role :=
  fun ty =>
    match splitTyConApp_maybe ty with
    | Some (pair tc tys) =>
        let num_tys := Data.Foldable.length tys in
        if num_tys GHC.Base.< tyConArity tc : bool
        then ListSetOps.getNth (tyConRoles tc) num_tys else
        Nominal
    | _ => Nominal
    end.

Definition pprUserTypeErrorTy : Type_ -> GHC.Base.String :=
  fix pprUserTypeErrorTy ty
        := let scrut_0__ := splitTyConApp_maybe ty in
           let j_2__ := Panic.noString ty in
           let j_4__ :=
             match scrut_0__ with
             | Some (pair tc (cons t1 (cons t2 nil))) =>
                 if tyConName tc GHC.Base.== PrelNames.typeErrorVAppendDataConName : bool
                 then pprUserTypeErrorTy t1 Outputable.$$ pprUserTypeErrorTy t2 else
                 j_2__
             | _ => j_2__
             end in
           let j_6__ :=
             match scrut_0__ with
             | Some (pair tc (cons t1 (cons t2 nil))) =>
                 if tyConName tc GHC.Base.== PrelNames.typeErrorAppendDataConName : bool
                 then GHC.Base.mappend (pprUserTypeErrorTy t1) (pprUserTypeErrorTy t2) else
                 j_4__
             | _ => j_4__
             end in
           match scrut_0__ with
           | Some (pair tc (cons txt nil)) =>
               if tyConName tc GHC.Base.== PrelNames.typeErrorTextDataConName : bool
               then match isStrLitTy txt with
                    | Some str => Panic.noString str
                    | _ => j_6__
                    end else
               j_6__
           | Some (pair tc (cons _k (cons t nil))) =>
               if tyConName tc GHC.Base.== PrelNames.typeErrorShowTypeDataConName : bool
               then Panic.noString t else
               j_6__
           | _ => j_6__
           end.

Definition predTypeEqRel : PredType -> EqRel :=
  fun ty =>
    match splitTyConApp_maybe ty with
    | Some (pair tc _) =>
        if Unique.hasKey tc PrelNames.eqReprPrimTyConKey : bool then ReprEq else
        NomEq
    | _ => NomEq
    end.

Definition getEqPredRole : PredType -> Role :=
  fun ty => eqRelRole (predTypeEqRel ty).

Definition splitCoercionType_maybe : Type_ -> option (Type_ * Type_)%type :=
  fun ty =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | pair tc (cons _ (cons _ (cons ty1 (cons ty2 nil)))) =>
          Control.Monad.guard (orb (Unique.hasKey tc PrelNames.eqPrimTyConKey)
                                   (Unique.hasKey tc PrelNames.eqReprPrimTyConKey)) GHC.Base.>>
          GHC.Base.return_ (pair ty1 ty2)
      | _ =>
          missingValue (GHC.Base.hs_string__ "Partial pattern match in `do' notation")
      end in
    splitTyConApp_maybe ty GHC.Base.>>= cont_0__.

Definition splitListTyConApp_maybe : Type_ -> option Type_ :=
  fun ty =>
    let scrut_0__ := splitTyConApp_maybe ty in
    let j_1__ := let '_other := scrut_0__ in None in
    match scrut_0__ with
    | Some (pair tc (cons e nil)) =>
        if tc GHC.Base.== TysWiredIn.listTyCon : bool then Some e else
        j_1__
    | _ => j_1__
    end.

Definition splitTyConApp : Type_ -> (TyCon * list Type_)%type :=
  fun ty =>
    match splitTyConApp_maybe ty with
    | Some stuff => stuff
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "splitTyConApp") (Panic.noString ty)
    end.

Definition userTypeError_maybe : Type_ -> option Type_ :=
  fun t =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | pair tc (cons _kind (cons msg _)) =>
          Control.Monad.guard (tyConName tc GHC.Base.==
                               PrelNames.errorMessageTypeErrorFamName) GHC.Base.>>
          GHC.Base.return_ msg
      | _ =>
          missingValue (GHC.Base.hs_string__ "Partial pattern match in `do' notation")
      end in
    splitTyConApp_maybe t GHC.Base.>>= cont_0__.

Definition classifyPredType : PredType -> PredTree :=
  fun ev_ty =>
    let scrut_0__ := splitTyConApp_maybe ev_ty in
    let j_2__ := IrredPred ev_ty in
    let j_4__ :=
      match scrut_0__ with
      | Some (pair tc tys) =>
          match tyConClass_maybe tc with
          | Some clas => ClassPred clas tys
          | _ => j_2__
          end
      | _ => j_2__
      end in
    match scrut_0__ with
    | Some (pair tc (cons _ (cons _ (cons ty1 (cons ty2 nil))))) =>
        if Unique.hasKey tc PrelNames.eqReprPrimTyConKey : bool
        then EqPred ReprEq ty1 ty2 else
        if Unique.hasKey tc PrelNames.eqPrimTyConKey : bool
        then EqPred NomEq ty1 ty2 else
        j_4__
    | _ => j_4__
    end.

Definition tyConAppArgs : Type_ -> list Type_ :=
  fun ty =>
    Maybes.orElse (tyConAppArgs_maybe ty) (Panic.panicStr (GHC.Base.hs_string__
                                                           "tyConAppArgs") (Panic.noString ty)).

Definition getRuntimeRepFromKind `{Util.HasDebugCallStack} : Type_ -> Type_ :=
  fun k =>
    match getRuntimeRepFromKind_maybe k with
    | Some r => r
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "getRuntimeRepFromKind") (GHC.Base.mappend
                                                                       (GHC.Base.mappend (Panic.noString k)
                                                                                         Outputable.dcolon)
                                                                       (Panic.noString (typeKind k)))
    end.

Definition isLiftedType_maybe `{Util.HasDebugCallStack}
   : Type_ -> option bool :=
  fun ty =>
    let fix go arg_0__
              := let 'rr := arg_0__ in
                 match coreView rr with
                 | Some rr' => go rr'
                 | _ =>
                     let j_2__ := match arg_0__ with | TyConApp _ _ => Some false | _ => None end in
                     match arg_0__ with
                     | TyConApp lifted_rep nil =>
                         if Unique.hasKey lifted_rep PrelNames.liftedRepDataConKey : bool
                         then Some true else
                         j_2__
                     | _ => j_2__
                     end
                 end in
    go (getRuntimeRep ty).

Definition splitAppCo_maybe : Coercion -> option (Coercion * Coercion)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AppCo co arg => Some (pair co arg)
    | TyConAppCo r tc args =>
        if orb (mightBeUnsaturatedTyCon tc) (Util.lengthExceeds args (tyConArity
                                                                 tc)) : bool
        then match Util.snocView args with
             | Some (pair args' arg') =>
                 match setNominalRole_maybe arg' with
                 | Some arg'' => Some (pair (mkTyConAppCo r tc args') arg'')
                 | _ => None
                 end
             | _ => None
             end else
        None
    | Refl r ty =>
        match splitAppTy_maybe ty with
        | Some (pair ty1 ty2) => Some (pair (mkReflCo r ty1) (mkNomReflCo ty2))
        | _ => None
        end
    end.

Definition repSplitAppTys `{Util.HasDebugCallStack}
   : Type_ -> (Type_ * list Type_)%type :=
  fun ty =>
    let fix split arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | AppTy ty arg, args => split ty (cons arg args)
                 | TyConApp tc tc_args, args =>
                     let n := if mightBeUnsaturatedTyCon tc : bool then #0 else tyConArity tc in
                     let 'pair tc_args1 tc_args2 := GHC.List.splitAt n tc_args in
                     pair (TyConApp tc tc_args1) (Coq.Init.Datatypes.app tc_args2 args)
                 | FunTy ty1 ty2, args =>
                     let rep2 := getRuntimeRep ty2 in
                     let rep1 := getRuntimeRep ty1 in
                     if andb Util.debugIsOn (negb (Data.Foldable.null args)) : bool
                     then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
                           #805)
                     else pair (TyConApp TysPrim.funTyCon nil) (cons rep1 (cons rep2 (cons ty1 (cons
                                                                                            ty2 nil))))
                 | ty, args => pair ty args
                 end in
    split ty nil.

Definition splitAppTys : Type_ -> (Type_ * list Type_)%type :=
  fun ty =>
    let fix split arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | orig_ty, ty, args =>
                     match coreView ty with
                     | Some ty' => split orig_ty ty' args
                     | _ =>
                         match arg_0__, arg_1__, arg_2__ with
                         | _, AppTy ty arg, args => split ty ty (cons arg args)
                         | _, TyConApp tc tc_args, args =>
                             let n := if mightBeUnsaturatedTyCon tc : bool then #0 else tyConArity tc in
                             let 'pair tc_args1 tc_args2 := GHC.List.splitAt n tc_args in
                             pair (TyConApp tc tc_args1) (Coq.Init.Datatypes.app tc_args2 args)
                         | _, FunTy ty1 ty2, args =>
                             let rep2 := getRuntimeRep ty2 in
                             let rep1 := getRuntimeRep ty1 in
                             if andb Util.debugIsOn (negb (Data.Foldable.null args)) : bool
                             then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
                                   #785)
                             else pair (TyConApp TysPrim.funTyCon nil) (cons rep1 (cons rep2 (cons ty1 (cons
                                                                                                    ty2 nil))))
                         | orig_ty, _, args => pair orig_ty args
                         end
                     end
                 end in
    split ty ty nil.

Definition tcRepSplitTyConApp_maybe `{GHC.Stack.Types.HasCallStack}
   : Type_ -> option (TyCon * list Type_)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | TyConApp tc tys => Some (pair tc tys)
    | FunTy arg res =>
        let res_rep := getRuntimeRep res in
        let arg_rep := getRuntimeRep arg in
        Some (pair TysPrim.funTyCon (cons arg_rep (cons res_rep (cons arg (cons res
                                                                                nil)))))
    | _ => None
    end.

Definition tcSplitTyConApp_maybe `{GHC.Stack.Types.HasCallStack}
   : Type_ -> option (TyCon * list Type_)%type :=
  fix tcSplitTyConApp_maybe arg_0__
        := let 'ty := arg_0__ in
           match tcView ty with
           | Some ty' => tcSplitTyConApp_maybe ty'
           | _ => let 'ty := arg_0__ in tcRepSplitTyConApp_maybe ty
           end.

Definition isUnboxedSumType : Type_ -> bool :=
  fun ty =>
    Unique.hasKey (tyConAppTyCon (getRuntimeRep ty)) PrelNames.sumRepDataConKey.

Definition isUnboxedTupleType : Type_ -> bool :=
  fun ty =>
    Unique.hasKey (tyConAppTyCon (getRuntimeRep ty)) PrelNames.tupleRepDataConKey.

Definition isUnliftedType `{Util.HasDebugCallStack} : Type_ -> bool :=
  fun ty =>
    negb (Maybes.orElse (isLiftedType_maybe ty) (Panic.panicStr
                         (GHC.Base.hs_string__ "isUnliftedType") (GHC.Base.mappend (GHC.Base.mappend
                                                                                    (Panic.noString ty)
                                                                                    Outputable.dcolon) (Panic.noString
                                                                                    (typeKind ty))))).

Definition isStrictType `{Util.HasDebugCallStack} : Type_ -> bool :=
  isUnliftedType.

Definition eqTypeX : RnEnv2 -> Type_ -> Type_ -> bool :=
  fun env t1 t2 => Util.isEqual (nonDetCmpTypeX env t1 t2).

Definition eqCoercionX : RnEnv2 -> Coercion -> Coercion -> bool :=
  fun env => Data.Function.on (eqTypeX env) coercionType.

Definition eqVarBndrs : RnEnv2 -> list Var -> list Var -> option RnEnv2 :=
  fix eqVarBndrs arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | env, nil, nil => Some env
           | env, cons tv1 tvs1, cons tv2 tvs2 =>
               if eqTypeX env (tyVarKind tv1) (tyVarKind tv2) : bool
               then eqVarBndrs (rnBndr2 env tv1 tv2) tvs1 tvs2 else
               None
           | _, _, _ => None
           end.

Definition mkUnsafeCo : Role -> Type_ -> Type_ -> Coercion :=
  fun role ty1 ty2 => mkUnivCo UnsafeCoerceProv role ty1 ty2.

Definition mkHomoPhantomCo : Type_ -> Type_ -> Coercion :=
  fun t1 t2 =>
    let k1 := typeKind t1 in
    if andb Util.debugIsOn (negb (eqType k1 (typeKind t2))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #1025)
    else mkPhantomCo (mkNomReflCo k1) t1 t2.

Definition eqCoercion : Coercion -> Coercion -> bool :=
  Data.Function.on eqType coercionType.

Definition decomposeCo : BasicTypes.Arity -> Coercion -> list Coercion :=
  fun arity co =>
    Coq.Lists.List.flat_map (fun n => cons (mkNthCo n co) nil) (enumFromTo #0 (arity
                                                                            GHC.Num.-
                                                                            #1)).

Definition mkCoCast : Coercion -> Coercion -> Coercion :=
  fun c g =>
    let 'pair _ args := splitTyConApp (Pair.pFst (coercionKind g)) in
    let n_args := Data.Foldable.length args in
    let co_list := decomposeCo n_args g in
    let g1 := ListSetOps.getNth co_list (n_args GHC.Num.- #2) in
    let g2 := ListSetOps.getNth co_list (n_args GHC.Num.- #1) in
    mkTransCo (mkTransCo (mkSymCo g1) c) g2.

Definition decomposeFunCo : Coercion -> (Coercion * Coercion)%type :=
  fun co =>
    let 'Pair.Mk_Pair s1t1 s2t2 := coercionKind co in
    let all_ok := andb (isFunTy s1t1) (isFunTy s2t2) in
    if andb Util.debugIsOn (negb (all_ok)) : bool
    then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                     "ghc/compiler/types/Coercion.hs") #241 (Panic.noString co))
    else pair (mkNthCo #2 co) (mkNthCo #3 co).

Definition instCoercion
   : Pair.Pair Type_ -> Coercion -> Coercion -> option Coercion :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Pair.Mk_Pair lty rty, g, w =>
        let j_3__ :=
          if andb (isFunTy lty) (isFunTy rty) : bool then Some (mkNthCo #3 g) else
          None in
        if andb (isForAllTy lty) (isForAllTy rty) : bool
        then match setNominalRole_maybe w with
             | Some w' => Some (mkInstCo g w')
             | _ => j_3__
             end else
        j_3__
    end.

Definition instCoercions : Coercion -> list Coercion -> option Coercion :=
  fun g ws =>
    let go
     : (Pair.Pair Type_ * Coercion)%type ->
       (Pair.Pair Type_ * Coercion)%type -> option (Pair.Pair Type_ * Coercion)%type :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair g_tys g, pair w_tys w =>
            instCoercion g_tys g w GHC.Base.>>=
            (fun g' =>
               GHC.Base.return_ (pair ((piResultTy Data.Functor.<$> g_tys) GHC.Base.<*> w_tys)
                                      g'))
        end in
    let arg_ty_pairs := GHC.Base.map coercionKind ws in
    Data.Tuple.snd Data.Functor.<$>
    Control.Monad.foldM go (pair (coercionKind g) g) (GHC.List.zip arg_ty_pairs ws).

Definition splitTyConAppCo_maybe
   : Coercion -> option (TyCon * list Coercion)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Refl r ty =>
        let cont_1__ arg_2__ :=
          let 'pair tc tys := arg_2__ in
          let args := GHC.List.zipWith mkReflCo (tyConRolesX r tc) tys in
          GHC.Base.return_ (pair tc args) in
        splitTyConApp_maybe ty GHC.Base.>>= cont_1__
    | TyConAppCo _ tc cos => Some (pair tc cos)
    | FunCo _ arg res =>
        let cos :=
          cons (mkRuntimeRepCo arg) (cons (mkRuntimeRepCo res) (cons arg (cons res
                                                                               nil))) in
        Some (pair TysPrim.funTyCon cos)
    | _ => None
    end.

Definition maybeSubCo : EqRel -> Coercion -> Coercion :=
  fun arg_0__ =>
    match arg_0__ with
    | NomEq => GHC.Base.id
    | ReprEq => mkSubCo
    end.

Definition mkNthCoRole : Role -> GHC.Num.Int -> Coercion -> Coercion :=
  fun role n co =>
    let nth_co := mkNthCo n co in
    let nth_role := coercionRole nth_co in downgradeRole role nth_role nth_co.

Definition liftCoSubstTyVar
   : LiftingContext -> Role -> TyVar -> option Coercion :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | LC subst env, r, v =>
        match lookupVarEnv env v with
        | Some co_arg => downgradeRole_maybe r (coercionRole co_arg) co_arg
        | _ => Some (Refl r (substTyVar subst v))
        end
    end.

Definition mkTransAppCo
   : Role ->
     Coercion ->
     Type_ -> Type_ -> Role -> Coercion -> Type_ -> Type_ -> Role -> Coercion :=
  fun r1 co1 ty1a ty1b r2 co2 ty2a ty2b r3 =>
    let go :=
      fun co1_repr =>
        let j_0__ :=
          Panic.panicStr (GHC.Base.hs_string__ "mkTransAppCo") (Panic.noString (cons
                                                                                (Panic.noString r1) (cons
                                                                                 (Panic.noString co1) (cons
                                                                                  (Panic.noString ty1a) (cons
                                                                                   (Panic.noString ty1b) (cons
                                                                                    (Panic.noString r2) (cons
                                                                                     (Panic.noString co2) (cons
                                                                                      (Panic.noString ty2a) (cons
                                                                                       (Panic.noString ty2b) (cons
                                                                                        (Panic.noString r3)
                                                                                        nil)))))))))) in
        let j_1__ :=
          match splitTyConApp_maybe ty1a with
          | Some (pair tc1a tys1a) =>
              if nextRole ty1a GHC.Base.== r2 : bool
              then mkTransCo (mkTyConAppCo Representational tc1a (Coq.Init.Datatypes.app
                                                                  (GHC.List.zipWith mkReflCo (tyConRolesRepresentational
                                                                                              tc1a) tys1a) (cons co2
                                                                                                                 nil)))
                             (mkAppCo co1_repr (mkNomReflCo ty2b)) else
              j_0__
          | _ => j_0__
          end in
        match splitTyConApp_maybe ty1b with
        | Some (pair tc1b tys1b) =>
            if nextRole ty1b GHC.Base.== r2 : bool
            then mkTransCo (mkAppCo co1_repr (mkNomReflCo ty2a)) (mkTyConAppCo
                            Representational tc1b (Coq.Init.Datatypes.app (GHC.List.zipWith mkReflCo
                                                                           (tyConRolesRepresentational tc1b) tys1b)
                                                                          (cons co2 nil))) else
            j_1__
        | _ => j_1__
        end in
    match pair (pair r1 r2) r3 with
    | pair (pair _ _) Phantom =>
        let kind_co1 := mkKindCo co1 in
        let kind_co := mkNthCo #1 kind_co1 in
        mkPhantomCo kind_co (mkAppTy ty1a ty2a) (mkAppTy ty1b ty2b)
    | pair (pair _ _) Nominal =>
        if andb Util.debugIsOn (negb (andb (r1 GHC.Base.== Nominal) (r2 GHC.Base.==
                                            Nominal))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
              #600)
        else mkAppCo co1 co2
    | pair (pair Nominal Nominal) Representational => mkSubCo (mkAppCo co1 co2)
    | pair (pair _ Nominal) Representational =>
        if andb Util.debugIsOn (negb (r1 GHC.Base.== Representational)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
              #605)
        else mkAppCo co1 co2
    | pair (pair Nominal Representational) Representational => go (mkSubCo co1)
    | pair (pair _ _) Representational =>
        if andb Util.debugIsOn (negb (andb (r1 GHC.Base.== Representational) (r2
                                            GHC.Base.==
                                            Representational))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
              #610)
        else go co1
    end.

Definition isReflCoVar_maybe : CoVar -> option Coercion :=
  fun cv =>
    match coVarTypes cv with
    | Pair.Mk_Pair ty1 ty2 =>
        if eqType ty1 ty2 : bool then Some (Refl (coVarRole cv) ty1) else
        None
    | _ => None
    end.

Definition nonDetCmpTypesX : RnEnv2 -> list Type_ -> list Type_ -> comparison :=
  fix nonDetCmpTypesX arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, nil, nil => Eq
           | env, cons t1 tys1, cons t2 tys2 =>
               Util.thenCmp (nonDetCmpTypeX env t1 t2) (nonDetCmpTypesX env tys1 tys2)
           | _, nil, _ => Lt
           | _, _, nil => Gt
           end.

Definition nonDetCmpTypes : list Type_ -> list Type_ -> comparison :=
  fun ts1 ts2 =>
    let rn_env :=
      mkRnEnv2 (mkInScopeSet (tyCoVarsOfTypes (Coq.Init.Datatypes.app ts1 ts2))) in
    nonDetCmpTypesX rn_env ts1 ts2.

Definition eqTypes : list Type_ -> list Type_ -> bool :=
  fun tys1 tys2 => Util.isEqual (nonDetCmpTypes tys1 tys2).

Definition tcRepSplitAppTy_maybe : Type_ -> option (Type_ * Type_)%type :=
  fun arg_0__ =>
    let j_1__ := let '_other := arg_0__ in None in
    match arg_0__ with
    | FunTy ty1 ty2 =>
        let rep2 := getRuntimeRep ty2 in
        let rep1 := getRuntimeRep ty1 in
        if Kind.isConstraintKind (typeKind ty1) : bool then None else
        Some (pair (TyConApp TysPrim.funTyCon (cons rep1 (cons rep2 (cons ty1 nil))))
                   ty2)
    | AppTy ty1 ty2 => Some (pair ty1 ty2)
    | TyConApp tc tys =>
        if orb (mightBeUnsaturatedTyCon tc) (Util.lengthExceeds tys (tyConArity
                                                                 tc)) : bool
        then match Util.snocView tys with
             | Some (pair tys' ty') => Some (pair (TyConApp tc tys') ty')
             | _ => j_1__
             end else
        j_1__
    | _ => j_1__
    end.

Definition substTys `{GHC.Stack.Types.HasCallStack}
   : TCvSubst -> list Type_ -> list Type_ :=
  fun subst tys =>
    if isEmptyTCvSubst subst : bool then tys else
    checkValidSubst subst tys nil (GHC.Base.map (subst_ty subst) tys).

Definition substTheta `{GHC.Stack.Types.HasCallStack}
   : TCvSubst -> ThetaType -> ThetaType :=
  substTys.

Definition substTysWith
   : list TyVar -> list Type_ -> list Type_ -> list Type_ :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Util.equalLength tvs tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #2106)
    else substTys (zipTvSubst tvs tys).

Definition substTysWithCoVars
   : list CoVar -> list Coercion -> list Type_ -> list Type_ :=
  fun cvs cos =>
    if andb Util.debugIsOn (negb (Util.equalLength cvs cos)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #2111)
    else substTys (zipCvSubst cvs cos).

Definition mkFamilyTyConApp : TyCon -> list Type_ -> Type_ :=
  fun tc tys =>
    match tyConFamInst_maybe tc with
    | Some (pair fam_tc fam_tys) =>
        let tvs := tyConTyVars tc in
        let fam_subst :=
          if andb Util.debugIsOn (negb (Util.equalLength tvs tys)) : bool
          then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                           "ghc/compiler/types/Type.hs") #1883 (GHC.Base.mappend (Panic.noString tc)
                                                                                                 (Panic.noString tys)))
          else zipTvSubst tvs tys in
        mkTyConApp fam_tc (substTys fam_subst fam_tys)
    | _ => mkTyConApp tc tys
    end.

Definition substCo `{GHC.Stack.Types.HasCallStack}
   : TCvSubst -> Coercion -> Coercion :=
  fun subst co =>
    if isEmptyTCvSubst subst : bool then co else
    checkValidSubst subst nil (cons co nil) (subst_co subst co).

Definition substCoWith `{GHC.Stack.Types.HasCallStack}
   : list TyVar -> list Type_ -> Coercion -> Coercion :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Util.equalLength tvs tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #2085)
    else substCo (zipTvSubst tvs tys).

Definition substForAllCoBndr
   : TCvSubst -> TyVar -> Coercion -> (TCvSubst * TyVar * Coercion)%type :=
  fun subst => substForAllCoBndrCallback false (substCo subst) subst.

Definition composeTCvSubstEnv
   : InScopeSet ->
     (TvSubstEnv * CvSubstEnv)%type ->
     (TvSubstEnv * CvSubstEnv)%type -> (TvSubstEnv * CvSubstEnv)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | in_scope, pair tenv1 cenv1, pair tenv2 cenv2 =>
        let subst1 := TCvSubst in_scope tenv1 cenv1 in
        pair (plusVarEnv tenv1 (mapVarEnv (substTy subst1) tenv2)) (plusVarEnv cenv1
                                                                               (mapVarEnv (substCo subst1) cenv2))
    end.

Definition composeTCvSubst : TCvSubst -> TCvSubst -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst is1 tenv1 cenv1, TCvSubst is2 tenv2 cenv2 =>
        let is3 := unionInScope is1 is2 in
        let 'pair tenv3 cenv3 := composeTCvSubstEnv is3 (pair tenv1 cenv1) (pair tenv2
                                                                                 cenv2) in
        TCvSubst is3 tenv3 cenv3
    end.

Definition liftEnvSubst
   : (forall {a}, Pair.Pair a -> a) -> TCvSubst -> LiftCoEnv -> TCvSubst :=
  fun selector subst lc_env =>
    let ty_or_co
     : (Unique.Unique * Coercion)%type ->
       Data.Either.Either (Unique.Unique * Type_)%type (Unique.Unique *
                                                        Coercion)%type :=
      fun arg_0__ =>
        let 'pair u co := arg_0__ in
        let equality_ty := selector (coercionKind co) in
        match isCoercionTy_maybe equality_ty with
        | Some equality_co => Data.Either.Right (pair u equality_co)
        | _ => Data.Either.Left (pair u equality_ty)
        end in
    let pairs := UniqFM.nonDetUFMToList lc_env in
    let 'pair tpairs cpairs := Util.partitionWith ty_or_co pairs in
    let tenv := mkVarEnv_Directly tpairs in
    let cenv := mkVarEnv_Directly cpairs in
    composeTCvSubst (TCvSubst emptyInScopeSet tenv cenv) subst.

Definition liftEnvSubstLeft : TCvSubst -> LiftCoEnv -> TCvSubst :=
  liftEnvSubst Pair.pFst.

Definition lcSubstLeft : LiftingContext -> TCvSubst :=
  fun arg_0__ => let 'LC subst lc_env := arg_0__ in liftEnvSubstLeft subst lc_env.

Definition substLeftCo : LiftingContext -> Coercion -> Coercion :=
  fun lc co => substCo (lcSubstLeft lc) co.

Definition liftEnvSubstRight : TCvSubst -> LiftCoEnv -> TCvSubst :=
  liftEnvSubst Pair.pSnd.

Definition lcSubstRight : LiftingContext -> TCvSubst :=
  fun arg_0__ =>
    let 'LC subst lc_env := arg_0__ in
    liftEnvSubstRight subst lc_env.

Definition liftCoSubstWithEx
   : Role ->
     list TyVar ->
     list Coercion ->
     list TyVar -> list Type_ -> ((Type_ -> Coercion) * list Type_)%type :=
  fun role univs omegas exs rhos =>
    let theta :=
      mkLiftingContext (Util.zipEqual (GHC.Base.hs_string__ "liftCoSubstWithExU")
                        univs omegas) in
    let psi :=
      extendLiftingContextEx theta (Util.zipEqual (GHC.Base.hs_string__
                                                   "liftCoSubstWithExX") exs rhos) in
    pair (ty_co_subst psi role) (substTyVars (lcSubstRight psi) exs).

Definition substRightCo : LiftingContext -> Coercion -> Coercion :=
  fun lc co => substCo (lcSubstRight lc) co.

Definition substCos `{GHC.Stack.Types.HasCallStack}
   : TCvSubst -> list Coercion -> list Coercion :=
  fun subst cos =>
    if isEmptyTCvSubst subst : bool then cos else
    checkValidSubst subst nil cos (GHC.Base.map (subst_co subst) cos).

Definition mapCoercion {m} {env} `{GHC.Base.Monad m}
   : TyCoMapper env m -> env -> Coercion -> m Coercion :=
  fix mapCoercion arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | (TyCoMapper smart _ covar cohole tybinder as mapper), env, co =>
               let 'pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                             mktyconappco mkappco) mkaxiominstco) mkunivco) mksymco) mktransco) mknthco)
                       mklrco) mkinstco) mkcoherenceco) mkkindco) mksubco) mkforallco :=
                 (if smart : bool
                  then pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                                         mkTyConAppCo mkAppCo)
                                                                                        mkAxiomInstCo) mkUnivCo)
                                                                            mkSymCo) mkTransCo) mkNthCo) mkLRCo)
                                                    mkInstCo) mkCoherenceCo) mkKindCo) mkSubCo) mkForAllCo else
                  pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair (pair
                                                                                    TyConAppCo AppCo) AxiomInstCo)
                                                                             UnivCo) SymCo) TransCo) NthCo) LRCo)
                                               InstCo) CoherenceCo) KindCo) SubCo) ForAllCo) in
               let fix go arg_5__
                         := match arg_5__ with
                            | Refl r ty => Refl r Data.Functor.<$> mapType mapper env ty
                            | TyConAppCo r tc args =>
                                mktyconappco r tc Data.Functor.<$> Data.Traversable.mapM go args
                            | AppCo c1 c2 => (mkappco Data.Functor.<$> go c1) GHC.Base.<*> go c2
                            | ForAllCo tv kind_co co =>
                                go kind_co GHC.Base.>>=
                                (fun kind_co' =>
                                   let cont_9__ arg_10__ :=
                                     let 'pair env' tv' := arg_10__ in
                                     mapCoercion mapper env' co GHC.Base.>>=
                                     (fun co' => GHC.Base.return_ (mkforallco tv' kind_co' co')) in
                                   tybinder env tv Inferred GHC.Base.>>= cont_9__)
                            | FunCo r c1 c2 => (mkFunCo r Data.Functor.<$> go c1) GHC.Base.<*> go c2
                            | CoVarCo cv => covar env cv
                            | AxiomInstCo ax i args =>
                                mkaxiominstco ax i Data.Functor.<$> Data.Traversable.mapM go args
                            | HoleCo hole => cohole env hole
                            | UnivCo p r t1 t2 =>
                                (((mkunivco Data.Functor.<$> go_prov p) GHC.Base.<*> GHC.Base.pure r)
                                 GHC.Base.<*>
                                 mapType mapper env t1) GHC.Base.<*>
                                mapType mapper env t2
                            | SymCo co => mksymco Data.Functor.<$> go co
                            | TransCo c1 c2 => (mktransco Data.Functor.<$> go c1) GHC.Base.<*> go c2
                            | AxiomRuleCo r cos =>
                                AxiomRuleCo r Data.Functor.<$> Data.Traversable.mapM go cos
                            | NthCo i co => mknthco i Data.Functor.<$> go co
                            | LRCo lr co => mklrco lr Data.Functor.<$> go co
                            | InstCo co arg => (mkinstco Data.Functor.<$> go co) GHC.Base.<*> go arg
                            | CoherenceCo c1 c2 => (mkcoherenceco Data.Functor.<$> go c1) GHC.Base.<*> go c2
                            | KindCo co => mkkindco Data.Functor.<$> go co
                            | SubCo co => mksubco Data.Functor.<$> go co
                            end in
               let go_prov :=
                 fun arg_27__ =>
                   match arg_27__ with
                   | UnsafeCoerceProv => GHC.Base.return_ UnsafeCoerceProv
                   | PhantomProv co => PhantomProv Data.Functor.<$> go co
                   | ProofIrrelProv co => ProofIrrelProv Data.Functor.<$> go co
                   | (PluginProv _ as p) => GHC.Base.return_ p
                   end in
               go co
           end.

Definition mapType {m} {env} `{GHC.Base.Monad m}
   : TyCoMapper env m -> env -> Type_ -> m Type_ :=
  fix mapType arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | (TyCoMapper smart tyvar _ _ tybinder as mapper), env, ty =>
               let 'pair (pair mktyconapp mkappty) mkcastty := (if smart : bool
                                                                then pair (pair mkTyConApp mkAppTy) mkCastTy else
                                                                pair (pair TyConApp AppTy) CastTy) in
               let fix go arg_5__
                         := match arg_5__ with
                            | TyVarTy tv => tyvar env tv
                            | AppTy t1 t2 => (mkappty Data.Functor.<$> go t1) GHC.Base.<*> go t2
                            | (TyConApp _ nil as t) => GHC.Base.return_ t
                            | TyConApp tc tys => mktyconapp tc Data.Functor.<$> Data.Traversable.mapM go tys
                            | FunTy arg res => (FunTy Data.Functor.<$> go arg) GHC.Base.<*> go res
                            | ForAllTy (TvBndr tv vis) inner =>
                                let cont_11__ arg_12__ :=
                                  let 'pair env' tv' := arg_12__ in
                                  mapType mapper env' inner GHC.Base.>>=
                                  (fun inner' => GHC.Base.return_ (ForAllTy (TvBndr tv' vis) inner')) in
                                tybinder env tv vis GHC.Base.>>= cont_11__
                            | (LitTy _ as ty) => GHC.Base.return_ ty
                            | CastTy ty co =>
                                (mkcastty Data.Functor.<$> go ty) GHC.Base.<*> mapCoercion mapper env co
                            | CoercionTy co => CoercionTy Data.Functor.<$> mapCoercion mapper env co
                            end in
               go ty
           end.

Definition expandTypeSynonyms : Type_ -> Type_ :=
  fun ty =>
    let in_scope := mkInScopeSet (tyCoVarsOfType ty) in
    let fix go arg_1__ arg_2__
              := match arg_1__, arg_2__ with
                 | subst, TyConApp tc tys =>
                     let expanded_tys := (GHC.Base.map (go subst) tys) in
                     match expandSynTyCon_maybe tc expanded_tys with
                     | Some (pair (pair tenv rhs) tys') =>
                         let subst' := mkTvSubst in_scope (mkVarEnv tenv) in
                         mkAppTys (go subst' rhs) tys'
                     | _ => TyConApp tc expanded_tys
                     end
                 | _, LitTy l => LitTy l
                 | subst, TyVarTy tv => substTyVar subst tv
                 | subst, AppTy t1 t2 => mkAppTy (go subst t1) (go subst t2)
                 | subst, FunTy arg res => mkFunTy (go subst arg) (go subst res)
                 | subst, ForAllTy (TvBndr tv vis) t =>
                     let 'pair subst' tv' := substTyVarBndrCallback go subst tv in
                     ForAllTy (TvBndr tv' vis) (go subst' t)
                 | subst, CastTy ty co => mkCastTy (go subst ty) (go_co subst co)
                 | subst, CoercionTy co => mkCoercionTy (go_co subst co)
                 end in
    let fix go_co arg_16__ arg_17__
              := match arg_16__, arg_17__ with
                 | subst, Refl r ty => mkReflCo r (go subst ty)
                 | subst, TyConAppCo r tc args =>
                     mkTyConAppCo r tc (GHC.Base.map (go_co subst) args)
                 | subst, AppCo co arg => mkAppCo (go_co subst co) (go_co subst arg)
                 | subst, ForAllCo tv kind_co co =>
                     let 'pair (pair subst' tv') kind_co' := go_cobndr subst tv kind_co in
                     mkForAllCo tv' kind_co' (go_co subst' co)
                 | subst, FunCo r co1 co2 => mkFunCo r (go_co subst co1) (go_co subst co2)
                 | subst, CoVarCo cv => substCoVar subst cv
                 | subst, AxiomInstCo ax ind args =>
                     mkAxiomInstCo ax ind (GHC.Base.map (go_co subst) args)
                 | subst, UnivCo p r t1 t2 =>
                     mkUnivCo (go_prov subst p) r (go subst t1) (go subst t2)
                 | subst, SymCo co => mkSymCo (go_co subst co)
                 | subst, TransCo co1 co2 => mkTransCo (go_co subst co1) (go_co subst co2)
                 | subst, NthCo n co => mkNthCo n (go_co subst co)
                 | subst, LRCo lr co => mkLRCo lr (go_co subst co)
                 | subst, InstCo co arg => mkInstCo (go_co subst co) (go_co subst arg)
                 | subst, CoherenceCo co1 co2 =>
                     mkCoherenceCo (go_co subst co1) (go_co subst co2)
                 | subst, KindCo co => mkKindCo (go_co subst co)
                 | subst, SubCo co => mkSubCo (go_co subst co)
                 | subst, AxiomRuleCo ax cs => AxiomRuleCo ax (GHC.Base.map (go_co subst) cs)
                 | _, HoleCo h =>
                     Panic.panicStr (GHC.Base.hs_string__ "expandTypeSynonyms hit a hole")
                     (Panic.noString h)
                 end in
    let go_prov :=
      fun arg_38__ arg_39__ =>
        match arg_38__, arg_39__ with
        | _, UnsafeCoerceProv => UnsafeCoerceProv
        | subst, PhantomProv co => PhantomProv (go_co subst co)
        | subst, ProofIrrelProv co => ProofIrrelProv (go_co subst co)
        | _, (PluginProv _ as p) => p
        end in
    let go_cobndr :=
      fun subst => substForAllCoBndrCallback false (go_co subst) subst in
    go (mkEmptyTCvSubst in_scope) ty.

Definition pprCoAxBranchHdr {br}
   : CoAxiom br -> BranchIndex -> GHC.Base.String :=
  fun ax index => pprCoAxBranch ax (coAxiomNthBranch ax index).

Definition coAxBranchCoVars : CoAxBranch -> list CoVar :=
  cab_cvs.

Definition coAxBranchIncomps : CoAxBranch -> list CoAxBranch :=
  cab_incomps.

Definition coAxBranchLHS : CoAxBranch -> list Type_ :=
  cab_lhs.

Definition coAxiomNumPats {br} : CoAxiom br -> GHC.Num.Int :=
  Data.Foldable.length GHC.Base.∘
  (coAxBranchLHS GHC.Base.∘ (GHC.Base.flip coAxiomNthBranch #0)).

Definition coAxBranchRHS : CoAxBranch -> Type_ :=
  cab_rhs.

Definition coAxBranchRoles : CoAxBranch -> list Role :=
  cab_roles.

Definition coAxBranchSpan : CoAxBranch -> SrcLoc.SrcSpan :=
  cab_loc.

Definition coAxBranchTyVars : CoAxBranch -> list TyVar :=
  cab_tvs.

Definition mkAxInstRHS {br}
   : CoAxiom br -> BranchIndex -> list Type_ -> list Coercion -> Type_ :=
  fun ax index tys cos =>
    let branch := coAxiomNthBranch ax index in
    let tvs := coAxBranchTyVars branch in
    let 'pair tys1 tys2 := Util.splitAtList tvs tys in
    let cvs := coAxBranchCoVars branch in
    let rhs' :=
      substTyWith tvs tys1 (substTyWithCoVars cvs cos (coAxBranchRHS branch)) in
    if andb Util.debugIsOn (negb (Util.equalLength tvs tys1)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #732)
    else mkAppTys rhs' tys2.

Definition mkUnbranchedAxInstRHS
   : CoAxiom Unbranched -> list Type_ -> list Coercion -> Type_ :=
  fun ax => mkAxInstRHS ax #0.

Definition coAxiomBranches {br} : CoAxiom br -> Branches br :=
  co_ax_branches.

Definition coAxiomName {br} : CoAxiom br -> Name.Name :=
  co_ax_name.

Definition coAxiomRole {br} : CoAxiom br -> Role :=
  co_ax_role.

Definition coAxiomSingleBranch : CoAxiom Unbranched -> CoAxBranch :=
  fun arg_0__ =>
    let 'CoAxiom _ _ _ _ (MkBranches arr) _ := arg_0__ in
    arr GHC.Arr.! #0.

Definition coAxiomSingleBranch_maybe {br} : CoAxiom br -> option CoAxBranch :=
  fun arg_0__ =>
    let 'CoAxiom _ _ _ _ (MkBranches arr) _ := arg_0__ in
    if Data.Tuple.snd (GHC.Arr.bounds arr) GHC.Base.== #0 : bool
    then Some (arr GHC.Arr.! #0) else
    None.

Definition coAxiomTyCon {br} : CoAxiom br -> TyCon :=
  co_ax_tc.

Definition mkAxInstLHS {br}
   : CoAxiom br -> BranchIndex -> list Type_ -> list Coercion -> Type_ :=
  fun ax index tys cos =>
    let fam_tc := coAxiomTyCon ax in
    let branch := coAxiomNthBranch ax index in
    let tvs := coAxBranchTyVars branch in
    let 'pair tys1 tys2 := Util.splitAtList tvs tys in
    let cvs := coAxBranchCoVars branch in
    let lhs_tys :=
      substTysWith tvs tys1 (substTysWithCoVars cvs cos (coAxBranchLHS branch)) in
    if andb Util.debugIsOn (negb (Util.equalLength tvs tys1)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #750)
    else mkTyConApp fam_tc (Util.chkAppend lhs_tys tys2).

Definition mkUnbranchedAxInstLHS
   : CoAxiom Unbranched -> list Type_ -> list Coercion -> Type_ :=
  fun ax => mkAxInstLHS ax #0.

Definition tyConsOfType : Type_ -> UniqSet.UniqSet TyCon :=
  fun ty =>
    let go_tc := fun tc => UniqSet.unitUniqSet tc in
    let go_ax := fun ax => go_tc (coAxiomTyCon ax) in
    let go : Type_ -> UniqSet.UniqSet TyCon :=
      fix go arg_2__
            := let 'ty := arg_2__ in
               match coreView ty with
               | Some ty' => go ty'
               | _ =>
                   match arg_2__ with
                   | TyVarTy _ => UniqSet.emptyUniqSet
                   | LitTy _ => UniqSet.emptyUniqSet
                   | TyConApp tc tys => UniqSet.unionUniqSets (go_tc tc) (go_s tys)
                   | AppTy a b => UniqSet.unionUniqSets (go a) (go b)
                   | FunTy a b =>
                       UniqSet.unionUniqSets (UniqSet.unionUniqSets (go a) (go b)) (go_tc
                                              TysPrim.funTyCon)
                   | ForAllTy (TvBndr tv _) ty => UniqSet.unionUniqSets (go ty) (go (tyVarKind tv))
                   | CastTy ty co => UniqSet.unionUniqSets (go ty) (go_co co)
                   | CoercionTy co => go_co co
                   end
               end in
    let fix go_co arg_12__
              := match arg_12__ with
                 | Refl _ ty => go ty
                 | TyConAppCo _ tc args => UniqSet.unionUniqSets (go_tc tc) (go_cos args)
                 | AppCo co arg => UniqSet.unionUniqSets (go_co co) (go_co arg)
                 | ForAllCo _ kind_co co => UniqSet.unionUniqSets (go_co kind_co) (go_co co)
                 | FunCo _ co1 co2 => UniqSet.unionUniqSets (go_co co1) (go_co co2)
                 | AxiomInstCo ax _ args => UniqSet.unionUniqSets (go_ax ax) (go_cos args)
                 | UnivCo p _ t1 t2 =>
                     UniqSet.unionUniqSets (UniqSet.unionUniqSets (go_prov p) (go t1)) (go t2)
                 | CoVarCo _ => UniqSet.emptyUniqSet
                 | HoleCo _ => UniqSet.emptyUniqSet
                 | SymCo co => go_co co
                 | TransCo co1 co2 => UniqSet.unionUniqSets (go_co co1) (go_co co2)
                 | NthCo _ co => go_co co
                 | LRCo _ co => go_co co
                 | InstCo co arg => UniqSet.unionUniqSets (go_co co) (go_co arg)
                 | CoherenceCo co1 co2 => UniqSet.unionUniqSets (go_co co1) (go_co co2)
                 | KindCo co => go_co co
                 | SubCo co => go_co co
                 | AxiomRuleCo _ cs => go_cos cs
                 end in
    let go_prov :=
      fun arg_30__ =>
        match arg_30__ with
        | UnsafeCoerceProv => UniqSet.emptyUniqSet
        | PhantomProv co => go_co co
        | ProofIrrelProv co => go_co co
        | PluginProv _ => UniqSet.emptyUniqSet
        end in
    let go_cos :=
      fun cos =>
        Data.Foldable.foldr (UniqSet.unionUniqSets GHC.Base.∘ go_co)
        UniqSet.emptyUniqSet cos in
    let go_s :=
      fun tys =>
        Data.Foldable.foldr (UniqSet.unionUniqSets GHC.Base.∘ go) UniqSet.emptyUniqSet
        tys in
    go ty.

Definition coAxNthLHS {br} : CoAxiom br -> GHC.Num.Int -> Type_ :=
  fun ax ind =>
    mkTyConApp (coAxiomTyCon ax) (coAxBranchLHS (coAxiomNthBranch ax ind)).

Definition fromBranches {br} : Branches br -> list CoAxBranch :=
  GHC.Arr.elems GHC.Base.∘ unMkBranches.

Definition pprCoAxiom {br} : CoAxiom br -> GHC.Base.String :=
  fun arg_0__ =>
    let '(CoAxiom _ _ _ _ branches _ as ax) := arg_0__ in
    Outputable.hang (GHC.Base.mappend (GHC.Base.mappend (id (GHC.Base.hs_string__
                                                             "axiom")) (Panic.noString ax)) Outputable.dcolon) #2
    (Panic.noString (GHC.Base.map (ppr_co_ax_branch (GHC.Base.const pprType) ax)
                     (fromBranches branches))).

Definition fsFromRole : Role -> FastString.FastString :=
  fun arg_0__ =>
    match arg_0__ with
    | Nominal => FastString.fsLit (GHC.Base.hs_string__ "nominal")
    | Representational => FastString.fsLit (GHC.Base.hs_string__ "representational")
    | Phantom => FastString.fsLit (GHC.Base.hs_string__ "phantom")
    end.

Definition isImplicitCoAxiom {br} : CoAxiom br -> bool :=
  co_ax_implicit.

Definition manyBranches : list CoAxBranch -> Branches Branched :=
  fun brs =>
    let bnds := pair #0 (Data.Foldable.length brs GHC.Num.- #1) in
    if andb Util.debugIsOn (negb (Data.Tuple.snd bnds GHC.Base.>=
                                  Data.Tuple.fst bnds)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/CoAxiom.hs")
          #139)
    else MkBranches (GHC.Arr.listArray bnds brs).

Definition mapAccumBranches {br}
   : (list CoAxBranch -> CoAxBranch -> CoAxBranch) ->
     Branches br -> Branches br :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, MkBranches arr =>
        let go : list CoAxBranch -> CoAxBranch -> (list CoAxBranch * CoAxBranch)%type :=
          fun prev_branches cur_branch =>
            pair (cons cur_branch prev_branches) (f prev_branches cur_branch) in
        MkBranches (GHC.Arr.listArray (GHC.Arr.bounds arr) (Data.Tuple.snd
                                                            (Data.Traversable.mapAccumL go nil (GHC.Arr.elems arr))))
    end.

Definition numBranches {br} : Branches br -> GHC.Num.Int :=
  fun arg_0__ =>
    let 'MkBranches arr := arg_0__ in
    Data.Tuple.snd (GHC.Arr.bounds arr) GHC.Num.+ #1.

Definition placeHolderIncomps : list CoAxBranch :=
  Panic.panic (GHC.Base.hs_string__ "placeHolderIncomps").

Definition toBranched {br} : Branches br -> Branches Branched :=
  MkBranches GHC.Base.∘ unMkBranches.

Definition toBranchedAxiom {br} : CoAxiom br -> CoAxiom Branched :=
  fun arg_0__ =>
    let 'CoAxiom unique name role tc branches implicit := arg_0__ in
    CoAxiom unique name role tc (toBranched branches) implicit.

Definition mkAxInstCo {br}
   : Role ->
     CoAxiom br -> BranchIndex -> list Type_ -> list Coercion -> Coercion :=
  fun role ax index tys cos =>
    let ax_role := coAxiomRole ax in
    let ax_br := toBranchedAxiom ax in
    let branch := coAxiomNthBranch ax_br index in
    let tvs := coAxBranchTyVars branch in
    let arity := Data.Foldable.length tvs in
    let arg_roles := coAxBranchRoles branch in
    let rtys :=
      GHC.List.zipWith mkReflCo (Coq.Init.Datatypes.app arg_roles (GHC.List.repeat
                                                         Nominal)) tys in
    let 'pair ax_args leftover_args := GHC.List.splitAt arity rtys in
    let n_tys := Data.Foldable.length tys in
    if arity GHC.Base.== n_tys : bool
    then downgradeRole role ax_role (mkAxiomInstCo ax_br index (Util.chkAppend rtys
                                                                               cos)) else
    if andb Util.debugIsOn (negb (arity GHC.Base.< n_tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #697)
    else downgradeRole role ax_role (mkAppCos (mkAxiomInstCo ax_br index
                                               (Util.chkAppend ax_args cos)) leftover_args).

Definition mkUnbranchedAxInstCo
   : Role -> CoAxiom Unbranched -> list Type_ -> list Coercion -> Coercion :=
  fun role ax tys cos => mkAxInstCo role ax #0 tys cos.

Definition instNewTyCon_maybe
   : TyCon -> list Type_ -> option (Type_ * Coercion)%type :=
  fun tc tys =>
    match unwrapNewTyConEtad_maybe tc with
    | Some (pair (pair tvs ty) co_tc) =>
        if Util.leLength tvs tys : bool
        then Some (pair (applyTysX tvs ty tys) (mkUnbranchedAxInstCo Representational
                         co_tc tys nil)) else
        None
    | _ => None
    end.

Definition unwrapNewTypeStepper : NormaliseStepper Coercion :=
  fun rec_nts tc tys =>
    match instNewTyCon_maybe tc tys with
    | Some (pair ty' co) =>
        match checkRecTc rec_nts tc with
        | Some rec_nts' => NS_Step rec_nts' ty' co
        | None => NS_Abort
        end
    | _ => NS_Done
    end.

Definition topNormaliseNewType_maybe
   : Type_ -> option (Coercion * Type_)%type :=
  fun ty => topNormaliseTypeX unwrapNewTypeStepper mkTransCo ty.

Definition toUnbranched {br} : Branches br -> Branches Unbranched :=
  fun arg_0__ =>
    let 'MkBranches arr := arg_0__ in
    if andb Util.debugIsOn (negb (GHC.Arr.bounds arr GHC.Base.== pair #0 #0)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/CoAxiom.hs")
          #151)
    else MkBranches arr.

Definition toUnbranchedAxiom {br} : CoAxiom br -> CoAxiom Unbranched :=
  fun arg_0__ =>
    let 'CoAxiom unique name role tc branches implicit := arg_0__ in
    CoAxiom unique name role tc (toUnbranched branches) implicit.

Definition trivialBuiltInFamily : BuiltInSynFamily :=
  Mk_BuiltInSynFamily (fun arg_0__ => None) (fun arg_1__ arg_2__ => nil)
                      (fun arg_3__ arg_4__ arg_5__ arg_6__ => nil).

Definition unbranched : CoAxBranch -> Branches Unbranched :=
  fun br => MkBranches (GHC.Arr.listArray (pair #0 #0) (cons br nil)).

(* External variables:
     ArgFlag Branched CoVar CoVarEnv Coercion CoercionN Eq Gt Id InScopeSet
     KindCoercion KindOrType Lt None RecTcChecker Some TCvSubst TyCon TyVar
     TyVarBinder TyVarBndr TyVarEnv Type_ Unbranched Var VarEnv VarSet andb
     applyRoles bool coVarsOfCoVar coVarsOfCos coVarsOfProv coVarsOfType
     coVarsOfTypes coercionType comparison cons coreView downgradeRole
     downgradeRole_maybe enumFrom enumFromTo eqType false getRuntimeRep
     getRuntimeRepFromKind_maybe getRuntimeRep_maybe go_co go_cobndr go_cos go_prov
     go_s go_tc gos id isForAllTy isLiftedTypeKind isReflexiveCo isReflexiveCo_maybe
     is_TYPE liftCoSubst list mapType mkAppCo mkCastTy mkCoercionType mkInstCo
     mkKindCo mkLRCo mkNthCo mkPhantomCo mkPrimEqPred mkReprPrimEqPred mkRuntimeRepCo
     mkSubCo mkTyConAppCo mkUnivCo negb nil noFreeVarsOfCo noFreeVarsOfProv
     nonDetCmpType nonDetCmpTypeX op_zt__ option orb pair piResultTy piResultTy_maybe
     piResultTys pprTyVar provSize repSplitAppTy_maybe repSplitTyConApp_maybe seqType
     splitAppTy splitAppTy_maybe splitForAllTy_maybe splitTyConApp_maybe
     substCoUnchecked substCoWithUnchecked substForAllCoBndrUnchecked substTy
     substTyUnchecked substTyVarBndrCallback substTyVarBndrUnchecked subst_ty tidyCo
     tidyCos tidyFreeTyCoVars tidyKind tidyOpenTyCoVars tidyTyCoVarBndr
     tidyTyCoVarBndrs tidyTyVarOcc tidyTypes toPhantomCo true tt tyCoFVsBndr
     tyCoFVsOfCo tyCoFVsOfCoVar tyCoFVsOfCos tyCoFVsOfProv tyCoFVsOfTypes
     tyConAppArgN tyConAppArgs_maybe tyConAppTyCon tyConAppTyCon_maybe typeKind
     typeSize unit BasicTypes.Arity BasicTypes.Boxity BasicTypes.FunPrec
     BasicTypes.JoinArity BasicTypes.LeftOrRight BasicTypes.TopPrec
     BasicTypes.TupleSort BasicTypes.TyConPrec BasicTypes.TyPrec BasicTypes.isBoxed
     BasicTypes.maybeParen BasicTypes.pickLR BasicTypes.tupleSortBoxity Class.Class
     Class.classATs Class.classTyCon ConLike.ConLike ConLike.PatSynCon
     ConLike.RealDataCon Constants.fLOAT_SIZE Constants.wORD64_SIZE
     Control.Arrow.first Control.Arrow.second Control.Monad.foldM Control.Monad.guard
     Coq.Init.Datatypes.app Coq.Lists.List.flat_map Core.CType Core.TcTyVarDetails
     Core.dataConExTyVars Data.Either.Either Data.Either.Left Data.Either.Right
     Data.Foldable.all Data.Foldable.and Data.Foldable.concatMap
     Data.Foldable.foldMap Data.Foldable.foldl Data.Foldable.foldr
     Data.Foldable.foldr1 Data.Foldable.length Data.Foldable.null Data.Foldable.sum
     Data.Function.on Data.Functor.op_zlzdzg__ Data.Maybe.isJust Data.Maybe.mapMaybe
     Data.Traversable.mapAccumL Data.Traversable.mapM Data.Traversable.sequenceA
     Data.Traversable.traverse Data.Tuple.fst Data.Tuple.snd Data.Tuple.uncurry
     DataCon.DataCon DataCon.dataConFieldLabels DataCon.dataConFullSig
     DataCon.dataConTyCon DataCon.dataConUserTyVarBinders Digraph.DigraphNode
     Digraph.Node Digraph.graphFromEdgedVerticesOrd Digraph.node_payload
     Digraph.topologicalSortG DynFlags.DynFlags DynFlags.Opt_PrintExplicitKinds
     DynFlags.dOUBLE_SIZE DynFlags.gopt DynFlags.wORD_SIZE FastString.FastString
     FastString.fsLit FastStringEnv.dFsEnvElts FastStringEnv.emptyDFsEnv
     FastStringEnv.lookupDFsEnv FastStringEnv.mkDFsEnv FieldLabel.FieldLabel
     FieldLabel.FieldLabelEnv FieldLabel.FieldLabelString FieldLabel.flLabel
     GHC.Arr.Array GHC.Arr.bounds GHC.Arr.elems GHC.Arr.listArray GHC.Arr.op_zn__
     GHC.Base.Eq_ GHC.Base.Monad GHC.Base.Ord GHC.Base.String GHC.Base.Synonym
     GHC.Base.compare GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.id GHC.Base.map GHC.Base.mappend GHC.Base.max__ GHC.Base.mempty
     GHC.Base.min__ GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____
     GHC.Base.op_zg__ GHC.Base.op_zg____ GHC.Base.op_zgze__ GHC.Base.op_zgze____
     GHC.Base.op_zgzg__ GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zl____
     GHC.Base.op_zlze__ GHC.Base.op_zlze____ GHC.Base.op_zlztzg__ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Base.pure GHC.Base.return_ GHC.Err.Build_Default
     GHC.Err.Default GHC.Err.error GHC.IORef.IORef GHC.List.drop GHC.List.dropWhile
     GHC.List.repeat GHC.List.replicate GHC.List.reverse GHC.List.span
     GHC.List.splitAt GHC.List.take GHC.List.zip GHC.List.zipWith GHC.Num.Int
     GHC.Num.Integer GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__
     GHC.Num.op_zt__ GHC.Stack.Types.HasCallStack IdInfo.IdDetails IdInfo.IdInfo
     IdInfo.coVarDetails IdInfo.isCoVarDetails IdInfo.pprIdDetails
     IdInfo.vanillaIdInfo IfaceType.IfaceCoercion IfaceType.IfaceType
     IfaceType.ShowForAllWhen IfaceType.pprIfaceCoercion IfaceType.pprIfaceContext
     IfaceType.pprIfaceContextArr IfaceType.pprIfaceForAll
     IfaceType.pprIfaceSigmaType IfaceType.pprIfaceTyLit IfaceType.pprIfaceTypeApp
     IfaceType.pprParendIfaceCoercion IfaceType.pprPrecIfaceType
     IfaceType.pprUserIfaceForAll Kind.isConstraintKind Kind.isKindLevPoly
     Kind.isStarKindSynonymTyCon ListSetOps.getNth Maybes.orElse Module.Module
     Name.Name Name.getName Name.getOccName Name.isHoleName Name.isSystemName
     Name.isWiredInName Name.mkExternalName Name.mkInternalName Name.nameModule
     Name.nameOccName Name.nameSrcSpan Name.nameUnique Name.setNameUnique
     Name.tidyNameOcc NameEnv.NameEnv NameEnv.emptyNameEnv NameEnv.extendNameEnv
     NameEnv.lookupNameEnv OccName.OccName OccName.TidyOccEnv
     OccName.avoidClashesOccEnv OccName.emptyTidyOccEnv OccName.initTidyOccEnv
     OccName.isTcOcc OccName.mkTyConRepOcc OccName.mkTyVarOcc OccName.occNameString
     OccName.tidyOccName Outputable.PprStyle Outputable.arrow
     Outputable.assertPprPanic Outputable.dcolon Outputable.debugStyle Outputable.dot
     Outputable.dumpStyle Outputable.equals Outputable.getPprStyle Outputable.hang
     Outputable.hangNotEmpty Outputable.hsep Outputable.op_zdzd__ Outputable.ppUnless
     Outputable.pprTrace Outputable.pprTraceDebug Outputable.quotes
     Outputable.sdocWithDynFlags Outputable.sep Outputable.userStyle Pair.Mk_Pair
     Pair.Pair Pair.pFst Pair.pSnd Panic.assertPanic Panic.noString Panic.panic
     Panic.panicStr Panic.someSDoc Panic.warnPprTrace
     PrelNames.constraintKindTyConKey PrelNames.eqPrimTyConKey
     PrelNames.eqReprPrimTyConKey PrelNames.errorMessageTypeErrorFamName
     PrelNames.funTyConKey PrelNames.gHC_PRIM PrelNames.gHC_TYPES
     PrelNames.ipClassKey PrelNames.liftedRepDataConKey
     PrelNames.liftedTypeKindTyConKey PrelNames.runtimeRepTyConKey
     PrelNames.starKindTyConKey PrelNames.sumRepDataConKey PrelNames.tYPETyConKey
     PrelNames.tupleRepDataConKey PrelNames.typeErrorAppendDataConName
     PrelNames.typeErrorShowTypeDataConName PrelNames.typeErrorTextDataConName
     PrelNames.typeErrorVAppendDataConName PrelNames.unicodeStarKindTyConKey
     SrcLoc.SrcSpan SrcLoc.isGoodSrcSpan SrcLoc.srcSpanStart TcType.pprTcTyVarDetails
     TcType.vanillaSkolemTv ToIface.toIfaceCoercionX ToIface.toIfaceForAllBndr
     ToIface.toIfaceTcArgs ToIface.toIfaceTyCon ToIface.toIfaceTyLit
     ToIface.toIfaceTypeX TysPrim.eqPhantPrimTyCon TysPrim.eqPrimTyCon
     TysPrim.eqReprPrimTyCon TysPrim.funTyCon TysWiredIn.constraintKind
     TysWiredIn.liftedTypeKind TysWiredIn.listTyCon TysWiredIn.mkForAllKind
     TysWiredIn.mkFunKind TysWiredIn.runtimeRepTyCon TysWiredIn.typeNatKind
     TysWiredIn.typeSymbolKind TysWiredIn.vecCountTyCon TysWiredIn.vecElemTyCon
     UniqDFM.UniqDFM UniqDFM.addListToUDFM UniqDFM.addToUDFM UniqDFM.addToUDFM_C
     UniqDFM.allUDFM UniqDFM.alterUDFM UniqDFM.anyUDFM UniqDFM.delFromUDFM
     UniqDFM.delListFromUDFM UniqDFM.disjointUDFM UniqDFM.elemUDFM UniqDFM.eltsUDFM
     UniqDFM.emptyUDFM UniqDFM.filterUDFM UniqDFM.foldUDFM UniqDFM.isNullUDFM
     UniqDFM.listToUDFM UniqDFM.lookupUDFM UniqDFM.mapUDFM UniqDFM.minusUDFM
     UniqDFM.partitionUDFM UniqDFM.plusUDFM UniqDFM.plusUDFM_C UniqDFM.udfmToUfm
     UniqDFM.unitUDFM UniqDSet.UniqDSet UniqDSet.addListToUniqDSet
     UniqDSet.addOneToUniqDSet UniqDSet.delListFromUniqDSet
     UniqDSet.delOneFromUniqDSet UniqDSet.elementOfUniqDSet UniqDSet.emptyUniqDSet
     UniqDSet.filterUniqDSet UniqDSet.foldUniqDSet UniqDSet.intersectUniqDSets
     UniqDSet.isEmptyUniqDSet UniqDSet.minusUniqDSet UniqDSet.mkUniqDSet
     UniqDSet.partitionUniqDSet UniqDSet.sizeUniqDSet UniqDSet.unionManyUniqDSets
     UniqDSet.unionUniqDSets UniqDSet.uniqDSetIntersectUniqSet
     UniqDSet.uniqDSetMinusUniqSet UniqDSet.uniqDSetToList UniqDSet.unitUniqDSet
     UniqFM.UniqFM UniqFM.addListToUFM UniqFM.addToUFM UniqFM.addToUFM_Acc
     UniqFM.addToUFM_C UniqFM.addToUFM_Directly UniqFM.alterUFM UniqFM.delFromUFM
     UniqFM.delFromUFM_Directly UniqFM.delListFromUFM UniqFM.disjointUFM
     UniqFM.elemUFM UniqFM.elemUFM_Directly UniqFM.emptyUFM UniqFM.filterUFM
     UniqFM.filterUFM_Directly UniqFM.intersectUFM UniqFM.isNullUFM UniqFM.listToUFM
     UniqFM.listToUFM_Directly UniqFM.lookupUFM UniqFM.lookupUFM_Directly
     UniqFM.lookupWithDefaultUFM UniqFM.mapUFM UniqFM.minusUFM UniqFM.nonDetEltsUFM
     UniqFM.nonDetKeysUFM UniqFM.nonDetUFMToList UniqFM.partitionUFM UniqFM.pluralUFM
     UniqFM.plusMaybeUFM_C UniqFM.plusUFM UniqFM.plusUFMList UniqFM.plusUFM_C
     UniqFM.plusUFM_CD UniqFM.pprUFM UniqFM.unitUFM UniqSet.UniqSet
     UniqSet.addListToUniqSet UniqSet.addOneToUniqSet UniqSet.delListFromUniqSet
     UniqSet.delListFromUniqSet_Directly UniqSet.delOneFromUniqSet
     UniqSet.delOneFromUniqSet_Directly UniqSet.elemUniqSet_Directly
     UniqSet.elementOfUniqSet UniqSet.emptyUniqSet UniqSet.filterUniqSet
     UniqSet.getUniqSet UniqSet.intersectUniqSets UniqSet.isEmptyUniqSet
     UniqSet.lookupUniqSet UniqSet.lookupUniqSet_Directly UniqSet.mapUniqSet
     UniqSet.minusUniqSet UniqSet.mkUniqSet UniqSet.nonDetEltsUniqSet
     UniqSet.partitionUniqSet UniqSet.sizeUniqSet UniqSet.unionManyUniqSets
     UniqSet.unionUniqSets UniqSet.uniqSetAll UniqSet.uniqSetAny UniqSet.unitUniqSet
     UniqSet.unsafeUFMToUniqSet UniqSupply.UniqSupply UniqSupply.takeUniqFromSupply
     Unique.Uniquable Unique.Unique Unique.dataConRepNameUnique Unique.deriveUnique
     Unique.getKey Unique.getUnique Unique.hasKey Unique.mkUniqueGrimily
     Unique.nonDetCmpUnique Unique.tyConRepNameUnique Util.HasDebugCallStack
     Util.capitalise Util.chkAppend Util.debugIsOn Util.equalLength Util.filterByList
     Util.foldl2 Util.isEqual Util.leLength Util.lengthAtLeast Util.lengthAtMost
     Util.lengthExceeds Util.lengthIs Util.listLengthCmp Util.neLength
     Util.op_zlzbzbzg__ Util.partitionWith Util.seqList Util.snocView
     Util.splitAtList Util.thenCmp Util.zipEqual
*)
