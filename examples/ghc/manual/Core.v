(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require GHC.Base.
Require GHC.Num.
(* Require Var. *)
Require ConLike.
Require PatSyn.
Require Class.
(* Require CoAxiom. *)
(* Require FV. *)
(* Require VarEnv. *)
Require DataCon.
Require BasicTypes.
Require IdInfo.

(* Move elsewhere *)
Instance Panic_Default_datacon : Panic.Default DataCon.DataCon.
Admitted.

(* Some information we don't care about *)

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
Definition TyConRepName := Name.Name%type.

Inductive Injectivity : Type := NotInjective : Injectivity
                             |  Injective : list bool -> Injectivity.


(* From TyCoRep *)
Inductive VisibilityFlag : Type := Visible : VisibilityFlag
                                |  Specified : VisibilityFlag
                                |  Invisible : VisibilityFlag.


Inductive TyPrec : Type := TopPrec : TyPrec
                        |  FunPrec : TyPrec
                        |  TyOpPrec : TyPrec
                        |  TyConPrec : TyPrec.

Inductive TyLit : Type := NumTyLit : GHC.Num.Integer -> TyLit
                       |  StrTyLit : FastString.FastString -> TyLit.


Inductive LeftOrRight : Type := CLeft : LeftOrRight
                             |  CRight : LeftOrRight.


(* From CoAxiom *)
Inductive Role : Type := Nominal : Role
                      |  Representational : Role
                      |  Phantom : Role.

(* Should these be parameters ??? *)
Inductive CoAxiomRule      : Type := Mk_CoAxiomRule_Dummy.
Inductive BuiltInSynFamily : Type := Mk_BuiltInSynFamily_Dummy.

Definition BranchIndex := GHC.Num.Int%type.

Inductive BranchFlag : Type := Branched : BranchFlag
                            |  Unbranched : BranchFlag.

(* Notations *)
Inductive CoercionN__raw : Type :=.
Reserved Notation "'CoercionN'".
Inductive KindCoercion__raw : Type :=.
Reserved Notation "'KindCoercion'".
Inductive KindOrType__raw : Type :=.
Reserved Notation "'KindOrType'".
Inductive Kind__raw : Type := .
Reserved Notation "'Kind'".
Inductive PredType__raw : Type := .
Reserved Notation "'PredType'".
Inductive ThetaType__raw : Type := .
Reserved Notation "'ThetaType'".
Inductive TyVar__raw : Type :=.
Reserved Notation "'TyVar'".
Inductive CoVar__raw : Type :=.
Reserved Notation "'CoVar'".


Inductive TyThing : Type
  := AnId     : Var -> TyThing
  |  AConLike : ConLike.ConLike -> TyThing
  |  ATyCon   : TyCon -> TyThing
  |  ACoAxiom : (CoAxiom Branched) -> TyThing

with Coercion : Type :=
       Refl : Role -> Type_ -> Coercion
     |  TyConAppCo : Role -> TyCon -> list Coercion -> Coercion
     |  AppCo : Coercion -> CoercionN -> Coercion
     |  ForAllCo : TyVar -> KindCoercion -> Coercion -> Coercion
     |  CoVarCo : CoVar -> Coercion
     |  AxiomInstCo : (CoAxiom Branched)
                      -> BranchIndex -> list Coercion -> Coercion
     |  UnivCo : UnivCoProvenance -> Role -> Type_ -> Type_ -> Coercion
     |  SymCo : Coercion -> Coercion
     |  TransCo : Coercion -> Coercion -> Coercion
     |  AxiomRuleCo : CoAxiomRule -> list Coercion -> Coercion
     |  NthCo : GHC.Num.Int -> Coercion -> Coercion
     |  LRCo : LeftOrRight -> CoercionN -> Coercion
     |  InstCo : Coercion -> CoercionN -> Coercion
     |  CoherenceCo : Coercion -> KindCoercion -> Coercion
     |  KindCo : Coercion -> Coercion
     |  SubCo : CoercionN -> Coercion

with Type_ : Type :=
       TyVarTy : Var -> Type_
     |  AppTy : Type_ -> Type_ -> Type_
     |  TyConApp : TyCon -> list KindOrType -> Type_
     |  ForAllTy : TyBinder -> Type_ -> Type_
     |  LitTy : TyLit -> Type_
     |  CastTy : Type_ -> KindCoercion -> Type_
     |  CoercionTy : Coercion -> Type_

with TyBinder : Type :=
       Named : TyVar -> VisibilityFlag -> TyBinder
     |  Anon : Type_ -> TyBinder

with UnivCoProvenance : Type :=
       UnsafeCoerceProv : UnivCoProvenance
     |  PhantomProv : KindCoercion -> UnivCoProvenance
     |  ProofIrrelProv : KindCoercion -> UnivCoProvenance
     |  PluginProv : GHC.Base.String -> UnivCoProvenance
     |  HoleProv : CoercionHole -> UnivCoProvenance

with AlgTyConFlav : Type
       := VanillaAlgTyCon : TyConRepName -> AlgTyConFlav
       |  UnboxedAlgTyCon : AlgTyConFlav
       |  ClassTyCon : Class.Class -> TyConRepName -> AlgTyConFlav
       |  DataFamInstTyCon : (CoAxiom Unbranched)
                             -> TyCon -> list Type_ -> AlgTyConFlav

with TyCon : Type :=
       FunTyCon : Unique.Unique -> Name.Name -> list TyBinder -> Kind -> Kind
                  -> BasicTypes.Arity -> TyConRepName -> TyCon
     |  AlgTyCon : Unique.Unique -> Name.Name -> list TyBinder -> Kind -> Kind
                   -> BasicTypes.Arity -> list TyVar -> list Role
                   -> option CType -> bool -> list PredType
                   -> AlgTyConRhs -> FieldLabel.FieldLabelEnv -> BasicTypes.RecFlag
                   -> AlgTyConFlav -> TyCon
     |  SynonymTyCon : Unique.Unique -> Name.Name -> list TyBinder -> Kind -> Kind
                       -> BasicTypes.Arity -> list TyVar -> list Role
                       -> Type_ -> TyCon
     |  FamilyTyCon : Unique.Unique -> Name.Name -> list TyBinder -> Kind -> Kind
                      -> BasicTypes.Arity -> list TyVar -> option Name.Name
                      -> FamTyConFlav -> option Class.Class -> Injectivity
                      -> TyCon
     |  PrimTyCon : Unique.Unique -> Name.Name -> list TyBinder -> Kind -> Kind
                    -> BasicTypes.Arity -> list Role -> bool
                    -> option TyConRepName -> TyCon
     |  PromotedDataCon : Unique.Unique -> Name.Name -> BasicTypes.Arity
                          -> list TyBinder -> Kind -> Kind -> list Role
                          -> DataCon.DataCon -> TyConRepName -> RuntimeRepInfo -> TyCon
     |  TcTyCon : Unique.Unique -> Name.Name -> bool -> list TyVar -> list TyBinder
                  -> Kind -> Kind -> BasicTypes.Arity -> list TyVar -> TyCon

with AlgTyConRhs : Type :=
       AbstractTyCon : bool -> AlgTyConRhs
     |  DataTyCon : list DataCon.DataCon -> bool -> AlgTyConRhs
     |  TupleTyCon : DataCon.DataCon -> BasicTypes.TupleSort -> AlgTyConRhs
     |  NewTyCon : DataCon.DataCon -> Type_ -> (list TyVar * Type_)%type
                   -> CoAxiom Unbranched -> AlgTyConRhs

with FamTyConFlav : Type :=
       DataFamilyTyCon : TyConRepName -> FamTyConFlav
     |  OpenSynFamilyTyCon : FamTyConFlav
     |  ClosedSynFamilyTyCon : (option (CoAxiom
                                          Branched)) -> FamTyConFlav
     |  AbstractClosedSynFamilyTyCon : FamTyConFlav
     |  BuiltInSynFamTyCon : BuiltInSynFamily -> FamTyConFlav

with Var : Type := Mk_TyVar   : Name.Name -> GHC.Num.Int -> Kind -> Var
                |  Mk_TcTyVar : Name.Name -> GHC.Num.Int -> Kind -> TcTyVarDetails -> Var
                |  Mk_Id      : Name.Name -> GHC.Num.Int -> Type_ -> IdScope -> IdInfo.IdDetails -> IdInfo.IdInfo -> Var
with CoAxBranch : Type := Mk_CoAxBranch :
                                    SrcLoc.SrcSpan -> list TyVar
                                    -> list CoVar -> list Role ->
                                    list Type_ -> Type_ -> list (CoAxBranch) -> CoAxBranch

with Branches : BranchFlag -> Type := MkBranches :
                                       forall br, list (BranchIndex * CoAxBranch)%type -> Branches br

with CoAxiom : BranchFlag -> Type := Mk_CoAxiom
                                    : forall br, Unique.Unique -> Name.Name -> Role -> TyCon ->
                                            Branches br -> bool -> CoAxiom br



where "'KindOrType'" := (GHC.Base.Synonym KindOrType__raw Type_%type)
and   "'CoercionN'" := (GHC.Base.Synonym CoercionN__raw Coercion%type)
and   "'KindCoercion'" := (GHC.Base.Synonym KindCoercion__raw CoercionN%type)
and   "'Kind'" := (GHC.Base.Synonym Kind__raw Type_%type)
and   "'PredType'" := (GHC.Base.Synonym PredType__raw Type_%type)
and   "'ThetaType'" := (GHC.Base.Synonym ThetaType__raw (list PredType%type))
and   "'TyVar'" := ((GHC.Base.Synonym TyVar__raw (Var%type)))
and   "'CoVar'" := ((GHC.Base.Synonym CoVar__raw (Var%type)))
.

Arguments MkBranches {_} _.

Arguments Mk_CoAxiom {_} _ _ _ _ _ _.


Definition CoercionP :=
  Coercion%type.

Definition CoercionR :=
  Coercion%type.

(*
*)

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




(* * Var and TyVar operations that mention types and kinds *
   These cannot be part of Var because we would like to compile
   that module ahead of time.
Parameter tyVarKind       : Var.TyVar -> Kind.
Parameter setTyVarKind    : Var.TyVar -> Kind -> Var.TyVar.
Parameter updateTyVarKind : (Kind -> Kind) -> Var.TyVar -> Var.TyVar.
Parameter mkCoVar         : Name.Name -> Kind -> Var.TyVar.

Parameter varType         : Var -> Type_.
Parameter setVarTyp       : Var -> Type_ -> Var.
*)

(* Record projections (TyCon) *)

Definition tyConUnique (tc : TyCon) : Unique.Unique :=
  match tc with
  | FunTyCon u _ _ _ _ _ _ => u
  | AlgTyCon u _ _ _ _ _ _ _ _ _ _ _ _ _ _ => u
  | SynonymTyCon u _ _ _ _ _ _ _ _ => u
  | FamilyTyCon u _ _ _ _ _ _ _ _ _ _ => u
  | PrimTyCon u _ _ _ _ _ _ _ _ => u
  | PromotedDataCon u _ _ _ _ _ _ _ _ _ => u
  | TcTyCon u _ _ _ _ _ _ _ _ => u
  end.

Definition tyConName (tc : TyCon) : Name.Name :=
  match tc with
  | FunTyCon _ u _ _ _ _ _ => u
  | AlgTyCon _ u _ _ _ _ _ _ _ _ _ _ _ _ _ => u
  | SynonymTyCon _ u _ _ _ _ _ _ _ => u
  | FamilyTyCon _ u _ _ _ _ _ _ _ _ _ => u
  | PrimTyCon _ u _ _ _ _ _ _ _ => u
  | PromotedDataCon _ u _ _ _ _ _ _ _ _ => u
  | TcTyCon _ u _ _ _ _ _ _ _ => u
  end.

Definition tyConArity (tc : TyCon) : BasicTypes.Arity :=
  match tc with
  | FunTyCon _ _ _ _ _ u _ => u
  | AlgTyCon _ _ _ _ _ u _ _ _ _ _ _ _ _ _ => u
  | SynonymTyCon _ _ _ _ _ u _ _ _ => u
  | FamilyTyCon _ _ _ _ _ u _ _ _ _ _ => u
  | PrimTyCon _ _ _ _ _ u _ _ _ => u
  | PromotedDataCon _ _ u _ _ _ _ _ _ _ => u
  | TcTyCon _ _ _ _ _ _ _ u _ => u
  end.



Instance uniquableTyCon : Unique.Uniquable TyCon.
Admitted.
Instance namedTyCon : Name.NamedThing TyCon.
Admitted.


Instance defaultCoAxiom {br} : Panic.Default (CoAxiom br).
Admitted.
Instance defaultType_ : Panic.Default Type_.
Admitted.
Instance defaultCoercion : Panic.Default Coercion.
Admitted.
Instance defaultTyCon : Panic.Default TyCon.
Admitted.
Instance defaultTCvSubst : Panic.Default TCvSubst.
Admitted.
Instance Panic_Default_CoAxiom {br} : Panic.Default (CoAxiom br).
Admitted.
