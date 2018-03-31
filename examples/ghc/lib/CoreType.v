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
Definition TyConRepName := Name.Name%type.

Inductive Injectivity : Type := NotInjective : Injectivity
                             |  Injective : list bool -> Injectivity.

(* Converted imports: *)

Require BasicTypes.
Require CoAxiom.
Require Control.Monad.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require Data.Either.
Require Data.Foldable.
Require Data.Function.
Require Data.Functor.
Require Data.Maybe.
Require Data.Traversable.
Require Data.Tuple.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require ListSetOps.
Require Name.
Require Pair.
Require Panic.
Require PrelNames.
Require TyCon.
Require Unique.
Require Util.
Require VarEnv.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.List.Notations.
Import GHC.Num.Notations.
Require BasicTypes.
Require Class.
Require ConLike.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require Data.Foldable.
Require Data.OldList.
Require Data.Traversable.
Require Data.Tuple.
Require DataCon.
Require DynFlags.
Require FV.
Require FastString.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require GHC.Real.
Require Name.
Require OccName.
Require Pair.
Require Panic.
Require PrelNames.
Require TyCon.
Require UniqFM.
Require UniqSupply.
Require Unique.
Require Util.
Require VarEnv.
Require VarSet.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import GHC.Prim.Notations.
Require BasicTypes.
Require Class.
Require CoAxiom.
Require Control.Arrow.
Require Control.Monad.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Data.Maybe.
Require Data.Traversable.
Require Data.Tuple.
Require Digraph.
Require FastString.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require ListSetOps.
Require Maybes.
Require NameEnv.
Require Pair.
Require Panic.
Require PrelNames.
Require TyCon.
Require TysWiredIn.
Require Unique.
Require Util.
Require VarEnv.
Require VarSet.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import GHC.Prim.Notations.
Require Core.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require IdInfo.
Require Name.
Require Panic.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive NormaliseStepResult ev : Type
  := NS_Done : NormaliseStepResult ev
  |  NS_Abort : NormaliseStepResult ev
  |  NS_Step : TyCon.RecTcChecker -> Type_ -> ev -> NormaliseStepResult ev.

Definition NormaliseStepper ev :=
  (TyCon.RecTcChecker -> Core.TyCon -> list Type_ -> NormaliseStepResult ev)%type.

Definition LiftCoEnv :=
  (VarEnv.VarEnv Coercion)%type.

Inductive LiftingContext : Type := LC : TCvSubst -> LiftCoEnv -> LiftingContext.

Arguments NS_Done {_}.

Arguments NS_Abort {_}.

Arguments NS_Step {_} _ _ _.

Inductive VisibilityFlag : Type
  := Visible : VisibilityFlag
  |  Specified : VisibilityFlag
  |  Invisible : VisibilityFlag.

Inductive TyThing : Type
  := AnId : Id -> TyThing
  |  AConLike : ConLike.ConLike -> TyThing
  |  ATyCon : Core.TyCon -> TyThing
  |  ACoAxiom : (Core.CoAxiom Core.Branched) -> TyThing.

Inductive TyPrec : Type
  := TopPrec : TyPrec
  |  FunPrec : TyPrec
  |  TyOpPrec : TyPrec
  |  TyConPrec : TyPrec.

Inductive TyLit : Type
  := NumTyLit : GHC.Num.Integer -> TyLit
  |  StrTyLit : FastString.FastString -> TyLit.

Inductive LeftOrRight : Type := CLeft : LeftOrRight |  CRight : LeftOrRight.

Inductive CoercionN__raw : Type :=.

Reserved Notation "'CoercionN'".

Inductive KindCoercion__raw : Type :=.

Reserved Notation "'KindCoercion'".

Inductive KindOrType__raw : Type :=.

Reserved Notation "'KindOrType'".

Inductive Coercion : Type
  := Refl : Core.Role -> Type_ -> Coercion
  |  TyConAppCo : Core.Role -> Core.TyCon -> list Coercion -> Coercion
  |  AppCo : Coercion -> CoercionN -> Coercion
  |  ForAllCo : TyVar -> KindCoercion -> Coercion -> Coercion
  |  CoVarCo : CoVar -> Coercion
  |  AxiomInstCo
   : (Core.CoAxiom Core.Branched) -> Core.BranchIndex -> list Coercion -> Coercion
  |  UnivCo : UnivCoProvenance -> Core.Role -> Type_ -> Type_ -> Coercion
  |  SymCo : Coercion -> Coercion
  |  TransCo : Coercion -> Coercion -> Coercion
  |  AxiomRuleCo : Core.CoAxiomRule -> list Coercion -> Coercion
  |  NthCo : GHC.Num.Int -> Coercion -> Coercion
  |  LRCo : LeftOrRight -> CoercionN -> Coercion
  |  InstCo : Coercion -> CoercionN -> Coercion
  |  CoherenceCo : Coercion -> KindCoercion -> Coercion
  |  KindCo : Coercion -> Coercion
  |  SubCo : CoercionN -> Coercion
with Type_ : Type
  := TyVarTy : Var -> Type_
  |  AppTy : Type_ -> Type_ -> Type_
  |  TyConApp : Core.TyCon -> list KindOrType -> Type_
  |  ForAllTy : TyBinder -> Type_ -> Type_
  |  LitTy : TyLit -> Type_
  |  CastTy : Type_ -> KindCoercion -> Type_
  |  CoercionTy : Coercion -> Type_
with TyBinder : Type
  := Named : TyVar -> VisibilityFlag -> TyBinder
  |  Anon : Type_ -> TyBinder
with UnivCoProvenance : Type
  := UnsafeCoerceProv : UnivCoProvenance
  |  PhantomProv : KindCoercion -> UnivCoProvenance
  |  ProofIrrelProv : KindCoercion -> UnivCoProvenance
  |  PluginProv : GHC.Base.String -> UnivCoProvenance
  |  HoleProv : CoercionHole -> UnivCoProvenance
with CoercionHole : Type
  := CoercionHole
   : Unique.Unique -> GHC.IORef.IORef (option Coercion) -> CoercionHole
where "'KindOrType'" := (GHC.Base.Synonym KindOrType__raw Type_%type)
and   "'CoercionN'" := (GHC.Base.Synonym CoercionN__raw Coercion%type)
and   "'KindCoercion'" := (GHC.Base.Synonym KindCoercion__raw CoercionN%type).

Definition CoercionP :=
  Coercion%type.

Definition CoercionR :=
  Coercion%type.

Definition CvSubstEnv :=
  (VarEnv.CoVarEnv Coercion)%type.

Definition Kind :=
  Type_%type.

Definition PredType :=
  Type_%type.

Definition ThetaType :=
  (list PredType)%type.

Definition TvSubstEnv :=
  (VarEnv.TyVarEnv Type_)%type.

Inductive TCvSubst : Type
  := TCvSubst : VarEnv.InScopeSet -> TvSubstEnv -> CvSubstEnv -> TCvSubst.

Definition chCoercion (arg_0__ : CoercionHole) :=
  let 'CoercionHole _ chCoercion := arg_0__ in
  chCoercion.

Definition chUnique (arg_1__ : CoercionHole) :=
  let 'CoercionHole chUnique _ := arg_1__ in
  chUnique.

Definition UnaryType :=
  Type_%type.

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
     (env -> CoercionHole -> Core.Role -> Type_ -> Type_ -> m Coercion) ->
     (env -> TyVar -> VisibilityFlag -> m (env * TyVar)%type) -> TyCoMapper env m.

Inductive RepType : Type
  := UbxTupleRep : list UnaryType -> RepType
  |  UnaryRep : UnaryType -> RepType.

Inductive EqRel : Type := NomEq : EqRel |  ReprEq : EqRel.

Inductive PredTree : Type
  := ClassPred : Class.Class -> list Type_ -> PredTree
  |  EqPred : EqRel -> Type_ -> Type_ -> PredTree
  |  IrredPred : PredType -> PredTree.

Arguments TyCoMapper {_} {_} _ _ _ _ _.

Definition tcm_covar {env} {m} (arg_2__ : TyCoMapper env m) :=
  let 'TyCoMapper _ _ tcm_covar _ _ := arg_2__ in
  tcm_covar.

Definition tcm_hole {env} {m} (arg_3__ : TyCoMapper env m) :=
  let 'TyCoMapper _ _ _ tcm_hole _ := arg_3__ in
  tcm_hole.

Definition tcm_smart {env} {m} (arg_4__ : TyCoMapper env m) :=
  let 'TyCoMapper tcm_smart _ _ _ _ := arg_4__ in
  tcm_smart.

Definition tcm_tybinder {env} {m} (arg_5__ : TyCoMapper env m) :=
  let 'TyCoMapper _ _ _ _ tcm_tybinder := arg_5__ in
  tcm_tybinder.

Definition tcm_tyvar {env} {m} (arg_6__ : TyCoMapper env m) :=
  let 'TyCoMapper _ tcm_tyvar _ _ _ := arg_6__ in
  tcm_tyvar.

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

Definition KindVar :=
  Var%type.

Definition NcId :=
  Id%type.

Definition TKVar :=
  Var%type.

Definition TyCoVar :=
  Id%type.

Definition TyVar :=
  Var%type.

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

Definition idScope (arg_7__ : Var) :=
  match arg_7__ with
  | TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `idScope' has no match in constructor `TyVar' of type `Var'")
  | TcTyVar _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `idScope' has no match in constructor `TcTyVar' of type `Var'")
  | Id _ _ _ idScope _ _ => idScope
  end.

Definition id_details (arg_8__ : Var) :=
  match arg_8__ with
  | TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_details' has no match in constructor `TyVar' of type `Var'")
  | TcTyVar _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_details' has no match in constructor `TcTyVar' of type `Var'")
  | Id _ _ _ _ id_details _ => id_details
  end.

Definition id_info (arg_9__ : Var) :=
  match arg_9__ with
  | TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_info' has no match in constructor `TyVar' of type `Var'")
  | TcTyVar _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `id_info' has no match in constructor `TcTyVar' of type `Var'")
  | Id _ _ _ _ _ id_info => id_info
  end.

Definition realUnique (arg_10__ : Var) :=
  match arg_10__ with
  | TyVar _ realUnique _ => realUnique
  | TcTyVar _ realUnique _ _ => realUnique
  | Id _ realUnique _ _ _ _ => realUnique
  end.

Definition tc_tv_details (arg_11__ : Var) :=
  match arg_11__ with
  | TyVar _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tc_tv_details' has no match in constructor `TyVar' of type `Var'")
  | TcTyVar _ _ _ tc_tv_details => tc_tv_details
  | Id _ _ _ _ _ _ =>
      GHC.Err.error (GHC.Base.hs_string__
                     "Partial record selector: field `tc_tv_details' has no match in constructor `Id' of type `Var'")
  end.

Definition varName (arg_12__ : Var) :=
  match arg_12__ with
  | TyVar varName _ _ => varName
  | TcTyVar varName _ _ _ => varName
  | Id varName _ _ _ _ _ => varName
  end.

Definition varType (arg_13__ : Var) :=
  match arg_13__ with
  | TyVar _ _ varType => varType
  | TcTyVar _ _ varType _ => varType
  | Id _ _ varType _ _ _ => varType
  end.

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

(* Translating `instance Outputable__EqRel' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__RepType' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Bounded__TypeOrdering' failed: OOPS! Cannot find
   information for class Qualified "GHC.Enum" "Bounded" unsupported *)

(* Translating `instance Enum__TypeOrdering' failed: negative `Integer' literals
   unsupported *)

Local Definition Ord__TypeOrdering_compare
   : TypeOrdering -> TypeOrdering -> comparison :=
  fun a b =>
    let 'lop_azh__ := (_Deriving.$con2tag_g5QILjRA04KRgR1r4UStZ_ a) in
    let 'lop_bzh__ := (_Deriving.$con2tag_g5QILjRA04KRgR1r4UStZ_ b) in
    if ((_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.<# lop_bzh__)) : bool) : bool
    then Lt
    else if ((_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.==#
                                     lop_bzh__)) : bool) : bool
         then Eq
         else Gt.

Local Definition Ord__TypeOrdering_op_zg__
   : TypeOrdering -> TypeOrdering -> bool :=
  fun a b =>
    let 'lop_azh__ := (_Deriving.$con2tag_g5QILjRA04KRgR1r4UStZ_ a) in
    let 'lop_bzh__ := (_Deriving.$con2tag_g5QILjRA04KRgR1r4UStZ_ b) in
    (_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.># lop_bzh__)).

Local Definition Ord__TypeOrdering_op_zgze__
   : TypeOrdering -> TypeOrdering -> bool :=
  fun a b =>
    let 'lop_azh__ := (_Deriving.$con2tag_g5QILjRA04KRgR1r4UStZ_ a) in
    let 'lop_bzh__ := (_Deriving.$con2tag_g5QILjRA04KRgR1r4UStZ_ b) in
    (_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.>=# lop_bzh__)).

Local Definition Ord__TypeOrdering_op_zl__
   : TypeOrdering -> TypeOrdering -> bool :=
  fun a b =>
    let 'lop_azh__ := (_Deriving.$con2tag_g5QILjRA04KRgR1r4UStZ_ a) in
    let 'lop_bzh__ := (_Deriving.$con2tag_g5QILjRA04KRgR1r4UStZ_ b) in
    (_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.<# lop_bzh__)).

Local Definition Ord__TypeOrdering_op_zlze__
   : TypeOrdering -> TypeOrdering -> bool :=
  fun a b =>
    let 'lop_azh__ := (_Deriving.$con2tag_g5QILjRA04KRgR1r4UStZ_ a) in
    let 'lop_bzh__ := (_Deriving.$con2tag_g5QILjRA04KRgR1r4UStZ_ b) in
    (_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.<=# lop_bzh__)).

Local Definition Ord__TypeOrdering_min
   : TypeOrdering -> TypeOrdering -> TypeOrdering :=
  fun x y => if Ord__TypeOrdering_op_zlze__ x y : bool then x else y.

Local Definition Ord__TypeOrdering_max
   : TypeOrdering -> TypeOrdering -> TypeOrdering :=
  fun x y => if Ord__TypeOrdering_op_zlze__ x y : bool then y else x.

Program Instance Ord__TypeOrdering : GHC.Base.Ord TypeOrdering :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__TypeOrdering_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__TypeOrdering_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__TypeOrdering_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__TypeOrdering_op_zgze__ ;
         GHC.Base.compare__ := Ord__TypeOrdering_compare ;
         GHC.Base.max__ := Ord__TypeOrdering_max ;
         GHC.Base.min__ := Ord__TypeOrdering_min |}.

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
  fun a b => negb (Eq___TypeOrdering_op_zeze__ a b).

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

Local Definition Ord__EqRel_op_zg__ : EqRel -> EqRel -> bool :=
  fun a b =>
    match a with
    | NomEq => match b with | NomEq => false | _ => false end
    | ReprEq => match b with | ReprEq => false | _ => true end
    end.

Local Definition Ord__EqRel_op_zgze__ : EqRel -> EqRel -> bool :=
  fun a b =>
    match a with
    | NomEq => match b with | NomEq => true | _ => false end
    | ReprEq => match b with | ReprEq => true | _ => true end
    end.

Local Definition Ord__EqRel_op_zl__ : EqRel -> EqRel -> bool :=
  fun a b =>
    match a with
    | NomEq => match b with | NomEq => false | _ => true end
    | ReprEq => match b with | ReprEq => false | _ => false end
    end.

Local Definition Ord__EqRel_op_zlze__ : EqRel -> EqRel -> bool :=
  fun a b =>
    match a with
    | NomEq => match b with | NomEq => true | _ => true end
    | ReprEq => match b with | ReprEq => true | _ => false end
    end.

Local Definition Ord__EqRel_min : EqRel -> EqRel -> EqRel :=
  fun x y => if Ord__EqRel_op_zlze__ x y : bool then x else y.

Local Definition Ord__EqRel_max : EqRel -> EqRel -> EqRel :=
  fun x y => if Ord__EqRel_op_zlze__ x y : bool then y else x.

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
  fun a b => negb (Eq___EqRel_op_zeze__ a b).

Program Instance Eq___EqRel : GHC.Base.Eq_ EqRel :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___EqRel_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___EqRel_op_zsze__ |}.

(* Translating `instance Binary__VisibilityFlag' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Binary__LeftOrRight' failed: OOPS! Cannot find
   information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable__UnivCoProvenance' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Data__CoercionHole' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Outputable__CoercionHole' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__TyThing' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance NamedThing__TyThing' failed: OOPS! Cannot find
   information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Outputable__TCvSubst' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__Type_' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__TyLit' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__TyBinder' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__VisibilityFlag' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__Coercion' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Outputable__LeftOrRight' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

Local Definition Ord__TyPrec_compare : TyPrec -> TyPrec -> comparison :=
  fun a b =>
    let 'lop_azh__ := (_Deriving.$con2tag_Fe4fHaknkFc7AP9msRFEWZ_ a) in
    let 'lop_bzh__ := (_Deriving.$con2tag_Fe4fHaknkFc7AP9msRFEWZ_ b) in
    if ((_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.<# lop_bzh__)) : bool) : bool
    then Lt
    else if ((_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.==#
                                     lop_bzh__)) : bool) : bool
         then Eq
         else Gt.

Local Definition Ord__TyPrec_op_zg__ : TyPrec -> TyPrec -> bool :=
  fun a b =>
    let 'lop_azh__ := (_Deriving.$con2tag_Fe4fHaknkFc7AP9msRFEWZ_ a) in
    let 'lop_bzh__ := (_Deriving.$con2tag_Fe4fHaknkFc7AP9msRFEWZ_ b) in
    (_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.># lop_bzh__)).

Local Definition Ord__TyPrec_op_zgze__ : TyPrec -> TyPrec -> bool :=
  fun a b =>
    let 'lop_azh__ := (_Deriving.$con2tag_Fe4fHaknkFc7AP9msRFEWZ_ a) in
    let 'lop_bzh__ := (_Deriving.$con2tag_Fe4fHaknkFc7AP9msRFEWZ_ b) in
    (_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.>=# lop_bzh__)).

Local Definition Ord__TyPrec_op_zl__ : TyPrec -> TyPrec -> bool :=
  fun a b =>
    let 'lop_azh__ := (_Deriving.$con2tag_Fe4fHaknkFc7AP9msRFEWZ_ a) in
    let 'lop_bzh__ := (_Deriving.$con2tag_Fe4fHaknkFc7AP9msRFEWZ_ b) in
    (_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.<# lop_bzh__)).

Local Definition Ord__TyPrec_op_zlze__ : TyPrec -> TyPrec -> bool :=
  fun a b =>
    let 'lop_azh__ := (_Deriving.$con2tag_Fe4fHaknkFc7AP9msRFEWZ_ a) in
    let 'lop_bzh__ := (_Deriving.$con2tag_Fe4fHaknkFc7AP9msRFEWZ_ b) in
    (_GHC.Prim.tagToEnum#_ (lop_azh__ GHC.Prim.<=# lop_bzh__)).

Local Definition Ord__TyPrec_min : TyPrec -> TyPrec -> TyPrec :=
  fun x y => if Ord__TyPrec_op_zlze__ x y : bool then x else y.

Local Definition Ord__TyPrec_max : TyPrec -> TyPrec -> TyPrec :=
  fun x y => if Ord__TyPrec_op_zlze__ x y : bool then y else x.

Program Instance Ord__TyPrec : GHC.Base.Ord TyPrec :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__TyPrec_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__TyPrec_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__TyPrec_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__TyPrec_op_zgze__ ;
         GHC.Base.compare__ := Ord__TyPrec_compare ;
         GHC.Base.max__ := Ord__TyPrec_max ;
         GHC.Base.min__ := Ord__TyPrec_min |}.

Local Definition Eq___TyPrec_op_zeze__ : TyPrec -> TyPrec -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TopPrec, TopPrec => true
    | FunPrec, FunPrec => true
    | TyOpPrec, TyOpPrec => true
    | TyConPrec, TyConPrec => true
    | _, _ => false
    end.

Local Definition Eq___TyPrec_op_zsze__ : TyPrec -> TyPrec -> bool :=
  fun a b => negb (Eq___TyPrec_op_zeze__ a b).

Program Instance Eq___TyPrec : GHC.Base.Eq_ TyPrec :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TyPrec_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TyPrec_op_zsze__ |}.

Local Definition Ord__TyThing_compare : TyThing -> TyThing -> comparison :=
  fun a b =>
    match a with
    | AnId a1 => match b with | AnId b1 => (GHC.Base.compare a1 b1) | _ => Lt end
    | AConLike a1 =>
        match b with
        | AnId _ => Gt
        | AConLike b1 => (GHC.Base.compare a1 b1)
        | _ => Lt
        end
    | ATyCon a1 =>
        match b with
        | ACoAxiom _ => Lt
        | ATyCon b1 => (GHC.Base.compare a1 b1)
        | _ => Gt
        end
    | ACoAxiom a1 =>
        match b with
        | ACoAxiom b1 => (GHC.Base.compare a1 b1)
        | _ => Gt
        end
    end.

Local Definition Ord__TyThing_op_zg__ : TyThing -> TyThing -> bool :=
  fun x y => Ord__TyThing_compare x y GHC.Base.== Gt.

Local Definition Ord__TyThing_op_zgze__ : TyThing -> TyThing -> bool :=
  fun x y => Ord__TyThing_compare x y GHC.Base./= Lt.

Local Definition Ord__TyThing_op_zl__ : TyThing -> TyThing -> bool :=
  fun x y => Ord__TyThing_compare x y GHC.Base.== Lt.

Local Definition Ord__TyThing_op_zlze__ : TyThing -> TyThing -> bool :=
  fun x y => Ord__TyThing_compare x y GHC.Base./= Gt.

Local Definition Ord__TyThing_max : TyThing -> TyThing -> TyThing :=
  fun x y => if Ord__TyThing_op_zlze__ x y : bool then y else x.

Local Definition Ord__TyThing_min : TyThing -> TyThing -> TyThing :=
  fun x y => if Ord__TyThing_op_zlze__ x y : bool then x else y.

Program Instance Ord__TyThing : GHC.Base.Ord TyThing :=
  fun _ k =>
    k {| GHC.Base.op_zl____ := Ord__TyThing_op_zl__ ;
         GHC.Base.op_zlze____ := Ord__TyThing_op_zlze__ ;
         GHC.Base.op_zg____ := Ord__TyThing_op_zg__ ;
         GHC.Base.op_zgze____ := Ord__TyThing_op_zgze__ ;
         GHC.Base.compare__ := Ord__TyThing_compare ;
         GHC.Base.max__ := Ord__TyThing_max ;
         GHC.Base.min__ := Ord__TyThing_min |}.

Local Definition Eq___TyThing_op_zeze__ : TyThing -> TyThing -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | AnId a1, AnId b1 => ((a1 GHC.Base.== b1))
    | AConLike a1, AConLike b1 => ((a1 GHC.Base.== b1))
    | ATyCon a1, ATyCon b1 => ((a1 GHC.Base.== b1))
    | ACoAxiom a1, ACoAxiom b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___TyThing_op_zsze__ : TyThing -> TyThing -> bool :=
  fun a b => negb (Eq___TyThing_op_zeze__ a b).

Program Instance Eq___TyThing : GHC.Base.Eq_ TyThing :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TyThing_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TyThing_op_zsze__ |}.

(* Translating `instance Data__TyBinder' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__Type_' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__UnivCoProvenance' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__Coercion' failed: OOPS! Cannot find information
   for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Data__LeftOrRight' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___LeftOrRight_op_zeze__
   : LeftOrRight -> LeftOrRight -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CLeft, CLeft => true
    | CRight, CRight => true
    | _, _ => false
    end.

Local Definition Eq___LeftOrRight_op_zsze__
   : LeftOrRight -> LeftOrRight -> bool :=
  fun a b => negb (Eq___LeftOrRight_op_zeze__ a b).

Program Instance Eq___LeftOrRight : GHC.Base.Eq_ LeftOrRight :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___LeftOrRight_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___LeftOrRight_op_zsze__ |}.

(* Translating `instance Data__VisibilityFlag' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___VisibilityFlag_op_zeze__
   : VisibilityFlag -> VisibilityFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Visible, Visible => true
    | Specified, Specified => true
    | Invisible, Invisible => true
    | _, _ => false
    end.

Local Definition Eq___VisibilityFlag_op_zsze__
   : VisibilityFlag -> VisibilityFlag -> bool :=
  fun a b => negb (Eq___VisibilityFlag_op_zeze__ a b).

Program Instance Eq___VisibilityFlag : GHC.Base.Eq_ VisibilityFlag :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___VisibilityFlag_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___VisibilityFlag_op_zsze__ |}.

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

Local Definition Ord__TyLit_op_zg__ : TyLit -> TyLit -> bool :=
  fun a b =>
    match a with
    | NumTyLit a1 =>
        match b with
        | NumTyLit b1 => (a1 GHC.Base.> b1)
        | _ => false
        end
    | StrTyLit a1 =>
        match b with
        | StrTyLit b1 => (a1 GHC.Base.> b1)
        | _ => true
        end
    end.

Local Definition Ord__TyLit_op_zgze__ : TyLit -> TyLit -> bool :=
  fun a b =>
    match a with
    | NumTyLit a1 =>
        match b with
        | NumTyLit b1 => (a1 GHC.Base.>= b1)
        | _ => false
        end
    | StrTyLit a1 =>
        match b with
        | StrTyLit b1 => (a1 GHC.Base.>= b1)
        | _ => true
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
  fun a b =>
    match a with
    | NumTyLit a1 =>
        match b with
        | NumTyLit b1 => (a1 GHC.Base.<= b1)
        | _ => true
        end
    | StrTyLit a1 =>
        match b with
        | StrTyLit b1 => (a1 GHC.Base.<= b1)
        | _ => false
        end
    end.

Local Definition Ord__TyLit_min : TyLit -> TyLit -> TyLit :=
  fun x y => if Ord__TyLit_op_zlze__ x y : bool then x else y.

Local Definition Ord__TyLit_max : TyLit -> TyLit -> TyLit :=
  fun x y => if Ord__TyLit_op_zlze__ x y : bool then y else x.

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
  fun a b => negb (Eq___TyLit_op_zeze__ a b).

Program Instance Eq___TyLit : GHC.Base.Eq_ TyLit :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TyLit_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TyLit_op_zsze__ |}.

(* Translating `instance Outputable__LiftingContext' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

Definition globaliseId : Id -> Id :=
  fun id =>
    match id with
    | TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
    | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
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

Definition idInfo : Id -> IdInfo.IdInfo :=
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
          #431)
    else match id with
         | TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
         | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
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

Definition isTKVar : Var -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | TyVar _ _ _ => true
    | TcTyVar _ _ _ _ => true
    | _ => false
    end.

Definition isTyVar : Var -> bool :=
  isTKVar.

Definition isTyCoVar : Var -> bool :=
  fun v => orb (isTyVar v) (isCoVar v).

Definition isTcTyVar : Var -> bool :=
  fun arg_0__ => match arg_0__ with | TcTyVar _ _ _ _ => true | _ => false end.

Definition lazySetIdInfo : Id -> IdInfo.IdInfo -> Var :=
  fun id info =>
    match id with
    | TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
    | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
    | Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
    id_info_5__ =>
        Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__ info
    end.

Definition mkTcTyVar : Name.Name -> Kind -> Core.TcTyVarDetails -> TyVar :=
  fun name kind details =>
    TcTyVar name (Unique.getKey (Name.nameUnique name)) kind details.

Definition mkTyVar : Name.Name -> Kind -> TyVar :=
  fun name kind => TyVar name (Unique.getKey (Name.nameUnique name)) kind.

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

Definition ppr_id_scope : IdScope -> Outputable.SDoc :=
  fun arg_0__ =>
    match arg_0__ with
    | GlobalId => id (GHC.Base.hs_string__ "gid")
    | LocalId Exported => id (GHC.Base.hs_string__ "lidx")
    | LocalId NotExported => id (GHC.Base.hs_string__ "lid")
    end.

Definition ppr_debug : Var -> Outputable.PprStyle -> Outputable.SDoc :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TyVar _ _ _, sty =>
        if Outputable.debugStyle sty : bool
        then Outputable.brackets (id (GHC.Base.hs_string__ "tv")) else
        Outputable.empty
    | TcTyVar _ _ _ d, sty =>
        if orb (Outputable.dumpStyle sty) (Outputable.debugStyle sty) : bool
        then Outputable.brackets (TcType.pprTcTyVarDetails d) else
        Outputable.empty
    | Id _ _ _ s d _, sty =>
        if Outputable.debugStyle sty : bool
        then Outputable.brackets (ppr_id_scope s Outputable.<>
                                  IdInfo.pprIdDetails d) else
        Outputable.empty
    end.

Definition setIdDetails : Id -> IdInfo.IdDetails -> Id :=
  fun id details =>
    match id with
    | TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
    | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
    | Id varName_0__ realUnique_1__ varType_2__ idScope_3__ id_details_4__
    id_info_5__ =>
        Id varName_0__ realUnique_1__ varType_2__ idScope_3__ details id_info_5__
    end.

Definition setIdExported : Id -> Id :=
  fun arg_0__ =>
    match arg_0__ with
    | (Id _ _ _ (LocalId _) _ _ as id) =>
        match id with
        | TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
        | TcTyVar _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
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
    | TyVar _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
    | TcTyVar varName_0__ realUnique_1__ varType_2__ tc_tv_details_3__ =>
        TcTyVar varName_0__ realUnique_1__ varType_2__ details
    | Id _ _ _ _ _ _ => error (GHC.Base.hs_string__ "Partial record update")
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

Definition tcTyVarDetails : TyVar -> Core.TcTyVarDetails :=
  fun arg_0__ =>
    match arg_0__ with
    | TcTyVar _ _ _ details => details
    | TyVar _ _ _ => TcType.vanillaSkolemTv
    | var =>
        Panic.panicStr (GHC.Base.hs_string__ "tcTyVarDetails") (GHC.Base.mappend
                                                                (GHC.Base.mappend (Panic.noString var)
                                                                                  Outputable.dcolon) (Panic.noString
                                                                 (tyVarKind var)))
    end.

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
  fun arg_0__ => match arg_0__ with | Named _ _ => None | Anon ty => Some ty end.

Definition binderVar : GHC.Base.String -> TyBinder -> Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Named v _ => v
    | e, Anon t =>
        Panic.panicStr (Coq.Init.Datatypes.app (GHC.Base.hs_string__ "binderVar (")
                                               (Coq.Init.Datatypes.app e (GHC.Base.hs_string__ ")"))) (Panic.noString t)
    end.

Definition binderVar_maybe : TyBinder -> option Var :=
  fun arg_0__ => match arg_0__ with | Named v _ => Some v | Anon _ => None end.

Definition caseBinder {a} : TyBinder -> (TyVar -> a) -> (Type_ -> a) -> a :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Named v _, f, _ => f v
    | Anon t, _, d => d t
    end.

Definition partitionBinders : list TyBinder -> (list TyVar * list Type_)%type :=
  let named_or_anon :=
    fun bndr => caseBinder bndr Data.Either.Left Data.Either.Right in
  Util.partitionWith named_or_anon.

Definition partitionBindersIntoBinders
   : list TyBinder -> (list TyBinder * list Type_)%type :=
  let named_or_anon :=
    fun bndr =>
      caseBinder bndr (fun arg_0__ => Data.Either.Left bndr) Data.Either.Right in
  Util.partitionWith named_or_anon.

Definition cmpTc : Core.TyCon -> Core.TyCon -> comparison :=
  fun tc1 tc2 =>
    let u2 := TyCon.tyConUnique tc2 in
    let u1 := TyCon.tyConUnique tc1 in
    if andb Util.debugIsOn (negb (andb (negb (Kind.isStarKindSynonymTyCon tc1))
                                       (negb (Kind.isStarKindSynonymTyCon tc2)))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
          #2236)
    else Unique.nonDetCmpUnique u1 u2.

Definition eqRelRole : EqRel -> Core.Role :=
  fun arg_0__ =>
    match arg_0__ with
    | NomEq => Core.Nominal
    | ReprEq => Core.Representational
    end.

Definition equalityTyCon : Core.Role -> Core.TyCon :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.Nominal => TysPrim.eqPrimTyCon
    | Core.Representational => TysPrim.eqReprPrimTyCon
    | Core.Phantom => TysPrim.eqPhantPrimTyCon
    end.

Definition flattenRepType : RepType -> list UnaryType :=
  fun arg_0__ =>
    match arg_0__ with
    | UbxTupleRep tys => tys
    | UnaryRep ty => cons ty nil
    end.

Definition isCTupleClass : Class.Class -> bool :=
  fun cls => TyCon.isTupleTyCon (Class.classTyCon cls).

Definition isCoercionTy : Type_ -> bool :=
  fun arg_0__ => match arg_0__ with | CoercionTy _ => true | _ => false end.

Definition isCoercionTy_maybe : Type_ -> option Coercion :=
  fun arg_0__ => match arg_0__ with | CoercionTy co => Some co | _ => None end.

Definition isForAllTy : Type_ -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | ForAllTy (Named _ _) _ => true
    | _ => false
    end.

Definition isIPClass : Class.Class -> bool :=
  fun cls => Unique.hasKey cls PrelNames.ipClassKey.

Definition isIPTyCon : Core.TyCon -> bool :=
  fun tc => Unique.hasKey tc PrelNames.ipClassKey.

Definition isIdLikeBinder : TyBinder -> bool :=
  fun arg_0__ => match arg_0__ with | Named _ _ => false | Anon _ => true end.

Definition isPiTy : Type_ -> bool :=
  fun arg_0__ => match arg_0__ with | ForAllTy _ _ => true | _ => false end.

Definition mkAnonBinder : Type_ -> TyBinder :=
  Anon.

Definition mkClassPred : Class.Class -> list Type_ -> PredType :=
  fun clas tys => TyConApp (Class.classTyCon clas) tys.

Definition mkCoercionTy : Coercion -> Type_ :=
  CoercionTy.

Definition mkForAllTy : TyBinder -> Type_ -> Type_ :=
  ForAllTy.

Definition mkPiType : Var -> Type_ -> Type_ :=
  fun v ty =>
    if isTyVar v : bool then mkForAllTy (Named v Invisible) ty else
    mkForAllTy (Anon (varType v)) ty.

Definition mkPiTypes : list Var -> Type_ -> Type_ :=
  fun vs ty => Data.Foldable.foldr mkPiType ty vs.

Definition mkHeteroPrimEqPred : Kind -> Kind -> Type_ -> Type_ -> Type_ :=
  fun k1 k2 ty1 ty2 =>
    TyConApp TysPrim.eqPrimTyCon (cons k1 (cons k2 (cons ty1 (cons ty2 nil)))).

Definition mkHeteroReprPrimEqPred : Kind -> Kind -> Type_ -> Type_ -> Type_ :=
  fun k1 k2 ty1 ty2 =>
    TyConApp TysPrim.eqReprPrimTyCon (cons k1 (cons k2 (cons ty1 (cons ty2 nil)))).

Definition mkNamedBinder : VisibilityFlag -> Var -> TyBinder :=
  fun vis var => Named var vis.

Definition mkNamedBinders : VisibilityFlag -> list TyVar -> list TyBinder :=
  fun vis => GHC.Base.map (mkNamedBinder vis).

Definition mkNamedForAllTy : TyVar -> VisibilityFlag -> Type_ -> Type_ :=
  fun tv vis =>
    if andb Util.debugIsOn (negb (isTyVar tv)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
          #1192)
    else ForAllTy (Named tv vis).

Definition mkNumLitTy : GHC.Num.Integer -> Type_ :=
  fun n => LitTy (NumTyLit n).

Definition mkStrLitTy : FastString.FastString -> Type_ :=
  fun s => LitTy (StrTyLit s).

Definition mkTyConApp : Core.TyCon -> list Type_ -> Type_ :=
  fun tycon tys =>
    let j_0__ := TyConApp tycon tys in
    if TyCon.isFunTyCon tycon : bool
    then match tys with
         | cons ty1 (cons ty2 nil) => ForAllTy (Anon ty1) ty2
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

Definition coAxNthLHS {br} : Core.CoAxiom br -> GHC.Num.Int -> Type_ :=
  fun ax ind =>
    mkTyConApp (CoAxiom.coAxiomTyCon ax) (CoAxiom.coAxBranchLHS
                                          (CoAxiom.coAxiomNthBranch ax ind)).

Definition pprSourceTyCon : Core.TyCon -> Outputable.SDoc :=
  fun tycon =>
    match TyCon.tyConFamInst_maybe tycon with
    | Some (pair fam_tc tys) => Panic.noString (TyConApp fam_tc tys)
    | _ => Panic.noString tycon
    end.

Definition pprTyVar : TyVar -> Outputable.SDoc :=
  fun tv =>
    GHC.Base.mappend (GHC.Base.mappend (Panic.noString tv) Outputable.dcolon)
                     (Panic.noString (tyVarKind tv)).

Definition repGetTyVar_maybe : Type_ -> option TyVar :=
  fun arg_0__ => match arg_0__ with | TyVarTy tv => Some tv | _ => None end.

Definition repSplitAppTy_maybe : Type_ -> option (Type_ * Type_)%type :=
  fun arg_0__ =>
    let j_1__ := let '_other := arg_0__ in None in
    match arg_0__ with
    | ForAllTy (Anon ty1) ty2 =>
        Some (pair (TyConApp TysPrim.funTyCon (cons ty1 nil)) ty2)
    | AppTy ty1 ty2 => Some (pair ty1 ty2)
    | TyConApp tc tys =>
        if orb (TyCon.mightBeUnsaturatedTyCon tc) (Util.lengthExceeds tys
                                                                      (TyCon.tyConArity tc)) : bool
        then match Util.snocView tys with
             | Some (pair tys' ty') => Some (pair (TyConApp tc tys') ty')
             | _ => j_1__
             end else
        j_1__
    | _ => j_1__
    end.

Definition repSplitAppTys : Type_ -> (Type_ * list Type_)%type :=
  fun ty =>
    let fix split arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | AppTy ty arg, args => split ty (cons arg args)
                 | TyConApp tc tc_args, args =>
                     let n :=
                       if TyCon.mightBeUnsaturatedTyCon tc : bool then #0 else
                       TyCon.tyConArity tc in
                     let 'pair tc_args1 tc_args2 := GHC.List.splitAt n tc_args in
                     pair (TyConApp tc tc_args1) (Coq.Init.Datatypes.app tc_args2 args)
                 | ForAllTy (Anon ty1) ty2, args =>
                     if andb Util.debugIsOn (negb (Data.Foldable.null args)) : bool
                     then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
                           #729)
                     else pair (TyConApp TysPrim.funTyCon nil) (cons ty1 (cons ty2 nil))
                 | ty, args => pair ty args
                 end in
    split ty nil.

Definition repSplitTyConApp_maybe
   : Type_ -> option (Core.TyCon * list Type_)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | TyConApp tc tys => Some (pair tc tys)
    | ForAllTy (Anon arg) res =>
        Some (pair TysPrim.funTyCon (cons arg (cons res nil)))
    | _ => None
    end.

Definition stripCoercionTy : Type_ -> Coercion :=
  fun arg_0__ =>
    match arg_0__ with
    | CoercionTy co => co
    | ty =>
        Panic.panicStr (GHC.Base.hs_string__ "stripCoercionTy") (Panic.noString ty)
    end.

Definition tyConAppTyConPicky_maybe : Type_ -> option Core.TyCon :=
  fun arg_0__ =>
    match arg_0__ with
    | TyConApp tc _ => Some tc
    | ForAllTy (Anon _) _ => Some TysPrim.funTyCon
    | _ => None
    end.

Definition typeLiteralKind : TyLit -> Kind :=
  fun l =>
    match l with
    | NumTyLit _ => TysWiredIn.typeNatKind
    | StrTyLit _ => TysWiredIn.typeSymbolKind
    end.

Definition binderType : TyBinder -> Type_ :=
  fun arg_0__ => match arg_0__ with | Named v _ => varType v | Anon ty => ty end.

Axiom defaultRuntimeRepVars' : forall {A : Type}, A.

Definition defaultRuntimeRepVars : Type_ -> Type_ :=
  defaultRuntimeRepVars' VarSet.emptyVarSet.

Definition eliminateRuntimeRep
   : (Type_ -> Outputable.SDoc) -> Type_ -> Outputable.SDoc :=
  fun f ty =>
    Outputable.sdocWithDynFlags (fun dflags =>
                                   if DynFlags.gopt DynFlags.Opt_PrintExplicitRuntimeReps dflags : bool
                                   then f ty
                                   else f (defaultRuntimeRepVars ty)).

(* Translating `defaultRuntimeRepVars'' failed: invalid record update with
   non-record-field `CoreType.varType' unsupported *)

Definition delBinderVar : VarSet.VarSet -> TyBinder -> VarSet.VarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | vars, Named tv _ => VarSet.delVarSet vars tv
    | vars, Anon _ => vars
    end.

Definition coVarsOfType : Type_ -> VarSet.CoVarSet :=
  fix coVarsOfType arg_0__
        := match arg_0__ with
           | TyVarTy v => coVarsOfType (tyVarKind v)
           | TyConApp _ tys => coVarsOfTypes tys
           | LitTy _ => VarSet.emptyVarSet
           | AppTy fun_ arg => VarSet.unionVarSet (coVarsOfType fun_) (coVarsOfType arg)
           | ForAllTy bndr ty =>
               VarSet.unionVarSet (delBinderVar (coVarsOfType ty) bndr) (coVarsOfType
                                   (binderType bndr))
           | CastTy ty co => VarSet.unionVarSet (coVarsOfType ty) (coVarsOfCo co)
           | CoercionTy co => coVarsOfCo co
           end.

Definition coVarsOfCo : Coercion -> VarSet.CoVarSet :=
  fix coVarsOfCo arg_0__
        := match arg_0__ with
           | Refl _ ty => coVarsOfType ty
           | TyConAppCo _ _ args => coVarsOfCos args
           | AppCo co arg => VarSet.unionVarSet (coVarsOfCo co) (coVarsOfCo arg)
           | ForAllCo tv kind_co co =>
               VarSet.unionVarSet (VarSet.delVarSet (coVarsOfCo co) tv) (coVarsOfCo kind_co)
           | CoVarCo v =>
               VarSet.unionVarSet (VarSet.unitVarSet v) (coVarsOfType (varType v))
           | AxiomInstCo _ _ args => coVarsOfCos args
           | UnivCo p _ t1 t2 =>
               VarSet.unionVarSet (coVarsOfProv p) (coVarsOfTypes (cons t1 (cons t2 nil)))
           | SymCo co => coVarsOfCo co
           | TransCo co1 co2 => VarSet.unionVarSet (coVarsOfCo co1) (coVarsOfCo co2)
           | NthCo _ co => coVarsOfCo co
           | LRCo _ co => coVarsOfCo co
           | InstCo co arg => VarSet.unionVarSet (coVarsOfCo co) (coVarsOfCo arg)
           | CoherenceCo c1 c2 => coVarsOfCos (cons c1 (cons c2 nil))
           | KindCo co => coVarsOfCo co
           | SubCo co => coVarsOfCo co
           | AxiomRuleCo _ cs => coVarsOfCos cs
           end.

Definition coVarsOfCos : list Coercion -> VarSet.CoVarSet :=
  fun cos => VarSet.mapUnionVarSet coVarsOfCo cos.

Definition coVarsOfProv : UnivCoProvenance -> VarSet.CoVarSet :=
  fun arg_0__ =>
    match arg_0__ with
    | UnsafeCoerceProv => VarSet.emptyVarSet
    | PhantomProv co => coVarsOfCo co
    | ProofIrrelProv co => coVarsOfCo co
    | PluginProv _ => VarSet.emptyVarSet
    | HoleProv _ => VarSet.emptyVarSet
    end.

Definition coVarsOfTypes : list Type_ -> VarSet.TyCoVarSet :=
  fun tys => VarSet.mapUnionVarSet coVarsOfType tys.

Definition delBinderVarFV : TyBinder -> FV.FV -> FV.FV :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | Named tv _, vars, fv_cand, in_scope, acc =>
        FV.delFV tv vars fv_cand in_scope acc
    | Anon _, vars, fv_cand, in_scope, acc => vars fv_cand in_scope acc
    end.

Definition tyCoFVsBndr : TyBinder -> FV.FV -> FV.FV :=
  fun bndr fvs =>
    FV.unionFV (delBinderVarFV bndr fvs) (tyCoFVsOfType (binderType bndr)).

Definition tyCoFVsOfType : Type_ -> FV.FV :=
  fix tyCoFVsOfType arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | TyVarTy v, a, b, c =>
               (FV.unionFV (FV.unitFV v) (tyCoFVsOfType (tyVarKind v))) a b c
           | TyConApp _ tys, a, b, c => tyCoFVsOfTypes tys a b c
           | LitTy _, a, b, c => FV.emptyFV a b c
           | AppTy fun_ arg, a, b, c =>
               (FV.unionFV (tyCoFVsOfType fun_) (tyCoFVsOfType arg)) a b c
           | ForAllTy bndr ty, a, b, c => tyCoFVsBndr bndr (tyCoFVsOfType ty) a b c
           | CastTy ty co, a, b, c =>
               (FV.unionFV (tyCoFVsOfType ty) (tyCoFVsOfCo co)) a b c
           | CoercionTy co, a, b, c => tyCoFVsOfCo co a b c
           end.

Definition tyCoFVsOfCo : Coercion -> FV.FV :=
  fix tyCoFVsOfCo arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | Refl _ ty, fv_cand, in_scope, acc => tyCoFVsOfType ty fv_cand in_scope acc
           | TyConAppCo _ _ cos, fv_cand, in_scope, acc =>
               tyCoFVsOfCos cos fv_cand in_scope acc
           | AppCo co arg, fv_cand, in_scope, acc =>
               (FV.unionFV (tyCoFVsOfCo co) (tyCoFVsOfCo arg)) fv_cand in_scope acc
           | ForAllCo tv kind_co co, fv_cand, in_scope, acc =>
               (FV.unionFV (FV.delFV tv (tyCoFVsOfCo co)) (tyCoFVsOfCo kind_co)) fv_cand
               in_scope acc
           | CoVarCo v, fv_cand, in_scope, acc =>
               (FV.unionFV (FV.unitFV v) (tyCoFVsOfType (varType v))) fv_cand in_scope acc
           | AxiomInstCo _ _ cos, fv_cand, in_scope, acc =>
               tyCoFVsOfCos cos fv_cand in_scope acc
           | UnivCo p _ t1 t2, fv_cand, in_scope, acc =>
               (FV.unionFV (FV.unionFV (tyCoFVsOfProv p) (tyCoFVsOfType t1)) (tyCoFVsOfType
                            t2)) fv_cand in_scope acc
           | SymCo co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
           | TransCo co1 co2, fv_cand, in_scope, acc =>
               (FV.unionFV (tyCoFVsOfCo co1) (tyCoFVsOfCo co2)) fv_cand in_scope acc
           | NthCo _ co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
           | LRCo _ co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
           | InstCo co arg, fv_cand, in_scope, acc =>
               (FV.unionFV (tyCoFVsOfCo co) (tyCoFVsOfCo arg)) fv_cand in_scope acc
           | CoherenceCo c1 c2, fv_cand, in_scope, acc =>
               (FV.unionFV (tyCoFVsOfCo c1) (tyCoFVsOfCo c2)) fv_cand in_scope acc
           | KindCo co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
           | SubCo co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
           | AxiomRuleCo _ cs, fv_cand, in_scope, acc =>
               tyCoFVsOfCos cs fv_cand in_scope acc
           end.

Definition tyCoFVsOfCos : list Coercion -> FV.FV :=
  fix tyCoFVsOfCos arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | nil, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
           | cons co cos, fv_cand, in_scope, acc =>
               (FV.unionFV (tyCoFVsOfCo co) (tyCoFVsOfCos cos)) fv_cand in_scope acc
           end.

Definition tyCoFVsOfProv : UnivCoProvenance -> FV.FV :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | UnsafeCoerceProv, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
    | PhantomProv co, fv_cand, in_scope, acc => tyCoFVsOfCo co fv_cand in_scope acc
    | ProofIrrelProv co, fv_cand, in_scope, acc =>
        tyCoFVsOfCo co fv_cand in_scope acc
    | PluginProv _, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
    | HoleProv _, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
    end.

Definition tyCoFVsOfTypes : list Type_ -> FV.FV :=
  fix tyCoFVsOfTypes arg_0__ arg_1__ arg_2__ arg_3__
        := match arg_0__, arg_1__, arg_2__, arg_3__ with
           | cons ty tys, fv_cand, in_scope, acc =>
               (FV.unionFV (tyCoFVsOfType ty) (tyCoFVsOfTypes tys)) fv_cand in_scope acc
           | nil, fv_cand, in_scope, acc => FV.emptyFV fv_cand in_scope acc
           end.

Definition tyCoVarsOfCos : list Coercion -> VarSet.TyCoVarSet :=
  fun cos => FV.fvVarSet (tyCoFVsOfCos cos).

Definition tyCoVarsOfProv : UnivCoProvenance -> VarSet.TyCoVarSet :=
  fun prov => FV.fvVarSet (tyCoFVsOfProv prov).

Definition tyCoVarsOfCo : Coercion -> VarSet.TyCoVarSet :=
  fun co => FV.fvVarSet (tyCoFVsOfCo co).

Definition tyCoVarsOfCoDSet : Coercion -> VarSet.DTyCoVarSet :=
  fun co => FV.fvDVarSet (tyCoFVsOfCo co).

Definition tyCoVarsOfCoList : Coercion -> list TyCoVar :=
  fun co => FV.fvVarList (tyCoFVsOfCo co).

Definition tyCoVarsOfTypes : list Type_ -> VarSet.TyCoVarSet :=
  fun tys => FV.fvVarSet (tyCoFVsOfTypes tys).

Definition getTCvSubstRangeFVs : TCvSubst -> VarSet.VarSet :=
  fun arg_0__ =>
    let 'TCvSubst _ tenv cenv := arg_0__ in
    let cenvFVs := tyCoVarsOfCos (VarEnv.varEnvElts cenv) in
    let tenvFVs := tyCoVarsOfTypes (VarEnv.varEnvElts tenv) in
    VarSet.unionVarSet tenvFVs cenvFVs.

Definition isValidTCvSubst : TCvSubst -> bool :=
  fun arg_0__ =>
    let 'TCvSubst in_scope tenv cenv := arg_0__ in
    let cenvFVs := tyCoVarsOfCos (VarEnv.varEnvElts cenv) in
    let tenvFVs := tyCoVarsOfTypes (VarEnv.varEnvElts tenv) in
    andb (VarEnv.varSetInScope tenvFVs in_scope) (VarEnv.varSetInScope cenvFVs
                                                                       in_scope).

Definition checkValidSubst {a} `{(GHC.Stack.CallStack)}
   : TCvSubst -> list Type_ -> list Coercion -> a -> a :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | (TCvSubst in_scope tenv cenv as subst), tys, cos, a =>
        let substDomain :=
          Coq.Init.Datatypes.app (VarEnv.varEnvKeys tenv) (VarEnv.varEnvKeys cenv) in
        let needInScope :=
          UniqFM.delListFromUFM_Directly (VarSet.unionVarSet (tyCoVarsOfTypes tys)
                                                             (tyCoVarsOfCos cos)) substDomain in
        let tysCosFVsInScope := VarEnv.varSetInScope needInScope in_scope in
        if andb Util.debugIsOn (negb (isValidTCvSubst subst)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/types/TyCoRep.hs") #2021 (GHC.Base.mappend (GHC.Base.mappend
                                                                                                   (GHC.Base.mappend
                                                                                                    (GHC.Base.mappend
                                                                                                     (GHC.Base.mappend
                                                                                                      (GHC.Base.mappend
                                                                                                       (GHC.Base.mappend
                                                                                                        (id
                                                                                                         (GHC.Base.hs_string__
                                                                                                          "in_scope"))
                                                                                                        (Panic.noString
                                                                                                         in_scope)
                                                                                                        Outputable.$$
                                                                                                        id
                                                                                                        (GHC.Base.hs_string__
                                                                                                         "tenv"))
                                                                                                       (Panic.noString
                                                                                                        tenv)
                                                                                                       Outputable.$$
                                                                                                       id
                                                                                                       (GHC.Base.hs_string__
                                                                                                        "tenvFVs"))
                                                                                                      (Panic.noString
                                                                                                       (tyCoVarsOfTypes
                                                                                                        (VarEnv.varEnvElts
                                                                                                         tenv)))
                                                                                                      Outputable.$$
                                                                                                      id
                                                                                                      (GHC.Base.hs_string__
                                                                                                       "cenv"))
                                                                                                     (Panic.noString
                                                                                                      cenv)
                                                                                                     Outputable.$$
                                                                                                     id
                                                                                                     (GHC.Base.hs_string__
                                                                                                      "cenvFVs"))
                                                                                                    (Panic.noString
                                                                                                     (tyCoVarsOfCos
                                                                                                      (VarEnv.varEnvElts
                                                                                                       cenv)))
                                                                                                    Outputable.$$
                                                                                                    id
                                                                                                    (GHC.Base.hs_string__
                                                                                                     "tys"))
                                                                                                   (Panic.noString tys)
                                                                                                   Outputable.$$
                                                                                                   id
                                                                                                   (GHC.Base.hs_string__
                                                                                                    "cos"))
                                                                                                  (Panic.noString cos)))
        else if andb Util.debugIsOn (negb (tysCosFVsInScope)) : bool
             then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                              "ghc/compiler/types/TyCoRep.hs") #2028 (GHC.Base.mappend (GHC.Base.mappend
                                                                                                        (GHC.Base.mappend
                                                                                                         (GHC.Base.mappend
                                                                                                          (GHC.Base.mappend
                                                                                                           (GHC.Base.mappend
                                                                                                            (id
                                                                                                             (GHC.Base.hs_string__
                                                                                                              "in_scope"))
                                                                                                            (Panic.noString
                                                                                                             in_scope)
                                                                                                            Outputable.$$
                                                                                                            id
                                                                                                            (GHC.Base.hs_string__
                                                                                                             "tenv"))
                                                                                                           (Panic.noString
                                                                                                            tenv)
                                                                                                           Outputable.$$
                                                                                                           id
                                                                                                           (GHC.Base.hs_string__
                                                                                                            "cenv"))
                                                                                                          (Panic.noString
                                                                                                           cenv)
                                                                                                          Outputable.$$
                                                                                                          id
                                                                                                          (GHC.Base.hs_string__
                                                                                                           "tys"))
                                                                                                         (Panic.noString
                                                                                                          tys)
                                                                                                         Outputable.$$
                                                                                                         id
                                                                                                         (GHC.Base.hs_string__
                                                                                                          "cos"))
                                                                                                        (Panic.noString
                                                                                                         cos)
                                                                                                        Outputable.$$
                                                                                                        id
                                                                                                        (GHC.Base.hs_string__
                                                                                                         "needInScope"))
                                                                                                       (Panic.noString
                                                                                                        needInScope)))
             else a
    end.

Definition mkTyCoInScopeSet
   : list Type_ -> list Coercion -> VarEnv.InScopeSet :=
  fun tys cos =>
    VarEnv.mkInScopeSet (VarSet.unionVarSet (tyCoVarsOfTypes tys) (tyCoVarsOfCos
                                             cos)).

Definition tyCoVarsOfTypesDSet : list Type_ -> VarSet.DTyCoVarSet :=
  fun tys => FV.fvDVarSet (tyCoFVsOfTypes tys).

Definition tyCoVarsOfTypesList : list Type_ -> list TyCoVar :=
  fun tys => FV.fvVarList (tyCoFVsOfTypes tys).

Definition closeOverKindsFV : list TyVar -> FV.FV :=
  fun tvs =>
    FV.unionFV (FV.mapUnionFV (tyCoFVsOfType GHC.Base.∘ tyVarKind) tvs) (FV.mkFVs
                tvs).

Definition closeOverKinds : VarSet.TyVarSet -> VarSet.TyVarSet :=
  FV.fvVarSet GHC.Base.∘ (closeOverKindsFV GHC.Base.∘ VarSet.varSetElems).

Definition closeOverKindsDSet : VarSet.DTyVarSet -> VarSet.DTyVarSet :=
  FV.fvDVarSet GHC.Base.∘ (closeOverKindsFV GHC.Base.∘ VarSet.dVarSetElems).

Definition closeOverKindsList : list TyVar -> list TyVar :=
  fun tvs => FV.fvVarList (closeOverKindsFV tvs).

Definition tyCoVarsOfType : Type_ -> VarSet.TyCoVarSet :=
  fun ty => FV.fvVarSet (tyCoFVsOfType ty).

Definition extendTvSubstAndInScope : TCvSubst -> TyVar -> Type_ -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | TCvSubst in_scope tenv cenv, tv, ty =>
        TCvSubst (VarEnv.extendInScopeSetSet in_scope (tyCoVarsOfType ty))
        (VarEnv.extendVarEnv tenv tv ty) cenv
    end.

Definition tyCoVarsOfTelescope
   : list Var -> VarSet.TyCoVarSet -> VarSet.TyCoVarSet :=
  fix tyCoVarsOfTelescope arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | nil, fvs => fvs
           | cons v vs, fvs =>
               VarSet.unionVarSet (VarSet.delVarSet (tyCoVarsOfTelescope vs fvs) v)
                                  (tyCoVarsOfType (varType v))
           end.

Definition mkTyBindersPreferAnon : list TyVar -> Type_ -> list TyBinder :=
  fun vars inner_ty =>
    let go : list TyVar -> Type_ -> (list TyBinder * VarSet.VarSet)%type :=
      fix go arg_0__ arg_1__
            := match arg_0__, arg_1__ with
               | nil, ty => pair nil (tyCoVarsOfType ty)
               | cons v vs, ty =>
                   let kind_vars := tyCoVarsOfType (tyVarKind v) in
                   let 'pair binders fvs := go vs ty in
                   if VarSet.elemVarSet v fvs : bool
                   then pair (cons (Named v Visible) binders) (VarSet.unionVarSet (VarSet.delVarSet
                                                                                   fvs v) kind_vars) else
                   pair (cons (Anon (tyVarKind v)) binders) (VarSet.unionVarSet fvs kind_vars)
               end in
    Data.Tuple.fst (go vars inner_ty).

Definition tyCoVarsOfTypeDSet : Type_ -> VarSet.DTyCoVarSet :=
  fun ty => FV.fvDVarSet (tyCoFVsOfType ty).

Definition tyCoVarsOfTypeList : Type_ -> list TyCoVar :=
  fun ty => FV.fvVarList (tyCoFVsOfType ty).

Definition toposortTyVars : list TyVar -> list TyVar :=
  fun tvs =>
    let var_ids : VarEnv.VarEnv GHC.Num.Int :=
      VarEnv.mkVarEnv (GHC.List.zip tvs (enumFrom #1)) in
    let nodes :=
      Coq.Lists.List.flat_map (fun tv =>
                                 cons (pair (pair tv (VarEnv.lookupVarEnv_NF var_ids tv)) (Data.Maybe.mapMaybe
                                             (VarEnv.lookupVarEnv var_ids) (tyCoVarsOfTypeList (tyVarKind tv)))) nil)
                              tvs in
    GHC.List.reverse (let cont_2__ arg_3__ :=
                        let 'pair (pair tv _) _ := arg_3__ in
                        cons tv nil in
                      Coq.Lists.List.flat_map cont_2__ (Digraph.topologicalSortG
                                               (Digraph.graphFromEdgedVertices nodes))).

Definition tyCoVarsOfTypesWellScoped : list Type_ -> list TyVar :=
  toposortTyVars GHC.Base.∘ tyCoVarsOfTypesList.

Definition dVarSetElemsWellScoped : VarSet.DVarSet -> list Var :=
  toposortTyVars GHC.Base.∘ VarSet.dVarSetElems.

Definition tyCoVarsOfTypeWellScoped : Type_ -> list TyVar :=
  toposortTyVars GHC.Base.∘ tyCoVarsOfTypeList.

Definition emptyCvSubstEnv : CvSubstEnv :=
  VarEnv.emptyVarEnv.

Definition mkTvSubst : VarEnv.InScopeSet -> TvSubstEnv -> TCvSubst :=
  fun in_scope tenv => TCvSubst in_scope tenv emptyCvSubstEnv.

Definition mkTvSubstPrs : list (TyVar * Type_)%type -> TCvSubst :=
  fun prs =>
    let onlyTyVarsAndNoCoercionTy :=
      Data.Foldable.and (let cont_0__ arg_1__ :=
                           let 'pair tv ty := arg_1__ in
                           cons (andb (isTyVar tv) (negb (isCoercionTy ty))) nil in
                         Coq.Lists.List.flat_map cont_0__ prs) in
    let in_scope :=
      VarEnv.mkInScopeSet (tyCoVarsOfTypes (GHC.Base.map Data.Tuple.snd prs)) in
    let tenv := VarEnv.mkVarEnv prs in
    if andb Util.debugIsOn (negb (onlyTyVarsAndNoCoercionTy)) : bool
    then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                     "ghc/compiler/types/TyCoRep.hs") #1810 (GHC.Base.mappend (id
                                                                                               (GHC.Base.hs_string__
                                                                                                "prs")) (Panic.noString
                                                                                               prs)))
    else mkTvSubst in_scope tenv.

Definition zipTyBinderSubst : list TyBinder -> list Type_ -> TCvSubst :=
  fun bndrs tys =>
    let tenv :=
      VarEnv.mkVarEnv (let cont_0__ arg_1__ :=
                         match arg_1__ with
                         | pair (Named tv _) ty => cons (pair tv ty) nil
                         | _ => nil
                         end in
                       Coq.Lists.List.flat_map cont_0__ (GHC.List.zip bndrs tys)) in
    let is_ := VarEnv.mkInScopeSet (tyCoVarsOfTypes tys) in mkTvSubst is_ tenv.

Definition emptyTvSubstEnv : TvSubstEnv :=
  VarEnv.emptyVarEnv.

Definition emptyTCvSubst : TCvSubst :=
  TCvSubst VarEnv.emptyInScopeSet emptyTvSubstEnv emptyCvSubstEnv.

Definition mkEmptyTCvSubst : VarEnv.InScopeSet -> TCvSubst :=
  fun is_ => TCvSubst is_ emptyTvSubstEnv emptyCvSubstEnv.

Definition extendCvSubst : TCvSubst -> CoVar -> Coercion -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | TCvSubst in_scope tenv cenv, v, co =>
        TCvSubst in_scope tenv (VarEnv.extendVarEnv cenv v co)
    end.

Definition extendTCvInScope : TCvSubst -> Var -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst in_scope tenv cenv, var =>
        TCvSubst (VarEnv.extendInScopeSet in_scope var) tenv cenv
    end.

Definition extendTCvInScopeList : TCvSubst -> list Var -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst in_scope tenv cenv, vars =>
        TCvSubst (VarEnv.extendInScopeSetList in_scope vars) tenv cenv
    end.

Definition extendTCvInScopeSet : TCvSubst -> VarSet.VarSet -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst in_scope tenv cenv, vars =>
        TCvSubst (VarEnv.extendInScopeSetSet in_scope vars) tenv cenv
    end.

Definition extendTvSubst : TCvSubst -> TyVar -> Type_ -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | TCvSubst in_scope tenv cenv, tv, ty =>
        TCvSubst in_scope (VarEnv.extendVarEnv tenv tv ty) cenv
    end.

Definition extendTvSubstBinder : TCvSubst -> TyBinder -> Type_ -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | env, Anon _, _ => env
    | env, Named tv _, ty => extendTvSubst env tv ty
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

Definition getTCvInScope : TCvSubst -> VarEnv.InScopeSet :=
  fun arg_0__ => let 'TCvSubst in_scope _ _ := arg_0__ in in_scope.

Definition getTvSubstEnv : TCvSubst -> TvSubstEnv :=
  fun arg_0__ => let 'TCvSubst _ env _ := arg_0__ in env.

Definition if_print_coercions
   : Outputable.SDoc -> Outputable.SDoc -> Outputable.SDoc :=
  fun yes no =>
    Outputable.sdocWithDynFlags (fun dflags =>
                                   Outputable.getPprStyle (fun style =>
                                                             if orb (DynFlags.gopt DynFlags.Opt_PrintExplicitCoercions
                                                                     dflags) (orb (Outputable.dumpStyle style)
                                                                                  (Outputable.debugStyle style)) : bool
                                                             then yes
                                                             else no)).

Definition isAnonBinder : TyBinder -> bool :=
  fun arg_0__ => match arg_0__ with | Anon _ => true | _ => false end.

Definition isCoercionType : Type_ -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | TyConApp tc tys =>
        if andb (orb (Unique.hasKey tc PrelNames.eqPrimTyConKey) (Unique.hasKey tc
                                                                                PrelNames.eqReprPrimTyConKey))
                (Data.Foldable.length tys GHC.Base.== #4) : bool
        then true else
        false
    | _ => false
    end.

Definition isEmptyTCvSubst : TCvSubst -> bool :=
  fun arg_0__ =>
    let 'TCvSubst _ tenv cenv := arg_0__ in
    andb (VarEnv.isEmptyVarEnv tenv) (VarEnv.isEmptyVarEnv cenv).

Definition isInScope : Var -> TCvSubst -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, TCvSubst in_scope _ _ => VarEnv.elemInScopeSet v in_scope
    end.

Definition isNamedBinder : TyBinder -> bool :=
  fun arg_0__ => match arg_0__ with | Named _ _ => true | _ => false end.

Definition lookupCoVar : TCvSubst -> Var -> option Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst _ _ cenv, v => VarEnv.lookupVarEnv cenv v
    end.

Definition lookupTyVar : TCvSubst -> TyVar -> option Type_ :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst _ tenv _, tv =>
        if andb Util.debugIsOn (negb (isTyVar tv)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
              #2142)
        else VarEnv.lookupVarEnv tenv tv
    end.

Definition maybeParen
   : TyPrec -> TyPrec -> Outputable.SDoc -> Outputable.SDoc :=
  fun ctxt_prec inner_prec pretty =>
    if ctxt_prec GHC.Base.< inner_prec : bool then pretty else
    Outputable.parens pretty.

Definition pprArrowChain : TyPrec -> list Outputable.SDoc -> Outputable.SDoc :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, nil => Outputable.empty
    | p, cons arg args =>
        maybeParen p FunPrec (Outputable.sep (cons arg (cons (Outputable.sep
                                                              (GHC.Base.map (fun arg_2__ =>
                                                                               GHC.Base.mappend Outputable.arrow
                                                                                                arg_2__) args)) nil)))
    end.

Definition pprInfixApp {a}
   : TyPrec ->
     (TyPrec -> a -> Outputable.SDoc) ->
     Outputable.SDoc -> a -> a -> Outputable.SDoc :=
  fun p pp pp_tc ty1 ty2 =>
    maybeParen p TyOpPrec (Outputable.sep (cons (pp TyOpPrec ty1) (cons
                                                 (GHC.Base.mappend (Outputable.pprInfixVar true pp_tc) (pp TyOpPrec
                                                                    ty2)) nil))).

Definition pprPrefixApp
   : TyPrec -> Outputable.SDoc -> list Outputable.SDoc -> Outputable.SDoc :=
  fun p pp_fun pp_tys =>
    if Data.Foldable.null pp_tys : bool then pp_fun else
    maybeParen p TyConPrec (Outputable.hang pp_fun #2 (Outputable.sep pp_tys)).

Definition pprTupleApp {a}
   : TyPrec ->
     (TyPrec -> a -> Outputable.SDoc) ->
     Core.TyCon -> BasicTypes.TupleSort -> list a -> Outputable.SDoc :=
  fun p pp tc sort tys =>
    let j_0__ :=
      TyCon.pprPromotionQuote tc Outputable.<>
      BasicTypes.tupleParens sort (Outputable.pprWithCommas (pp TopPrec) tys) in
    if Data.Foldable.null tys : bool
    then match sort with
         | BasicTypes.ConstraintTuple =>
             if StaticFlags.opt_PprStyle_Debug : bool
             then id (GHC.Base.hs_string__ "(%%)")
             else maybeParen p FunPrec (id (GHC.Base.hs_string__ "() :: Constraint"))
         | _ => j_0__
         end else
    j_0__.

Definition mkForAllTys : list TyBinder -> Type_ -> Type_ :=
  fun tyvars ty => Data.Foldable.foldr ForAllTy ty tyvars.

Definition mkVisForAllTys : list TyVar -> Type_ -> Type_ :=
  fun tvs =>
    if andb Util.debugIsOn (negb (Data.Foldable.all isTyVar tvs)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
          #1209)
    else mkForAllTys (GHC.Base.map (GHC.Base.flip Named Visible) tvs).

Definition mkSpecForAllTys : list TyVar -> Type_ -> Type_ :=
  fun tvs =>
    if andb Util.debugIsOn (negb (Data.Foldable.all isTyVar tvs)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
          #1204)
    else mkForAllTys (GHC.Base.map (GHC.Base.flip Named Specified) tvs).

Definition mkInvForAllTys : list TyVar -> Type_ -> Type_ :=
  fun tvs =>
    if andb Util.debugIsOn (negb (Data.Foldable.all isTyVar tvs)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
          #1198)
    else mkForAllTys (GHC.Base.map (GHC.Base.flip Named Invisible) tvs).

Definition mkFunTy : Type_ -> Type_ -> Type_ :=
  fun arg res => ForAllTy (Anon arg) res.

Definition mkFunTys : list Type_ -> Type_ -> Type_ :=
  fun tys ty => Data.Foldable.foldr mkFunTy ty tys.

Definition mkTCvSubst
   : VarEnv.InScopeSet -> (TvSubstEnv * CvSubstEnv)%type -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | in_scope, pair tenv cenv => TCvSubst in_scope tenv cenv
    end.

Definition mkTyConTy : Core.TyCon -> Type_ :=
  fun tycon => TyConApp tycon nil.

Definition mkTyVarTy : TyVar -> Type_ :=
  fun v =>
    if andb Util.debugIsOn (negb (isTyVar v)) : bool
    then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                     "ghc/compiler/types/TyCoRep.hs") #517 (GHC.Base.mappend (GHC.Base.mappend
                                                                                              (Panic.noString v)
                                                                                              Outputable.dcolon)
                                                                                             (Panic.noString (tyVarKind
                                                                                                              v))))
    else TyVarTy v.

Definition mkTyVarTys : list TyVar -> list Type_ :=
  GHC.Base.map mkTyVarTy.

Definition extendTvSubstWithClone : TCvSubst -> TyVar -> TyVar -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | TCvSubst in_scope tenv cenv, tv, tv' =>
        let new_in_scope := VarSet.extendVarSet (tyCoVarsOfType (tyVarKind tv')) tv' in
        TCvSubst (VarEnv.extendInScopeSetSet in_scope new_in_scope) (VarEnv.extendVarEnv
                                                                     tenv tv (mkTyVarTy tv')) cenv
    end.

Definition notElemTCvSubst : Var -> TCvSubst -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, TCvSubst _ tenv cenv =>
        if isTyVar v : bool then negb (VarEnv.elemVarEnv v tenv) else
        negb (VarEnv.elemVarEnv v cenv)
    end.

Definition pickLR {a} : LeftOrRight -> (a * a)%type -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CLeft, pair l _ => l
    | CRight, pair _ r => r
    end.

Definition pprTyThingCategory : TyThing -> Outputable.SDoc :=
  fun arg_0__ =>
    match arg_0__ with
    | ATyCon tc =>
        if TyCon.isClassTyCon tc : bool then id (GHC.Base.hs_string__ "Class") else
        id (GHC.Base.hs_string__ "Type constructor")
    | ACoAxiom _ => id (GHC.Base.hs_string__ "Coercion axiom")
    | AnId _ => id (GHC.Base.hs_string__ "Identifier")
    | AConLike (ConLike.RealDataCon _) =>
        id (GHC.Base.hs_string__ "Data constructor")
    | AConLike (ConLike.PatSynCon _) => id (GHC.Base.hs_string__ "Pattern synonym")
    end.

Definition pprTyThing : TyThing -> Outputable.SDoc :=
  fun thing =>
    GHC.Base.mappend (pprTyThingCategory thing) (Outputable.quotes (Panic.noString
                                                                    (Name.getName thing))).

Definition ppr_tvar : TyVar -> Outputable.SDoc :=
  fun tv => OccName.parenSymOcc (Name.getOccName tv) (Panic.noString tv).

Definition ppr_tylit : TyPrec -> TyLit -> Outputable.SDoc :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, tl =>
        match tl with
        | NumTyLit n => Outputable.integer n
        | StrTyLit s => id (GHC.Show.show s)
        end
    end.

Definition pprTyLit : TyLit -> Outputable.SDoc :=
  ppr_tylit TopPrec.

Definition sameVis : VisibilityFlag -> VisibilityFlag -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Visible, Visible => true
    | Visible, _ => false
    | _, Visible => false
    | _, _ => true
    end.

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

Definition substCoVar : TCvSubst -> CoVar -> Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst _ _ cenv, cv =>
        match VarEnv.lookupVarEnv cenv cv with
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
              #2131)
        else match VarEnv.lookupVarEnv tenv tv with
             | Some ty => ty
             | None => TyVarTy tv
             end
    end.

Definition substTyVars : TCvSubst -> list TyVar -> list Type_ :=
  fun subst => GHC.Base.map (substTyVar subst).

Definition tidyCo : VarEnv.TidyEnv -> Coercion -> Coercion :=
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
                            | CoVarCo cv =>
                                match VarEnv.lookupVarEnv subst cv with
                                | None => CoVarCo cv
                                | Some cv' => CoVarCo cv'
                                end
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
                 fun arg_28__ =>
                   match arg_28__ with
                   | UnsafeCoerceProv => UnsafeCoerceProv
                   | PhantomProv co => PhantomProv (go co)
                   | ProofIrrelProv co => ProofIrrelProv (go co)
                   | (PluginProv _ as p) => p
                   | (HoleProv _ as p) => p
                   end in
               go co
           end.

Definition tidyCos : VarEnv.TidyEnv -> list Coercion -> list Coercion :=
  fun env => GHC.Base.map (tidyCo env).

Definition tidyTyCoVarBndr
   : VarEnv.TidyEnv -> TyCoVar -> (VarEnv.TidyEnv * TyCoVar)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (pair occ_env subst as tidy_env), tyvar =>
        let name := tyVarName tyvar in
        let occ := Name.getOccName name in
        let occ1 :=
          if Name.isSystemName name : bool
          then if isTyVar tyvar : bool
               then OccName.mkTyVarOcc (Coq.Init.Datatypes.app (OccName.occNameString occ)
                                                               (GHC.Base.hs_string__ "0"))
               else OccName.mkVarOcc (Coq.Init.Datatypes.app (OccName.occNameString occ)
                                                             (GHC.Base.hs_string__ "0")) else
          occ in
        let 'pair tidy' occ' := OccName.tidyOccName occ_env occ1 in
        let kind' := tidyKind tidy_env (tyVarKind tyvar) in
        let name' := Name.tidyNameOcc name occ' in
        let tyvar' := setTyVarKind (setTyVarName tyvar name') kind' in
        let subst' := VarEnv.extendVarEnv subst tyvar tyvar' in
        pair (pair tidy' subst') tyvar'
    end.

Definition tidyKind : VarEnv.TidyEnv -> Kind -> Kind :=
  tidyType.

Definition tidyType : VarEnv.TidyEnv -> Type_ -> Type_ :=
  fix tidyType arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, LitTy n => LitTy n
           | env, TyVarTy tv => TyVarTy (tidyTyVarOcc env tv)
           | env, TyConApp tycon tys =>
               let args := tidyTypes env tys in Util.seqList args (TyConApp tycon args)
           | env, AppTy fun_ arg => AppTy (tidyType env fun_) (tidyType env arg)
           | env, ForAllTy (Anon fun_) arg =>
               ForAllTy (Anon (tidyType env fun_)) (tidyType env arg)
           | env, ForAllTy (Named tv vis) ty =>
               let 'pair envp tvp := tidyTyCoVarBndr env tv in
               ForAllTy (Named tvp vis) (tidyType envp ty)
           | env, CastTy ty co => CastTy (tidyType env ty) (tidyCo env co)
           | env, CoercionTy co => CoercionTy (tidyCo env co)
           end.

Definition tidyTyVarOcc : VarEnv.TidyEnv -> TyVar -> TyVar :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (pair _ subst as env), tv =>
        match VarEnv.lookupVarEnv subst tv with
        | None => updateTyVarKind (tidyType env) tv
        | Some tv' => tv'
        end
    end.

Definition tidyTypes : VarEnv.TidyEnv -> list Type_ -> list Type_ :=
  fun env tys => GHC.Base.map (tidyType env) tys.

Definition tidyTyCoVarBndrs
   : VarEnv.TidyEnv -> list TyCoVar -> (VarEnv.TidyEnv * list TyCoVar)%type :=
  fun env tvs => Data.Traversable.mapAccumL tidyTyCoVarBndr env tvs.

Definition tidyOpenTyCoVar
   : VarEnv.TidyEnv -> TyCoVar -> (VarEnv.TidyEnv * TyCoVar)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (pair _ subst as env), tyvar =>
        match VarEnv.lookupVarEnv subst tyvar with
        | Some tyvar' => pair env tyvar'
        | None =>
            let env' := tidyFreeTyCoVars env (tyCoVarsOfTypeList (tyVarKind tyvar)) in
            tidyTyCoVarBndr env' tyvar
        end
    end.

Definition tidyFreeTyCoVars
   : VarEnv.TidyEnv -> list TyCoVar -> VarEnv.TidyEnv :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair full_occ_env var_env, tyvars =>
        Data.Tuple.fst (tidyOpenTyCoVars (pair full_occ_env var_env) tyvars)
    end.

Definition tidyOpenTyCoVars
   : VarEnv.TidyEnv -> list TyCoVar -> (VarEnv.TidyEnv * list TyCoVar)%type :=
  fun env tyvars => Data.Traversable.mapAccumL tidyOpenTyCoVar env tyvars.

Definition tidyOpenTypes
   : VarEnv.TidyEnv -> list Type_ -> (VarEnv.TidyEnv * list Type_)%type :=
  fun env tys =>
    let 'pair (pair _ var_env as env') tvs' := tidyOpenTyCoVars env
                                                 (tyCoVarsOfTypesWellScoped tys) in
    let trimmed_occ_env :=
      OccName.initTidyOccEnv (GHC.Base.map Name.getOccName tvs') in
    pair env' (tidyTypes (pair trimmed_occ_env var_env) tys).

Definition tidyOpenType
   : VarEnv.TidyEnv -> Type_ -> (VarEnv.TidyEnv * Type_)%type :=
  fun env ty =>
    let 'pair env' (cons ty' nil) := tidyOpenTypes env (cons ty nil) in
    pair env' ty'.

Definition tidyOpenKind
   : VarEnv.TidyEnv -> Kind -> (VarEnv.TidyEnv * Kind)%type :=
  tidyOpenType.

Definition tidyTopType : Type_ -> Type_ :=
  fun ty => tidyType VarEnv.emptyTidyEnv ty.

Definition tidyTyBinder
   : VarEnv.TidyEnv -> TyBinder -> (VarEnv.TidyEnv * TyBinder)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | tidy_env, Named tv vis =>
        let 'pair tidy_env' tv' := tidyTyCoVarBndr tidy_env tv in
        pair tidy_env' (Named tv' vis)
    | tidy_env, Anon ty => pair tidy_env (Anon (tidyType tidy_env ty))
    end.

Definition tidyTyBinders
   : VarEnv.TidyEnv -> list TyBinder -> (VarEnv.TidyEnv * list TyBinder)%type :=
  Data.Traversable.mapAccumL tidyTyBinder.

Definition unionTCvSubst : TCvSubst -> TCvSubst -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst in_scope1 tenv1 cenv1, TCvSubst in_scope2 tenv2 cenv2 =>
        if andb Util.debugIsOn (negb (andb (negb (VarEnv.intersectsVarEnv tenv1 tenv2))
                                           (negb (VarEnv.intersectsVarEnv cenv1 cenv2)))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
              #1758)
        else TCvSubst (VarEnv.unionInScope in_scope1 in_scope2) (VarEnv.plusVarEnv tenv1
                                                                                   tenv2) (VarEnv.plusVarEnv cenv1
                                                                                                             cenv2)
    end.

Definition zapTCvSubst : TCvSubst -> TCvSubst :=
  fun arg_0__ =>
    let 'TCvSubst in_scope _ _ := arg_0__ in
    TCvSubst in_scope VarEnv.emptyVarEnv VarEnv.emptyVarEnv.

Definition zipCoEnv : list CoVar -> list Coercion -> CvSubstEnv :=
  fun cvs cos =>
    VarEnv.mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipCoEnv") cvs cos).

Definition zipCvSubst : list CoVar -> list Coercion -> TCvSubst :=
  fun cvs cos =>
    let cenv := zipCoEnv cvs cos in
    if andb Util.debugIsOn (orb (negb (Data.Foldable.all isCoVar cvs))
                                (Data.Foldable.length cvs GHC.Base./= Data.Foldable.length cos)) : bool
    then Outputable.pprTrace (GHC.Base.hs_string__ "zipCvSubst") (Panic.noString cvs
                                                                  Outputable.$$
                                                                  Panic.noString cos) emptyTCvSubst else
    TCvSubst (VarEnv.mkInScopeSet (tyCoVarsOfCos cos)) emptyTvSubstEnv cenv.

Definition zipTyEnv : list TyVar -> list Type_ -> TvSubstEnv :=
  fun tyvars tys =>
    if andb Util.debugIsOn (negb (Data.Foldable.all (negb GHC.Base.∘ isCoercionTy)
                                  tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #1820)
    else VarEnv.mkVarEnv (Util.zipEqual (GHC.Base.hs_string__ "zipTyEnv") tyvars
                          tys).

Definition zipTvSubst : list TyVar -> list Type_ -> TCvSubst :=
  fun tvs tys =>
    let tenv := zipTyEnv tvs tys in
    if andb Util.debugIsOn (orb (negb (Data.Foldable.all isTyVar tvs))
                                (Data.Foldable.length tvs GHC.Base./= Data.Foldable.length tys)) : bool
    then Outputable.pprTrace (GHC.Base.hs_string__ "zipTvSubst") (Panic.noString tvs
                                                                  Outputable.$$
                                                                  Panic.noString tys) emptyTCvSubst else
    mkTvSubst (VarEnv.mkInScopeSet (tyCoVarsOfTypes tys)) tenv.

Definition coVarKind : CoVar -> Type_ :=
  fun cv =>
    if andb Util.debugIsOn (negb (isCoVar cv)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #396)
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
        let new_var := VarEnv.uniqAway (getTCvInScope subst) (setVarType old_var k1) in
        let lifted := Refl Core.Nominal (TyVarTy new_var) in
        let new_cenv := VarEnv.extendVarEnv cenv old_var lifted in
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
        let no_kind_change := VarSet.isEmptyVarSet (tyCoVarsOfCo old_kind_co) in
        let new_kind_co :=
          if no_kind_change : bool then old_kind_co else
          sco old_kind_co in
        let 'Pair.Mk_Pair new_ki1 _ := coercionKind new_kind_co in
        let new_var := VarEnv.uniqAway in_scope (setTyVarKind old_var new_ki1) in
        let no_change := andb no_kind_change (new_var GHC.Base.== old_var) in
        let new_env :=
          if andb no_change (negb sym) : bool then VarEnv.delVarEnv tenv old_var else
          if sym : bool
          then VarEnv.extendVarEnv tenv old_var (CastTy (TyVarTy new_var)
                                                        new_kind_co) else
          VarEnv.extendVarEnv tenv old_var (TyVarTy new_var) in
        pair (pair (TCvSubst (VarEnv.extendInScopeSet in_scope new_var) new_env cenv)
                   new_var) new_kind_co
    end.

(* Translating `coercionKind' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Axiom coercionKindRole : forall {A : Type}, A.

Definition coercionRole : Coercion -> Core.Role :=
  Data.Tuple.snd GHC.Base.∘ coercionKindRole.

Definition setNominalRole_maybe : Coercion -> option Coercion :=
  fix setNominalRole_maybe arg_0__
        := let 'co := arg_0__ in
           match coercionRole co with
           | Core.Nominal => Some co
           | _ =>
               match arg_0__ with
               | SubCo co => Some co
               | Refl _ ty => Some (Refl Core.Nominal ty)
               | TyConAppCo Core.Representational tc cos =>
                   Data.Traversable.mapM setNominalRole_maybe cos GHC.Base.>>=
                   (fun cos' => GHC.Base.return_ (TyConAppCo Core.Nominal tc cos'))
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
                       | HoleProv _ => false
                       end) : bool
                   then Some (UnivCo prov Core.Nominal co1 co2) else
                   None
               end
           end.

(* Translating `coercionKindRole' failed: using a record pattern for the unknown
   constructor `LRCo' unsupported *)

Definition coercionSize : Coercion -> GHC.Num.Int :=
  fix coercionSize arg_0__
        := match arg_0__ with
           | Refl _ ty => typeSize ty
           | TyConAppCo _ _ args =>
               #1 GHC.Num.+ Data.Foldable.sum (GHC.Base.map coercionSize args)
           | AppCo co arg => coercionSize co GHC.Num.+ coercionSize arg
           | ForAllCo _ h co => (#1 GHC.Num.+ coercionSize co) GHC.Num.+ coercionSize h
           | CoVarCo _ => #1
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
    | HoleProv h =>
        Panic.panicStr (GHC.Base.hs_string__ "provSize hits a hole") (Panic.noString h)
    end.

Definition typeSize : Type_ -> GHC.Num.Int :=
  fix typeSize arg_0__
        := match arg_0__ with
           | LitTy _ => #1
           | TyVarTy _ => #1
           | AppTy t1 t2 => typeSize t1 GHC.Num.+ typeSize t2
           | ForAllTy b t => typeSize (binderType b) GHC.Num.+ typeSize t
           | TyConApp _ ts => #1 GHC.Num.+ Data.Foldable.sum (GHC.Base.map typeSize ts)
           | CastTy ty co => typeSize ty GHC.Num.+ coercionSize co
           | CoercionTy co => coercionSize co
           end.

Definition composeSteppers {ev}
   : NormaliseStepper ev -> NormaliseStepper ev -> NormaliseStepper ev :=
  fun step1 step2 rec_nts tc tys =>
    match step1 rec_nts tc tys with
    | (NS_Step _ _ _ as success) => success
    | NS_Done => step2 rec_nts tc tys
    | NS_Abort => NS_Abort
    end.

Definition emptyLiftingContext : VarEnv.InScopeSet -> LiftingContext :=
  fun in_scope => LC (mkEmptyTCvSubst in_scope) VarEnv.emptyVarEnv.

Definition extendLiftingContext
   : LiftingContext -> TyVar -> Coercion -> LiftingContext :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | LC subst env, tv, arg =>
        if andb Util.debugIsOn (negb (isTyVar tv)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
              #1482)
        else LC subst (VarEnv.extendVarEnv env tv arg)
    end.

Definition getCoVar_maybe : Coercion -> option CoVar :=
  fun arg_0__ => match arg_0__ with | CoVarCo cv => Some cv | _ => None end.

Definition isCoVar_maybe : Coercion -> option CoVar :=
  fun arg_0__ => match arg_0__ with | CoVarCo cv => Some cv | _ => None end.

Definition isMappedByLC : TyCoVar -> LiftingContext -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | tv, LC _ env => VarEnv.elemVarEnv tv env
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

Definition isReflCo_maybe : Coercion -> option (Type_ * Core.Role)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Refl r ty => Some (pair ty r)
    | _ => None
    end.

Definition lcInScopeSet : LiftingContext -> VarEnv.InScopeSet :=
  fun arg_0__ => let 'LC subst _ := arg_0__ in getTCvInScope subst.

Definition lcTCvSubst : LiftingContext -> TCvSubst :=
  fun arg_0__ => let 'LC subst _ := arg_0__ in subst.

Definition ltRole : Core.Role -> Core.Role -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Core.Phantom, _ => false
    | Core.Representational, Core.Phantom => true
    | Core.Representational, _ => false
    | Core.Nominal, Core.Nominal => false
    | Core.Nominal, _ => true
    end.

Definition mapStepResult {ev1} {ev2}
   : (ev1 -> ev2) -> NormaliseStepResult ev1 -> NormaliseStepResult ev2 :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, NS_Step rec_nts ty ev => NS_Step rec_nts ty (f ev)
    | _, NS_Done => NS_Done
    | _, NS_Abort => NS_Abort
    end.

Definition mkAxiomInstCo
   : Core.CoAxiom Core.Branched ->
     Core.BranchIndex -> list Coercion -> Coercion :=
  fun ax index args =>
    if andb Util.debugIsOn (negb (CoAxiom.coAxiomArity ax index GHC.Base.==
                                  Data.Foldable.length args)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #766)
    else AxiomInstCo ax index args.

Definition mkAxiomRuleCo : Core.CoAxiomRule -> list Coercion -> Coercion :=
  AxiomRuleCo.

Axiom mkCoherenceCo : forall {A : Type}, A.

Definition mkCoherenceLeftCo : Coercion -> Coercion -> Coercion :=
  mkCoherenceCo.

(* Translating `mkCoherenceCo' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Axiom mkForAllCo : forall {A : Type}, A.

(* Translating `mkForAllCo' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Definition mkHeteroCoercionType
   : Core.Role -> Kind -> Kind -> Type_ -> Type_ -> Type_ :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.Nominal => mkHeteroPrimEqPred
    | Core.Representational => mkHeteroReprPrimEqPred
    | Core.Phantom => Panic.panic (GHC.Base.hs_string__ "mkHeteroCoercionType")
    end.

Definition mkLiftingContext
   : list (TyCoVar * Coercion)%type -> LiftingContext :=
  fun pairs =>
    LC (mkEmptyTCvSubst (VarEnv.mkInScopeSet (tyCoVarsOfCos (GHC.Base.map
                                                             Data.Tuple.snd pairs)))) (VarEnv.mkVarEnv pairs).

Axiom mkProofIrrelCo : forall {A : Type}, A.

(* Translating `mkProofIrrelCo' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Definition mkReflCo : Core.Role -> Type_ -> Coercion :=
  fun r ty => Refl r ty.

Definition mkRepReflCo : Type_ -> Coercion :=
  mkReflCo Core.Representational.

Definition mkNomReflCo : Type_ -> Coercion :=
  mkReflCo Core.Nominal.

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

Definition mkSubstLiftingContext : TCvSubst -> LiftingContext :=
  fun subst => LC subst VarEnv.emptyVarEnv.

Axiom mkSymCo : forall {A : Type}, A.

Definition swapLiftCoEnv : LiftCoEnv -> LiftCoEnv :=
  VarEnv.mapVarEnv mkSymCo.

Definition mkCoherenceRightCo : Coercion -> Coercion -> Coercion :=
  fun c1 c2 => mkSymCo (mkCoherenceCo (mkSymCo c1) c2).

Definition castCoercionKind : Coercion -> Coercion -> Coercion -> Coercion :=
  fun g h1 h2 => mkCoherenceRightCo (mkCoherenceLeftCo g h1) h2.

(* Translating `mkSymCo' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Axiom mkTransCo : forall {A : Type}, A.

(* Translating `mkTransCo' failed: using a record pattern for the unknown
   constructor `Refl' unsupported *)

Axiom pprCoAxiom : forall {A : Type}, A.

(* Translating `pprCoAxiom' failed: using a record pattern for the unknown
   constructor `CoAxiom' unsupported *)

Definition pprCoBndr : Name.Name -> Coercion -> Outputable.SDoc :=
  fun name eta =>
    GHC.Base.mappend Outputable.forAllLit (Outputable.parens (GHC.Base.mappend
                                                              (GHC.Base.mappend (Panic.noString name) Outputable.dcolon)
                                                              (Panic.noString eta))) Outputable.<>
    Outputable.dot.

Definition ppr_axiom_rule_co
   : Core.CoAxiomRule -> list Coercion -> Outputable.SDoc :=
  fun co ps =>
    GHC.Base.mappend (Panic.noString (CoAxiom.coaxrName co)) (Outputable.parens
                      (Outputable.interpp'SP ps)).

Axiom ppr_co : forall {A : Type}, A.

Definition ppr_fun_co : TyPrec -> Coercion -> Outputable.SDoc :=
  fun p co =>
    let split : Coercion -> list Outputable.SDoc :=
      fix split arg_0__
            := let j_2__ := let 'co := arg_0__ in cons (ppr_co TopPrec co) nil in
               let 'TyConAppCo _ f (cons arg (cons res nil)) := arg_0__ in
               if Unique.hasKey f PrelNames.funTyConKey : bool
               then cons (ppr_co FunPrec arg) (split res) else
               j_2__ in
    pprArrowChain p (split co).

Definition pprParendCo : Coercion -> Outputable.SDoc :=
  fun co => ppr_co TyConPrec co.

Definition ppr_forall_co : TyPrec -> Coercion -> Outputable.SDoc :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | p, ForAllCo tv h co =>
        maybeParen p FunPrec (Outputable.sep (cons (pprCoBndr (tyVarName tv) h) (cons
                                                    (ppr_co TopPrec co) nil)))
    | _, _ => Panic.panic (GHC.Base.hs_string__ "ppr_forall_co")
    end.

Definition pprCo : Coercion -> Outputable.SDoc :=
  fun co => ppr_co TopPrec co.

(* Translating `ppr_co' failed: using a record pattern for the unknown
   constructor `ForAllCo' unsupported *)

Axiom ppr_co_ax_branch : forall {A : Type}, A.

(* Translating `ppr_co_ax_branch' failed: using a record pattern for the unknown
   constructor `CoAxiom' unsupported *)

Definition ppr_role : Core.Role -> Outputable.SDoc :=
  fun r =>
    let pp_role :=
      match r with
      | Core.Nominal => Outputable.char (GHC.Char.hs_char__ "N")
      | Core.Representational => Outputable.char (GHC.Char.hs_char__ "R")
      | Core.Phantom => Outputable.char (GHC.Char.hs_char__ "P")
      end in
    Outputable.underscore Outputable.<> pp_role.

Axiom promoteCoercion : forall {A : Type}, A.

(* Translating `promoteCoercion' failed: using a record pattern for the unknown
   constructor `CoVarCo' unsupported *)

Definition seqCo : Coercion -> unit :=
  fix seqCo arg_0__
        := match arg_0__ with
           | Refl r ty => GHC.Prim.seq r (seqType ty)
           | TyConAppCo r tc cos => GHC.Prim.seq r (GHC.Prim.seq tc (seqCos cos))
           | AppCo co1 co2 => GHC.Prim.seq (seqCo co1) (seqCo co2)
           | ForAllCo tv k co =>
               GHC.Prim.seq (seqType (tyVarKind tv)) (GHC.Prim.seq (seqCo k) (seqCo co))
           | CoVarCo cv => GHC.Prim.seq cv tt
           | AxiomInstCo con ind cos => GHC.Prim.seq con (GHC.Prim.seq ind (seqCos cos))
           | UnivCo p r t1 t2 =>
               GHC.Prim.seq (seqProv p) (GHC.Prim.seq r (GHC.Prim.seq (seqType t1) (seqType
                                                                       t2)))
           | SymCo co => seqCo co
           | TransCo co1 co2 => GHC.Prim.seq (seqCo co1) (seqCo co2)
           | NthCo n co => GHC.Prim.seq n (seqCo co)
           | LRCo lr co => GHC.Prim.seq lr (seqCo co)
           | InstCo co arg => GHC.Prim.seq (seqCo co) (seqCo arg)
           | CoherenceCo co1 co2 => GHC.Prim.seq (seqCo co1) (seqCo co2)
           | KindCo co => seqCo co
           | SubCo co => seqCo co
           | AxiomRuleCo _ cs => seqCos cs
           end.

Definition seqCos : list Coercion -> unit :=
  fix seqCos arg_0__
        := match arg_0__ with
           | nil => tt
           | cons co cos => GHC.Prim.seq (seqCo co) (seqCos cos)
           end.

Definition seqProv : UnivCoProvenance -> unit :=
  fun arg_0__ =>
    match arg_0__ with
    | UnsafeCoerceProv => tt
    | PhantomProv co => seqCo co
    | ProofIrrelProv co => seqCo co
    | PluginProv _ => tt
    | HoleProv _ => tt
    end.

Definition seqType : Type_ -> unit :=
  fix seqType arg_0__
        := match arg_0__ with
           | LitTy n => GHC.Prim.seq n tt
           | TyVarTy tv => GHC.Prim.seq tv tt
           | AppTy t1 t2 => GHC.Prim.seq (seqType t1) (seqType t2)
           | TyConApp tc tys => GHC.Prim.seq tc (seqTypes tys)
           | ForAllTy bndr ty => GHC.Prim.seq (seqType (binderType bndr)) (seqType ty)
           | CastTy ty co => GHC.Prim.seq (seqType ty) (seqCo co)
           | CoercionTy co => seqCo co
           end.

Definition seqTypes : list Type_ -> unit :=
  fix seqTypes arg_0__
        := match arg_0__ with
           | nil => tt
           | cons ty tys => GHC.Prim.seq (seqType ty) (seqTypes tys)
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

Definition trans_co_list : Coercion -> list Coercion -> list Coercion :=
  fix trans_co_list arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | TransCo co1 co2, cos => trans_co_list co1 (trans_co_list co2 cos)
           | co, cos => cons co cos
           end.

Definition tyConRolesRepresentational : Core.TyCon -> list Core.Role :=
  fun tc =>
    Coq.Init.Datatypes.app (TyCon.tyConRoles tc) (GHC.List.repeat Core.Nominal).

Definition tyConRolesX : Core.Role -> Core.TyCon -> list Core.Role :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Core.Representational, tc => tyConRolesRepresentational tc
    | role, _ => GHC.List.repeat role
    end.

Definition nthRole : Core.Role -> Core.TyCon -> GHC.Num.Int -> Core.Role :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Core.Nominal, _, _ => Core.Nominal
    | Core.Phantom, _, _ => Core.Phantom
    | Core.Representational, tc, n =>
        ListSetOps.getNth (tyConRolesRepresentational tc) n
    end.

Axiom ty_co_subst : forall {A : Type}, A.

Definition liftCoSubst : Core.Role -> LiftingContext -> Type_ -> Coercion :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | r, (LC subst env as lc), ty =>
        if VarEnv.isEmptyVarEnv env : bool then Refl r (substTy subst ty) else
        ty_co_subst lc r ty
    end.

Definition substTy `{(GHC.Stack.CallStack)} : TCvSubst -> Type_ -> Type_ :=
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
                        | ForAllTy (Anon arg) res => ForAllTy (Anon (go arg)) (go res)
                        | ForAllTy (Named tv vis) ty =>
                            let 'pair subst' tv' := substTyVarBndrUnchecked subst tv in
                            ForAllTy (Named tv' vis) (subst_ty subst' ty)
                        | LitTy n => LitTy n
                        | CastTy ty co => CastTy (go ty) (subst_co subst co)
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
        let no_kind_change := VarSet.isEmptyVarSet (tyCoVarsOfType old_ki) in
        let new_var :=
          if no_kind_change : bool then VarEnv.uniqAway in_scope old_var else
          VarEnv.uniqAway in_scope (setTyVarKind old_var (subst_fn subst old_ki)) in
        let no_change := andb no_kind_change (new_var GHC.Base.== old_var) in
        let _no_capture :=
          negb (VarSet.elemVarSet new_var (tyCoVarsOfTypes (VarEnv.varEnvElts tenv))) in
        let new_env :=
          if no_change : bool then VarEnv.delVarEnv tenv old_var else
          VarEnv.extendVarEnv tenv old_var (TyVarTy new_var) in
        if andb Util.debugIsOn (negb (_no_capture)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/types/TyCoRep.hs") #2292 ((pprTvBndr old_var Outputable.$$
                                                                                  pprTvBndr new_var) Outputable.$$
                                                                                 Panic.noString subst))
        else if andb Util.debugIsOn (negb (isTyVar old_var)) : bool
             then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
                   #2293)
             else pair (TCvSubst (VarEnv.extendInScopeSet in_scope new_var) new_env cenv)
                       new_var
    end.

Definition pprTvBndr : TyVar -> Outputable.SDoc :=
  fun tv =>
    let kind := tyVarKind tv in
    if isLiftedTypeKind kind : bool then ppr_tvar tv else
    Outputable.parens (GHC.Base.mappend (GHC.Base.mappend (ppr_tvar tv)
                                                          Outputable.dcolon) (pprKind kind)).

Definition isLiftedTypeKind : Kind -> bool :=
  fix isLiftedTypeKind arg_0__
        := let 'ki := arg_0__ in
           match coreView ki with
           | Some ki' => isLiftedTypeKind ki'
           | _ =>
               match arg_0__ with
               | TyConApp tc (cons (TyConApp ptr_rep nil) nil) =>
                   andb (Unique.hasKey tc PrelNames.tYPETyConKey) (Unique.hasKey ptr_rep
                                                                                 PrelNames.ptrRepLiftedDataConKey)
               | _ => false
               end
           end.

Definition coreView : Type_ -> option Type_ :=
  fun arg_0__ =>
    match arg_0__ with
    | TyConApp tc tys =>
        match TyCon.expandSynTyCon_maybe tc tys with
        | Some (pair (pair tenv rhs) tys') =>
            Some (mkAppTys (substTy (mkTvSubstPrs tenv) rhs) tys')
        | _ => None
        end
    | _ => None
    end.

Definition pprKind : Kind -> Outputable.SDoc :=
  pprType.

Definition pprType : Type_ -> Outputable.SDoc :=
  fun ty => eliminateRuntimeRep (ppr_type TopPrec) ty.

Definition ppr_type : TyPrec -> Type_ -> Outputable.SDoc :=
  fix ppr_type arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | _, TyVarTy tv => ppr_tvar tv
           | p, TyConApp tc tys => pprTyTcApp p tc tys
           | p, LitTy l => ppr_tylit p l
           | p, (ForAllTy _ _ as ty) => ppr_forall_type p ty
           | p, AppTy t1 t2 =>
               let mk_app_tys :=
                 fun arg_6__ arg_7__ =>
                   match arg_6__, arg_7__ with
                   | TyConApp tc tys1, tys2 => TyConApp tc (Coq.Init.Datatypes.app tys1 tys2)
                   | ty1, tys2 => Data.Foldable.foldl AppTy ty1 tys2
                   end in
               let fix split_app_tys arg_11__ arg_12__
                         := match arg_11__, arg_12__ with
                            | AppTy ty1 ty2, args => split_app_tys ty1 (cons ty2 args)
                            | head, args => pair head args
                            end in
               let ppr_app_ty :=
                 maybeParen p TyConPrec (GHC.Base.mappend (ppr_type FunPrec t1) (ppr_type
                                                           TyConPrec t2)) in
               if_print_coercions ppr_app_ty (match split_app_tys t1 (cons t2 nil) with
                                              | pair (CastTy head _) args => ppr_type p (mk_app_tys head args)
                                              | _ => ppr_app_ty
                                              end)
           | p, CastTy ty co =>
               if_print_coercions (Outputable.parens (GHC.Base.mappend (GHC.Base.mappend
                                                                        (ppr_type TopPrec ty) (id (GHC.Base.hs_string__
                                                                                                   "|>")))
                                                                       (Panic.noString co))) (ppr_type p ty)
           | _, CoercionTy co =>
               if_print_coercions (Outputable.parens (Panic.noString co)) (id
                                                                           (GHC.Base.hs_string__ "<>"))
           end.

Definition pprTyTcApp : TyPrec -> Core.TyCon -> list Type_ -> Outputable.SDoc :=
  fun p tc tys =>
    let ppr_deflt := pprTcAppTy p ppr_type tc tys in
    let j_1__ :=
      if Unique.hasKey tc PrelNames.tYPETyConKey : bool
      then match tys with
           | cons (TyConApp ptr_rep nil) nil =>
               if Unique.hasKey ptr_rep PrelNames.ptrRepUnliftedDataConKey : bool
               then Outputable.char (GHC.Char.hs_char__ "#") else
               ppr_deflt
           | _ => ppr_deflt
           end else
      ppr_deflt in
    let j_2__ :=
      if Unique.hasKey tc PrelNames.tYPETyConKey : bool
      then match tys with
           | cons (TyConApp ptr_rep nil) nil =>
               if Unique.hasKey ptr_rep PrelNames.ptrRepLiftedDataConKey : bool
               then Outputable.unicodeSyntax (Outputable.char (GHC.Char.hs_char__ "★"))
                    (Outputable.char (GHC.Char.hs_char__ "*")) else
               j_1__
           | _ => j_1__
           end else
      j_1__ in
    let j_3__ :=
      if andb (negb StaticFlags.opt_PprStyle_Debug) (Unique.hasKey tc
                                                                   PrelNames.errorMessageTypeErrorFamKey) : bool
      then id (GHC.Base.hs_string__ "(TypeError ...)") else
      j_2__ in
    let j_5__ :=
      if Unique.hasKey tc PrelNames.consDataConKey : bool
      then match tys with
           | cons _kind (cons ty1 (cons ty2 nil)) =>
               Outputable.sdocWithDynFlags (fun dflags =>
                                              if DynFlags.gopt DynFlags.Opt_PrintExplicitKinds dflags : bool
                                              then ppr_deflt
                                              else pprTyList p ty1 ty2)
           | _ => j_3__
           end else
      j_3__ in
    if Unique.hasKey tc PrelNames.ipClassKey : bool
    then match tys with
         | cons (LitTy (StrTyLit n)) (cons ty nil) =>
             maybeParen p FunPrec (((Outputable.char (GHC.Char.hs_char__ "?") Outputable.<>
                                     Outputable.ftext n) Outputable.<>
                                    id (GHC.Base.hs_string__ "::")) Outputable.<>
                                   ppr_type TopPrec ty)
         | _ => j_5__
         end else
    j_5__.

Definition pprTcAppTy
   : TyPrec ->
     (TyPrec -> Type_ -> Outputable.SDoc) ->
     Core.TyCon -> list Type_ -> Outputable.SDoc :=
  fun p pp tc tys =>
    Outputable.getPprStyle (fun style => pprTcApp style GHC.Base.id p pp tc tys).

Definition pprTcApp {a}
   : Outputable.PprStyle ->
     (a -> Type_) ->
     TyPrec ->
     (TyPrec -> a -> Outputable.SDoc) -> Core.TyCon -> list a -> Outputable.SDoc :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ arg_5__ =>
    let j_18__ :=
      match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
      | style, to_type, p, pp, tc, tys =>
          let j_7__ :=
            Outputable.sdocWithDynFlags (fun dflags =>
                                           pprTcApp_help to_type p pp tc tys dflags style) in
          let j_11__ :=
            if negb (Outputable.debugStyle style) : bool
            then match TyCon.isPromotedDataCon_maybe tc with
                 | Some dc =>
                     let dc_tc := DataCon.dataConTyCon dc in
                     match TyCon.tyConTuple_maybe dc_tc with
                     | Some tup_sort =>
                         let arity := TyCon.tyConArity dc_tc in
                         let ty_args := GHC.List.drop arity tys in
                         if Util.lengthIs ty_args arity : bool
                         then TyCon.pprPromotionQuote tc Outputable.<>
                              (BasicTypes.tupleParens tup_sort (Outputable.pprWithCommas (pp TopPrec)
                                                                                         ty_args)) else
                         j_7__
                     | _ => j_7__
                     end
                 | _ => j_7__
                 end else
            j_7__ in
          if negb (Outputable.debugStyle style) : bool
          then match TyCon.tyConTuple_maybe tc with
               | Some sort =>
                   let arity := TyCon.tyConArity tc in
                   if arity GHC.Base.== Data.Foldable.length tys : bool
                   then let num_to_drop :=
                          match sort with
                          | BasicTypes.UnboxedTuple => GHC.Real.div arity #2
                          | _ => #0
                          end in
                        pprTupleApp p pp tc sort (GHC.List.drop num_to_drop tys) else
                   j_11__
               | _ => j_11__
               end else
          j_11__
      end in
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__, arg_5__ with
    | _, _, _, pp, tc, cons ty nil =>
        if Unique.hasKey tc PrelNames.listTyConKey : bool
        then TyCon.pprPromotionQuote tc Outputable.<>
             Outputable.brackets (pp TopPrec ty) else
        if Unique.hasKey tc PrelNames.parrTyConKey : bool
        then TyCon.pprPromotionQuote tc Outputable.<>
             Outputable.paBrackets (pp TopPrec ty) else
        j_18__
    | _, _, _, _, _, _ => j_18__
    end.

Definition pprTcApp_help {a}
   : (a -> Type_) ->
     TyPrec ->
     (TyPrec -> a -> Outputable.SDoc) ->
     Core.TyCon ->
     list a -> DynFlags.DynFlags -> Outputable.PprStyle -> Outputable.SDoc :=
  fun to_type p pp tc tys dflags style =>
    let print_eqs :=
      orb (DynFlags.gopt DynFlags.Opt_PrintEqualityRelations dflags) (orb
           (Outputable.dumpStyle style) (Outputable.debugStyle style)) in
    let print_kinds := DynFlags.gopt DynFlags.Opt_PrintExplicitKinds dflags in
    let hetero_eq_tc :=
      orb (Unique.hasKey tc PrelNames.eqPrimTyConKey) (orb (Unique.hasKey tc
                                                                          PrelNames.eqReprPrimTyConKey) (Unique.hasKey
                                                            tc PrelNames.heqTyConKey)) in
    let homo_eq_tc := Unique.hasKey tc PrelNames.eqTyConKey in
    let mb_saturated_equality :=
      let j_4__ :=
        if homo_eq_tc : bool
        then match tys with
             | cons k (cons t1 (cons t2 nil)) => Some (pair (pair (pair k k) t1) t2)
             | _ => None
             end else
        None in
      if hetero_eq_tc : bool
      then match tys with
           | cons k1 (cons k2 (cons t1 (cons t2 nil))) =>
               Some (pair (pair (pair k1 k2) t1) t2)
           | _ => j_4__
           end else
      j_4__ in
    let tys_wo_kinds := suppressInvisibles to_type dflags tc tys in
    let pp_tc := Panic.noString tc in
    let print_equality :=
      fun arg_8__ =>
        let 'pair (pair (pair ki1 ki2) ty1) ty2 := arg_8__ in
        let ppr_infix_eq :=
          fun eq_op =>
            Outputable.sep (cons (Outputable.parens (GHC.Base.mappend (GHC.Base.mappend (pp
                                                                                         TyOpPrec ty1)
                                                                                        Outputable.dcolon) (pp TyOpPrec
                                                                       ki1))) (cons eq_op (cons (Outputable.parens
                                                                                                 (GHC.Base.mappend
                                                                                                  (GHC.Base.mappend (pp
                                                                                                                     TyOpPrec
                                                                                                                     ty2)
                                                                                                                    Outputable.dcolon)
                                                                                                  (pp TyOpPrec ki2)))
                                                                                                nil))) in
        if print_eqs : bool then ppr_infix_eq pp_tc else
        if andb hetero_eq_tc (orb print_kinds (negb (eqType (to_type ki1) (to_type
                                                             ki2)))) : bool
        then ppr_infix_eq (if Unique.hasKey tc PrelNames.eqPrimTyConKey : bool
                           then id (GHC.Base.hs_string__ "~~")
                           else pp_tc) else
        if Unique.hasKey tc PrelNames.eqReprPrimTyConKey : bool
        then GHC.Base.mappend (id (GHC.Base.hs_string__ "Coercible")) (Outputable.sep
                               (cons (pp TyConPrec ty1) (cons (pp TyConPrec ty2) nil)))
        else Outputable.sep (cons (pp TyOpPrec ty1) (cons (id (GHC.Base.hs_string__
                                                               "~")) (cons (pp TyOpPrec ty2) nil))) in
    let tc_name := TyCon.tyConName tc in
    if negb (OccName.isSymOcc (Name.nameOccName tc_name)) : bool
    then pprPrefixApp p pp_tc (GHC.Base.map (pp TyConPrec) tys_wo_kinds) else
    match mb_saturated_equality with
    | Some args => print_equality args
    | _ =>
        match tys_wo_kinds with
        | cons ty1 (cons ty2 nil) => pprInfixApp p pp pp_tc ty1 ty2
        | _ =>
            if orb (Unique.hasKey tc_name PrelNames.starKindTyConKey) (orb (Unique.hasKey
                                                                            tc_name PrelNames.unicodeStarKindTyConKey)
                                                                           (Unique.hasKey tc_name
                                                                                          PrelNames.unliftedTypeKindTyConKey)) : bool
            then pp_tc else
            pprPrefixApp p (Outputable.parens (pp_tc)) (GHC.Base.map (pp TyConPrec)
                                                        tys_wo_kinds)
        end
    end.

Definition suppressInvisibles {a}
   : (a -> Type_) -> DynFlags.DynFlags -> Core.TyCon -> list a -> list a :=
  fun to_type dflags tc xs =>
    if DynFlags.gopt DynFlags.Opt_PrintExplicitKinds dflags : bool then xs else
    Data.Tuple.snd (partitionInvisibles tc to_type xs).

Definition partitionInvisibles {a}
   : Core.TyCon -> (a -> Type_) -> list a -> (list a * list a)%type :=
  fun tc get_ty =>
    let fix go arg_0__ arg_1__ arg_2__
              := let j_4__ :=
                   match arg_0__, arg_1__, arg_2__ with
                   | _, _, xs => pair nil xs
                   end in
                 match arg_0__, arg_1__, arg_2__ with
                 | _, _, nil => pair nil nil
                 | subst, ForAllTy bndr res_ki, cons x xs =>
                     let subst' := extendTvSubstBinder subst bndr (get_ty x) in
                     if isVisibleBinder bndr : bool
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
    go emptyTCvSubst (TyCon.tyConKind tc).

Definition isVisibleBinder : TyBinder -> bool :=
  negb GHC.Base.∘ isInvisibleBinder.

Definition isInvisibleBinder : TyBinder -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Named _ vis => vis GHC.Base./= Visible
    | Anon ty => isPredTy ty
    end.

Definition isPredTy : Type_ -> bool :=
  fix isPredTy ty
        := let go_k : Kind -> list KindOrType -> bool :=
             fun k args => Kind.isConstraintKind (piResultTys k args) in
           let go_tc : Core.TyCon -> list KindOrType -> bool :=
             fun tc args =>
               if orb (Unique.hasKey tc PrelNames.eqPrimTyConKey) (Unique.hasKey tc
                                                                                 PrelNames.eqReprPrimTyConKey) : bool
               then Data.Foldable.length args GHC.Base.== #4 else
               go_k (TyCon.tyConKind tc) args in
           let go : Type_ -> list KindOrType -> bool :=
             fix go arg_3__ arg_4__
                   := match arg_3__, arg_4__ with
                      | AppTy ty1 ty2, args => go ty1 (cons ty2 args)
                      | TyVarTy tv, args => go_k (tyVarKind tv) args
                      | TyConApp tc tys, args =>
                          if andb Util.debugIsOn (negb (Data.Foldable.null args)) : bool
                          then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
                                #1497)
                          else go_tc tc tys
                      | ForAllTy (Anon arg) res, nil =>
                          if isPredTy arg : bool then isPredTy res else
                          false
                      | _, _ =>
                          match arg_3__, arg_4__ with
                          | ForAllTy (Named _ _) ty, nil => go ty nil
                          | _, _ => false
                          end
                      end in
           go ty nil.

Definition piResultTys : Type_ -> list Type_ -> Type_ :=
  fix piResultTys arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | ty, nil => ty
           | ty, (cons arg args as orig_args) =>
               let go : TvSubstEnv -> Type_ -> list Type_ -> Type_ :=
                 fix go arg_2__ arg_3__ arg_4__
                       := match arg_2__, arg_3__, arg_4__ with
                          | tv_env, ty, nil =>
                              let in_scope := VarEnv.mkInScopeSet (tyCoVarsOfTypes (cons ty orig_args)) in
                              substTy (mkTvSubst in_scope tv_env) ty
                          | tv_env, ty, (cons arg args as all_args) =>
                              match coreView ty with
                              | Some ty' => go tv_env ty' all_args
                              | _ =>
                                  match ty with
                                  | ForAllTy bndr res =>
                                      match bndr with
                                      | Anon _ => go tv_env res args
                                      | Named tv _ => go (VarEnv.extendVarEnv tv_env tv arg) res args
                                      end
                                  | _ =>
                                      let j_7__ :=
                                        Panic.panicStr (GHC.Base.hs_string__ "piResultTys2") ((Panic.noString ty
                                                                                               Outputable.$$
                                                                                               Panic.noString orig_args)
                                                                                              Outputable.$$
                                                                                              Panic.noString
                                                                                              all_args) in
                                      match ty with
                                      | TyVarTy tv =>
                                          match VarEnv.lookupVarEnv tv_env tv with
                                          | Some ty' => piResultTys ty' all_args
                                          | _ => j_7__
                                          end
                                      | _ => j_7__
                                      end
                                  end
                              end
                          end in
               match coreView ty with
               | Some ty' => piResultTys ty' orig_args
               | _ =>
                   match ty with
                   | ForAllTy bndr res =>
                       match bndr with
                       | Anon _ => piResultTys res args
                       | Named tv _ => go (VarEnv.extendVarEnv emptyTvSubstEnv tv arg) res args
                       end
                   | _ =>
                       Panic.panicStr (GHC.Base.hs_string__ "piResultTys1") (Panic.noString ty
                                                                             Outputable.$$
                                                                             Panic.noString orig_args)
                   end
               end
           end.

Definition eqType : Type_ -> Type_ -> bool :=
  fun t1 t2 => Util.isEqual (cmpType t1 t2).

Definition cmpType : Type_ -> Type_ -> comparison :=
  fun t1 t2 =>
    let rn_env :=
      VarEnv.mkRnEnv2 (VarEnv.mkInScopeSet (tyCoVarsOfTypes (cons t1 (cons t2
                                                                           nil)))) in
    cmpTypeX rn_env t1 t2.

Definition cmpTypeX : VarEnv.RnEnv2 -> Type_ -> Type_ -> comparison :=
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
    let go : VarEnv.RnEnv2 -> Type_ -> Type_ -> TypeOrdering :=
      fix go arg_8__ arg_9__ arg_10__
            := match arg_8__, arg_9__, arg_10__ with
               | env, t1, t2 =>
                   match coreViewOneStarKind t1 with
                   | Some t1' => go env t1' t2
                   | _ =>
                       match coreViewOneStarKind t2 with
                       | Some t2' => go env t1 t2'
                       | _ =>
                           let j_27__ :=
                             match arg_8__, arg_9__, arg_10__ with
                             | env, ForAllTy (Anon s1) t1, ForAllTy (Anon s2) t2 =>
                                 thenCmpTy (go env s1 s2) (go env t1 t2)
                             | env, TyConApp tc1 tys1, TyConApp tc2 tys2 =>
                                 thenCmpTy (liftOrdering (cmpTc tc1 tc2)) (gos env tys1 tys2)
                             | _, LitTy l1, LitTy l2 => liftOrdering (GHC.Base.compare l1 l2)
                             | env, CastTy t1 _, t2 => hasCast (go env t1 t2)
                             | env, t1, CastTy t2 _ => hasCast (go env t1 t2)
                             | _, CoercionTy _, CoercionTy _ => TEQ
                             | _, ty1, ty2 =>
                                 let get_rank : Type_ -> GHC.Num.Int :=
                                   fun arg_16__ =>
                                     match arg_16__ with
                                     | CastTy _ _ =>
                                         Panic.panicStr (GHC.Base.hs_string__ "cmpTypeX.get_rank") (Panic.noString (cons
                                                                                                                    ty1
                                                                                                                    (cons
                                                                                                                     ty2
                                                                                                                     nil)))
                                     | TyVarTy _ => #0
                                     | CoercionTy _ => #1
                                     | AppTy _ _ => #3
                                     | LitTy _ => #4
                                     | TyConApp _ _ => #5
                                     | ForAllTy (Anon _) _ => #6
                                     | ForAllTy (Named _ _) _ => #7
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
                               liftOrdering (nonDetCmpVar (VarEnv.rnOccL env tv1) (VarEnv.rnOccR env tv2))
                           | env, ForAllTy (Named tv1 _) t1, ForAllTy (Named tv2 _) t2 =>
                               thenCmpTy (go env (tyVarKind tv1) (tyVarKind tv2)) (go (VarEnv.rnBndr2 env tv1
                                                                                       tv2) t1 t2)
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
    let gos : VarEnv.RnEnv2 -> list Type_ -> list Type_ -> TypeOrdering :=
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

Definition coreViewOneStarKind : Type_ -> option Type_ :=
  let fix go arg_0__ arg_1__
            := match arg_0__, arg_1__ with
               | _, t =>
                   match coreView t with
                   | Some t' => go (Some t') t'
                   | _ =>
                       let j_2__ := match arg_0__, arg_1__ with | res, _ => res end in
                       match arg_0__, arg_1__ with
                       | _, TyConApp tc nil =>
                           let t' := TysWiredIn.liftedTypeKind in
                           if Kind.isStarKindSynonymTyCon tc : bool then go (Some t') t' else
                           j_2__
                       | _, _ => j_2__
                       end
                   end
               end in
  go None.

Definition typeKind : Type_ -> Kind :=
  fix typeKind arg_0__
        := match arg_0__ with
           | TyConApp tc tys => piResultTys (TyCon.tyConKind tc) tys
           | AppTy fun_ arg => piResultTy (typeKind fun_) arg
           | LitTy l => typeLiteralKind l
           | ForAllTy (Anon _) _ => TysWiredIn.liftedTypeKind
           | ForAllTy _ ty => typeKind ty
           | TyVarTy tyvar => tyVarKind tyvar
           | CastTy _ty co => Pair.pSnd (coercionKind co)
           | CoercionTy co => coercionType co
           end.

Definition coercionType : Coercion -> Type_ :=
  fun co =>
    let 'pair (Pair.Mk_Pair ty1 ty2) r := coercionKindRole co in
    mkCoercionType r ty1 ty2.

Definition mkCoercionType : Core.Role -> Type_ -> Type_ -> Type_ :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.Nominal => mkPrimEqPred
    | Core.Representational => mkReprPrimEqPred
    | Core.Phantom =>
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

Definition piResultTy : Type_ -> Type_ -> Type_ :=
  fix piResultTy ty arg
        := match coreView ty with
           | Some ty' => piResultTy ty' arg
           | _ =>
               match ty with
               | ForAllTy bndr res =>
                   match bndr with
                   | Anon _ => res
                   | Named tv _ =>
                       let empty_subst :=
                         mkEmptyTCvSubst (VarEnv.mkInScopeSet (tyCoVarsOfTypes (cons arg (cons res
                                                                                               nil)))) in
                       substTy (extendTvSubst empty_subst tv arg) res
                   end
               | _ =>
                   Panic.panicStr (GHC.Base.hs_string__ "piResultTy") (Panic.noString ty
                                                                       Outputable.$$
                                                                       Panic.noString arg)
               end
           end.

Definition pprTyList : TyPrec -> Type_ -> Type_ -> Outputable.SDoc :=
  fun p ty1 ty2 =>
    let gather : Type_ -> (list Type_ * option Type_)%type :=
      fix gather arg_0__
            := let j_2__ := let 'ty := arg_0__ in pair nil (Some ty) in
               match arg_0__ with
               | TyConApp tc tys =>
                   let j_3__ :=
                     if Unique.hasKey tc PrelNames.nilDataConKey : bool then pair nil None else
                     j_2__ in
                   if Unique.hasKey tc PrelNames.consDataConKey : bool
                   then match tys with
                        | cons _kind (cons ty1 (cons ty2 nil)) =>
                            let 'pair args tl := gather ty2 in
                            pair (cons ty1 args) tl
                        | _ => j_3__
                        end else
                   j_3__
               | _ => j_2__
               end in
    match gather ty2 with
    | pair arg_tys None =>
        Outputable.char (GHC.Char.hs_char__ "'") Outputable.<>
        Outputable.brackets (Outputable.fsep (Outputable.punctuate Outputable.comma
                                              (GHC.Base.map (ppr_type TopPrec) (cons ty1 arg_tys))))
    | pair arg_tys (Some tl) =>
        maybeParen p FunPrec (Outputable.hang (ppr_type FunPrec ty1) #2 (Outputable.fsep
                                               (Coq.Lists.List.flat_map (fun ty =>
                                                                           cons (GHC.Base.mappend Outputable.colon
                                                                                                  (ppr_type FunPrec ty))
                                                                                nil) (Coq.Init.Datatypes.app arg_tys
                                                                                                             (cons tl
                                                                                                                   nil)))))
    end.

Definition ppr_forall_type : TyPrec -> Type_ -> Outputable.SDoc :=
  fun p ty =>
    maybeParen p FunPrec (Outputable.sdocWithDynFlags (fun dflags =>
                                                         ppr_sigma_type dflags true ty)).

Definition ppr_sigma_type
   : DynFlags.DynFlags -> bool -> Type_ -> Outputable.SDoc :=
  fun arg_0__ arg_1__ arg_2__ =>
    let j_17__ :=
      match arg_0__, arg_1__, arg_2__ with
      | _, _, ty =>
          let fix split2 arg_3__ arg_4__
                    := let j_6__ :=
                         match arg_3__, arg_4__ with
                         | ps, ty => pair (GHC.List.reverse ps) ty
                         end in
                       match arg_3__, arg_4__ with
                       | ps, ForAllTy (Anon ty1) ty2 =>
                           if isPredTy ty1 : bool then split2 (cons ty1 ps) ty2 else
                           j_6__
                       | _, _ => j_6__
                       end in
          let fix split1 arg_9__ arg_10__
                    := match arg_9__, arg_10__ with
                       | bndrs, ForAllTy (Named _ _ as bndr) ty => split1 (cons bndr bndrs) ty
                       | bndrs, ty => pair (GHC.List.reverse bndrs) ty
                       end in
          let 'pair bndrs rho := split1 nil ty in
          let 'pair ctxt tau := split2 nil rho in
          Outputable.sep (cons (pprForAll bndrs) (cons (pprThetaArrowTy ctxt) (cons
                                                        (pprArrowChain TopPrec (ppr_fun_tail tau)) nil)))
      end in
    match arg_0__, arg_1__, arg_2__ with
    | dflags, false, orig_ty =>
        let fix split arg_18__ arg_19__
                  := let j_21__ :=
                       match arg_18__, arg_19__ with
                       | acc, ty => pair (GHC.List.reverse acc) ty
                       end in
                     match arg_18__, arg_19__ with
                     | acc, ForAllTy bndr ty =>
                         if isInvisibleBinder bndr : bool then split (cons bndr acc) ty else
                         j_21__
                     | _, _ => j_21__
                     end in
        let 'pair invis_bndrs tau := split nil orig_ty in
        let 'pair named ctxt := Data.OldList.partition isNamedBinder invis_bndrs in
        if andb (negb (DynFlags.gopt DynFlags.Opt_PrintExplicitForalls dflags))
                (Data.Foldable.all (VarSet.isEmptyVarSet GHC.Base.∘
                                    (tyCoVarsOfType GHC.Base.∘ binderType)) named) : bool
        then Outputable.sep (cons (pprThetaArrowTy (GHC.Base.map binderType ctxt)) (cons
                                   (pprArrowChain TopPrec (ppr_fun_tail tau)) nil)) else
        j_17__
    | _, _, _ => j_17__
    end.

Definition pprForAll : list TyBinder -> Outputable.SDoc :=
  fix pprForAll arg_0__
        := match arg_0__ with
           | nil => Outputable.empty
           | (cons (Named _ vis) _ as bndrs) =>
               let add_separator :=
                 fun stuff =>
                   match vis with
                   | Visible => GHC.Base.mappend stuff Outputable.arrow
                   | _inv => stuff Outputable.<> Outputable.dot
                   end in
               let 'pair bndrs' doc := ppr_tv_bndrs bndrs vis in
               GHC.Base.mappend (add_separator (GHC.Base.mappend Outputable.forAllLit doc))
                                (pprForAll bndrs')
           | bndrs =>
               Panic.panicStr (GHC.Base.hs_string__ "pprForAll: anonymous binder")
               (Panic.noString bndrs)
           end.

Definition ppr_tv_bndrs
   : list TyBinder -> VisibilityFlag -> (list TyBinder * Outputable.SDoc)%type :=
  fix ppr_tv_bndrs arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | (cons (Named tv vis) bndrs as all_bndrs), vis1 =>
               if sameVis vis vis1 : bool
               then let pp_tv :=
                      Outputable.sdocWithDynFlags (fun dflags =>
                                                     if andb (Invisible GHC.Base.== vis) (DynFlags.gopt
                                                              DynFlags.Opt_PrintExplicitForalls dflags) : bool
                                                     then Outputable.braces (pprTvBndrNoParens tv)
                                                     else pprTvBndr tv) in
                    let 'pair bndrs' doc := ppr_tv_bndrs bndrs vis1 in
                    pair bndrs' (GHC.Base.mappend pp_tv doc) else
               pair all_bndrs Outputable.empty
           | _, _ =>
               match arg_0__, arg_1__ with
               | nil, _ => pair nil Outputable.empty
               | bndrs, _ =>
                   Panic.panicStr (GHC.Base.hs_string__ "ppr_tv_bndrs: anonymous binder")
                   (Panic.noString bndrs)
               end
           end.

Definition pprTvBndrNoParens : TyVar -> Outputable.SDoc :=
  fun tv =>
    let kind := tyVarKind tv in
    if isLiftedTypeKind kind : bool then ppr_tvar tv else
    GHC.Base.mappend (GHC.Base.mappend (ppr_tvar tv) Outputable.dcolon) (pprKind
                      kind).

Definition pprThetaArrowTy : ThetaType -> Outputable.SDoc :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => Outputable.empty
    | cons pred nil => GHC.Base.mappend (ppr_type TyOpPrec pred) Outputable.darrow
    | preds =>
        GHC.Base.mappend (Outputable.parens (Outputable.fsep (Outputable.punctuate
                                                              Outputable.comma (GHC.Base.map (ppr_type TopPrec)
                                                                                preds)))) Outputable.darrow
    end.

Definition ppr_fun_tail : Type_ -> list Outputable.SDoc :=
  fix ppr_fun_tail arg_0__
        := let j_2__ :=
             let 'other_ty := arg_0__ in
             cons (ppr_type TopPrec other_ty) nil in
           match arg_0__ with
           | ForAllTy (Anon ty1) ty2 =>
               if negb (isPredTy ty1) : bool
               then cons (ppr_type FunPrec ty1) (ppr_fun_tail ty2) else
               j_2__
           | _ => j_2__
           end.

Definition substTyUnchecked : TCvSubst -> Type_ -> Type_ :=
  fun subst ty => if isEmptyTCvSubst subst : bool then ty else subst_ty subst ty.

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
                      end in
           let go_prov :=
             fun arg_24__ =>
               match arg_24__ with
               | UnsafeCoerceProv => UnsafeCoerceProv
               | PhantomProv kco => PhantomProv (go kco)
               | ProofIrrelProv kco => ProofIrrelProv (go kco)
               | (PluginProv _ as p) => p
               | (HoleProv _ as p) => p
               end in
           go co.

Definition mkUnivCo
   : UnivCoProvenance -> Core.Role -> Type_ -> Type_ -> Coercion :=
  fun prov role ty1 ty2 =>
    if eqType ty1 ty2 : bool then Refl role ty1 else
    UnivCo prov role ty1 ty2.

Definition mkNthCo : GHC.Num.Int -> Coercion -> Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | num_2__, Refl _ ty =>
        let j_10__ :=
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
              then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
                    #871)
              else mkReflCo r' (tyConAppArgN n ty)
          | n, TyConAppCo _ _ cos => ListSetOps.getNth cos n
          | n, co => NthCo n co
          end in
        if num_2__ GHC.Base.== #0 : bool
        then match splitForAllTy_maybe ty with
             | Some (pair tv _) => Refl Core.Nominal (tyVarKind tv)
             | _ => j_10__
             end else
        j_10__
    end.

Definition splitForAllTy_maybe : Type_ -> option (TyVar * Type_)%type :=
  fun ty =>
    let fix splitFAT_m arg_0__
              := let 'ty := arg_0__ in
                 match coreView ty with
                 | Some ty' => splitFAT_m ty'
                 | _ =>
                     match arg_0__ with
                     | ForAllTy (Named tv _) ty => Some (pair tv ty)
                     | _ => None
                     end
                 end in
    splitFAT_m ty.

Definition splitTyConApp_maybe
   : Type_ -> option (Core.TyCon * list Type_)%type :=
  fix splitTyConApp_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => splitTyConApp_maybe ty'
           | _ => let 'ty := arg_0__ in repSplitTyConApp_maybe ty
           end.

Definition tyConAppArgN : GHC.Num.Int -> Type_ -> Type_ :=
  fun n ty =>
    match tyConAppArgs_maybe ty with
    | Some tys =>
        if andb Util.debugIsOn (negb (n GHC.Base.< Data.Foldable.length tys)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/types/Type.hs") #975 (GHC.Base.mappend (Panic.noString n)
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
               | ForAllTy (Anon arg) res => Some (cons arg (cons res nil))
               | _ => None
               end
           end.

Definition tyConAppTyCon : Type_ -> Core.TyCon :=
  fun ty =>
    Maybes.orElse (tyConAppTyCon_maybe ty) (Panic.panicStr (GHC.Base.hs_string__
                                                            "tyConAppTyCon") (Panic.noString ty)).

Definition tyConAppTyCon_maybe : Type_ -> option Core.TyCon :=
  fix tyConAppTyCon_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => tyConAppTyCon_maybe ty'
           | _ =>
               match arg_0__ with
               | TyConApp tc _ => Some tc
               | ForAllTy (Anon _) _ => Some TysPrim.funTyCon
               | _ => None
               end
           end.

Definition mkLRCo : LeftOrRight -> Coercion -> Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | lr, Refl eq ty => Refl eq (pickLR lr (splitAppTy ty))
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
    if andb Util.debugIsOn (negb (Data.Foldable.length tvs GHC.Base.==
                                  Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #1943)
    else substCoUnchecked (zipTvSubst tvs tys).

Definition substCoUnchecked : TCvSubst -> Coercion -> Coercion :=
  fun subst co => if isEmptyTCvSubst subst : bool then co else subst_co subst co.

Definition mkKindCo : Coercion -> Coercion :=
  fun arg_0__ =>
    match arg_0__ with
    | Refl _ ty => Refl Core.Nominal (typeKind ty)
    | UnivCo (PhantomProv h) _ _ _ => h
    | UnivCo (ProofIrrelProv h) _ _ _ => h
    | co =>
        let j_2__ := KindCo co in
        match coercionKind co with
        | Pair.Mk_Pair ty1 ty2 =>
            if eqType (typeKind ty1) (typeKind ty2) : bool
            then Refl Core.Nominal (typeKind ty1) else
            j_2__
        | _ => j_2__
        end
    end.

Definition mkSubCo : Coercion -> Coercion :=
  fun arg_0__ =>
    match arg_0__ with
    | Refl Core.Nominal ty => Refl Core.Representational ty
    | TyConAppCo Core.Nominal tc cos =>
        TyConAppCo Core.Representational tc (applyRoles tc cos)
    | co =>
        if andb Util.debugIsOn (negb (coercionRole co GHC.Base.== Core.Nominal)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/types/Coercion.hs") #942 (GHC.Base.mappend (Panic.noString co)
                                                                                                  (Panic.noString
                                                                                                   (coercionRole co))))
        else SubCo co
    end.

Definition applyRoles : Core.TyCon -> list Coercion -> list Coercion :=
  fun tc cos =>
    GHC.List.zipWith (fun r => downgradeRole r Core.Nominal)
    (tyConRolesRepresentational tc) cos.

Definition downgradeRole : Core.Role -> Core.Role -> Coercion -> Coercion :=
  fun r1 r2 co =>
    match downgradeRole_maybe r1 r2 co with
    | Some co' => co'
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "downgradeRole") (Panic.noString co)
    end.

Definition downgradeRole_maybe
   : Core.Role -> Core.Role -> Coercion -> option Coercion :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Core.Representational, Core.Nominal, co => Some (mkSubCo co)
    | Core.Nominal, Core.Representational, _ => None
    | Core.Phantom, Core.Phantom, co => Some co
    | Core.Phantom, _, co => Some (toPhantomCo co)
    | _, Core.Phantom, _ => None
    | _, _, co => Some co
    end.

Definition toPhantomCo : Coercion -> Coercion :=
  fun co =>
    let 'Pair.Mk_Pair ty1 ty2 := coercionKind co in
    mkPhantomCo (mkKindCo co) ty1 ty2.

Definition mkPhantomCo : Coercion -> Type_ -> Type_ -> Coercion :=
  fun h t1 t2 => mkUnivCo (PhantomProv h) Core.Phantom t1 t2.

Definition mkAppCo : Coercion -> Coercion -> Coercion :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Refl r ty1, arg =>
        let j_10__ :=
          match arg_0__, arg_1__ with
          | TyConAppCo r tc args, arg =>
              match r with
              | Core.Nominal =>
                  TyConAppCo Core.Nominal tc (Coq.Init.Datatypes.app args (cons arg nil))
              | Core.Representational =>
                  let new_role :=
                    (tyConRolesRepresentational tc) GHC.List.!! (Data.Foldable.length args) in
                  let arg' := downgradeRole new_role Core.Nominal arg in
                  TyConAppCo Core.Representational tc (Coq.Init.Datatypes.app args (cons arg'
                                                                                         nil))
              | Core.Phantom =>
                  TyConAppCo Core.Phantom tc (Coq.Init.Datatypes.app args (cons (toPhantomCo arg)
                                                                                nil))
              end
          | co, arg => AppCo co arg
          end in
        let fix zip_roles arg_11__ arg_12__
                  := match arg_11__, arg_12__ with
                     | cons r1 _, nil => cons (downgradeRole r1 Core.Nominal arg) nil
                     | cons r1 rs, cons ty1 tys => cons (mkReflCo r1 ty1) (zip_roles rs tys)
                     | _, _ => Panic.panic (GHC.Base.hs_string__ "zip_roles")
                     end in
        match isReflCo_maybe arg with
        | Some (pair ty2 _) => Refl r (mkAppTy ty1 ty2)
        | _ =>
            match splitTyConApp_maybe ty1 with
            | Some (pair tc tys) => TyConAppCo r tc (zip_roles (tyConRolesX r tc) tys)
            | _ => j_10__
            end
        end
    end.

Definition mkTyConAppCo
   : Core.Role -> Core.TyCon -> list Coercion -> Coercion :=
  fun r tc cos =>
    match TyCon.expandSynTyCon_maybe tc cos with
    | Some (pair (pair tv_co_prs rhs_ty) leftover_cos) =>
        mkAppCos (liftCoSubst r (mkLiftingContext tv_co_prs) rhs_ty) leftover_cos
    | _ =>
        match Data.Traversable.traverse isReflCo_maybe cos with
        | Some tys_roles =>
            Refl r (mkTyConApp tc (GHC.Base.map Data.Tuple.fst tys_roles))
        | _ => TyConAppCo r tc cos
        end
    end.

Definition mkAppCos : Coercion -> list Coercion -> Coercion :=
  fun co1 cos => Data.Foldable.foldl mkAppCo co1 cos.

Definition substForAllCoBndrUnchecked
   : TCvSubst -> TyVar -> Coercion -> (TCvSubst * TyVar * Coercion)%type :=
  fun subst => substForAllCoBndrCallback false (substCoUnchecked subst) subst.

Definition liftCoSubstWith
   : Core.Role -> list TyCoVar -> list Coercion -> Type_ -> Coercion :=
  fun r tvs cos ty =>
    liftCoSubst r (mkLiftingContext (Util.zipEqual (GHC.Base.hs_string__
                                                    "liftCoSubstWith") tvs cos)) ty.

Definition mkFunCo : Core.Role -> Coercion -> Coercion -> Coercion :=
  fun r co1 co2 => mkTyConAppCo r TysPrim.funTyCon (cons co1 (cons co2 nil)).

Definition mkFunCos : Core.Role -> list Coercion -> Coercion -> Coercion :=
  fun r cos res_co => Data.Foldable.foldr (mkFunCo r) res_co cos.

Definition mkPiCo : Core.Role -> Var -> Coercion -> Coercion :=
  fun r v co =>
    if isTyVar v : bool then mkHomoForAllCos (cons v nil) co else
    mkFunCo r (mkReflCo r (varType v)) co.

Definition mkPiCos : Core.Role -> list Var -> Coercion -> Coercion :=
  fun r vs co => Data.Foldable.foldr (mkPiCo r) co vs.

Definition substTyWithBindersUnchecked
   : list TyBinder -> list Type_ -> Type_ -> Type_ :=
  fun bndrs tys =>
    if andb Util.debugIsOn (negb (Data.Foldable.length bndrs GHC.Base.==
                                  Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #1981)
    else substTyUnchecked (zipTyBinderSubst bndrs tys).

Definition substTyWithUnchecked : list TyVar -> list Type_ -> Type_ -> Type_ :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Data.Foldable.length tvs GHC.Base.==
                                  Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #1913)
    else substTyUnchecked (zipTvSubst tvs tys).

Definition cloneTyVarBndr
   : TCvSubst -> TyVar -> Unique.Unique -> (TCvSubst * TyVar)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | (TCvSubst in_scope tv_env cv_env as subst), tv, uniq =>
        let old_ki := tyVarKind tv in
        let no_kind_change := VarSet.isEmptyVarSet (tyCoVarsOfType old_ki) in
        let tv1 :=
          if no_kind_change : bool then tv else
          setTyVarKind tv (substTy subst old_ki) in
        let tv' := setVarUnique tv1 uniq in
        if andb Util.debugIsOn (negb (isTyVar tv)) : bool
        then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                         "ghc/compiler/types/TyCoRep.hs") #2352 (Panic.noString tv))
        else pair (TCvSubst (VarEnv.extendInScopeSet in_scope tv') (VarEnv.extendVarEnv
                                                                    tv_env tv (mkTyVarTy tv')) cv_env) tv'
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

Definition substTyWith `{(GHC.Stack.CallStack)}
   : list TyVar -> list Type_ -> Type_ -> Type_ :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Data.Foldable.length tvs GHC.Base.==
                                  Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #1903)
    else substTy (zipTvSubst tvs tys).

Definition applyTysX : list TyVar -> Type_ -> list Type_ -> Type_ :=
  fun tvs body_ty arg_tys =>
    let n_tvs := Data.Foldable.length tvs in
    let pp_stuff :=
      Outputable.vcat (cons (Panic.noString tvs) (cons (Panic.noString body_ty) (cons
                                                        (Panic.noString arg_tys) nil))) in
    if andb Util.debugIsOn (negb (Data.Foldable.length arg_tys GHC.Base.>=
                                  n_tvs)) : bool
    then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                     "ghc/compiler/types/Type.hs") #1375 (pp_stuff))
    else if andb Util.debugIsOn (negb (VarSet.subVarSet (tyCoVarsOfType body_ty)
                                                        (VarSet.mkVarSet tvs))) : bool
         then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                          "ghc/compiler/types/Type.hs") #1376 (pp_stuff))
         else mkAppTys (substTyWith tvs (GHC.List.take n_tvs arg_tys) body_ty)
              (GHC.List.drop n_tvs arg_tys).

Definition newTyConInstRhs : Core.TyCon -> list Type_ -> Type_ :=
  fun tycon tys =>
    let 'pair tvs rhs := TyCon.newTyConEtadRhs tycon in
    if andb Util.debugIsOn (negb (Util.leLength tvs tys)) : bool
    then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                     "ghc/compiler/types/Type.hs") #1025 ((Panic.noString tycon Outputable.$$
                                                                           Panic.noString tys) Outputable.$$
                                                                          Panic.noString tvs))
    else applyTysX tvs rhs tys.

Definition substTyWithBinders `{(GHC.Stack.CallStack)}
   : list TyBinder -> list Type_ -> Type_ -> Type_ :=
  fun bndrs tys =>
    if andb Util.debugIsOn (negb (Data.Foldable.length bndrs GHC.Base.==
                                  Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #1970)
    else substTy (zipTyBinderSubst bndrs tys).

Definition substTyWithCoVars : list CoVar -> list Coercion -> Type_ -> Type_ :=
  fun cvs cos => substTy (zipCvSubst cvs cos).

Definition mkAxInstRHS {br}
   : Core.CoAxiom br ->
     Core.BranchIndex -> list Type_ -> list Coercion -> Type_ :=
  fun ax index tys cos =>
    let branch := CoAxiom.coAxiomNthBranch ax index in
    let tvs := CoAxiom.coAxBranchTyVars branch in
    let 'pair tys1 tys2 := Util.splitAtList tvs tys in
    let cvs := CoAxiom.coAxBranchCoVars branch in
    let rhs' :=
      substTyWith tvs tys1 (substTyWithCoVars cvs cos (CoAxiom.coAxBranchRHS
                                               branch)) in
    if andb Util.debugIsOn (negb (Util.equalLength tvs tys1)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #781)
    else mkAppTys rhs' tys2.

Definition mkUnbranchedAxInstRHS
   : Core.CoAxiom Core.Unbranched -> list Type_ -> list Coercion -> Type_ :=
  fun ax => mkAxInstRHS ax #0.

Definition substTyWithInScope
   : VarEnv.InScopeSet -> list TyVar -> list Type_ -> Type_ -> Type_ :=
  fun in_scope tvs tys ty =>
    let tenv := zipTyEnv tvs tys in
    if andb Util.debugIsOn (negb (Data.Foldable.length tvs GHC.Base.==
                                  Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #1922)
    else substTy (mkTvSubst in_scope tenv) ty.

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

Definition isUnliftedTypeKind : Kind -> bool :=
  fix isUnliftedTypeKind arg_0__
        := let 'ki := arg_0__ in
           match coreView ki with
           | Some ki' => isUnliftedTypeKind ki'
           | _ =>
               let j_2__ :=
                 match arg_0__ with
                 | TyConApp tc (cons arg nil) =>
                     andb (Unique.hasKey tc PrelNames.tYPETyConKey) (VarSet.isEmptyVarSet
                           (tyCoVarsOfType arg))
                 | _ => false
                 end in
               match arg_0__ with
               | TyConApp tc (cons (TyConApp ptr_rep nil) nil) =>
                   if andb (Unique.hasKey tc PrelNames.tYPETyConKey) (Unique.hasKey ptr_rep
                                                                                    PrelNames.ptrRepLiftedDataConKey) : bool
                   then false else
                   j_2__
               | _ => j_2__
               end
           end.

Definition dropForAlls : Type_ -> Type_ :=
  fix dropForAlls ty
        := let fix go arg_0__
                     := match arg_0__ with
                        | ForAllTy (Named _ _) res => go res
                        | res => res
                        end in
           match coreView ty with
           | Some ty' => dropForAlls ty'
           | _ => go ty
           end.

Definition funArgTy : Type_ -> Type_ :=
  fix funArgTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => funArgTy ty'
           | _ =>
               match arg_0__ with
               | ForAllTy (Anon arg) _res => arg
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
               | ForAllTy (Anon _) res => res
               | ty => Panic.panicStr (GHC.Base.hs_string__ "funResultTy") (Panic.noString ty)
               end
           end.

Definition getCastedTyVar_maybe : Type_ -> option (TyVar * Coercion)%type :=
  fix getCastedTyVar_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => getCastedTyVar_maybe ty'
           | _ =>
               match arg_0__ with
               | CastTy (TyVarTy tv) co => Some (pair tv co)
               | TyVarTy tv => Some (pair tv (mkReflCo Core.Nominal (tyVarKind tv)))
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

Definition allDistinctTyVars : list KindOrType -> bool :=
  fun tkvs =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | _, nil => true
                 | so_far, cons ty tys =>
                     match getTyVar_maybe ty with
                     | None => false
                     | Some tv =>
                         if VarSet.elemVarSet tv so_far : bool then false else
                         go (VarSet.extendVarSet so_far tv) tys
                     end
                 end in
    go VarSet.emptyVarSet tkvs.

Definition isNumLitTy : Type_ -> option GHC.Num.Integer :=
  fix isNumLitTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty1 => isNumLitTy ty1
           | _ => match arg_0__ with | LitTy (NumTyLit n) => Some n | _ => None end
           end.

Definition isStrLitTy : Type_ -> option FastString.FastString :=
  fix isStrLitTy arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty1 => isStrLitTy ty1
           | _ => match arg_0__ with | LitTy (StrTyLit s) => Some s | _ => None end
           end.

Definition isUnliftedType : Type_ -> bool :=
  fix isUnliftedType arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => isUnliftedType ty'
           | _ =>
               match arg_0__ with
               | ForAllTy (Named _ _) ty => isUnliftedType ty
               | TyConApp tc _ => TyCon.isUnliftedTyCon tc
               | _ => false
               end
           end.

Definition isStrictType : Type_ -> bool :=
  isUnliftedType.

Definition kindPrimRep : Kind -> TyCon.PrimRep :=
  fix kindPrimRep arg_0__
        := let 'ki := arg_0__ in
           match coreViewOneStarKind ki with
           | Some ki' => kindPrimRep ki'
           | _ =>
               match arg_0__ with
               | TyConApp typ (cons runtime_rep nil) =>
                   let fix go arg_1__
                             := let 'rr := arg_1__ in
                                match coreView rr with
                                | Some rr' => go rr'
                                | _ =>
                                    let j_3__ :=
                                      let 'rr := arg_1__ in
                                      Panic.panicStr (GHC.Base.hs_string__ "kindPrimRep.go") (Panic.noString rr) in
                                    match arg_1__ with
                                    | TyConApp rr_dc args =>
                                        match TyCon.tyConRuntimeRepInfo rr_dc with
                                        | TyCon.RuntimeRep fun_ => fun_ args
                                        | _ => j_3__
                                        end
                                    | _ => j_3__
                                    end
                                end in
                   if andb Util.debugIsOn (negb (Unique.hasKey typ PrelNames.tYPETyConKey)) : bool
                   then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
                         #1840)
                   else go runtime_rep
               | ki =>
                   Panic.warnPprTrace (true) (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
                                      #1849 (GHC.Base.mappend (id (GHC.Base.hs_string__
                                                                   "kindPrimRep defaulting to PtrRep on"))
                                                              (Panic.noString ki)) TyCon.PtrRep
               end
           end.

Definition tyConPrimRep : Core.TyCon -> TyCon.PrimRep :=
  fun tc => let res_kind := TyCon.tyConResKind tc in kindPrimRep res_kind.

Definition splitAppCo_maybe : Coercion -> option (Coercion * Coercion)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AppCo co arg => Some (pair co arg)
    | TyConAppCo r tc args =>
        if orb (TyCon.mightBeUnsaturatedTyCon tc) (Util.lengthExceeds args
                                                                      (TyCon.tyConArity tc)) : bool
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
                             let n :=
                               if TyCon.mightBeUnsaturatedTyCon tc : bool then #0 else
                               TyCon.tyConArity tc in
                             let 'pair tc_args1 tc_args2 := GHC.List.splitAt n tc_args in
                             pair (TyConApp tc tc_args1) (Coq.Init.Datatypes.app tc_args2 args)
                         | _, ForAllTy (Anon ty1) ty2, args =>
                             if andb Util.debugIsOn (negb (Data.Foldable.null args)) : bool
                             then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
                                   #714)
                             else pair (TyConApp TysPrim.funTyCon nil) (cons ty1 (cons ty2 nil))
                         | orig_ty, _, args => pair orig_ty args
                         end
                     end
                 end in
    split ty ty nil.

Definition splitCastTy_maybe : Type_ -> option (Type_ * Coercion)%type :=
  fix splitCastTy_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => splitCastTy_maybe ty'
           | _ => match arg_0__ with | CastTy ty co => Some (pair ty co) | _ => None end
           end.

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
                         | _, ForAllTy (Named tv _) ty, tvs => split ty ty (cons tv tvs)
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
               | ForAllTy (Anon arg) res => pair arg res
               | other =>
                   Panic.panicStr (GHC.Base.hs_string__ "splitFunTy") (Panic.noString other)
               end
           end.

Definition splitFunTy_maybe : Type_ -> option (Type_ * Type_)%type :=
  fix splitFunTy_maybe arg_0__
        := let 'ty := arg_0__ in
           match coreView ty with
           | Some ty' => splitFunTy_maybe ty'
           | _ =>
               match arg_0__ with
               | ForAllTy (Anon arg) res => Some (pair arg res)
               | _ => None
               end
           end.

Definition isFunTy : Type_ -> bool :=
  fun ty => Data.Maybe.isJust (splitFunTy_maybe ty).

Definition splitFunTysN : GHC.Num.Int -> Type_ -> (list Type_ * Type_)%type :=
  fix splitFunTysN arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | num_2__, ty =>
               if num_2__ GHC.Base.== #0 : bool then pair nil ty else
               match arg_0__, arg_1__ with
               | n, ty =>
                   if andb Util.debugIsOn (negb (isFunTy ty)) : bool
                   then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                                    "ghc/compiler/types/Type.hs") #832 (GHC.Base.mappend (Outputable.int
                                                                                                          n)
                                                                                                         (Panic.noString
                                                                                                          ty)))
                   else let 'pair arg res := splitFunTy ty in
                        let 'pair args res := splitFunTysN (n GHC.Num.- #1) res in
                        pair (cons arg args) res
               end
           end.

Definition splitFunTys : Type_ -> (list Type_ * Type_)%type :=
  fun ty =>
    let fix split arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | args, orig_ty, ty =>
                     match coreView ty with
                     | Some ty' => split args orig_ty ty'
                     | _ =>
                         match arg_0__, arg_1__, arg_2__ with
                         | args, _, ForAllTy (Anon arg) res => split (cons arg args) res res
                         | args, orig_ty, _ => pair (GHC.List.reverse args) orig_ty
                         end
                     end
                 end in
    split nil ty ty.

Definition splitNamedPiTys : Type_ -> (list TyBinder * Type_)%type :=
  fun ty =>
    let fix split arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | orig_ty, ty, bs =>
                     match coreView ty with
                     | Some ty' => split orig_ty ty' bs
                     | _ =>
                         match arg_0__, arg_1__, arg_2__ with
                         | _, ForAllTy (Named _ _ as b) res, bs => split res res (cons b bs)
                         | orig_ty, _, bs => pair (GHC.List.reverse bs) orig_ty
                         end
                     end
                 end in
    split ty ty nil.

Definition splitPiTy_maybe : Type_ -> option (TyBinder * Type_)%type :=
  fun ty =>
    let fix go arg_0__
              := let 'ty := arg_0__ in
                 match coreView ty with
                 | Some ty' => go ty'
                 | _ =>
                     match arg_0__ with
                     | ForAllTy bndr ty => Some (pair bndr ty)
                     | _ => None
                     end
                 end in
    go ty.

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
                         | _, ForAllTy b res, bs => split res res (cons b bs)
                         | orig_ty, _, bs => pair (GHC.List.reverse bs) orig_ty
                         end
                     end
                 end in
    split ty ty nil.

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
        match stepper TyCon.initRecTc tc tys with
        | NS_Step rec_nts ty' ev => go rec_nts ev ty'
        | _ => None
        end
    | _ => None
    end.

Definition splitTyConAppCo_maybe
   : Coercion -> option (Core.TyCon * list Coercion)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Refl r ty =>
        let cont_1__ arg_2__ :=
          let 'pair tc tys := arg_2__ in
          let args := GHC.List.zipWith mkReflCo (tyConRolesX r tc) tys in
          GHC.Base.return_ (pair tc args) in
        splitTyConApp_maybe ty GHC.Base.>>= cont_1__
    | TyConAppCo _ tc cos => Some (pair tc cos)
    | _ => None
    end.

Definition coVarKindsTypesRole
   : CoVar -> (Kind * Kind * Type_ * Type_ * Core.Role)%type :=
  fun cv =>
    match splitTyConApp_maybe (varType cv) with
    | Some (pair tc (cons k1 (cons k2 (cons ty1 (cons ty2 nil))))) =>
        let role :=
          if Unique.hasKey tc PrelNames.eqPrimTyConKey : bool then Core.Nominal else
          if Unique.hasKey tc PrelNames.eqReprPrimTyConKey : bool
          then Core.Representational else
          Panic.panic (GHC.Base.hs_string__ "coVarKindsTypesRole") in
        pair (pair (pair (pair k1 k2) ty1) ty2) role
    | _ =>
        Panic.panicStr (GHC.Base.hs_string__
                        "coVarKindsTypesRole, non coercion variable") (Panic.noString cv Outputable.$$
                                                                       Panic.noString (varType cv))
    end.

Definition coVarTypes : CoVar -> (Type_ * Type_)%type :=
  fun cv =>
    let 'pair (pair (pair (pair _ _) ty1) ty2) _ := coVarKindsTypesRole cv in
    pair ty1 ty2.

Definition getClassPredTys_maybe
   : PredType -> option (Class.Class * list Type_)%type :=
  fun ty =>
    match splitTyConApp_maybe ty with
    | Some (pair tc tys) =>
        match TyCon.tyConClass_maybe tc with
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
   : PredType -> option (Core.Role * Type_ * Type_)%type :=
  fun ty =>
    match splitTyConApp_maybe ty with
    | Some (pair tc (cons _ (cons _ (cons ty1 (cons ty2 nil))))) =>
        if Unique.hasKey tc PrelNames.eqPrimTyConKey : bool
        then Some (pair (pair Core.Nominal ty1) ty2) else
        if Unique.hasKey tc PrelNames.eqReprPrimTyConKey : bool
        then Some (pair (pair Core.Representational ty1) ty2) else
        None
    | _ => None
    end.

Definition isAlgType : Type_ -> bool :=
  fun ty =>
    match splitTyConApp_maybe ty with
    | Some (pair tc ty_args) =>
        if andb Util.debugIsOn (negb (Util.lengthIs ty_args (TyCon.tyConArity
                                                     tc))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
              #2007)
        else TyCon.isAlgTyCon tc
    | _other => false
    end.

Definition isClosedAlgType : Type_ -> bool :=
  fun ty =>
    let scrut_0__ := splitTyConApp_maybe ty in
    let j_1__ := let '_other := scrut_0__ in false in
    match scrut_0__ with
    | Some (pair tc ty_args) =>
        if andb (TyCon.isAlgTyCon tc) (negb (TyCon.isFamilyTyCon tc)) : bool
        then if andb Util.debugIsOn (negb (Util.lengthIs ty_args (TyCon.tyConArity
                                                          tc))) : bool
             then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                              "ghc/compiler/types/Type.hs") #2019 (Panic.noString ty))
             else true else
        j_1__
    | _ => j_1__
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
        if andb Util.debugIsOn (negb (Util.lengthIs ty_args (TyCon.tyConArity
                                                     tc))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Type.hs")
              #2032)
        else TyCon.isPrimTyCon tc
    | _ => false
    end.

Definition nextRole : Type_ -> Core.Role :=
  fun ty =>
    match splitTyConApp_maybe ty with
    | Some (pair tc tys) =>
        let num_tys := Data.Foldable.length tys in
        if num_tys GHC.Base.< TyCon.tyConArity tc : bool
        then ListSetOps.getNth (TyCon.tyConRoles tc) num_tys else
        Core.Nominal
    | _ => Core.Nominal
    end.

Definition pprUserTypeErrorTy : Type_ -> Outputable.SDoc :=
  fix pprUserTypeErrorTy ty
        := let scrut_0__ := splitTyConApp_maybe ty in
           let j_2__ := Panic.noString ty in
           let j_4__ :=
             match scrut_0__ with
             | Some (pair tc (cons t1 (cons t2 nil))) =>
                 if TyCon.tyConName tc GHC.Base.== PrelNames.typeErrorVAppendDataConName : bool
                 then pprUserTypeErrorTy t1 Outputable.$$ pprUserTypeErrorTy t2 else
                 j_2__
             | _ => j_2__
             end in
           let j_6__ :=
             match scrut_0__ with
             | Some (pair tc (cons t1 (cons t2 nil))) =>
                 if TyCon.tyConName tc GHC.Base.== PrelNames.typeErrorAppendDataConName : bool
                 then pprUserTypeErrorTy t1 Outputable.<> pprUserTypeErrorTy t2 else
                 j_4__
             | _ => j_4__
             end in
           match scrut_0__ with
           | Some (pair tc (cons txt nil)) =>
               if TyCon.tyConName tc GHC.Base.== PrelNames.typeErrorTextDataConName : bool
               then match isStrLitTy txt with
                    | Some str => Outputable.ftext str
                    | _ => j_6__
                    end else
               j_6__
           | Some (pair tc (cons _k (cons t nil))) =>
               if TyCon.tyConName tc GHC.Base.== PrelNames.typeErrorShowTypeDataConName : bool
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

Definition getEqPredRole : PredType -> Core.Role :=
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

Definition splitTyConApp : Type_ -> (Core.TyCon * list Type_)%type :=
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
          Control.Monad.guard (TyCon.tyConName tc GHC.Base.==
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
          match TyCon.tyConClass_maybe tc with
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
                   if TyCon.isClassTyCon tc : bool then true else
                   if TyCon.isTupleTyCon tc : bool then Data.Foldable.all isDictLikeTy tys else
                   j_2__
               | _ => j_2__
               end
           end.

Definition tyConAppArgs : Type_ -> list Type_ :=
  fun ty =>
    Maybes.orElse (tyConAppArgs_maybe ty) (Panic.panicStr (GHC.Base.hs_string__
                                                           "tyConAppArgs") (Panic.noString ty)).

Definition coVarRole : CoVar -> Core.Role :=
  fun cv =>
    let tc :=
      match tyConAppTyCon_maybe (varType cv) with
      | Some tc0 => tc0
      | None =>
          Panic.panicStr (GHC.Base.hs_string__ "coVarRole: not tyconapp") (Panic.noString
                                                                           cv)
      end in
    if Unique.hasKey tc PrelNames.eqPrimTyConKey : bool then Core.Nominal else
    if Unique.hasKey tc PrelNames.eqReprPrimTyConKey : bool
    then Core.Representational else
    Panic.panicStr (GHC.Base.hs_string__ "coVarRole: unknown tycon")
    (GHC.Base.mappend (GHC.Base.mappend (Panic.noString cv) Outputable.dcolon)
                      (Panic.noString (varType cv))).

Definition isClassPred : PredType -> bool :=
  fun ty =>
    match tyConAppTyCon_maybe ty with
    | Some tyCon => if TyCon.isClassTyCon tyCon : bool then true else false
    | _ => false
    end.

Definition isDictTy : Type_ -> bool :=
  isClassPred.

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

Definition isUnboxedTupleType : Type_ -> bool :=
  fun ty =>
    match tyConAppTyCon_maybe ty with
    | Some tc => TyCon.isUnboxedTupleTyCon tc
    | _ => false
    end.

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

Definition tyConsOfType : Type_ -> NameEnv.NameEnv Core.TyCon :=
  fun ty =>
    let go_tc := fun tc => NameEnv.unitNameEnv (TyCon.tyConName tc) tc in
    let go_ax := fun ax => go_tc (CoAxiom.coAxiomTyCon ax) in
    let go : Type_ -> NameEnv.NameEnv Core.TyCon :=
      fix go arg_2__
            := let 'ty := arg_2__ in
               match coreView ty with
               | Some ty' => go ty'
               | _ =>
                   match arg_2__ with
                   | TyVarTy _ => NameEnv.emptyNameEnv
                   | LitTy _ => NameEnv.emptyNameEnv
                   | TyConApp tc tys => NameEnv.plusNameEnv (go_tc tc) (go_s tys)
                   | AppTy a b => NameEnv.plusNameEnv (go a) (go b)
                   | ForAllTy (Anon a) b =>
                       NameEnv.plusNameEnv (NameEnv.plusNameEnv (go a) (go b)) (go_tc TysPrim.funTyCon)
                   | ForAllTy (Named tv _) ty => NameEnv.plusNameEnv (go ty) (go (tyVarKind tv))
                   | CastTy ty co => NameEnv.plusNameEnv (go ty) (go_co co)
                   | CoercionTy co => go_co co
                   end
               end in
    let fix go_co arg_12__
              := match arg_12__ with
                 | Refl _ ty => go ty
                 | TyConAppCo _ tc args => NameEnv.plusNameEnv (go_tc tc) (go_cos args)
                 | AppCo co arg => NameEnv.plusNameEnv (go_co co) (go_co arg)
                 | ForAllCo _ kind_co co => NameEnv.plusNameEnv (go_co kind_co) (go_co co)
                 | CoVarCo _ => NameEnv.emptyNameEnv
                 | AxiomInstCo ax _ args => NameEnv.plusNameEnv (go_ax ax) (go_cos args)
                 | UnivCo p _ t1 t2 =>
                     NameEnv.plusNameEnv (NameEnv.plusNameEnv (go_prov p) (go t1)) (go t2)
                 | SymCo co => go_co co
                 | TransCo co1 co2 => NameEnv.plusNameEnv (go_co co1) (go_co co2)
                 | NthCo _ co => go_co co
                 | LRCo _ co => go_co co
                 | InstCo co arg => NameEnv.plusNameEnv (go_co co) (go_co arg)
                 | CoherenceCo co1 co2 => NameEnv.plusNameEnv (go_co co1) (go_co co2)
                 | KindCo co => go_co co
                 | SubCo co => go_co co
                 | AxiomRuleCo _ cs => go_cos cs
                 end in
    let go_prov :=
      fun arg_29__ =>
        match arg_29__ with
        | UnsafeCoerceProv => NameEnv.emptyNameEnv
        | PhantomProv co => go_co co
        | ProofIrrelProv co => go_co co
        | PluginProv _ => NameEnv.emptyNameEnv
        | HoleProv _ => NameEnv.emptyNameEnv
        end in
    let go_cos :=
      fun cos =>
        Data.Foldable.foldr (NameEnv.plusNameEnv GHC.Base.∘ go_co) NameEnv.emptyNameEnv
        cos in
    let go_s :=
      fun tys =>
        Data.Foldable.foldr (NameEnv.plusNameEnv GHC.Base.∘ go) NameEnv.emptyNameEnv
        tys in
    go ty.

Definition splitVisVarsOfType : Type_ -> Pair.Pair VarSet.TyCoVarSet :=
  fun orig_ty =>
    let invisible := fun vs => Pair.Mk_Pair vs VarSet.emptyVarSet in
    let fix go arg_1__
              := match arg_1__ with
                 | TyVarTy tv =>
                     Pair.Mk_Pair (tyCoVarsOfType (tyVarKind tv)) (VarSet.unitVarSet tv)
                 | AppTy t1 t2 => GHC.Base.mappend (go t1) (go t2)
                 | TyConApp tc tys => go_tc tc tys
                 | ForAllTy (Anon t1) t2 => GHC.Base.mappend (go t1) (go t2)
                 | ForAllTy (Named tv _) ty =>
                     GHC.Base.mappend ((fun arg_6__ => VarSet.delVarSet arg_6__ tv) Data.Functor.<$>
                                       go ty) (invisible (tyCoVarsOfType (tyVarKind tv)))
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
    let invis_vars := VarSet.minusVarSet invis_vars1 vis_vars in
    Pair.Mk_Pair invis_vars vis_vars.

Definition splitVisVarsOfTypes : list Type_ -> Pair.Pair VarSet.TyCoVarSet :=
  Data.Foldable.foldMap splitVisVarsOfType.

Definition filterOutInvisibleTypes : Core.TyCon -> list Type_ -> list Type_ :=
  fun tc tys => Data.Tuple.snd (partitionInvisibles tc GHC.Base.id tys).

Definition filterOutInvisibleTyVars : Core.TyCon -> list TyVar -> list TyVar :=
  fun tc tvs => Data.Tuple.snd (partitionInvisibles tc mkTyVarTy tvs).

Definition splitPiTysInvisible : Type_ -> (list TyBinder * Type_)%type :=
  fun ty =>
    let fix split arg_0__ arg_1__ arg_2__
              := match arg_0__, arg_1__, arg_2__ with
                 | orig_ty, ty, bndrs =>
                     match coreView ty with
                     | Some ty' => split orig_ty ty' bndrs
                     | _ =>
                         let j_4__ :=
                           match arg_0__, arg_1__, arg_2__ with
                           | orig_ty, _, bndrs => pair (GHC.List.reverse bndrs) orig_ty
                           end in
                         match arg_0__, arg_1__, arg_2__ with
                         | _, ForAllTy bndr ty, bndrs =>
                             if isInvisibleBinder bndr : bool then split ty ty (cons bndr bndrs) else
                             j_4__
                         | _, _, _ => j_4__
                         end
                     end
                 end in
    split ty ty nil.

Definition isVisibleType : Type_ -> bool :=
  negb GHC.Base.∘ isPredTy.

Definition binderVisibility : TyBinder -> VisibilityFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | Named _ vis => vis
    | Anon ty => if isVisibleType ty : bool then Visible else Invisible
    end.

Definition synTyConResKind : Core.TyCon -> Kind :=
  fun tycon =>
    piResultTys (TyCon.tyConKind tycon) (mkTyVarTys (TyCon.tyConTyVars tycon)).

Definition isRuntimeRepKindedTy : Type_ -> bool :=
  isRuntimeRepTy GHC.Base.∘ typeKind.

Definition dropRuntimeRepArgs : list Type_ -> list Type_ :=
  GHC.List.dropWhile isRuntimeRepKindedTy.

Definition repType : Type_ -> RepType :=
  fun ty =>
    let go : TyCon.RecTcChecker -> Type_ -> RepType :=
      fix go arg_0__ arg_1__
            := match arg_0__, arg_1__ with
               | rec_nts, ty =>
                   match coreView ty with
                   | Some ty' => go rec_nts ty'
                   | _ =>
                       let j_5__ :=
                         match arg_0__, arg_1__ with
                         | rec_nts, CastTy ty _ => go rec_nts ty
                         | _, (CoercionTy _ as ty) =>
                             Panic.panicStr (GHC.Base.hs_string__ "repType") (Panic.noString ty)
                         | _, ty => UnaryRep ty
                         end in
                       match arg_0__, arg_1__ with
                       | rec_nts, ForAllTy (Named _ _) ty2 => go rec_nts ty2
                       | rec_nts, TyConApp tc tys =>
                           let non_rr_tys := dropRuntimeRepArgs tys in
                           let j_8__ :=
                             if TyCon.isUnboxedTupleTyCon tc : bool
                             then UbxTupleRep (Data.Foldable.concatMap (flattenRepType GHC.Base.∘ go rec_nts)
                                               non_rr_tys) else
                             j_5__ in
                           if andb (TyCon.isNewTyCon tc) (Util.lengthAtLeast tys (TyCon.tyConArity
                                                                              tc)) : bool
                           then match TyCon.checkRecTc rec_nts tc with
                                | Some rec_nts' => go rec_nts' (newTyConInstRhs tc tys)
                                | _ => j_8__
                                end else
                           j_8__
                       | _, _ => j_5__
                       end
                   end
               end in
    go TyCon.initRecTc ty.

Definition isVoidTy : Type_ -> bool :=
  fun ty =>
    match repType ty with
    | UnaryRep (TyConApp tc _) =>
        andb (TyCon.isUnliftedTyCon tc) (TyCon.isVoidRep (tyConPrimRep tc))
    | _ => false
    end.

Definition typeRepArity : BasicTypes.Arity -> Type_ -> BasicTypes.RepArity :=
  fix typeRepArity arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | num_2__, _ =>
               if num_2__ GHC.Base.== #0 : bool then #0 else
               match arg_0__, arg_1__ with
               | n, ty =>
                   match repType ty with
                   | UnaryRep (ForAllTy bndr ty) =>
                       Data.Foldable.length (flattenRepType (repType (binderType bndr))) GHC.Num.+
                       typeRepArity (n GHC.Num.- #1) ty
                   | _ =>
                       Panic.panicStr (GHC.Base.hs_string__
                                       "typeRepArity: arity greater than type can handle") (Panic.noString (pair (pair
                                                                                                                  n ty)
                                                                                                                 (repType
                                                                                                                  ty)))
                   end
               end
           end.

Definition mkPrimEqPredRole : Core.Role -> Type_ -> Type_ -> PredType :=
  fun arg_0__ =>
    match arg_0__ with
    | Core.Nominal => mkPrimEqPred
    | Core.Representational => mkReprPrimEqPred
    | Core.Phantom => Panic.panic (GHC.Base.hs_string__ "mkPrimEqPredRole phantom")
    end.

Definition tcRepSplitAppTy_maybe : Type_ -> option (Type_ * Type_)%type :=
  fun arg_0__ =>
    let j_1__ := let '_other := arg_0__ in None in
    match arg_0__ with
    | ForAllTy (Anon ty1) ty2 =>
        if Kind.isConstraintKind (typeKind ty1) : bool then None else
        Some (pair (TyConApp TysPrim.funTyCon (cons ty1 nil)) ty2)
    | AppTy ty1 ty2 => Some (pair ty1 ty2)
    | TyConApp tc tys =>
        if orb (TyCon.mightBeUnsaturatedTyCon tc) (Util.lengthExceeds tys
                                                                      (TyCon.tyConArity tc)) : bool
        then match Util.snocView tys with
             | Some (pair tys' ty') => Some (pair (TyConApp tc tys') ty')
             | _ => j_1__
             end else
        j_1__
    | _ => j_1__
    end.

Definition typePrimRep : UnaryType -> TyCon.PrimRep :=
  fun ty => kindPrimRep (typeKind ty).

Definition getRuntimeRepFromKind : GHC.Base.String -> Type_ -> Type_ :=
  fun err =>
    let fix go arg_0__
              := let 'k := arg_0__ in
                 match coreViewOneStarKind k with
                 | Some k' => go k'
                 | _ =>
                     let 'k := arg_0__ in
                     let j_2__ :=
                       let 'k := arg_0__ in
                       Panic.panicStr (GHC.Base.hs_string__ "getRuntimeRep") (GHC.Base.mappend
                                                                              (GHC.Base.mappend (id err Outputable.$$
                                                                                                 Panic.noString k)
                                                                                                Outputable.dcolon)
                                                                              (Panic.noString (typeKind k))) in
                     match splitTyConApp_maybe k with
                     | Some (pair tc (cons arg nil)) =>
                         if Unique.hasKey tc PrelNames.tYPETyConKey : bool then arg else
                         j_2__
                     | _ => j_2__
                     end
                 end in
    go.

Definition getRuntimeRep : GHC.Base.String -> Type_ -> Type_ :=
  fun err ty => getRuntimeRepFromKind err (typeKind ty).

Definition mkUnsafeCo : Core.Role -> Type_ -> Type_ -> Coercion :=
  fun role ty1 ty2 => mkUnivCo UnsafeCoerceProv role ty1 ty2.

Definition mkHoleCo : CoercionHole -> Core.Role -> Type_ -> Type_ -> Coercion :=
  fun h r t1 t2 => mkUnivCo (HoleProv h) r t1 t2.

Definition mkHomoPhantomCo : Type_ -> Type_ -> Coercion :=
  fun t1 t2 =>
    let k1 := typeKind t1 in
    if andb Util.debugIsOn (negb (eqType k1 (typeKind t2))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #1042)
    else mkPhantomCo (mkNomReflCo k1) t1 t2.

Definition eqCoercion : Coercion -> Coercion -> bool :=
  Data.Function.on eqType coercionType.

Definition isReflexiveCo_maybe : Coercion -> option (Type_ * Core.Role)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | Refl r ty => Some (pair ty r)
    | co =>
        let 'pair (Pair.Mk_Pair ty1 ty2) r := coercionKindRole co in
        if eqType ty1 ty2 : bool then Some (pair ty1 r) else
        None
    end.

Definition isReflexiveCo : Coercion -> bool :=
  Data.Maybe.isJust GHC.Base.∘ isReflexiveCo_maybe.

Definition maybeSubCo : EqRel -> Coercion -> Coercion :=
  fun arg_0__ =>
    match arg_0__ with
    | NomEq => GHC.Base.id
    | ReprEq => mkSubCo
    end.

Definition mkNthCoRole : Core.Role -> GHC.Num.Int -> Coercion -> Coercion :=
  fun role n co =>
    let nth_co := mkNthCo n co in
    let nth_role := coercionRole nth_co in downgradeRole role nth_role nth_co.

Definition liftCoSubstTyVar
   : LiftingContext -> Core.Role -> TyVar -> option Coercion :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | LC subst env, r, v =>
        match VarEnv.lookupVarEnv env v with
        | Some co_arg => downgradeRole_maybe r (coercionRole co_arg) co_arg
        | _ => Some (Refl r (substTyVar subst v))
        end
    end.

Definition mkAxInstCo {br}
   : Core.Role ->
     Core.CoAxiom br ->
     Core.BranchIndex -> list Type_ -> list Coercion -> Coercion :=
  fun role ax index tys cos =>
    let ax_role := CoAxiom.coAxiomRole ax in
    let ax_br := CoAxiom.toBranchedAxiom ax in
    let branch := CoAxiom.coAxiomNthBranch ax_br index in
    let tvs := CoAxiom.coAxBranchTyVars branch in
    let arity := Data.Foldable.length tvs in
    let arg_roles := CoAxiom.coAxBranchRoles branch in
    let rtys :=
      GHC.List.zipWith mkReflCo (Coq.Init.Datatypes.app arg_roles (GHC.List.repeat
                                                         Core.Nominal)) tys in
    let 'pair ax_args leftover_args := GHC.List.splitAt arity rtys in
    let n_tys := Data.Foldable.length tys in
    if arity GHC.Base.== n_tys : bool
    then downgradeRole role ax_role (mkAxiomInstCo ax_br index (Util.chkAppend rtys
                                                                               cos)) else
    if andb Util.debugIsOn (negb (arity GHC.Base.< n_tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #746)
    else downgradeRole role ax_role (mkAppCos (mkAxiomInstCo ax_br index
                                               (Util.chkAppend ax_args cos)) leftover_args).

Definition mkUnbranchedAxInstCo
   : Core.Role ->
     Core.CoAxiom Core.Unbranched -> list Type_ -> list Coercion -> Coercion :=
  fun role ax tys cos => mkAxInstCo role ax #0 tys cos.

Definition instNewTyCon_maybe
   : Core.TyCon -> list Type_ -> option (Type_ * Coercion)%type :=
  fun tc tys =>
    match TyCon.unwrapNewTyConEtad_maybe tc with
    | Some (pair (pair tvs ty) co_tc) =>
        if Util.leLength tvs tys : bool
        then Some (pair (applyTysX tvs ty tys) (mkUnbranchedAxInstCo
                         Core.Representational co_tc tys nil)) else
        None
    | _ => None
    end.

Definition unwrapNewTypeStepper : NormaliseStepper Coercion :=
  fun rec_nts tc tys =>
    match instNewTyCon_maybe tc tys with
    | Some (pair ty' co) =>
        match TyCon.checkRecTc rec_nts tc with
        | Some rec_nts' => NS_Step rec_nts' ty' co
        | None => NS_Abort
        end
    | _ => NS_Done
    end.

Definition topNormaliseNewType_maybe
   : Type_ -> option (Coercion * Type_)%type :=
  fun ty => topNormaliseTypeX unwrapNewTypeStepper mkTransCo ty.

Definition mkTransAppCo
   : Core.Role ->
     Coercion ->
     Type_ ->
     Type_ -> Core.Role -> Coercion -> Type_ -> Type_ -> Core.Role -> Coercion :=
  fun r1 co1 ty1a ty1b r2 co2 ty2a ty2b r3 =>
    let go :=
      fun co1_repr =>
        let j_0__ :=
          Panic.panicStr (GHC.Base.hs_string__ "mkTransAppCo") (Outputable.vcat (cons
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
              then mkTransCo (mkTyConAppCo Core.Representational tc1a (Coq.Init.Datatypes.app
                                                                       (GHC.List.zipWith mkReflCo
                                                                        (tyConRolesRepresentational tc1a) tys1a) (cons
                                                                        co2 nil))) (mkAppCo co1_repr (mkNomReflCo
                                                                                                      ty2b)) else
              j_0__
          | _ => j_0__
          end in
        match splitTyConApp_maybe ty1b with
        | Some (pair tc1b tys1b) =>
            if nextRole ty1b GHC.Base.== r2 : bool
            then mkTransCo (mkAppCo co1_repr (mkNomReflCo ty2a)) (mkTyConAppCo
                            Core.Representational tc1b (Coq.Init.Datatypes.app (GHC.List.zipWith mkReflCo
                                                                                (tyConRolesRepresentational tc1b) tys1b)
                                                                               (cons co2 nil))) else
            j_1__
        | _ => j_1__
        end in
    match pair (pair r1 r2) r3 with
    | pair (pair _ _) Core.Phantom =>
        let kind_co1 := mkKindCo co1 in
        let kind_co := mkNthCo #1 kind_co1 in
        mkPhantomCo kind_co (mkAppTy ty1a ty2a) (mkAppTy ty1b ty2b)
    | pair (pair _ _) Core.Nominal =>
        if andb Util.debugIsOn (negb (andb (r1 GHC.Base.== Core.Nominal) (r2 GHC.Base.==
                                            Core.Nominal))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
              #654)
        else mkAppCo co1 co2
    | pair (pair Core.Nominal Core.Nominal) Core.Representational =>
        mkSubCo (mkAppCo co1 co2)
    | pair (pair _ Core.Nominal) Core.Representational =>
        if andb Util.debugIsOn (negb (r1 GHC.Base.== Core.Representational)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
              #659)
        else mkAppCo co1 co2
    | pair (pair Core.Nominal Core.Representational) Core.Representational =>
        go (mkSubCo co1)
    | pair (pair _ _) Core.Representational =>
        if andb Util.debugIsOn (negb (andb (r1 GHC.Base.== Core.Representational) (r2
                                            GHC.Base.==
                                            Core.Representational))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
              #664)
        else go co1
    end.

Definition mkCoVarCo : CoVar -> Coercion :=
  fun cv =>
    let 'pair ty1 ty2 := coVarTypes cv in
    if eqType ty1 ty2 : bool then Refl (coVarRole cv) ty1 else
    CoVarCo cv.

Definition mkCoVarCos : list CoVar -> list Coercion :=
  GHC.Base.map mkCoVarCo.

Definition substCoVarBndrCallback
   : bool ->
     (TCvSubst -> Type_ -> Type_) -> TCvSubst -> CoVar -> (TCvSubst * CoVar)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | sym, subst_fun, (TCvSubst in_scope tenv cenv as subst), old_var =>
        let 'pair (pair (pair (pair _ _) t1) t2) role := coVarKindsTypesRole old_var in
        let t1' := subst_fun subst t1 in
        let t2' := subst_fun subst t2 in
        let new_var_type :=
          Data.Tuple.uncurry (mkCoercionType role) (if sym : bool
                                                    then pair t2' t1'
                                                    else pair t1' t2') in
        let subst_old_var := mkCoVar (varName old_var) new_var_type in
        let new_var := VarEnv.uniqAway in_scope subst_old_var in
        let no_kind_change :=
          VarSet.isEmptyVarSet (tyCoVarsOfTypes (cons t1 (cons t2 nil))) in
        let new_co :=
          (if sym : bool
           then mkSymCo
           else GHC.Base.id) (mkCoVarCo new_var) in
        let no_change :=
          andb (new_var GHC.Base.== old_var) (andb (negb (isReflCo new_co))
                                                   no_kind_change) in
        let new_cenv :=
          if no_change : bool then VarEnv.delVarEnv cenv old_var else
          VarEnv.extendVarEnv cenv old_var new_co in
        if andb Util.debugIsOn (negb (isCoVar old_var)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
              #2327)
        else pair (TCvSubst (VarEnv.extendInScopeSet in_scope new_var) tenv new_cenv)
                  new_var
    end.

Definition substCoVarBndr : TCvSubst -> CoVar -> (TCvSubst * CoVar)%type :=
  substCoVarBndrCallback false substTy.

Definition extendCvSubstWithClone : TCvSubst -> CoVar -> CoVar -> TCvSubst :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | TCvSubst in_scope tenv cenv, cv, cv' =>
        let new_in_scope := VarSet.extendVarSet (tyCoVarsOfType (varType cv')) cv' in
        TCvSubst (VarEnv.extendInScopeSetSet in_scope new_in_scope) tenv
        (VarEnv.extendVarEnv cenv cv (mkCoVarCo cv'))
    end.

Definition pprTcAppCo
   : TyPrec ->
     (TyPrec -> Coercion -> Outputable.SDoc) ->
     Core.TyCon -> list Coercion -> Outputable.SDoc :=
  fun p pp tc cos =>
    Outputable.getPprStyle (fun style =>
                              pprTcApp style (Pair.pFst GHC.Base.∘ coercionKind) p pp tc cos).

Definition pprTvBndrs : list TyVar -> Outputable.SDoc :=
  fun tvs => Outputable.sep (GHC.Base.map pprTvBndr tvs).

Definition substTyVarBndr `{(GHC.Stack.CallStack)}
   : TCvSubst -> TyVar -> (TCvSubst * TyVar)%type :=
  substTyVarBndrCallback substTy.

Definition pprForAllImplicit : list TyVar -> Outputable.SDoc :=
  fun tvs => pprForAll (GHC.List.zipWith Named tvs (GHC.List.repeat Specified)).

Definition pprUserForAll : list TyBinder -> Outputable.SDoc :=
  fun bndrs =>
    let bndr_has_kind_var :=
      fun bndr => negb (VarSet.isEmptyVarSet (tyCoVarsOfType (binderType bndr))) in
    Outputable.sdocWithDynFlags (fun dflags =>
                                   Outputable.ppWhen (orb (Data.Foldable.any bndr_has_kind_var bndrs)
                                                          (DynFlags.gopt DynFlags.Opt_PrintExplicitForalls dflags))
                                   (pprForAll bndrs)).

Definition pprSigmaType : Type_ -> Outputable.SDoc :=
  fun ty =>
    Outputable.sdocWithDynFlags (fun dflags =>
                                   eliminateRuntimeRep (ppr_sigma_type dflags false) ty).

Definition pprParendType : Type_ -> Outputable.SDoc :=
  fun ty => eliminateRuntimeRep (ppr_type TyConPrec) ty.

Definition pprParendKind : Kind -> Outputable.SDoc :=
  pprParendType.

Definition pprDataConWithArgs : DataCon.DataCon -> Outputable.SDoc :=
  fun dc =>
    let ex_bndrs := DataCon.dataConExTyBinders dc in
    let univ_bndrs := DataCon.dataConUnivTyBinders dc in
    let 'pair (pair (pair (pair (pair _univ_tvs _ex_tvs) eq_spec) theta) arg_tys)
       _res_ty := DataCon.dataConFullSig dc in
    let forAllDoc :=
      pprUserForAll (Coq.Init.Datatypes.app (DataCon.filterEqSpec eq_spec univ_bndrs)
                                            ex_bndrs) in
    let thetaDoc := pprThetaArrowTy theta in
    let argsDoc := Outputable.hsep (GHC.Base.fmap pprParendType arg_tys) in
    Outputable.sep (cons forAllDoc (cons thetaDoc (cons (GHC.Base.mappend
                                                         (Panic.noString dc) argsDoc) nil))).

Definition pprDataCons : Core.TyCon -> Outputable.SDoc :=
  let sepWithVBars :=
    fun arg_0__ =>
      match arg_0__ with
      | nil => Outputable.empty
      | docs =>
          Outputable.sep (Outputable.punctuate (Outputable.space Outputable.<>
                                                Outputable.vbar) docs)
      end in
  sepWithVBars GHC.Base.∘
  (GHC.Base.fmap pprDataConWithArgs GHC.Base.∘ TyCon.tyConDataCons).

Definition pprCoAxBranch {br}
   : Core.CoAxiom br -> Core.CoAxBranch -> Outputable.SDoc :=
  let pprRhs :=
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | fam_tc, TyConApp tycon _ =>
          if TyCon.isDataFamilyTyCon fam_tc : bool then pprDataCons tycon else
          match arg_0__, arg_1__ with
          | _, rhs => Panic.noString rhs
          end
      end in
  ppr_co_ax_branch pprRhs.

Definition pprCoAxBranchHdr {br}
   : Core.CoAxiom br -> Core.BranchIndex -> Outputable.SDoc :=
  fun ax index => pprCoAxBranch ax (CoAxiom.coAxiomNthBranch ax index).

Definition pprTheta : ThetaType -> Outputable.SDoc :=
  fun arg_0__ =>
    match arg_0__ with
    | cons pred nil => ppr_type TopPrec pred
    | theta =>
        Outputable.parens (Outputable.sep (Outputable.punctuate Outputable.comma
                                           (GHC.Base.map (ppr_type TopPrec) theta)))
    end.

Definition pprTypeApp : Core.TyCon -> list Type_ -> Outputable.SDoc :=
  fun tc tys => pprTyTcApp TopPrec tc tys.

Definition pprClassPred : Class.Class -> list Type_ -> Outputable.SDoc :=
  fun clas tys => pprTypeApp (Class.classTyCon clas) tys.

Definition cmpTypesX
   : VarEnv.RnEnv2 -> list Type_ -> list Type_ -> comparison :=
  fix cmpTypesX arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | _, nil, nil => Eq
           | env, cons t1 tys1, cons t2 tys2 =>
               Util.thenCmp (cmpTypeX env t1 t2) (cmpTypesX env tys1 tys2)
           | _, nil, _ => Lt
           | _, _, nil => Gt
           end.

Definition cmpTypes : list Type_ -> list Type_ -> comparison :=
  fun ts1 ts2 =>
    let rn_env :=
      VarEnv.mkRnEnv2 (VarEnv.mkInScopeSet (tyCoVarsOfTypes (Coq.Init.Datatypes.app
                                                             ts1 ts2))) in
    cmpTypesX rn_env ts1 ts2.

Definition eqTypes : list Type_ -> list Type_ -> bool :=
  fun tys1 tys2 => Util.isEqual (cmpTypes tys1 tys2).

Definition eqTypeX : VarEnv.RnEnv2 -> Type_ -> Type_ -> bool :=
  fun env t1 t2 => Util.isEqual (cmpTypeX env t1 t2).

Definition eqCoercionX : VarEnv.RnEnv2 -> Coercion -> Coercion -> bool :=
  fun env => Data.Function.on (eqTypeX env) coercionType.

Definition eqVarBndrs
   : VarEnv.RnEnv2 -> list Var -> list Var -> option VarEnv.RnEnv2 :=
  fix eqVarBndrs arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | env, nil, nil => Some env
           | env, cons tv1 tvs1, cons tv2 tvs2 =>
               if eqTypeX env (tyVarKind tv1) (tyVarKind tv2) : bool
               then eqVarBndrs (VarEnv.rnBndr2 env tv1 tv2) tvs1 tvs2 else
               None
           | _, _, _ => None
           end.

Definition substTys `{(GHC.Stack.CallStack)}
   : TCvSubst -> list Type_ -> list Type_ :=
  fun subst tys =>
    if isEmptyTCvSubst subst : bool then tys else
    checkValidSubst subst tys nil (GHC.Base.map (subst_ty subst) tys).

Definition substTheta `{(GHC.Stack.CallStack)}
   : TCvSubst -> ThetaType -> ThetaType :=
  substTys.

Definition substTysWith
   : list TyVar -> list Type_ -> list Type_ -> list Type_ :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Data.Foldable.length tvs GHC.Base.==
                                  Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #1954)
    else substTys (zipTvSubst tvs tys).

Definition substTysWithCoVars
   : list CoVar -> list Coercion -> list Type_ -> list Type_ :=
  fun cvs cos =>
    if andb Util.debugIsOn (negb (Data.Foldable.length cvs GHC.Base.==
                                  Data.Foldable.length cos)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #1959)
    else substTys (zipCvSubst cvs cos).

Definition mkAxInstLHS {br}
   : Core.CoAxiom br ->
     Core.BranchIndex -> list Type_ -> list Coercion -> Type_ :=
  fun ax index tys cos =>
    let fam_tc := CoAxiom.coAxiomTyCon ax in
    let branch := CoAxiom.coAxiomNthBranch ax index in
    let tvs := CoAxiom.coAxBranchTyVars branch in
    let 'pair tys1 tys2 := Util.splitAtList tvs tys in
    let cvs := CoAxiom.coAxBranchCoVars branch in
    let lhs_tys :=
      substTysWith tvs tys1 (substTysWithCoVars cvs cos (CoAxiom.coAxBranchLHS
                                                 branch)) in
    if andb Util.debugIsOn (negb (Util.equalLength tvs tys1)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/Coercion.hs")
          #799)
    else mkTyConApp fam_tc (Util.chkAppend lhs_tys tys2).

Definition mkUnbranchedAxInstLHS
   : Core.CoAxiom Core.Unbranched -> list Type_ -> list Coercion -> Type_ :=
  fun ax => mkAxInstLHS ax #0.

Definition mkFamilyTyConApp : Core.TyCon -> list Type_ -> Type_ :=
  fun tc tys =>
    match TyCon.tyConFamInst_maybe tc with
    | Some (pair fam_tc fam_tys) =>
        let tvs := TyCon.tyConTyVars tc in
        let fam_subst :=
          if andb Util.debugIsOn (negb (Data.Foldable.length tvs GHC.Base.==
                                        Data.Foldable.length tys)) : bool
          then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                           "ghc/compiler/types/Type.hs") #1929 (GHC.Base.mappend (Panic.noString tc)
                                                                                                 (Panic.noString tys)))
          else zipTvSubst tvs tys in
        mkTyConApp fam_tc (substTys fam_subst fam_tys)
    | _ => mkTyConApp tc tys
    end.

Definition mkCastTy : Type_ -> Coercion -> Type_ :=
  fix mkCastTy arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | ty, co =>
               if isReflexiveCo co : bool then ty else
               match arg_0__, arg_1__ with
               | CastTy ty co1, co2 => mkCastTy ty (mkTransCo co1 co2)
               | (ForAllTy (Named tv vis) inner_ty as outer_ty), co =>
                   let fvs := VarSet.unionVarSet (tyCoVarsOfCo co) (tyCoVarsOfType outer_ty) in
                   let empty_subst := mkEmptyTCvSubst (VarEnv.mkInScopeSet fvs) in
                   let 'pair subst tv' := substTyVarBndr empty_subst tv in
                   ForAllTy (Named tv' vis) (mkCastTy (substTy subst inner_ty) co)
               | ty, co =>
                   let no_double_casts :=
                     fun arg_7__ arg_8__ =>
                       match arg_7__, arg_8__ with
                       | CastTy ty co1, co2 => CastTy ty (mkTransCo co1 co2)
                       | ty, co => CastTy ty co
                       end in
                   let affix_co :=
                     fun arg_12__ arg_13__ arg_14__ arg_15__ =>
                       match arg_12__, arg_13__, arg_14__, arg_15__ with
                       | _, ty, nil, co => no_double_casts ty co
                       | bndrs, ty, args, co =>
                           let 'pair no_dep_bndrs some_dep_bndrs := Util.spanEnd isAnonBinder bndrs in
                           let 'pair some_dep_args rest_args := Util.splitAtList some_dep_bndrs args in
                           let dep_subst := zipTyBinderSubst some_dep_bndrs some_dep_args in
                           let used_no_dep_bndrs := Util.takeList rest_args no_dep_bndrs in
                           let rest_arg_tys :=
                             substTys dep_subst (GHC.Base.map binderType used_no_dep_bndrs) in
                           let co' :=
                             mkFunCos Core.Nominal (GHC.Base.map (mkReflCo Core.Nominal) rest_arg_tys) co in
                           mkAppTys (no_double_casts (mkAppTys ty some_dep_args) co') rest_args
                       end in
                   let fix split_apps arg_25__ arg_26__ arg_27__
                             := match arg_25__, arg_26__, arg_27__ with
                                | args, AppTy t1 t2, co => split_apps (cons t2 args) t1 co
                                | args, TyConApp tc tc_args, co =>
                                    if TyCon.mightBeUnsaturatedTyCon tc : bool
                                    then affix_co (TyCon.tyConBinders tc) (mkTyConTy tc) (Util.chkAppend tc_args
                                                                                                         args) co else
                                    let 'pair non_decomp_args decomp_args := GHC.List.splitAt (TyCon.tyConArity tc)
                                                                               tc_args in
                                    let saturated_tc := mkTyConApp tc non_decomp_args in
                                    affix_co (Data.Tuple.fst (splitPiTys (typeKind saturated_tc))) saturated_tc
                                    (Util.chkAppend decomp_args args) co
                                | _, _, _ =>
                                    match arg_25__, arg_26__, arg_27__ with
                                    | args, ForAllTy (Anon arg) res, co =>
                                        affix_co (TyCon.tyConBinders TysPrim.funTyCon) (mkTyConTy TysPrim.funTyCon)
                                        (cons arg (cons res args)) co
                                    | args, ty, co =>
                                        affix_co (Data.Tuple.fst (splitPiTys (typeKind ty))) ty args co
                                    end
                                end in
                   let result := split_apps nil ty co in
                   if andb Util.debugIsOn (negb (eqType (CastTy ty co) result)) : bool
                   then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                                    "ghc/compiler/types/Type.hs") #1095 (GHC.Base.mappend
                                                                                         (GHC.Base.mappend
                                                                                          (GHC.Base.mappend
                                                                                           (GHC.Base.mappend
                                                                                            (GHC.Base.mappend
                                                                                             (GHC.Base.mappend
                                                                                              (Panic.noString ty)
                                                                                              Outputable.dcolon)
                                                                                             (Panic.noString (typeKind
                                                                                                              ty))
                                                                                             Outputable.$$
                                                                                             Panic.noString co)
                                                                                            Outputable.dcolon)
                                                                                           (Panic.noString (coercionKind
                                                                                                            co))
                                                                                           Outputable.$$
                                                                                           Panic.noString result)
                                                                                          Outputable.dcolon)
                                                                                         (Panic.noString (typeKind
                                                                                                          result))))
                   else result
               end
           end.

Definition substTysUnchecked : TCvSubst -> list Type_ -> list Type_ :=
  fun subst tys =>
    if isEmptyTCvSubst subst : bool then tys else
    GHC.Base.map (subst_ty subst) tys.

Definition substThetaUnchecked : TCvSubst -> ThetaType -> ThetaType :=
  substTysUnchecked.

Definition instCoercion
   : Pair.Pair Type_ -> Coercion -> Coercion -> option Coercion :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | Pair.Mk_Pair lty rty, g, w =>
        let j_3__ :=
          if andb (isFunTy lty) (isFunTy rty) : bool then Some (mkNthCo #1 g) else
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

Definition substCo `{(GHC.Stack.CallStack)}
   : TCvSubst -> Coercion -> Coercion :=
  fun subst co =>
    if isEmptyTCvSubst subst : bool then co else
    checkValidSubst subst nil (cons co nil) (subst_co subst co).

Definition composeTCvSubstEnv
   : VarEnv.InScopeSet ->
     (TvSubstEnv * CvSubstEnv)%type ->
     (TvSubstEnv * CvSubstEnv)%type -> (TvSubstEnv * CvSubstEnv)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | in_scope, pair tenv1 cenv1, pair tenv2 cenv2 =>
        let subst1 := TCvSubst in_scope tenv1 cenv1 in
        pair (VarEnv.plusVarEnv tenv1 (VarEnv.mapVarEnv (substTy subst1) tenv2))
             (VarEnv.plusVarEnv cenv1 (VarEnv.mapVarEnv (substCo subst1) cenv2))
    end.

Definition composeTCvSubst : TCvSubst -> TCvSubst -> TCvSubst :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | TCvSubst is1 tenv1 cenv1, TCvSubst is2 tenv2 cenv2 =>
        let is3 := VarEnv.unionInScope is1 is2 in
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
    let pairs := VarEnv.varEnvToList lc_env in
    let 'pair tpairs cpairs := Util.partitionWith ty_or_co pairs in
    let tenv := VarEnv.mkVarEnv_Directly tpairs in
    let cenv := VarEnv.mkVarEnv_Directly cpairs in
    composeTCvSubst (TCvSubst VarEnv.emptyInScopeSet tenv cenv) subst.

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

Definition substRightCo : LiftingContext -> Coercion -> Coercion :=
  fun lc co => substCo (lcSubstRight lc) co.

Definition substCoWith `{(GHC.Stack.CallStack)}
   : list TyVar -> list Type_ -> Coercion -> Coercion :=
  fun tvs tys =>
    if andb Util.debugIsOn (negb (Data.Foldable.length tvs GHC.Base.==
                                  Data.Foldable.length tys)) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/types/TyCoRep.hs")
          #1933)
    else substCo (zipTvSubst tvs tys).

Definition substForAllCoBndr
   : TCvSubst -> TyVar -> Coercion -> (TCvSubst * TyVar * Coercion)%type :=
  fun subst => substForAllCoBndrCallback false (substCo subst) subst.

Definition substCos `{(GHC.Stack.CallStack)}
   : TCvSubst -> list Coercion -> list Coercion :=
  fun subst cos =>
    if isEmptyTCvSubst subst : bool then cos else
    checkValidSubst subst nil cos (GHC.Base.map (subst_co subst) cos).

Definition expandTypeSynonyms : Type_ -> Type_ :=
  fun ty =>
    let in_scope := VarEnv.mkInScopeSet (tyCoVarsOfType ty) in
    let fix go arg_1__ arg_2__
              := match arg_1__, arg_2__ with
                 | subst, TyConApp tc tys =>
                     let expanded_tys := (GHC.Base.map (go subst) tys) in
                     match TyCon.expandSynTyCon_maybe tc expanded_tys with
                     | Some (pair (pair tenv rhs) tys') =>
                         let subst' := mkTvSubst in_scope (VarEnv.mkVarEnv tenv) in
                         mkAppTys (go subst' rhs) tys'
                     | _ => TyConApp tc expanded_tys
                     end
                 | _, LitTy l => LitTy l
                 | subst, TyVarTy tv => substTyVar subst tv
                 | subst, AppTy t1 t2 => mkAppTy (go subst t1) (go subst t2)
                 | subst, ForAllTy (Anon arg) res => mkFunTy (go subst arg) (go subst res)
                 | subst, ForAllTy (Named tv vis) t =>
                     let 'pair subst' tv' := substTyVarBndrCallback go subst tv in
                     ForAllTy (Named tv' vis) (go subst' t)
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
                 end in
    let go_prov :=
      fun arg_36__ arg_37__ =>
        match arg_36__, arg_37__ with
        | _, UnsafeCoerceProv => UnsafeCoerceProv
        | subst, PhantomProv co => PhantomProv (go_co subst co)
        | subst, ProofIrrelProv co => ProofIrrelProv (go_co subst co)
        | _, (PluginProv _ as p) => p
        | _, HoleProv h =>
            Panic.panicStr (GHC.Base.hs_string__ "expandTypeSynonyms hit a hole")
            (Panic.noString h)
        end in
    let go_cobndr :=
      fun subst => substForAllCoBndrCallback false (go_co subst) subst in
    go (mkEmptyTCvSubst in_scope) ty.

Definition mapCoercion {m} {env} `{GHC.Base.Applicative m} `{GHC.Base.Monad m}
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
                                   tybinder env tv Invisible GHC.Base.>>= cont_9__)
                            | CoVarCo cv => covar env cv
                            | AxiomInstCo ax i args =>
                                mkaxiominstco ax i Data.Functor.<$> Data.Traversable.mapM go args
                            | UnivCo (HoleProv hole) r t1 t2 => cohole env hole r t1 t2
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
                 fun arg_26__ =>
                   match arg_26__ with
                   | UnsafeCoerceProv => GHC.Base.return_ UnsafeCoerceProv
                   | PhantomProv co => PhantomProv Data.Functor.<$> go co
                   | ProofIrrelProv co => ProofIrrelProv Data.Functor.<$> go co
                   | (PluginProv _ as p) => GHC.Base.return_ p
                   | HoleProv _ => Panic.panic (GHC.Base.hs_string__ "mapCoercion")
                   end in
               go co
           end.

Definition mapType {m} {env} `{GHC.Base.Applicative m} `{GHC.Base.Monad m}
   : TyCoMapper env m -> env -> Type_ -> m Type_ :=
  fix mapType arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | (TyCoMapper smart tyvar _ _ tybinder as mapper), env, ty =>
               let 'pair (pair (pair mktyconapp mkappty) mkcastty) mkfunty := (if smart : bool
                                                                               then pair (pair (pair mkTyConApp mkAppTy)
                                                                                               mkCastTy) mkFunTy else
                                                                               pair (pair (pair TyConApp AppTy) CastTy)
                                                                                    (ForAllTy GHC.Base.∘ Anon)) in
               let fix go arg_5__
                         := match arg_5__ with
                            | TyVarTy tv => tyvar env tv
                            | AppTy t1 t2 => (mkappty Data.Functor.<$> go t1) GHC.Base.<*> go t2
                            | (TyConApp _ nil as t) => GHC.Base.return_ t
                            | TyConApp tc tys => mktyconapp tc Data.Functor.<$> Data.Traversable.mapM go tys
                            | ForAllTy (Anon arg) res =>
                                (mkfunty Data.Functor.<$> go arg) GHC.Base.<*> go res
                            | ForAllTy (Named tv vis) inner =>
                                let cont_11__ arg_12__ :=
                                  let 'pair env' tv' := arg_12__ in
                                  mapType mapper env' inner GHC.Base.>>=
                                  (fun inner' => GHC.Base.return_ (ForAllTy (Named tv' vis) inner')) in
                                tybinder env tv vis GHC.Base.>>= cont_11__
                            | (LitTy _ as ty) => GHC.Base.return_ ty
                            | CastTy ty co =>
                                (mkcastty Data.Functor.<$> go ty) GHC.Base.<*> mapCoercion mapper env co
                            | CoercionTy co => CoercionTy Data.Functor.<$> mapCoercion mapper env co
                            end in
               go ty
           end.

Definition extendLiftingContextEx
   : LiftingContext -> list (TyVar * Type_)%type -> LiftingContext :=
  fix extendLiftingContextEx arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | lc, nil => lc
           | (LC subst env as lc), cons (pair v ty) rest =>
               let lc' :=
                 LC (extendTCvInScopeSet subst (tyCoVarsOfType ty)) (VarEnv.extendVarEnv env v
                                                                     (mkSymCo (mkCoherenceCo (mkNomReflCo ty)
                                                                                             (ty_co_subst lc
                                                                                              Core.Nominal (tyVarKind
                                                                                                            v))))) in
               extendLiftingContextEx lc' rest
           end.

Definition liftCoSubstVarBndr
   : LiftingContext -> TyVar -> (LiftingContext * TyVar * Coercion)%type :=
  fun lc tv =>
    let callback := fun lc' ty' => pair (ty_co_subst lc' Core.Nominal ty') tt in
    let 'pair (pair (pair lc' tv') h) _ := liftCoSubstVarBndrCallback callback lc
                                             tv in
    pair (pair lc' tv') h.

Definition liftCoSubstWithEx
   : Core.Role ->
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

(* Translating `ty_co_subst' failed: using a record pattern for the unknown
   constructor `LitTy' unsupported *)

Definition zapLiftingContext : LiftingContext -> LiftingContext :=
  fun arg_0__ =>
    let 'LC subst _ := arg_0__ in
    LC (zapTCvSubst subst) VarEnv.emptyVarEnv.

(* Unbound variables:
     CoVar Coercion CoercionN Eq Gt Id KindCoercion KindOrType Lt None Some TCvSubst
     TyVar Type_ Var andb applyRoles bool cmpType cmpTypeX coVarsOfCo coVarsOfCos
     coVarsOfProv coVarsOfTypes coercionType comparison cons coreView
     coreViewOneStarKind downgradeRole downgradeRole_maybe enumFrom enumFromTo eqType
     error false go_co go_cobndr go_cos go_prov go_s go_tc gos id isInvisibleBinder
     isLiftedTypeKind isPredTy isVisibleBinder list mapType mkAppCo mkAppCos
     mkCoercionType mkInstCo mkKindCo mkLRCo mkNthCo mkPhantomCo mkPrimEqPred
     mkReprPrimEqPred mkSubCo mkTyConAppCo mkUnivCo negb nil op_zt__ option orb pair
     partitionInvisibles piResultTy piResultTys pprForAll pprKind pprTcApp pprTcAppTy
     pprTcApp_help pprThetaArrowTy pprTvBndr pprTvBndrNoParens pprTyList pprTyTcApp
     pprType ppr_forall_type ppr_fun_tail ppr_sigma_type ppr_tv_bndrs ppr_type
     provSize seqCos seqProv seqType seqTypes splitAppTy splitAppTy_maybe
     splitForAllTy_maybe splitTyConApp_maybe substCoUnchecked substCoWithUnchecked
     substForAllCoBndrUnchecked substTy substTyUnchecked substTyVarBndrCallback
     substTyVarBndrUnchecked subst_co subst_ty suppressInvisibles tidyCos
     tidyFreeTyCoVars tidyKind tidyOpenTyCoVars tidyTyCoVarBndr tidyTyVarOcc tidyType
     tidyTypes toPhantomCo true tt tyCoFVsOfCo tyCoFVsOfCos tyCoFVsOfProv
     tyCoFVsOfType tyCoFVsOfTypes tyConAppArgN tyConAppArgs_maybe tyConAppTyCon
     tyConAppTyCon_maybe typeKind typeSize unit BasicTypes.Arity
     BasicTypes.ConstraintTuple BasicTypes.RepArity BasicTypes.TupleSort
     BasicTypes.UnboxedTuple BasicTypes.tupleParens Class.Class Class.classTyCon
     CoAxiom.coAxBranchCoVars CoAxiom.coAxBranchLHS CoAxiom.coAxBranchRHS
     CoAxiom.coAxBranchRoles CoAxiom.coAxBranchTyVars CoAxiom.coAxiomArity
     CoAxiom.coAxiomNthBranch CoAxiom.coAxiomRole CoAxiom.coAxiomTyCon
     CoAxiom.coaxrName CoAxiom.toBranchedAxiom ConLike.ConLike ConLike.PatSynCon
     ConLike.RealDataCon Control.Arrow.first Control.Arrow.second Control.Monad.foldM
     Control.Monad.guard Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     Core.BranchIndex Core.Branched Core.CoAxBranch Core.CoAxiom Core.CoAxiomRule
     Core.Nominal Core.Phantom Core.Representational Core.Role Core.TcTyVarDetails
     Core.TyCon Core.Unbranched Data.Either.Either Data.Either.Left Data.Either.Right
     Data.Foldable.all Data.Foldable.and Data.Foldable.any Data.Foldable.concatMap
     Data.Foldable.foldMap Data.Foldable.foldl Data.Foldable.foldr
     Data.Foldable.length Data.Foldable.null Data.Foldable.sum Data.Function.on
     Data.Functor.op_zlzdzg__ Data.Maybe.isJust Data.Maybe.mapMaybe
     Data.OldList.partition Data.Traversable.mapAccumL Data.Traversable.mapM
     Data.Traversable.sequenceA Data.Traversable.traverse Data.Tuple.fst
     Data.Tuple.snd Data.Tuple.uncurry DataCon.DataCon DataCon.dataConExTyBinders
     DataCon.dataConFullSig DataCon.dataConTyCon DataCon.dataConUnivTyBinders
     DataCon.filterEqSpec Deriving.op_zdcon2tagzuFe4fHaknkFc7AP9msRFEWZZ__
     Deriving.op_zdcon2tagzug5QILjRA04KRgR1r4UStZZ__ Digraph.graphFromEdgedVertices
     Digraph.topologicalSortG DynFlags.DynFlags DynFlags.Opt_PrintEqualityRelations
     DynFlags.Opt_PrintExplicitCoercions DynFlags.Opt_PrintExplicitForalls
     DynFlags.Opt_PrintExplicitKinds DynFlags.Opt_PrintExplicitRuntimeReps
     DynFlags.gopt FV.FV FV.delFV FV.emptyFV FV.fvDVarSet FV.fvVarList FV.fvVarSet
     FV.mapUnionFV FV.mkFVs FV.unionFV FV.unitFV FastString.FastString
     GHC.Base.Applicative GHC.Base.Eq_ GHC.Base.Monad GHC.Base.Ord GHC.Base.String
     GHC.Base.Synonym GHC.Base.compare GHC.Base.flip GHC.Base.fmap GHC.Base.id
     GHC.Base.map GHC.Base.mappend GHC.Base.mempty GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zgze__ GHC.Base.op_zgzg__
     GHC.Base.op_zgzgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Base.op_zlztzg__
     GHC.Base.op_zsze__ GHC.Base.pure GHC.Base.return_ GHC.Err.error GHC.IORef.IORef
     GHC.List.drop GHC.List.dropWhile GHC.List.op_znzn__ GHC.List.repeat
     GHC.List.reverse GHC.List.span GHC.List.splitAt GHC.List.take GHC.List.zip
     GHC.List.zipWith GHC.Num.Int GHC.Num.Integer GHC.Num.fromInteger GHC.Num.op_zm__
     GHC.Num.op_zp__ GHC.Prim.op_tagToEnumzh__ GHC.Prim.op_zezezh__
     GHC.Prim.op_zgzezh__ GHC.Prim.op_zgzh__ GHC.Prim.op_zlzezh__ GHC.Prim.op_zlzh__
     GHC.Prim.seq GHC.Real.div GHC.Show.show GHC.Stack.CallStack IdInfo.IdDetails
     IdInfo.IdInfo IdInfo.coVarDetails IdInfo.isCoVarDetails IdInfo.pprIdDetails
     IdInfo.vanillaIdInfo Kind.isConstraintKind Kind.isStarKindSynonymTyCon
     ListSetOps.getNth Maybes.orElse Name.Name Name.getName Name.getOccName
     Name.isSystemName Name.nameOccName Name.nameUnique Name.setNameUnique
     Name.tidyNameOcc NameEnv.NameEnv NameEnv.emptyNameEnv NameEnv.plusNameEnv
     NameEnv.unitNameEnv OccName.initTidyOccEnv OccName.isSymOcc OccName.mkTyVarOcc
     OccName.mkVarOcc OccName.occNameString OccName.parenSymOcc OccName.tidyOccName
     Outputable.PprStyle Outputable.SDoc Outputable.arrow Outputable.assertPprPanic
     Outputable.braces Outputable.brackets Outputable.char Outputable.colon
     Outputable.comma Outputable.darrow Outputable.dcolon Outputable.debugStyle
     Outputable.dot Outputable.dumpStyle Outputable.empty Outputable.forAllLit
     Outputable.fsep Outputable.ftext Outputable.getPprStyle Outputable.hang
     Outputable.hsep Outputable.int Outputable.integer Outputable.interpp'SP
     Outputable.op_zdzd__ Outputable.op_zlzg__ Outputable.paBrackets
     Outputable.parens Outputable.ppWhen Outputable.pprInfixVar Outputable.pprTrace
     Outputable.pprWithCommas Outputable.punctuate Outputable.quotes
     Outputable.sdocWithDynFlags Outputable.sep Outputable.space
     Outputable.underscore Outputable.unicodeSyntax Outputable.vbar Outputable.vcat
     Pair.Mk_Pair Pair.Pair Pair.pFst Pair.pSnd Panic.assertPanic Panic.noString
     Panic.panic Panic.panicStr Panic.warnPprTrace PrelNames.consDataConKey
     PrelNames.eqPrimTyConKey PrelNames.eqReprPrimTyConKey PrelNames.eqTyConKey
     PrelNames.errorMessageTypeErrorFamKey PrelNames.errorMessageTypeErrorFamName
     PrelNames.funTyConKey PrelNames.heqTyConKey PrelNames.ipClassKey
     PrelNames.listTyConKey PrelNames.nilDataConKey PrelNames.parrTyConKey
     PrelNames.ptrRepLiftedDataConKey PrelNames.ptrRepUnliftedDataConKey
     PrelNames.runtimeRepTyConKey PrelNames.starKindTyConKey PrelNames.tYPETyConKey
     PrelNames.typeErrorAppendDataConName PrelNames.typeErrorShowTypeDataConName
     PrelNames.typeErrorTextDataConName PrelNames.typeErrorVAppendDataConName
     PrelNames.unicodeStarKindTyConKey PrelNames.unliftedTypeKindTyConKey
     StaticFlags.opt_PprStyle_Debug TcType.pprTcTyVarDetails TcType.vanillaSkolemTv
     TyCon.PrimRep TyCon.PtrRep TyCon.RecTcChecker TyCon.RuntimeRep TyCon.checkRecTc
     TyCon.expandSynTyCon_maybe TyCon.initRecTc TyCon.isAlgTyCon TyCon.isClassTyCon
     TyCon.isDataFamilyTyCon TyCon.isFamilyTyCon TyCon.isFunTyCon TyCon.isNewTyCon
     TyCon.isPrimTyCon TyCon.isPromotedDataCon_maybe TyCon.isTupleTyCon
     TyCon.isUnboxedTupleTyCon TyCon.isUnliftedTyCon TyCon.isVoidRep
     TyCon.mightBeUnsaturatedTyCon TyCon.newTyConEtadRhs TyCon.pprPromotionQuote
     TyCon.tyConArity TyCon.tyConBinders TyCon.tyConClass_maybe TyCon.tyConDataCons
     TyCon.tyConFamInst_maybe TyCon.tyConKind TyCon.tyConName TyCon.tyConResKind
     TyCon.tyConRoles TyCon.tyConRuntimeRepInfo TyCon.tyConTuple_maybe
     TyCon.tyConTyVars TyCon.tyConUnique TyCon.unwrapNewTyConEtad_maybe
     TysPrim.eqPhantPrimTyCon TysPrim.eqPrimTyCon TysPrim.eqReprPrimTyCon
     TysPrim.funTyCon TysWiredIn.liftedTypeKind TysWiredIn.listTyCon
     TysWiredIn.typeNatKind TysWiredIn.typeSymbolKind UniqFM.delListFromUFM_Directly
     UniqSupply.UniqSupply UniqSupply.takeUniqFromSupply Unique.Unique Unique.getKey
     Unique.getUnique Unique.hasKey Unique.mkUniqueGrimily Unique.nonDetCmpUnique
     Util.chkAppend Util.debugIsOn Util.equalLength Util.foldl2 Util.isEqual
     Util.leLength Util.lengthAtLeast Util.lengthExceeds Util.lengthIs
     Util.partitionWith Util.seqList Util.snocView Util.spanEnd Util.splitAtList
     Util.takeList Util.thenCmp Util.zipEqual VarEnv.CoVarEnv VarEnv.InScopeSet
     VarEnv.RnEnv2 VarEnv.TidyEnv VarEnv.TyVarEnv VarEnv.VarEnv VarEnv.delVarEnv
     VarEnv.elemInScopeSet VarEnv.elemVarEnv VarEnv.emptyInScopeSet
     VarEnv.emptyTidyEnv VarEnv.emptyVarEnv VarEnv.extendInScopeSet
     VarEnv.extendInScopeSetList VarEnv.extendInScopeSetSet VarEnv.extendVarEnv
     VarEnv.intersectsVarEnv VarEnv.isEmptyVarEnv VarEnv.lookupVarEnv
     VarEnv.lookupVarEnv_NF VarEnv.mapVarEnv VarEnv.mkInScopeSet VarEnv.mkRnEnv2
     VarEnv.mkVarEnv VarEnv.mkVarEnv_Directly VarEnv.plusVarEnv VarEnv.rnBndr2
     VarEnv.rnOccL VarEnv.rnOccR VarEnv.unionInScope VarEnv.uniqAway
     VarEnv.varEnvElts VarEnv.varEnvKeys VarEnv.varEnvToList VarEnv.varSetInScope
     VarSet.CoVarSet VarSet.DTyCoVarSet VarSet.DTyVarSet VarSet.DVarSet
     VarSet.TyCoVarSet VarSet.TyVarSet VarSet.VarSet VarSet.dVarSetElems
     VarSet.delVarSet VarSet.elemVarSet VarSet.emptyVarSet VarSet.extendVarSet
     VarSet.isEmptyVarSet VarSet.mapUnionVarSet VarSet.minusVarSet VarSet.mkVarSet
     VarSet.subVarSet VarSet.unionVarSet VarSet.unitVarSet VarSet.varSetElems
*)
