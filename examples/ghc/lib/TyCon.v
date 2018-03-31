(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Core.
Require Name.
Require Class.
Require Var.

(* Record selectors *)
Parameter tyConName    : TyCon -> Name.Name.
Parameter tyConKind    : TyCon -> Kind.
Parameter tyConResKind : TyCon -> Kind.
Parameter tyConBinders : TyCon -> list TyBinder.
Parameter tyConTyVars  : TyCon -> list TyVar.

Parameter isLiftedTypeKindTyConName : Name.Name -> bool.

(* Need to skip tyConAssoc_maybe *)
Parameter isTyConAssoc : TyCon -> bool.
Parameter makeTyConAbstract : TyCon -> TyCon.
Parameter mkClassTyCon : Name.Name -> list TyBinder -> list TyVar
                          -> list Role -> AlgTyConRhs -> Class.Class
                          -> BasicTypes.RecFlag -> Name.Name -> TyCon.
Parameter algTcFields : TyCon -> FieldLabel.FieldLabelEnv.

(* record label flLabel is not qualified. *)
Parameter fieldsOfAlgTcRhs : AlgTyConRhs -> FieldLabel.FieldLabelEnv.

(* Converted imports: *)

Require BasicTypes.
Require Constants.
Require Coq.Lists.List.
Require Core.
Require CoreType.
Require Data.Foldable.
Require DataCon.
Require DynFlags.
Require FastStringEnv.
Require FieldLabel.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require Maybes.
Require Module.
Require Name.
Require NameEnv.
Require OccName.
Require Panic.
Require PrelNames.
Require TysWiredIn.
Require UniqSet.
Require Unique.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import GHC.Prim.Notations.

(* Converted type declarations: *)

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
  := NamedTCB : CoreType.ArgFlag -> TyConBndrVis
  |  AnonTCB : TyConBndrVis.

Definition TyConBinder :=
  (CoreType.TyVarBndr CoreType.TyVar TyConBndrVis)%type.

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

Inductive FamTyConFlav : Type
  := DataFamilyTyCon : Core.TyConRepName -> FamTyConFlav
  |  OpenSynFamilyTyCon : FamTyConFlav
  |  ClosedSynFamilyTyCon : (option (Core.CoAxiom Core.Branched)) -> FamTyConFlav
  |  AbstractClosedSynFamilyTyCon : FamTyConFlav
  |  BuiltInSynFamTyCon : Core.BuiltInSynFamily -> FamTyConFlav.

Inductive AlgTyConRhs : Type
  := AbstractTyCon : AlgTyConRhs
  |  DataTyCon : list DataCon.DataCon -> bool -> AlgTyConRhs
  |  TupleTyCon : DataCon.DataCon -> BasicTypes.TupleSort -> AlgTyConRhs
  |  SumTyCon : list DataCon.DataCon -> AlgTyConRhs
  |  NewTyCon
   : DataCon.DataCon ->
     CoreType.Type_ ->
     (list CoreType.TyVar * CoreType.Type_)%type ->
     Core.CoAxiom Core.Unbranched -> AlgTyConRhs.

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

Definition data_cons (arg_1__ : AlgTyConRhs) :=
  match arg_1__ with
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

Definition is_enum (arg_2__ : AlgTyConRhs) :=
  match arg_2__ with
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

Definition nt_co (arg_3__ : AlgTyConRhs) :=
  match arg_3__ with
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

Definition nt_etad_rhs (arg_4__ : AlgTyConRhs) :=
  match arg_4__ with
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

Definition nt_rhs (arg_5__ : AlgTyConRhs) :=
  match arg_5__ with
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

Definition tup_sort (arg_6__ : AlgTyConRhs) :=
  match arg_6__ with
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
(* Converted value declarations: *)

(* Translating `instance Outputable__AlgTyConFlav' failed: using a record
   pattern for the unknown constructor `VanillaAlgTyCon' unsupported *)

Local Definition Eq___TyCon_op_zeze__ : Core.TyCon -> Core.TyCon -> bool :=
  fun a b => match Ord__TyCon_compare a b with | Eq => true | _ => false end.

Local Definition Eq___TyCon_op_zsze__ : Core.TyCon -> Core.TyCon -> bool :=
  fun a b =>
    let scrut_0__ := Ord__TyCon_compare a b in
    match scrut_0__ with
    | Eq => false
    | _ => true
    end.

Program Instance Eq___TyCon : GHC.Base.Eq_ Core.TyCon :=
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

Local Definition Eq___Injectivity_op_zeze__
   : Core.Injectivity -> Core.Injectivity -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NotInjective, NotInjective => true
    | Injective a1, Injective b1 => ((a1 GHC.Base.== b1))
    | _, _ => false
    end.

Local Definition Eq___Injectivity_op_zsze__
   : Core.Injectivity -> Core.Injectivity -> bool :=
  fun x y => negb (Eq___Injectivity_op_zeze__ x y).

Program Instance Eq___Injectivity : GHC.Base.Eq_ Core.Injectivity :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___Injectivity_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___Injectivity_op_zsze__ |}.

Axiom algTyConRhs : forall {A : Type}, A.

(* Translating `algTyConRhs' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Definition checkRecTc : RecTcChecker -> Core.TyCon -> option RecTcChecker :=
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

Axiom expandSynTyCon_maybe : forall {A : Type}, A.

(* Translating `expandSynTyCon_maybe' failed: using a record pattern for the
   unknown constructor `SynonymTyCon' unsupported *)

Axiom famTyConFlav_maybe : forall {A : Type}, A.

(* Translating `famTyConFlav_maybe' failed: using a record pattern for the
   unknown constructor `FamilyTyCon' unsupported *)

Definition initRecTc : RecTcChecker :=
  RC #100 NameEnv.emptyNameEnv.

Axiom isAbstractTyCon : forall {A : Type}, A.

(* Translating `isAbstractTyCon' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom isAlgTyCon : forall {A : Type}, A.

Definition tyConFieldLabelEnv : Core.TyCon -> FieldLabel.FieldLabelEnv :=
  fun tc =>
    if isAlgTyCon tc : bool then algTcFields tc else
    FastStringEnv.emptyDFsEnv.

Definition lookupTyConFieldLabel
   : FieldLabel.FieldLabelString -> Core.TyCon -> option FieldLabel.FieldLabel :=
  fun lbl tc => FastStringEnv.lookupDFsEnv (tyConFieldLabelEnv tc) lbl.

Definition tyConFieldLabels : Core.TyCon -> list FieldLabel.FieldLabel :=
  fun tc => FastStringEnv.dFsEnvElts (tyConFieldLabelEnv tc).

(* Translating `isAlgTyCon' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom isBoxedTupleTyCon : forall {A : Type}, A.

(* Translating `isBoxedTupleTyCon' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom isBuiltInSynFamTyCon_maybe : forall {A : Type}, A.

(* Translating `isBuiltInSynFamTyCon_maybe' failed: using a record pattern for
   the unknown constructor `FamilyTyCon' unsupported *)

Axiom isClassTyCon : forall {A : Type}, A.

(* Translating `isClassTyCon' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom isClosedSynFamilyTyConWithAxiom_maybe : forall {A : Type}, A.

(* Translating `isClosedSynFamilyTyConWithAxiom_maybe' failed: using a record
   pattern for the unknown constructor `FamilyTyCon' unsupported *)

Definition isDataFamFlav : FamTyConFlav -> bool :=
  fun arg_0__ => match arg_0__ with | DataFamilyTyCon _ => true | _ => false end.

Axiom isDataFamilyTyCon : forall {A : Type}, A.

(* Translating `isDataFamilyTyCon' failed: using a record pattern for the
   unknown constructor `FamilyTyCon' unsupported *)

Axiom isDataProductTyCon_maybe : forall {A : Type}, A.

(* Translating `isDataProductTyCon_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom isDataSumTyCon_maybe : forall {A : Type}, A.

(* Translating `isDataSumTyCon_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom isDataTyCon : forall {A : Type}, A.

(* Translating `isDataTyCon' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom isEnumerationTyCon : forall {A : Type}, A.

(* Translating `isEnumerationTyCon' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom isFamFreeTyCon : forall {A : Type}, A.

(* Translating `isFamFreeTyCon' failed: using a record pattern for the unknown
   constructor `SynonymTyCon' unsupported *)

Axiom isFamInstTyCon : forall {A : Type}, A.

(* Translating `isFamInstTyCon' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom isFamilyTyCon : forall {A : Type}, A.

(* Translating `isFamilyTyCon' failed: using a record pattern for the unknown
   constructor `FamilyTyCon' unsupported *)

Axiom isFunTyCon : forall {A : Type}, A.

(* Translating `isFunTyCon' failed: using a record pattern for the unknown
   constructor `FunTyCon' unsupported *)

Axiom isGadtSyntaxTyCon : forall {A : Type}, A.

(* Translating `isGadtSyntaxTyCon' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

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

Axiom isGenerativeTyCon : forall {A : Type}, A.

(* Translating `isGenerativeTyCon' failed: using a record pattern for the
   unknown constructor `FamilyTyCon' unsupported *)

Axiom isImplicitTyCon : forall {A : Type}, A.

(* Translating `isImplicitTyCon' failed: using a record pattern for the unknown
   constructor `FunTyCon' unsupported *)

Axiom isInjectiveTyCon : forall {A : Type}, A.

(* Translating `isInjectiveTyCon' failed: using a record pattern for the unknown
   constructor `FunTyCon' unsupported *)

Definition isNamedTyConBinder : TyConBinder -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreType.TvBndr _ (NamedTCB _) => true
    | _ => false
    end.

Axiom isNewTyCon : forall {A : Type}, A.

(* Translating `isNewTyCon' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom isNoParent : forall {A : Type}, A.

(* Translating `isNoParent' failed: using a record pattern for the unknown
   constructor `VanillaAlgTyCon' unsupported *)

Axiom isOpenFamilyTyCon : forall {A : Type}, A.

(* Translating `isOpenFamilyTyCon' failed: using a record pattern for the
   unknown constructor `FamilyTyCon' unsupported *)

Axiom isOpenTypeFamilyTyCon : forall {A : Type}, A.

(* Translating `isOpenTypeFamilyTyCon' failed: using a record pattern for the
   unknown constructor `FamilyTyCon' unsupported *)

Axiom isPrimTyCon : forall {A : Type}, A.

(* Translating `isPrimTyCon' failed: using a record pattern for the unknown
   constructor `PrimTyCon' unsupported *)

Axiom isProductTyCon : forall {A : Type}, A.

(* Translating `isProductTyCon' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom isPromotedDataCon : forall {A : Type}, A.

(* Translating `isPromotedDataCon' failed: using a record pattern for the
   unknown constructor `PromotedDataCon' unsupported *)

Axiom isPromotedDataCon_maybe : forall {A : Type}, A.

(* Translating `isPromotedDataCon_maybe' failed: using a record pattern for the
   unknown constructor `PromotedDataCon' unsupported *)

Axiom isTauTyCon : forall {A : Type}, A.

(* Translating `isTauTyCon' failed: using a record pattern for the unknown
   constructor `SynonymTyCon' unsupported *)

Axiom isTcLevPoly : forall {A : Type}, A.

(* Translating `isTcLevPoly' failed: using a record pattern for the unknown
   constructor `FunTyCon' unsupported *)

Axiom isTcTyCon : forall {A : Type}, A.

(* Translating `isTcTyCon' failed: using a record pattern for the unknown
   constructor `TcTyCon' unsupported *)

Axiom isTupleTyCon : forall {A : Type}, A.

Definition isPromotedTupleTyCon : Core.TyCon -> bool :=
  fun tyCon =>
    match isPromotedDataCon_maybe tyCon with
    | Some dataCon =>
        if isTupleTyCon (DataCon.dataConTyCon dataCon) : bool then true else
        false
    | _ => false
    end.

(* Translating `isTupleTyCon' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom isTyConWithSrcDataCons : forall {A : Type}, A.

(* Translating `isTyConWithSrcDataCons' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom isTypeFamilyTyCon : forall {A : Type}, A.

(* Translating `isTypeFamilyTyCon' failed: using a record pattern for the
   unknown constructor `FamilyTyCon' unsupported *)

Axiom isTypeSynonymTyCon : forall {A : Type}, A.

(* Translating `isTypeSynonymTyCon' failed: using a record pattern for the
   unknown constructor `SynonymTyCon' unsupported *)

Axiom isUnboxedSumTyCon : forall {A : Type}, A.

(* Translating `isUnboxedSumTyCon' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom isUnboxedTupleTyCon : forall {A : Type}, A.

(* Translating `isUnboxedTupleTyCon' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom isUnliftedTyCon : forall {A : Type}, A.

(* Translating `isUnliftedTyCon' failed: using a record pattern for the unknown
   constructor `PrimTyCon' unsupported *)

Axiom isVanillaAlgTyCon : forall {A : Type}, A.

(* Translating `isVanillaAlgTyCon' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Definition isVisibleTcbVis : TyConBndrVis -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | NamedTCB vis => CoreType.isVisibleArgFlag vis
    | AnonTCB => true
    end.

Definition isVisibleTyConBinder {tv}
   : CoreType.TyVarBndr tv TyConBndrVis -> bool :=
  fun arg_0__ =>
    let 'CoreType.TvBndr _ tcb_vis := arg_0__ in
    isVisibleTcbVis tcb_vis.

Definition isInvisibleTyConBinder {tv}
   : CoreType.TyVarBndr tv TyConBndrVis -> bool :=
  fun tcb => negb (isVisibleTyConBinder tcb).

Definition tyConVisibleTyVars : Core.TyCon -> list CoreType.TyVar :=
  fun tc =>
    let cont_0__ arg_1__ :=
      match arg_1__ with
      | CoreType.TvBndr tv vis =>
          if isVisibleTcbVis vis : bool then cons tv nil else
          nil
      | _ => nil
      end in
    Coq.Lists.List.flat_map cont_0__ (tyConBinders tc).

Definition isVoidRep : PrimRep -> bool :=
  fun arg_0__ => match arg_0__ with | VoidRep => true | _other => false end.

Axiom mkAlgTyCon : forall {A : Type}, A.

(* Translating `mkAlgTyCon' failed: creating a record with the unknown
   constructor `AlgTyCon' unsupported *)

Definition mkAnonTyConBinder : CoreType.TyVar -> TyConBinder :=
  fun tv => CoreType.TvBndr tv AnonTCB.

Definition mkAnonTyConBinders : list CoreType.TyVar -> list TyConBinder :=
  fun tvs => GHC.Base.map mkAnonTyConBinder tvs.

Axiom mkFamilyTyCon : forall {A : Type}, A.

(* Translating `mkFamilyTyCon' failed: creating a record with the unknown
   constructor `FamilyTyCon' unsupported *)

Axiom mkFunTyCon : forall {A : Type}, A.

(* Translating `mkFunTyCon' failed: creating a record with the unknown
   constructor `FunTyCon' unsupported *)

Definition mkNamedTyConBinder
   : CoreType.ArgFlag -> CoreType.TyVar -> TyConBinder :=
  fun vis tv => CoreType.TvBndr tv (NamedTCB vis).

Definition mkNamedTyConBinders
   : CoreType.ArgFlag -> list CoreType.TyVar -> list TyConBinder :=
  fun vis tvs => GHC.Base.map (mkNamedTyConBinder vis) tvs.

Axiom mkPrimTyCon' : forall {A : Type}, A.

Definition mkKindTyCon
   : Name.Name ->
     list TyConBinder ->
     CoreType.Kind -> list Core.Role -> Name.Name -> Core.TyCon :=
  fun name binders res_kind roles rep_nm =>
    let tc := mkPrimTyCon' name binders res_kind roles false (Some rep_nm) in tc.

(* Translating `mkPrimTyCon'' failed: creating a record with the unknown
   constructor `PrimTyCon' unsupported *)

Axiom mkPromotedDataCon : forall {A : Type}, A.

(* Translating `mkPromotedDataCon' failed: creating a record with the unknown
   constructor `PromotedDataCon' unsupported *)

Axiom mkSumTyCon : forall {A : Type}, A.

(* Translating `mkSumTyCon' failed: creating a record with the unknown
   constructor `AlgTyCon' unsupported *)

Axiom mkSynonymTyCon : forall {A : Type}, A.

(* Translating `mkSynonymTyCon' failed: creating a record with the unknown
   constructor `SynonymTyCon' unsupported *)

Axiom mkTcTyCon : forall {A : Type}, A.

(* Translating `mkTcTyCon' failed: creating a record with the unknown
   constructor `TcTyCon' unsupported *)

Axiom mkTupleTyCon : forall {A : Type}, A.

(* Translating `mkTupleTyCon' failed: creating a record with the unknown
   constructor `AlgTyCon' unsupported *)

Definition mkTyConKind : list TyConBinder -> CoreType.Kind -> CoreType.Kind :=
  fun bndrs res_kind =>
    let mk : TyConBinder -> CoreType.Kind -> CoreType.Kind :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | CoreType.TvBndr tv AnonTCB, k =>
            TysWiredIn.mkFunKind (CoreType.tyVarKind tv) k
        | CoreType.TvBndr tv (NamedTCB vis), k => TysWiredIn.mkForAllKind tv vis k
        end in
    Data.Foldable.foldr mk res_kind bndrs.

Axiom newTyConCo_maybe : forall {A : Type}, A.

Definition newTyConCo : Core.TyCon -> Core.CoAxiom Core.Unbranched :=
  fun tc =>
    match newTyConCo_maybe tc with
    | Some co => co
    | None => Panic.panicStr (GHC.Base.hs_string__ "newTyConCo") (Panic.noString tc)
    end.

(* Translating `newTyConCo_maybe' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom newTyConDataCon_maybe : forall {A : Type}, A.

(* Translating `newTyConDataCon_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom newTyConEtadArity : forall {A : Type}, A.

(* Translating `newTyConEtadArity' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom newTyConEtadRhs : forall {A : Type}, A.

(* Translating `newTyConEtadRhs' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom newTyConRhs : forall {A : Type}, A.

(* Translating `newTyConRhs' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom okParent : forall {A : Type}, A.

(* Translating `okParent' failed: using a record pattern for the unknown
   constructor `VanillaAlgTyCon' unsupported *)

Axiom pprPromotionQuote : forall {A : Type}, A.

(* Translating `pprPromotionQuote' failed: using a record pattern for the
   unknown constructor `PromotedDataCon' unsupported *)

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

Axiom synTyConDefn_maybe : forall {A : Type}, A.

(* Translating `synTyConDefn_maybe' failed: using a record pattern for the
   unknown constructor `SynonymTyCon' unsupported *)

Axiom synTyConRhs_maybe : forall {A : Type}, A.

(* Translating `synTyConRhs_maybe' failed: using a record pattern for the
   unknown constructor `SynonymTyCon' unsupported *)

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

Definition tyConBinderArgFlag : TyConBinder -> CoreType.ArgFlag :=
  fun arg_0__ =>
    match arg_0__ with
    | CoreType.TvBndr _ (NamedTCB vis) => vis
    | CoreType.TvBndr _ AnonTCB => CoreType.Required
    end.

Axiom tyConCType_maybe : forall {A : Type}, A.

(* Translating `tyConCType_maybe' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom tyConClass_maybe : forall {A : Type}, A.

(* Translating `tyConClass_maybe' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom tyConDataCons_maybe : forall {A : Type}, A.

Definition tyConDataCons : Core.TyCon -> list DataCon.DataCon :=
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

Definition isKindTyCon : Core.TyCon -> bool :=
  fun tc => UniqSet.elementOfUniqSet (Unique.getUnique tc) kindTyConKeys.

(* Translating `tyConDataCons_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom tyConFamInstSig_maybe : forall {A : Type}, A.

(* Translating `tyConFamInstSig_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom tyConFamInst_maybe : forall {A : Type}, A.

(* Translating `tyConFamInst_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom tyConFamilyCoercion_maybe : forall {A : Type}, A.

(* Translating `tyConFamilyCoercion_maybe' failed: using a record pattern for
   the unknown constructor `AlgTyCon' unsupported *)

Axiom tyConFamilyResVar_maybe : forall {A : Type}, A.

(* Translating `tyConFamilyResVar_maybe' failed: using a record pattern for the
   unknown constructor `FamilyTyCon' unsupported *)

Axiom tyConFamilySize : forall {A : Type}, A.

(* Translating `tyConFamilySize' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom tyConFamilySizeAtMost : forall {A : Type}, A.

(* Translating `tyConFamilySizeAtMost' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom tyConFlavour : forall {A : Type}, A.

Definition mightBeUnsaturatedTyCon : Core.TyCon -> bool :=
  tcFlavourCanBeUnsaturated GHC.Base.∘ tyConFlavour.

Definition makeRecoveryTyCon : Core.TyCon -> Core.TyCon :=
  fun tc =>
    mkTcTyCon (tyConName tc) (tyConBinders tc) (tyConResKind tc) nil (tyConFlavour
                                                                      tc).

(* Translating `tyConFlavour' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom tyConInjectivityInfo : forall {A : Type}, A.

(* Translating `tyConInjectivityInfo' failed: using a record pattern for the
   unknown constructor `FamilyTyCon' unsupported *)

Definition tyConRepModOcc
   : Module.Module -> OccName.OccName -> (Module.Module * OccName.OccName)%type :=
  fun tc_module tc_occ =>
    let rep_module :=
      if tc_module GHC.Base.== PrelNames.gHC_PRIM : bool then PrelNames.gHC_TYPES else
      tc_module in
    pair rep_module (OccName.mkTyConRepOcc tc_occ).

Definition mkPrelTyConRepName : Name.Name -> Core.TyConRepName :=
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
   : Name.Name ->
     list TyConBinder -> CoreType.Kind -> list Core.Role -> Core.TyCon :=
  fun name binders res_kind roles =>
    mkPrimTyCon' name binders res_kind roles true (Some (mkPrelTyConRepName name)).

Definition mkLiftedPrimTyCon
   : Name.Name ->
     list TyConBinder -> CoreType.Kind -> list Core.Role -> Core.TyCon :=
  fun name binders res_kind roles =>
    let rep_nm := mkPrelTyConRepName name in
    mkPrimTyCon' name binders res_kind roles false (Some rep_nm).

Axiom tyConRepName_maybe : forall {A : Type}, A.

(* Translating `tyConRepName_maybe' failed: using a record pattern for the
   unknown constructor `FunTyCon' unsupported *)

Axiom tyConRoles : forall {A : Type}, A.

(* Translating `tyConRoles' failed: using a record pattern for the unknown
   constructor `FunTyCon' unsupported *)

Axiom tyConRuntimeRepInfo : forall {A : Type}, A.

(* Translating `tyConRuntimeRepInfo' failed: using a record pattern for the
   unknown constructor `PromotedDataCon' unsupported *)

Axiom tyConSingleAlgDataCon_maybe : forall {A : Type}, A.

(* Translating `tyConSingleAlgDataCon_maybe' failed: using a record pattern for
   the unknown constructor `AlgTyCon' unsupported *)

Axiom tyConSingleDataCon_maybe : forall {A : Type}, A.

Definition tyConSingleDataCon : Core.TyCon -> DataCon.DataCon :=
  fun tc =>
    match tyConSingleDataCon_maybe tc with
    | Some c => c
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "tyConDataCon") (Panic.noString tc)
    end.

(* Translating `tyConSingleDataCon_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Definition tyConSkolem : Core.TyCon -> bool :=
  Name.isHoleName GHC.Base.∘ tyConName.

Axiom tyConStupidTheta : forall {A : Type}, A.

(* Translating `tyConStupidTheta' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom tyConTuple_maybe : forall {A : Type}, A.

(* Translating `tyConTuple_maybe' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Definition tyConTyVarBinders : list TyConBinder -> list CoreType.TyVarBinder :=
  fun tc_bndrs =>
    let mk_binder :=
      fun arg_0__ =>
        let 'CoreType.TvBndr tv tc_vis := arg_0__ in
        let vis :=
          match tc_vis with
          | AnonTCB => CoreType.Specified
          | NamedTCB CoreType.Required => CoreType.Specified
          | NamedTCB vis => vis
          end in
        CoreType.mkTyVarBinder vis tv in
    GHC.Base.map mk_binder tc_bndrs.

Axiom unwrapNewTyConEtad_maybe : forall {A : Type}, A.

(* Translating `unwrapNewTyConEtad_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom unwrapNewTyCon_maybe : forall {A : Type}, A.

(* Translating `unwrapNewTyCon_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Definition visibleDataCons : AlgTyConRhs -> list DataCon.DataCon :=
  fun arg_0__ =>
    match arg_0__ with
    | AbstractTyCon => nil
    | DataTyCon cs _ => cs
    | NewTyCon c _ _ _ => cons c nil
    | TupleTyCon c _ => cons c nil
    | SumTyCon cs => cs
    end.

(* Unbound variables:
     Injective None NotInjective Ord__TyCon_compare Some algTcFields andb bool cons
     false list negb nil op_zt__ option pair true tyConBinders tyConName tyConResKind
     BasicTypes.Boxity BasicTypes.TupleSort Constants.fLOAT_SIZE
     Constants.wORD64_SIZE Coq.Lists.List.flat_map Core.Branched
     Core.BuiltInSynFamily Core.CoAxiom Core.Injectivity Core.Role Core.TyCon
     Core.TyConRepName Core.Unbranched CoreType.ArgFlag CoreType.Kind
     CoreType.Required CoreType.Specified CoreType.TvBndr CoreType.TyVar
     CoreType.TyVarBinder CoreType.TyVarBndr CoreType.Type_ CoreType.isVisibleArgFlag
     CoreType.mkTyVarBinder CoreType.tyVarKind Data.Foldable.foldr DataCon.DataCon
     DataCon.dataConTyCon Deriving.op_zdcon2tagzuGDTzzQOFa1zzUIKOcsSgCJHI__
     DynFlags.DynFlags DynFlags.dOUBLE_SIZE DynFlags.wORD_SIZE
     FastStringEnv.dFsEnvElts FastStringEnv.emptyDFsEnv FastStringEnv.lookupDFsEnv
     FieldLabel.FieldLabel FieldLabel.FieldLabelEnv FieldLabel.FieldLabelString
     GHC.Base.Eq_ GHC.Base.map GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zgze__ GHC.Err.error GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zp__
     GHC.Num.op_zt__ GHC.Prim.op_tagToEnumzh__ GHC.Prim.op_zezezh__ Maybes.orElse
     Module.Module Name.Name Name.isHoleName Name.mkExternalName Name.nameModule
     Name.nameOccName Name.nameSrcSpan Name.nameUnique NameEnv.NameEnv
     NameEnv.emptyNameEnv NameEnv.extendNameEnv NameEnv.lookupNameEnv OccName.OccName
     OccName.isTcOcc OccName.mkTyConRepOcc Panic.noString Panic.panicStr
     PrelNames.constraintKindTyConKey PrelNames.gHC_PRIM PrelNames.gHC_TYPES
     PrelNames.liftedTypeKindTyConKey PrelNames.starKindTyConKey
     PrelNames.tYPETyConKey PrelNames.unicodeStarKindTyConKey TysWiredIn.mkForAllKind
     TysWiredIn.mkFunKind TysWiredIn.runtimeRepTyCon TysWiredIn.vecCountTyCon
     TysWiredIn.vecElemTyCon UniqSet.UniqSet UniqSet.elementOfUniqSet
     UniqSet.mkUniqSet UniqSet.unionManyUniqSets Unique.Unique
     Unique.dataConRepNameUnique Unique.getUnique Unique.tyConRepNameUnique
*)
