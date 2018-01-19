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

Definition error {a} `{Panic.Default a} := Panic.panic.

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
Require Core.
Require DataCon.
Require DynFlags.
Require FastStringEnv.
Require FieldLabel.
Require GHC.Base.
Require GHC.Num.
Require GHC.Real.
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

(* Converted type declarations: *)

Inductive RecTcChecker : Type := RC : GHC.Num.Int -> (NameEnv.NameEnv
                                      GHC.Num.Int) -> RecTcChecker.

Inductive PrimElemRep : Type := Int8ElemRep : PrimElemRep
                             |  Int16ElemRep : PrimElemRep
                             |  Int32ElemRep : PrimElemRep
                             |  Int64ElemRep : PrimElemRep
                             |  Word8ElemRep : PrimElemRep
                             |  Word16ElemRep : PrimElemRep
                             |  Word32ElemRep : PrimElemRep
                             |  Word64ElemRep : PrimElemRep
                             |  FloatElemRep : PrimElemRep
                             |  DoubleElemRep : PrimElemRep.

Inductive PrimRep : Type := VoidRep : PrimRep
                         |  PtrRep : PrimRep
                         |  IntRep : PrimRep
                         |  WordRep : PrimRep
                         |  Int64Rep : PrimRep
                         |  Word64Rep : PrimRep
                         |  AddrRep : PrimRep
                         |  FloatRep : PrimRep
                         |  DoubleRep : PrimRep
                         |  VecRep : GHC.Num.Int -> PrimElemRep -> PrimRep.

Inductive FamTyConFlav : Type := DataFamilyTyCon
                                : Core.TyConRepName -> FamTyConFlav
                              |  OpenSynFamilyTyCon : FamTyConFlav
                              |  ClosedSynFamilyTyCon : (option (Core.CoAxiom Core.Branched)) -> FamTyConFlav
                              |  AbstractClosedSynFamilyTyCon : FamTyConFlav
                              |  BuiltInSynFamTyCon : Core.BuiltInSynFamily -> FamTyConFlav.

Inductive AlgTyConRhs : Type := AbstractTyCon : bool -> AlgTyConRhs
                             |  DataTyCon : list DataCon.DataCon -> bool -> AlgTyConRhs
                             |  TupleTyCon : DataCon.DataCon -> BasicTypes.TupleSort -> AlgTyConRhs
                             |  NewTyCon : DataCon.DataCon -> Core.Type_ -> (list TyVar *
                                           Core.Type_)%type -> Core.CoAxiom Core.Unbranched -> AlgTyConRhs.

Definition data_con (arg_0__ : AlgTyConRhs) :=
  match arg_0__ with
    | AbstractTyCon _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `data_con' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
    | DataTyCon _ _ => error (GHC.Base.hs_string__
                             "Partial record selector: field `data_con' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
    | TupleTyCon data_con _ => data_con
    | NewTyCon data_con _ _ _ => data_con
  end.

Definition data_cons (arg_1__ : AlgTyConRhs) :=
  match arg_1__ with
    | AbstractTyCon _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `data_cons' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
    | DataTyCon data_cons _ => data_cons
    | TupleTyCon _ _ => error (GHC.Base.hs_string__
                              "Partial record selector: field `data_cons' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
    | NewTyCon _ _ _ _ => error (GHC.Base.hs_string__
                                "Partial record selector: field `data_cons' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

Definition is_enum (arg_2__ : AlgTyConRhs) :=
  match arg_2__ with
    | AbstractTyCon _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `is_enum' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
    | DataTyCon _ is_enum => is_enum
    | TupleTyCon _ _ => error (GHC.Base.hs_string__
                              "Partial record selector: field `is_enum' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
    | NewTyCon _ _ _ _ => error (GHC.Base.hs_string__
                                "Partial record selector: field `is_enum' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.

Definition nt_co (arg_3__ : AlgTyConRhs) :=
  match arg_3__ with
    | AbstractTyCon _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `nt_co' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
    | DataTyCon _ _ => error (GHC.Base.hs_string__
                             "Partial record selector: field `nt_co' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
    | TupleTyCon _ _ => error (GHC.Base.hs_string__
                              "Partial record selector: field `nt_co' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
    | NewTyCon _ _ _ nt_co => nt_co
  end.

Definition nt_etad_rhs (arg_4__ : AlgTyConRhs) :=
  match arg_4__ with
    | AbstractTyCon _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `nt_etad_rhs' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
    | DataTyCon _ _ => error (GHC.Base.hs_string__
                             "Partial record selector: field `nt_etad_rhs' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
    | TupleTyCon _ _ => error (GHC.Base.hs_string__
                              "Partial record selector: field `nt_etad_rhs' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
    | NewTyCon _ _ nt_etad_rhs _ => nt_etad_rhs
  end.

Definition nt_rhs (arg_5__ : AlgTyConRhs) :=
  match arg_5__ with
    | AbstractTyCon _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `nt_rhs' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
    | DataTyCon _ _ => error (GHC.Base.hs_string__
                             "Partial record selector: field `nt_rhs' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
    | TupleTyCon _ _ => error (GHC.Base.hs_string__
                              "Partial record selector: field `nt_rhs' has no match in constructor `TupleTyCon' of type `AlgTyConRhs'")
    | NewTyCon _ nt_rhs _ _ => nt_rhs
  end.

Definition tup_sort (arg_6__ : AlgTyConRhs) :=
  match arg_6__ with
    | AbstractTyCon _ => error (GHC.Base.hs_string__
                               "Partial record selector: field `tup_sort' has no match in constructor `AbstractTyCon' of type `AlgTyConRhs'")
    | DataTyCon _ _ => error (GHC.Base.hs_string__
                             "Partial record selector: field `tup_sort' has no match in constructor `DataTyCon' of type `AlgTyConRhs'")
    | TupleTyCon _ tup_sort => tup_sort
    | NewTyCon _ _ _ _ => error (GHC.Base.hs_string__
                                "Partial record selector: field `tup_sort' has no match in constructor `NewTyCon' of type `AlgTyConRhs'")
  end.
(* Converted value declarations: *)

(* Translating `instance Outputable.Outputable Core.AlgTyConFlav' failed: using
   a record pattern for the unknown constructor `VanillaAlgTyCon' unsupported *)

(* Translating `instance Outputable.Outputable TyCon.PrimRep' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance Outputable.Outputable TyCon.PrimElemRep' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

Local Definition Ord__TyCon_compare : Core.TyCon -> Core.TyCon -> comparison :=
  fun a b => GHC.Base.compare (Unique.getUnique a) (Unique.getUnique b).

Local Definition Ord__TyCon_op_zg__ : Core.TyCon -> Core.TyCon -> bool :=
  fun a b =>
    match (Ord__TyCon_compare a b) with
      | Lt => false
      | Eq => false
      | Gt => true
    end.

Local Definition Ord__TyCon_op_zgze__ : Core.TyCon -> Core.TyCon -> bool :=
  fun a b =>
    match (Ord__TyCon_compare a b) with
      | Lt => false
      | Eq => true
      | Gt => true
    end.

Local Definition Ord__TyCon_op_zl__ : Core.TyCon -> Core.TyCon -> bool :=
  fun a b =>
    match (Ord__TyCon_compare a b) with
      | Lt => true
      | Eq => false
      | Gt => false
    end.

Local Definition Ord__TyCon_op_zlze__ : Core.TyCon -> Core.TyCon -> bool :=
  fun a b =>
    match (Ord__TyCon_compare a b) with
      | Lt => true
      | Eq => true
      | Gt => false
    end.

Local Definition Ord__TyCon_max : Core.TyCon -> Core.TyCon -> Core.TyCon :=
  fun x y => if Ord__TyCon_op_zlze__ x y : bool then y else x.

Local Definition Ord__TyCon_min : Core.TyCon -> Core.TyCon -> Core.TyCon :=
  fun x y => if Ord__TyCon_op_zlze__ x y : bool then x else y.

Local Definition Eq___TyCon_op_zeze__ : Core.TyCon -> Core.TyCon -> bool :=
  fun a b => match Ord__TyCon_compare a b with | Eq => true | _ => false end.

Local Definition Eq___TyCon_op_zsze__ : Core.TyCon -> Core.TyCon -> bool :=
  fun a b =>
    let scrut_0__ := Ord__TyCon_compare a b in
    match scrut_0__ with
      | Eq => false
      | _ => true
    end.

Program Instance Eq___TyCon : GHC.Base.Eq_ Core.TyCon := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___TyCon_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___TyCon_op_zsze__ |}.

Program Instance Ord__TyCon : GHC.Base.Ord Core.TyCon := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__TyCon_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__TyCon_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__TyCon_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__TyCon_op_zgze__ ;
      GHC.Base.compare__ := Ord__TyCon_compare ;
      GHC.Base.max__ := Ord__TyCon_max ;
      GHC.Base.min__ := Ord__TyCon_min |}.

(* Translating `instance Unique.Uniquable Core.TyCon' failed: OOPS! Cannot find
   information for class Qualified "Unique" "Uniquable" unsupported *)

(* Translating `instance Outputable.Outputable Core.TyCon' failed: OOPS! Cannot
   find information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance Name.NamedThing Core.TyCon' failed: OOPS! Cannot find
   information for class Qualified "Name" "NamedThing" unsupported *)

(* Translating `instance Data.Data.Data Core.TyCon' failed: OOPS! Cannot find
   information for class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance Binary.Binary Core.Injectivity' failed: OOPS! Cannot
   find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance GHC.Show.Show TyCon.PrimRep' failed: OOPS! Cannot find
   information for class Qualified "GHC.Show" "Show" unsupported *)

(* Translating `instance GHC.Show.Show TyCon.PrimElemRep' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

Local Definition Eq___PrimElemRep_op_zeze__
    : PrimElemRep -> PrimElemRep -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | Int8ElemRep , Int8ElemRep => true
      | Int16ElemRep , Int16ElemRep => true
      | Int32ElemRep , Int32ElemRep => true
      | Int64ElemRep , Int64ElemRep => true
      | Word8ElemRep , Word8ElemRep => true
      | Word16ElemRep , Word16ElemRep => true
      | Word32ElemRep , Word32ElemRep => true
      | Word64ElemRep , Word64ElemRep => true
      | FloatElemRep , FloatElemRep => true
      | DoubleElemRep , DoubleElemRep => true
      | _ , _ => false
    end.

Local Definition Eq___PrimElemRep_op_zsze__
    : PrimElemRep -> PrimElemRep -> bool :=
  fun a b => negb (Eq___PrimElemRep_op_zeze__ a b).

Program Instance Eq___PrimElemRep : GHC.Base.Eq_ PrimElemRep := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___PrimElemRep_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___PrimElemRep_op_zsze__ |}.

Local Definition Eq___PrimRep_op_zeze__ : PrimRep -> PrimRep -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | VoidRep , VoidRep => true
      | PtrRep , PtrRep => true
      | IntRep , IntRep => true
      | WordRep , WordRep => true
      | Int64Rep , Int64Rep => true
      | Word64Rep , Word64Rep => true
      | AddrRep , AddrRep => true
      | FloatRep , FloatRep => true
      | DoubleRep , DoubleRep => true
      | VecRep a1 a2 , VecRep b1 b2 => (andb ((a1 GHC.Base.== b1)) ((a2 GHC.Base.==
                                             b2)))
      | _ , _ => false
    end.

Local Definition Eq___PrimRep_op_zsze__ : PrimRep -> PrimRep -> bool :=
  fun a b => negb (Eq___PrimRep_op_zeze__ a b).

Program Instance Eq___PrimRep : GHC.Base.Eq_ PrimRep := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___PrimRep_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___PrimRep_op_zsze__ |}.

Local Definition Eq___Injectivity_op_zeze__
    : Core.Injectivity -> Core.Injectivity -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | NotInjective , NotInjective => true
      | Injective a1 , Injective b1 => ((a1 GHC.Base.== b1))
      | _ , _ => false
    end.

Local Definition Eq___Injectivity_op_zsze__
    : Core.Injectivity -> Core.Injectivity -> bool :=
  fun a b => negb (Eq___Injectivity_op_zeze__ a b).

Program Instance Eq___Injectivity : GHC.Base.Eq_ Core.Injectivity := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Injectivity_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Injectivity_op_zsze__ |}.

Axiom algTyConRhs : forall {A : Type}, A.

(* Translating `algTyConRhs' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom expandSynTyCon_maybe : forall {A : Type}, A.

(* Translating `expandSynTyCon_maybe' failed: using a record pattern for the
   unknown constructor `SynonymTyCon' unsupported *)

Axiom famTyConFlav_maybe : forall {A : Type}, A.

(* Translating `famTyConFlav_maybe' failed: using a record pattern for the
   unknown constructor `FamilyTyCon' unsupported *)

Axiom familyTyConInjectivityInfo : forall {A : Type}, A.

(* Translating `familyTyConInjectivityInfo' failed: using a record pattern for
   the unknown constructor `FamilyTyCon' unsupported *)

Axiom isAbstractTyCon : forall {A : Type}, A.

(* Translating `isAbstractTyCon' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom isAlgTyCon : forall {A : Type}, A.

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

Axiom isDataFamilyTyCon : forall {A : Type}, A.

(* Translating `isDataFamilyTyCon' failed: using a record pattern for the
   unknown constructor `FamilyTyCon' unsupported *)

Axiom isDataProductTyCon_maybe : forall {A : Type}, A.

(* Translating `isDataProductTyCon_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom isDataTyCon : forall {A : Type}, A.

(* Translating `isDataTyCon' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom isEnumerationTyCon : forall {A : Type}, A.

(* Translating `isEnumerationTyCon' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

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

Axiom isGenerativeTyCon : forall {A : Type}, A.

(* Translating `isGenerativeTyCon' failed: using a record pattern for the
   unknown constructor `FamilyTyCon' unsupported *)

Axiom isImplicitTyCon : forall {A : Type}, A.

(* Translating `isImplicitTyCon' failed: using a record pattern for the unknown
   constructor `FunTyCon' unsupported *)

Axiom isInjectiveTyCon : forall {A : Type}, A.

(* Translating `isInjectiveTyCon' failed: using a record pattern for the unknown
   constructor `FunTyCon' unsupported *)

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

Axiom isRecursiveTyCon : forall {A : Type}, A.

(* Translating `isRecursiveTyCon' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom isTcTyCon : forall {A : Type}, A.

(* Translating `isTcTyCon' failed: using a record pattern for the unknown
   constructor `TcTyCon' unsupported *)

Axiom isTupleTyCon : forall {A : Type}, A.

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

Axiom isUnboxedTupleTyCon : forall {A : Type}, A.

(* Translating `isUnboxedTupleTyCon' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom isUnliftedTyCon : forall {A : Type}, A.

(* Translating `isUnliftedTyCon' failed: using a record pattern for the unknown
   constructor `PrimTyCon' unsupported *)

Axiom isVanillaAlgTyCon : forall {A : Type}, A.

(* Translating `isVanillaAlgTyCon' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom mightBeUnsaturatedTyCon : forall {A : Type}, A.

(* Translating `mightBeUnsaturatedTyCon' failed: using a record pattern for the
   unknown constructor `SynonymTyCon' unsupported *)

Axiom mkAlgTyCon : forall {A : Type}, A.

(* Translating `mkAlgTyCon' failed: creating a record with the unknown
   constructor `AlgTyCon' unsupported *)

Axiom mkFamilyTyCon : forall {A : Type}, A.

(* Translating `mkFamilyTyCon' failed: creating a record with the unknown
   constructor `FamilyTyCon' unsupported *)

Axiom mkFunTyCon : forall {A : Type}, A.

(* Translating `mkFunTyCon' failed: creating a record with the unknown
   constructor `FunTyCon' unsupported *)

Axiom mkPrimTyCon' : forall {A : Type}, A.

(* Translating `mkPrimTyCon'' failed: creating a record with the unknown
   constructor `PrimTyCon' unsupported *)

Axiom mkPromotedDataCon : forall {A : Type}, A.

(* Translating `mkPromotedDataCon' failed: creating a record with the unknown
   constructor `PromotedDataCon' unsupported *)

Axiom mkSynonymTyCon : forall {A : Type}, A.

(* Translating `mkSynonymTyCon' failed: creating a record with the unknown
   constructor `SynonymTyCon' unsupported *)

Axiom mkTcTyCon : forall {A : Type}, A.

(* Translating `mkTcTyCon' failed: creating a record with the unknown
   constructor `TcTyCon' unsupported *)

Axiom mkTupleTyCon : forall {A : Type}, A.

(* Translating `mkTupleTyCon' failed: creating a record with the unknown
   constructor `AlgTyCon' unsupported *)

Axiom newTyConCo_maybe : forall {A : Type}, A.

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

Axiom synTyConDefn_maybe : forall {A : Type}, A.

(* Translating `synTyConDefn_maybe' failed: using a record pattern for the
   unknown constructor `SynonymTyCon' unsupported *)

Axiom synTyConRhs_maybe : forall {A : Type}, A.

(* Translating `synTyConRhs_maybe' failed: using a record pattern for the
   unknown constructor `SynonymTyCon' unsupported *)

Axiom tyConAssoc_maybe : forall {A : Type}, A.

(* Translating `tyConAssoc_maybe' failed: using a record pattern for the unknown
   constructor `FamilyTyCon' unsupported *)

Axiom tyConCType_maybe : forall {A : Type}, A.

(* Translating `tyConCType_maybe' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom tyConClass_maybe : forall {A : Type}, A.

(* Translating `tyConClass_maybe' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom tyConDataCons_maybe : forall {A : Type}, A.

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

Axiom tyConFlavour : forall {A : Type}, A.

(* Translating `tyConFlavour' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

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

(* Translating `tyConSingleDataCon_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom tyConStupidTheta : forall {A : Type}, A.

(* Translating `tyConStupidTheta' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom tyConTuple_maybe : forall {A : Type}, A.

(* Translating `tyConTuple_maybe' failed: using a record pattern for the unknown
   constructor `AlgTyCon' unsupported *)

Axiom unwrapNewTyConEtad_maybe : forall {A : Type}, A.

(* Translating `unwrapNewTyConEtad_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Axiom unwrapNewTyCon_maybe : forall {A : Type}, A.

(* Translating `unwrapNewTyCon_maybe' failed: using a record pattern for the
   unknown constructor `AlgTyCon' unsupported *)

Definition checkRecTc : RecTcChecker -> Core.TyCon -> option RecTcChecker :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | (RC bound rec_nts as rc) , tc => let tc_name := tyConName tc in
                                         if negb (isRecursiveTyCon tc) : bool
                                         then Some rc
                                         else match NameEnv.lookupNameEnv rec_nts tc_name with
                                                | Some n => if n GHC.Base.>= bound : bool
                                                            then None
                                                            else Some (RC bound (NameEnv.extendNameEnv rec_nts tc_name
                                                                                (n GHC.Num.+ GHC.Num.fromInteger 1)))
                                                | None => Some (RC bound (NameEnv.extendNameEnv rec_nts tc_name
                                                                         (GHC.Num.fromInteger 1)))
                                              end
    end.

Definition initRecTc : RecTcChecker :=
  RC (GHC.Num.fromInteger 100) NameEnv.emptyNameEnv.

Definition isDataFamFlav : FamTyConFlav -> bool :=
  fun arg_0__ => match arg_0__ with | DataFamilyTyCon _ => true | _ => false end.

Definition isGcPtrRep : PrimRep -> bool :=
  fun arg_0__ => match arg_0__ with | PtrRep => true | _ => false end.

Definition isGenInjAlgRhs : AlgTyConRhs -> bool :=
  fun arg_0__ =>
    match arg_0__ with
      | TupleTyCon _ _ => true
      | DataTyCon _ _ => true
      | AbstractTyCon distinct => distinct
      | NewTyCon _ _ _ _ => false
    end.

Definition isVoidRep : PrimRep -> bool :=
  fun arg_0__ => match arg_0__ with | VoidRep => true | _other => false end.

Definition mkKindTyCon : Name.Name -> list Core.TyBinder -> Kind -> list
                         Core.Role -> Name.Name -> Core.TyCon :=
  fun name binders res_kind roles rep_nm =>
    let tc := mkPrimTyCon' name binders res_kind roles false (Some rep_nm) in tc.

Definition newTyConCo : Core.TyCon -> Core.CoAxiom Core.Unbranched :=
  fun tc =>
    match newTyConCo_maybe tc with
      | Some co => co
      | None => Panic.panicStr (GHC.Base.hs_string__ "newTyConCo") (Panic.noString tc)
    end.

Definition primElemRepSizeB : PrimElemRep -> GHC.Num.Int :=
  fun arg_0__ =>
    match arg_0__ with
      | Int8ElemRep => GHC.Num.fromInteger 1
      | Int16ElemRep => GHC.Num.fromInteger 2
      | Int32ElemRep => GHC.Num.fromInteger 4
      | Int64ElemRep => GHC.Num.fromInteger 8
      | Word8ElemRep => GHC.Num.fromInteger 1
      | Word16ElemRep => GHC.Num.fromInteger 2
      | Word32ElemRep => GHC.Num.fromInteger 4
      | Word64ElemRep => GHC.Num.fromInteger 8
      | FloatElemRep => GHC.Num.fromInteger 4
      | DoubleElemRep => GHC.Num.fromInteger 8
    end.

Definition primRepSizeW : DynFlags.DynFlags -> PrimRep -> GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__ , arg_1__ with
      | _ , IntRep => GHC.Num.fromInteger 1
      | _ , WordRep => GHC.Num.fromInteger 1
      | dflags , Int64Rep => GHC.Real.quot Constants.wORD64_SIZE (DynFlags.wORD_SIZE
                                           dflags)
      | dflags , Word64Rep => GHC.Real.quot Constants.wORD64_SIZE (DynFlags.wORD_SIZE
                                            dflags)
      | _ , FloatRep => GHC.Num.fromInteger 1
      | dflags , DoubleRep => GHC.Real.quot (DynFlags.dOUBLE_SIZE dflags)
                                            (DynFlags.wORD_SIZE dflags)
      | _ , AddrRep => GHC.Num.fromInteger 1
      | _ , PtrRep => GHC.Num.fromInteger 1
      | _ , VoidRep => GHC.Num.fromInteger 0
      | dflags , VecRep len rep => GHC.Real.quot (len GHC.Num.* primElemRepSizeB rep)
                                                 (DynFlags.wORD_SIZE dflags)
    end.

Definition primRepIsFloat : PrimRep -> option bool :=
  fun arg_0__ =>
    match arg_0__ with
      | FloatRep => Some true
      | DoubleRep => Some true
      | VecRep _ _ => None
      | _ => Some false
    end.

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
                                                                                            (cons PrelNames.tYPETyConKey
                                                                                                  nil))))))
                                  (GHC.Base.map (UniqSet.mkUniqSet GHC.Base.∘ tycon_with_datacons) (cons
                                                                                                   TysWiredIn.runtimeRepTyCon
                                                                                                   (cons
                                                                                                   TysWiredIn.vecCountTyCon
                                                                                                   (cons
                                                                                                   TysWiredIn.vecElemTyCon
                                                                                                   nil))))).

Definition isKindTyCon : Core.TyCon -> bool :=
  fun tc => UniqSet.elementOfUniqSet (Unique.getUnique tc) kindTyConKeys.

Definition tyConFieldLabelEnv : Core.TyCon -> FieldLabel.FieldLabelEnv :=
  fun tc =>
    if isAlgTyCon tc : bool
    then algTcFields tc
    else FastStringEnv.emptyFsEnv.

Definition tyConFieldLabels : Core.TyCon -> list FieldLabel.FieldLabel :=
  fun tc => FastStringEnv.fsEnvElts GHC.Base.$ tyConFieldLabelEnv tc.

Definition tyConRepModOcc : Module.Module -> OccName.OccName -> (Module.Module *
                            OccName.OccName)%type :=
  fun tc_module tc_occ =>
    let rep_module :=
      if tc_module GHC.Base.== PrelNames.gHC_PRIM : bool
      then PrelNames.gHC_TYPES
      else tc_module in
    pair rep_module (OccName.mkTyConRepOcc tc_occ).

Definition mkPrelTyConRepName : Name.Name -> Core.TyConRepName :=
  fun tc_name =>
    let name_uniq := Name.nameUnique tc_name in
    let name_mod := Name.nameModule tc_name in
    let name_occ := Name.nameOccName tc_name in
    let rep_uniq :=
      if OccName.isTcOcc name_occ : bool
      then Unique.tyConRepNameUnique name_uniq
      else Unique.dataConRepNameUnique name_uniq in
    match tyConRepModOcc name_mod name_occ with
      | pair rep_mod rep_occ => Name.mkExternalName rep_uniq rep_mod rep_occ
                                (Name.nameSrcSpan tc_name)
    end.

Definition mkPrimTyCon : Name.Name -> list Core.TyBinder -> Kind -> list
                         Core.Role -> Core.TyCon :=
  fun name binders res_kind roles =>
    mkPrimTyCon' name binders res_kind roles true (Some GHC.Base.$
                                                  mkPrelTyConRepName name).

Definition mkLiftedPrimTyCon : Name.Name -> list Core.TyBinder -> Kind -> list
                               Core.Role -> Core.TyCon :=
  fun name binders res_kind roles =>
    let rep_nm := mkPrelTyConRepName name in
    mkPrimTyCon' name binders res_kind roles false (Some rep_nm).

Definition tyConSingleDataCon : Core.TyCon -> DataCon.DataCon :=
  fun tc =>
    match tyConSingleDataCon_maybe tc with
      | Some c => c
      | None => Panic.panicStr (GHC.Base.hs_string__ "tyConDataCon") (Panic.noString
                                                                     tc)
    end.

Definition visibleDataCons : AlgTyConRhs -> list DataCon.DataCon :=
  fun arg_0__ =>
    match arg_0__ with
      | AbstractTyCon _ => nil
      | DataTyCon cs _ => cs
      | NewTyCon c _ _ _ => cons c nil
      | TupleTyCon c _ => cons c nil
    end.

(* Unbound variables:
     Eq Gt Injective Kind Lt None NotInjective Some TyVar algTcFields andb bool
     comparison cons error false list negb nil op_zt__ option pair true tyConName
     BasicTypes.TupleSort Constants.wORD64_SIZE Core.Branched Core.BuiltInSynFamily
     Core.CoAxiom Core.Injectivity Core.Role Core.TyBinder Core.TyCon
     Core.TyConRepName Core.Type_ Core.Unbranched DataCon.DataCon DynFlags.DynFlags
     DynFlags.dOUBLE_SIZE DynFlags.wORD_SIZE FastStringEnv.emptyFsEnv
     FastStringEnv.fsEnvElts FieldLabel.FieldLabel FieldLabel.FieldLabelEnv
     GHC.Base.Eq_ GHC.Base.Ord GHC.Base.compare GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zd__ GHC.Base.op_zeze__ GHC.Base.op_zgze__ GHC.Num.Int
     GHC.Num.op_zp__ GHC.Num.op_zt__ GHC.Real.quot Maybes.orElse Module.Module
     Name.Name Name.mkExternalName Name.nameModule Name.nameOccName Name.nameSrcSpan
     Name.nameUnique NameEnv.NameEnv NameEnv.emptyNameEnv NameEnv.extendNameEnv
     NameEnv.lookupNameEnv OccName.OccName OccName.isTcOcc OccName.mkTyConRepOcc
     Panic.noString Panic.panicStr PrelNames.constraintKindTyConKey
     PrelNames.gHC_PRIM PrelNames.gHC_TYPES PrelNames.liftedTypeKindTyConKey
     PrelNames.starKindTyConKey PrelNames.tYPETyConKey
     PrelNames.unicodeStarKindTyConKey TysWiredIn.runtimeRepTyCon
     TysWiredIn.vecCountTyCon TysWiredIn.vecElemTyCon UniqSet.UniqSet
     UniqSet.elementOfUniqSet UniqSet.mkUniqSet UniqSet.unionManyUniqSets
     Unique.Unique Unique.dataConRepNameUnique Unique.getUnique
     Unique.tyConRepNameUnique
*)
