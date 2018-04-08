(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)


(*
Require Name.
Require Class.

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
*)
(* Converted imports: *)

Require BasicTypes.
Require Constants.
Require Data.Foldable.
Require Data.Maybe.
Require Data.Tuple.
Require DynFlags.
Require FastStringEnv.
Require FieldLabel.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require IdInfo.
Require Maybes.
Require Module.
Require Name.
Require NameEnv.
Require OccName.
Require Panic.
Require PrelNames.
Require Unique.
Require Util.
Require Var.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

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

Inductive RuntimeRepInfo : Type := Mk_RuntimeRepInfo_Dummy.

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

Inductive Injectivity : Type
  := NotInjective : Injectivity
  |  Injective : list bool -> Injectivity.

Inductive FamTyConFlav : Type
  := DataFamilyTyCon : TyConRepName -> FamTyConFlav
  |  OpenSynFamilyTyCon : FamTyConFlav
  |  ClosedSynFamilyTyCon : (option (list unit)) -> FamTyConFlav
  |  AbstractClosedSynFamilyTyCon : FamTyConFlav
  |  BuiltInSynFamTyCon : unit -> FamTyConFlav.

Inductive AlgTyConRhs : Type
  := AbstractTyCon : AlgTyConRhs
  |  DataTyCon : list IdInfo.DataConId -> bool -> AlgTyConRhs
  |  TupleTyCon : IdInfo.DataConId -> BasicTypes.TupleSort -> AlgTyConRhs
  |  SumTyCon : list IdInfo.DataConId -> AlgTyConRhs
  |  NewTyCon
   : IdInfo.DataConId ->
     unit -> (list Var.TyVar * unit)%type -> list unit -> AlgTyConRhs.

Inductive AlgTyConFlav : Type
  := VanillaAlgTyCon : TyConRepName -> AlgTyConFlav
  |  UnboxedAlgTyCon : (option TyConRepName) -> AlgTyConFlav
  |  ClassTyCon : IdInfo.ClassId -> TyConRepName -> AlgTyConFlav
  |  DataFamInstTyCon : (list unit) -> TyCon -> list unit -> AlgTyConFlav
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
     list unit ->
     option unit ->
     bool ->
     list unit -> AlgTyConRhs -> FieldLabel.FieldLabelEnv -> AlgTyConFlav -> TyCon
  |  SynonymTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     list Var.TyVar ->
     unit -> unit -> BasicTypes.Arity -> list unit -> unit -> bool -> bool -> TyCon
  |  FamilyTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     list Var.TyVar ->
     unit ->
     unit ->
     BasicTypes.Arity ->
     option Name.Name ->
     FamTyConFlav -> option IdInfo.ClassId -> Injectivity -> TyCon
  |  PrimTyCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     unit ->
     unit -> BasicTypes.Arity -> list unit -> bool -> option TyConRepName -> TyCon
  |  PromotedDataCon
   : Unique.Unique ->
     Name.Name ->
     list TyConBinder ->
     unit ->
     unit ->
     BasicTypes.Arity ->
     list unit -> IdInfo.DataConId -> TyConRepName -> RuntimeRepInfo -> TyCon
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



Instance Default__AlgTyConFlav : Err.Default AlgTyConFlav :=
  Err.Build_Default _ (VanillaAlgTyCon Err.default).

Instance Default__RuntimRepInfo : Err.Default RuntimeRepInfo :=
  Err.Build_Default _ Mk_RuntimeRepInfo_Dummy.                                 

Instance Uniquable_Tycon : Unique.Uniquable TyCon. 
Admitted.
(* Converted value declarations: *)

(* Skipping instance Outputable__AlgTyConFlav of class Outputable *)

Local Definition Eq___TyCon_op_zeze__ : TyCon -> TyCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base.== Unique.getUnique b.

Local Definition Eq___TyCon_op_zsze__ : TyCon -> TyCon -> bool :=
  fun a b => Unique.getUnique a GHC.Base./= Unique.getUnique b.

Program Instance Eq___TyCon : GHC.Base.Eq_ TyCon :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TyCon_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TyCon_op_zsze__ |}.

Local Definition Uniquable__TyCon_getUnique : TyCon -> Unique.Unique :=
  fun tc => tyConUnique tc.

Program Instance Uniquable__TyCon : Unique.Uniquable TyCon :=
  fun _ k => k {| Unique.getUnique__ := Uniquable__TyCon_getUnique |}.

(* Skipping instance Outputable__TyCon of class Outputable *)

Local Definition NamedThing__TyCon_getName : TyCon -> Name.Name :=
  tyConName.

Local Definition NamedThing__TyCon_getOccName : TyCon -> OccName.OccName :=
  fun n => Name.nameOccName (NamedThing__TyCon_getName n).

Program Instance NamedThing__TyCon : Name.NamedThing TyCon :=
  fun _ k =>
    k {| Name.getName__ := NamedThing__TyCon_getName ;
         Name.getOccName__ := NamedThing__TyCon_getOccName |}.

(* Skipping instance Data__TyCon of class Data *)

(* Skipping instance Outputable__TyConFlavour of class Outputable *)

(* Skipping instance Outputable__PrimRep of class Outputable *)

(* Skipping instance Outputable__PrimElemRep of class Outputable *)

(* Skipping instance Outputable__FamTyConFlav of class Outputable *)

(* Skipping instance Binary__Injectivity of class Binary *)

(* Skipping instance Outputable__TyVarBndr__TyConBndrVis__11 of class
   Outputable *)

(* Skipping instance Binary__TyConBndrVis of class Binary *)

Local Definition Eq___TyConFlavour_op_zeze__
   : TyConFlavour -> TyConFlavour -> bool :=
  fun a b => false.

Local Definition Eq___TyConFlavour_op_zsze__
   : TyConFlavour -> TyConFlavour -> bool :=
  fun x y => negb (Eq___TyConFlavour_op_zeze__ x y).

Program Instance Eq___TyConFlavour : GHC.Base.Eq_ TyConFlavour :=
  fun _ k =>
    k {| GHC.Base.op_zeze____ := Eq___TyConFlavour_op_zeze__ ;
         GHC.Base.op_zsze____ := Eq___TyConFlavour_op_zsze__ |}.

(* Skipping instance Show__PrimRep of class Show *)

(* Skipping instance Show__PrimElemRep of class Show *)

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

Definition isBuiltInSynFamTyCon_maybe : TyCon -> option unit :=
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
   : TyCon -> option (list unit) :=
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

Definition isPromotedDataCon_maybe : TyCon -> option IdInfo.DataConId :=
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

Definition isVoidRep : PrimRep -> bool :=
  fun arg_0__ => match arg_0__ with | VoidRep => true | _other => false end.

Definition mkAnonTyConBinder : Var.TyVar -> TyConBinder :=
  fun tv => Var.TvBndr tv AnonTCB.

Definition mkAnonTyConBinders : list Var.TyVar -> list TyConBinder :=
  fun tvs => GHC.Base.map mkAnonTyConBinder tvs.

Definition mkFamilyTyCon
   : Name.Name ->
     list TyConBinder ->
     unit ->
     option Name.Name ->
     FamTyConFlav -> option IdInfo.ClassId -> Injectivity -> TyCon :=
  fun name binders res_kind resVar flav parent inj =>
    FamilyTyCon (Name.nameUnique name) name binders (Var.binderVars binders)
                res_kind tt (Data.Foldable.length binders) resVar flav parent inj.

Definition mkFunTyCon : Name.Name -> list TyConBinder -> Name.Name -> TyCon :=
  fun name binders rep_nm =>
    FunTyCon (Name.nameUnique name) name binders tt tt (Data.Foldable.length
              binders) rep_nm.

Definition mkNamedTyConBinder : Var.ArgFlag -> Var.TyVar -> TyConBinder :=
  fun vis tv => Var.TvBndr tv (NamedTCB vis).

Definition mkNamedTyConBinders
   : Var.ArgFlag -> list Var.TyVar -> list TyConBinder :=
  fun vis tvs => GHC.Base.map (mkNamedTyConBinder vis) tvs.

Definition mkPrimTyCon'
   : Name.Name ->
     list TyConBinder -> unit -> list unit -> bool -> option TyConRepName -> TyCon :=
  fun name binders res_kind roles is_unlifted rep_nm =>
    PrimTyCon (Name.nameUnique name) name binders res_kind tt (Data.Foldable.length
               roles) roles is_unlifted rep_nm.

Definition mkKindTyCon
   : Name.Name -> list TyConBinder -> unit -> list unit -> Name.Name -> TyCon :=
  fun name binders res_kind roles rep_nm =>
    let tc := mkPrimTyCon' name binders res_kind roles false (Some rep_nm) in tc.

Definition mkPromotedDataCon
   : IdInfo.DataConId ->
     Name.Name ->
     TyConRepName ->
     list TyConBinder -> unit -> list unit -> RuntimeRepInfo -> TyCon :=
  fun con name rep_name binders res_kind roles rep_info =>
    PromotedDataCon (Name.nameUnique name) name binders res_kind tt
                    (Data.Foldable.length roles) roles con rep_name rep_info.

Definition mkSumTyCon
   : Name.Name ->
     list TyConBinder ->
     unit ->
     BasicTypes.Arity ->
     list Var.TyVar -> list IdInfo.DataConId -> AlgTyConFlav -> TyCon :=
  fun name binders res_kind arity tyvars cons_ parent =>
    AlgTyCon (Name.nameUnique name) name binders tyvars res_kind tt arity
             (GHC.List.replicate arity tt) None false nil (SumTyCon cons_)
             FastStringEnv.emptyDFsEnv parent.

Definition mkSynonymTyCon
   : Name.Name ->
     list TyConBinder -> unit -> list unit -> unit -> bool -> bool -> TyCon :=
  fun name binders res_kind roles rhs is_tau is_fam_free =>
    SynonymTyCon (Name.nameUnique name) name binders (Var.binderVars binders)
                 res_kind tt (Data.Foldable.length binders) roles rhs is_tau is_fam_free.

Definition mkTcTyCon
   : Name.Name ->
     list TyConBinder ->
     unit -> list (Name.Name * Var.TyVar)%type -> TyConFlavour -> TyCon :=
  fun name binders res_kind scoped_tvs flav =>
    TcTyCon (Unique.getUnique name) name binders (Var.binderVars binders) res_kind
            tt (Data.Foldable.length binders) scoped_tvs flav.

Definition mkTupleTyCon
   : Name.Name ->
     list TyConBinder ->
     unit ->
     BasicTypes.Arity ->
     IdInfo.DataConId -> BasicTypes.TupleSort -> AlgTyConFlav -> TyCon :=
  fun name binders res_kind arity con sort parent =>
    AlgTyCon (Name.nameUnique name) name binders (Var.binderVars binders) res_kind
             tt arity (GHC.List.replicate arity tt) None false nil (TupleTyCon con sort)
             FastStringEnv.emptyDFsEnv parent.

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
    | None => Panic.panicStr (GHC.Base.hs_string__ "newTyConCo") (Panic.noString tc)
    end.

Definition newTyConDataCon_maybe : TyCon -> option IdInfo.DataConId :=
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

Definition tyConClass_maybe : TyCon -> option IdInfo.ClassId :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ _ _ (ClassTyCon clas _) => Some clas
    | _ => None
    end.

Definition tyConDataCons_maybe : TyCon -> option (list IdInfo.DataConId) :=
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

Definition tyConDataCons : TyCon -> list IdInfo.DataConId :=
  fun tycon => Maybes.orElse (tyConDataCons_maybe tycon) nil.

Definition tyConFamInstSig_maybe
   : TyCon -> option (TyCon * list unit * list unit)%type :=
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

Definition tyConFamilyCoercion_maybe : TyCon -> option (list unit) :=
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
   : Name.Name -> list TyConBinder -> unit -> list unit -> TyCon :=
  fun name binders res_kind roles =>
    mkPrimTyCon' name binders res_kind roles true (Some (mkPrelTyConRepName name)).

Definition mkLiftedPrimTyCon
   : Name.Name -> list TyConBinder -> unit -> list unit -> TyCon :=
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

Definition tyConRoles : TyCon -> list unit :=
  fun tc =>
    let const_role := fun r => GHC.List.replicate (tyConArity tc) r in
    match tc with
    | FunTyCon _ _ _ _ _ _ _ => const_role tt
    | AlgTyCon _ _ _ _ _ _ _ roles _ _ _ _ _ _ => roles
    | SynonymTyCon _ _ _ _ _ _ _ roles _ _ _ => roles
    | FamilyTyCon _ _ _ _ _ _ _ _ _ _ _ => const_role tt
    | PrimTyCon _ _ _ _ _ _ roles _ _ => roles
    | PromotedDataCon _ _ _ _ _ _ roles _ _ _ => roles
    | TcTyCon _ _ _ _ _ _ _ _ _ => const_role tt
    end.

Definition tyConSingleAlgDataCon_maybe : TyCon -> option IdInfo.DataConId :=
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

Definition tyConSingleDataCon_maybe : TyCon -> option IdInfo.DataConId :=
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

Definition tyConSingleDataCon : TyCon -> IdInfo.DataConId :=
  fun tc =>
    match tyConSingleDataCon_maybe tc with
    | Some c => c
    | None =>
        Panic.panicStr (GHC.Base.hs_string__ "tyConDataCon") (Panic.noString tc)
    end.

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
   : TyCon -> option (list Var.TyVar * unit * list unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ _ _ _ _ _ _ _ _ (NewTyCon _ _ (pair tvs rhs) co) _ _ =>
        Some (pair (pair tvs rhs) co)
    | _ => None
    end.

Definition unwrapNewTyCon_maybe
   : TyCon -> option (list Var.TyVar * unit * list unit)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | AlgTyCon _ _ _ tvs _ _ _ _ _ _ _ (NewTyCon _ rhs _ co) _ _ =>
        Some (pair (pair tvs rhs) co)
    | _ => None
    end.

Definition visibleDataCons : AlgTyConRhs -> list IdInfo.DataConId :=
  fun arg_0__ =>
    match arg_0__ with
    | AbstractTyCon => nil
    | DataTyCon cs _ => cs
    | NewTyCon c _ _ _ => cons c nil
    | TupleTyCon c _ => cons c nil
    | SumTyCon cs => cs
    end.

(* External variables:
     Eq Gt Lt None Some Type andb bool cons false list negb nil op_zt__ option pair
     true tt unit BasicTypes.Arity BasicTypes.Boxity BasicTypes.TupleSort
     BasicTypes.isBoxed BasicTypes.tupleSortBoxity Constants.fLOAT_SIZE
     Constants.wORD64_SIZE Data.Foldable.length Data.Maybe.isJust Data.Tuple.fst
     DynFlags.DynFlags DynFlags.dOUBLE_SIZE DynFlags.wORD_SIZE
     FastStringEnv.dFsEnvElts FastStringEnv.emptyDFsEnv FastStringEnv.lookupDFsEnv
     FieldLabel.FieldLabel FieldLabel.FieldLabelEnv FieldLabel.FieldLabelString
     GHC.Base.Eq_ GHC.Base.String GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zgze__ GHC.Base.op_zlze__
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Err.Build_Default GHC.Err.Default
     GHC.Err.error GHC.List.drop GHC.List.replicate GHC.List.zip GHC.Num.Int
     GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Num.op_zt__ IdInfo.ClassId
     IdInfo.DataConId Maybes.orElse Module.Module Name.Name Name.NamedThing
     Name.getName__ Name.getOccName__ Name.isWiredInName Name.mkExternalName
     Name.nameModule Name.nameOccName Name.nameSrcSpan Name.nameUnique
     NameEnv.NameEnv NameEnv.emptyNameEnv NameEnv.extendNameEnv NameEnv.lookupNameEnv
     OccName.OccName OccName.isTcOcc OccName.mkTyConRepOcc Panic.noString
     Panic.panicStr Panic.someSDoc PrelNames.gHC_PRIM PrelNames.gHC_TYPES
     Unique.Uniquable Unique.Unique Unique.dataConRepNameUnique Unique.getUnique
     Unique.getUnique__ Unique.tyConRepNameUnique Util.lengthAtMost
     Util.listLengthCmp Var.ArgFlag Var.Required Var.Specified Var.TvBndr Var.TyVar
     Var.TyVarBinder Var.TyVarBndr Var.binderVars Var.isVisibleArgFlag
     Var.mkTyVarBinder
*)
