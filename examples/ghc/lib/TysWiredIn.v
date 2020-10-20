(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require AxiomatizedTypes.
Require BasicTypes.
Require Core.
Require FastString.
Require GHC.Base.
Require Module.
Require Name.
Require NameEnv.
Require NameSet.
Require OccName.
Require PrelNames.
Require Unique.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom alpha_tyvar : list Core.TyVar.

Axiom alpha_ty : list AxiomatizedTypes.Type_.

Axiom wiredInTyCons : list Core.TyCon.

Axiom mkWiredInTyConName : Name.BuiltInSyntax ->
                           Module.Module ->
                           FastString.FastString -> Unique.Unique -> Core.TyCon -> Name.Name.

Axiom mkWiredInDataConName : Name.BuiltInSyntax ->
                             Module.Module ->
                             FastString.FastString -> Unique.Unique -> Core.DataCon -> Name.Name.

Axiom mkWiredInIdName : Module.Module ->
                        FastString.FastString -> Unique.Unique -> Core.Id -> Name.Name.

Axiom heqTyConName : Name.Name.

Axiom heqDataConName : Name.Name.

Axiom heqSCSelIdName : Name.Name.

Axiom coercibleTyConName : Name.Name.

Axiom coercibleDataConName : Name.Name.

Axiom coercibleSCSelIdName : Name.Name.

Axiom charTyConName : Name.Name.

Axiom charDataConName : Name.Name.

Axiom intTyConName : Name.Name.

Axiom intDataConName : Name.Name.

Axiom boolTyConName : Name.Name.

Axiom falseDataConName : Name.Name.

Axiom trueDataConName : Name.Name.

Axiom listTyConName : Name.Name.

Axiom nilDataConName : Name.Name.

Axiom consDataConName : Name.Name.

Axiom maybeTyConName : Name.Name.

Axiom nothingDataConName : Name.Name.

Axiom justDataConName : Name.Name.

Axiom wordTyConName : Name.Name.

Axiom wordDataConName : Name.Name.

Axiom word8TyConName : Name.Name.

Axiom word8DataConName : Name.Name.

Axiom floatTyConName : Name.Name.

Axiom floatDataConName : Name.Name.

Axiom doubleTyConName : Name.Name.

Axiom doubleDataConName : Name.Name.

Axiom anyTyConName : Name.Name.

Axiom anyTyCon : Core.TyCon.

Axiom anyTy : AxiomatizedTypes.Type_.

Axiom anyTypeOfKind : AxiomatizedTypes.Kind -> AxiomatizedTypes.Type_.

Axiom typeNatKindConName : Name.Name.

Axiom typeSymbolKindConName : Name.Name.

Axiom constraintKindTyConName : Name.Name.

Axiom liftedTypeKindTyConName : Name.Name.

Axiom starKindTyConName : Name.Name.

Axiom unicodeStarKindTyConName : Name.Name.

Axiom runtimeRepTyConName : Name.Name.

Axiom vecRepDataConName : Name.Name.

Axiom tupleRepDataConName : Name.Name.

Axiom sumRepDataConName : Name.Name.

Axiom runtimeRepSimpleDataConNames : list Name.Name.

Axiom vecCountTyConName : Name.Name.

Axiom vecCountDataConNames : list Name.Name.

Axiom vecElemTyConName : Name.Name.

Axiom vecElemDataConNames : list Name.Name.

Axiom mk_special_dc_name : FastString.FastString ->
                           Unique.Unique -> Core.DataCon -> Name.Name.

Axiom parrTyConName : Name.Name.

Axiom parrDataConName : Name.Name.

Axiom boolTyCon_RDR : PrelNames.RdrName.

Axiom false_RDR : PrelNames.RdrName.

Axiom true_RDR : PrelNames.RdrName.

Axiom intTyCon_RDR : PrelNames.RdrName.

Axiom charTyCon_RDR : PrelNames.RdrName.

Axiom intDataCon_RDR : PrelNames.RdrName.

Axiom listTyCon_RDR : PrelNames.RdrName.

Axiom consDataCon_RDR : PrelNames.RdrName.

Axiom parrTyCon_RDR : PrelNames.RdrName.

Axiom pcNonEnumTyCon : Name.Name ->
                       option AxiomatizedTypes.CType ->
                       list Core.TyVar -> list Core.DataCon -> Core.TyCon.

Axiom pcTyCon : bool ->
                Name.Name ->
                option AxiomatizedTypes.CType ->
                list Core.TyVar -> list Core.DataCon -> Core.TyCon.

Axiom pcDataCon : Name.Name ->
                  list Core.TyVar -> list AxiomatizedTypes.Type_ -> Core.TyCon -> Core.DataCon.

Axiom pcDataConWithFixity : bool ->
                            Name.Name ->
                            list Core.TyVar ->
                            list Core.TyVar ->
                            list Core.TyVar -> list AxiomatizedTypes.Type_ -> Core.TyCon -> Core.DataCon.

Axiom pcDataConWithFixity' : bool ->
                             Name.Name ->
                             Unique.Unique ->
                             Core.RuntimeRepInfo ->
                             list Core.TyVar ->
                             list Core.TyVar ->
                             list Core.TyVar -> list AxiomatizedTypes.Type_ -> Core.TyCon -> Core.DataCon.

Axiom mkDataConWorkerName : Core.DataCon -> Unique.Unique -> Name.Name.

Axiom pcSpecialDataCon : Name.Name ->
                         list AxiomatizedTypes.Type_ ->
                         Core.TyCon -> Core.RuntimeRepInfo -> Core.DataCon.

Axiom typeNatKindCon : Core.TyCon.

Axiom typeSymbolKindCon : Core.TyCon.

Axiom typeNatKind : AxiomatizedTypes.Kind.

Axiom typeSymbolKind : AxiomatizedTypes.Kind.

Axiom constraintKindTyCon : Core.TyCon.

(* Skipping definition `AxiomatizedTypes.liftedTypeKind' *)

(* Skipping definition `AxiomatizedTypes.constraintKind' *)

Axiom mkFunKind : AxiomatizedTypes.Kind ->
                  AxiomatizedTypes.Kind -> AxiomatizedTypes.Kind.

Axiom mkForAllKind : Core.TyVar ->
                     Core.ArgFlag -> AxiomatizedTypes.Kind -> AxiomatizedTypes.Kind.

Axiom isBuiltInOcc_maybe : OccName.OccName -> option Name.Name.

Axiom mkTupleOcc : OccName.NameSpace ->
                   BasicTypes.Boxity -> BasicTypes.Arity -> OccName.OccName.

Axiom mkCTupleOcc : OccName.NameSpace -> BasicTypes.Arity -> OccName.OccName.

Axiom mkBoxedTupleStr : BasicTypes.Arity -> GHC.Base.String.

Axiom mkUnboxedTupleStr : BasicTypes.Arity -> GHC.Base.String.

Axiom mkConstraintTupleStr : BasicTypes.Arity -> GHC.Base.String.

Axiom commas : BasicTypes.Arity -> GHC.Base.String.

Axiom cTupleTyConName : BasicTypes.Arity -> Name.Name.

Axiom cTupleTyConNames : list Name.Name.

Axiom cTupleTyConNameSet : NameSet.NameSet.

Axiom isCTupleTyConName : Name.Name -> bool.

Axiom cTupleDataConName : BasicTypes.Arity -> Name.Name.

Axiom cTupleDataConNames : list Name.Name.

Axiom tupleTyCon : BasicTypes.Boxity -> BasicTypes.Arity -> Core.TyCon.

Axiom tupleTyConName : BasicTypes.TupleSort -> BasicTypes.Arity -> Name.Name.

Axiom promotedTupleDataCon : BasicTypes.Boxity ->
                             BasicTypes.Arity -> Core.TyCon.

Axiom tupleDataCon : BasicTypes.Boxity -> BasicTypes.Arity -> Core.DataCon.

(* Skipping definition `TysWiredIn.boxedTupleArr' *)

(* Skipping definition `TysWiredIn.unboxedTupleArr' *)

Axiom unboxedTupleSumKind : Core.TyCon ->
                            list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Kind.

Axiom unboxedTupleKind : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Kind.

Axiom mk_tuple : BasicTypes.Boxity -> nat -> (Core.TyCon * Core.DataCon)%type.

Axiom unitTyCon : Core.TyCon.

Axiom unitTyConKey : Unique.Unique.

Axiom unitDataCon : Core.DataCon.

Axiom unitDataConId : Core.Id.

Axiom pairTyCon : Core.TyCon.

Axiom unboxedUnitTyCon : Core.TyCon.

Axiom unboxedUnitDataCon : Core.DataCon.

Axiom mkSumTyConOcc : BasicTypes.Arity -> OccName.OccName.

Axiom mkSumDataConOcc : BasicTypes.ConTag ->
                        BasicTypes.Arity -> OccName.OccName.

Axiom sumTyCon : BasicTypes.Arity -> Core.TyCon.

Axiom sumDataCon : BasicTypes.ConTag -> BasicTypes.Arity -> Core.DataCon.

(* Skipping definition `TysWiredIn.unboxedSumArr' *)

Axiom unboxedSumKind : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Kind.

(* Skipping definition `TysWiredIn.mk_sum' *)

Axiom mk_class : Core.TyCon ->
                 AxiomatizedTypes.PredType -> Core.Id -> Core.Class.

Axiom runtimeRepTy : AxiomatizedTypes.Type_.

Axiom liftedTypeKindTyCon : Core.TyCon.

Axiom starKindTyCon : Core.TyCon.

Axiom unicodeStarKindTyCon : Core.TyCon.

Axiom runtimeRepTyCon : Core.TyCon.

Axiom vecRepDataCon : Core.DataCon.

Axiom vecRepDataConTyCon : Core.TyCon.

Axiom tupleRepDataCon : Core.DataCon.

Axiom tupleRepDataConTyCon : Core.TyCon.

Axiom sumRepDataCon : Core.DataCon.

Axiom sumRepDataConTyCon : Core.TyCon.

Axiom vecCountTyCon : Core.TyCon.

Axiom vecCountDataCons : list Core.DataCon.

Axiom vecElemTyCon : Core.TyCon.

Axiom vecElemDataCons : list Core.DataCon.

Axiom liftedRepDataConTyCon : Core.TyCon.

Axiom liftedRepTy : AxiomatizedTypes.Type_.

Axiom boxingDataCon_maybe : Core.TyCon -> option Core.DataCon.

Axiom boxing_constr_env : NameEnv.NameEnv Core.DataCon.

Axiom charTy : AxiomatizedTypes.Type_.

Axiom charTyCon : Core.TyCon.

Axiom charDataCon : Core.DataCon.

Axiom stringTy : AxiomatizedTypes.Type_.

Axiom intTy : AxiomatizedTypes.Type_.

Axiom intTyCon : Core.TyCon.

Axiom intDataCon : Core.DataCon.

Axiom wordTy : AxiomatizedTypes.Type_.

Axiom wordTyCon : Core.TyCon.

Axiom wordDataCon : Core.DataCon.

Axiom word8Ty : AxiomatizedTypes.Type_.

Axiom word8TyCon : Core.TyCon.

Axiom word8DataCon : Core.DataCon.

Axiom floatTy : AxiomatizedTypes.Type_.

Axiom floatTyCon : Core.TyCon.

Axiom floatDataCon : Core.DataCon.

Axiom doubleTy : AxiomatizedTypes.Type_.

Axiom doubleTyCon : Core.TyCon.

Axiom doubleDataCon : Core.DataCon.

Axiom boolTy : AxiomatizedTypes.Type_.

Axiom boolTyCon : Core.TyCon.

Axiom falseDataCon : Core.DataCon.

Axiom trueDataCon : Core.DataCon.

Axiom falseDataConId : Core.Id.

Axiom trueDataConId : Core.Id.

Axiom orderingTyCon : Core.TyCon.

Axiom ltDataCon : Core.DataCon.

Axiom eqDataCon : Core.DataCon.

Axiom gtDataCon : Core.DataCon.

Axiom ltDataConId : Core.Id.

Axiom eqDataConId : Core.Id.

Axiom gtDataConId : Core.Id.

Axiom mkListTy : AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom listTyCon : Core.TyCon.

Axiom nilDataCon : Core.DataCon.

Axiom consDataCon : Core.DataCon.

Axiom maybeTyCon : Core.TyCon.

Axiom nothingDataCon : Core.DataCon.

Axiom justDataCon : Core.DataCon.

Axiom mkTupleTy : BasicTypes.Boxity ->
                  list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkBoxedTupleTy : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom unitTy : AxiomatizedTypes.Type_.

Axiom mkSumTy : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkPArrTy : AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom parrTyCon : Core.TyCon.

Axiom parrDataCon : Core.DataCon.

Axiom isPArrTyCon : Core.TyCon -> bool.

Axiom parrFakeCon : BasicTypes.Arity -> Core.DataCon.

(* Skipping definition `TysWiredIn.parrFakeConArr' *)

Axiom mkPArrFakeCon : nat -> Core.DataCon.

Axiom isPArrFakeCon : Core.DataCon -> bool.

Axiom promotedTrueDataCon : Core.TyCon.

Axiom promotedFalseDataCon : Core.TyCon.

Axiom promotedNothingDataCon : Core.TyCon.

Axiom promotedJustDataCon : Core.TyCon.

Axiom promotedLTDataCon : Core.TyCon.

Axiom promotedEQDataCon : Core.TyCon.

Axiom promotedGTDataCon : Core.TyCon.

Axiom promotedConsDataCon : Core.TyCon.

Axiom promotedNilDataCon : Core.TyCon.

Axiom mkPromotedListTy : AxiomatizedTypes.Kind ->
                         list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom extractPromotedList : AxiomatizedTypes.Type_ ->
                            list AxiomatizedTypes.Type_.

(* External variables:
     bool list nat op_zt__ option AxiomatizedTypes.CType AxiomatizedTypes.Kind
     AxiomatizedTypes.PredType AxiomatizedTypes.Type_ BasicTypes.Arity
     BasicTypes.Boxity BasicTypes.ConTag BasicTypes.TupleSort Core.ArgFlag Core.Class
     Core.DataCon Core.Id Core.RuntimeRepInfo Core.TyCon Core.TyVar
     FastString.FastString GHC.Base.String Module.Module Name.BuiltInSyntax Name.Name
     NameEnv.NameEnv NameSet.NameSet OccName.NameSpace OccName.OccName
     PrelNames.RdrName Unique.Unique
*)
