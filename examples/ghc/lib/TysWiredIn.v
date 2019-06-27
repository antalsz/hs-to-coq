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

Axiom wordTyConName : Name.Name.

Axiom wordTyCon : Core.TyCon.

Axiom wordTy : AxiomatizedTypes.Type_.

Axiom wordDataConName : Name.Name.

Axiom wordDataCon : Core.DataCon.

Axiom word8TyConName : Name.Name.

Axiom word8TyCon : Core.TyCon.

Axiom word8Ty : AxiomatizedTypes.Type_.

Axiom word8DataConName : Name.Name.

Axiom word8DataCon : Core.DataCon.

Axiom wiredInTyCons : list Core.TyCon.

Axiom vecRepDataConTyCon : Core.TyCon.

Axiom vecRepDataConName : Name.Name.

Axiom vecRepDataCon : Core.DataCon.

Axiom vecElemTyConName : Name.Name.

Axiom vecElemTyCon : Core.TyCon.

Axiom vecElemDataCons : list Core.DataCon.

Axiom vecElemDataConNames : list Name.Name.

Axiom vecCountTyConName : Name.Name.

Axiom vecCountTyCon : Core.TyCon.

Axiom vecCountDataCons : list Core.DataCon.

Axiom vecCountDataConNames : list Name.Name.

Axiom unitTyConKey : Unique.Unique.

Axiom unitTyCon : Core.TyCon.

Axiom unitTy : AxiomatizedTypes.Type_.

Axiom unitDataConId : Core.Id.

Axiom unitDataCon : Core.DataCon.

Axiom unicodeStarKindTyConName : Name.Name.

Axiom unicodeStarKindTyCon : Core.TyCon.

Axiom unboxedUnitTyCon : Core.TyCon.

Axiom unboxedUnitDataCon : Core.DataCon.

Axiom unboxedTupleSumKind : Core.TyCon ->
                            list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Kind.

Axiom unboxedTupleKind : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Kind.

Axiom unboxedSumKind : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Kind.

Axiom typeSymbolKindConName : Name.Name.

Axiom typeSymbolKindCon : Core.TyCon.

Axiom typeSymbolKind : AxiomatizedTypes.Kind.

Axiom typeNatKindConName : Name.Name.

Axiom typeNatKindCon : Core.TyCon.

Axiom typeNatKind : AxiomatizedTypes.Kind.

Axiom tupleTyConName : BasicTypes.TupleSort -> BasicTypes.Arity -> Name.Name.

Axiom tupleTyCon : BasicTypes.Boxity -> BasicTypes.Arity -> Core.TyCon.

Axiom tupleRepDataConTyCon : Core.TyCon.

Axiom tupleRepDataConName : Name.Name.

Axiom tupleRepDataCon : Core.DataCon.

Axiom tupleDataCon : BasicTypes.Boxity -> BasicTypes.Arity -> Core.DataCon.

Axiom true_RDR : PrelNames.RdrName.

Axiom trueDataConName : Name.Name.

Axiom trueDataConId : Core.Id.

Axiom trueDataCon : Core.DataCon.

Axiom sumTyCon : BasicTypes.Arity -> Core.TyCon.

Axiom sumRepDataConTyCon : Core.TyCon.

Axiom sumRepDataConName : Name.Name.

Axiom sumRepDataCon : Core.DataCon.

Axiom sumDataCon : BasicTypes.ConTag -> BasicTypes.Arity -> Core.DataCon.

Axiom stringTy : AxiomatizedTypes.Type_.

Axiom starKindTyConName : Name.Name.

Axiom starKindTyCon : Core.TyCon.

Axiom runtimeRepTyConName : Name.Name.

Axiom runtimeRepTyCon : Core.TyCon.

Axiom runtimeRepTy : AxiomatizedTypes.Type_.

Axiom runtimeRepSimpleDataConNames : list Name.Name.

Axiom promotedTupleDataCon : BasicTypes.Boxity ->
                             BasicTypes.Arity -> Core.TyCon.

Axiom promotedTrueDataCon : Core.TyCon.

Axiom promotedNothingDataCon : Core.TyCon.

Axiom promotedNilDataCon : Core.TyCon.

Axiom promotedLTDataCon : Core.TyCon.

Axiom promotedJustDataCon : Core.TyCon.

Axiom promotedGTDataCon : Core.TyCon.

Axiom promotedFalseDataCon : Core.TyCon.

Axiom promotedEQDataCon : Core.TyCon.

Axiom promotedConsDataCon : Core.TyCon.

Axiom pcSpecialDataCon : Name.Name ->
                         list AxiomatizedTypes.Type_ ->
                         Core.TyCon -> Core.RuntimeRepInfo -> Core.DataCon.

Axiom pcDataConWithFixity' : bool ->
                             Name.Name ->
                             Unique.Unique ->
                             Core.RuntimeRepInfo ->
                             list Core.TyVar ->
                             list Core.TyVar ->
                             list Core.TyVar -> list AxiomatizedTypes.Type_ -> Core.TyCon -> Core.DataCon.

Axiom pcDataConWithFixity : bool ->
                            Name.Name ->
                            list Core.TyVar ->
                            list Core.TyVar ->
                            list Core.TyVar -> list AxiomatizedTypes.Type_ -> Core.TyCon -> Core.DataCon.

Axiom pcDataCon : Name.Name ->
                  list Core.TyVar -> list AxiomatizedTypes.Type_ -> Core.TyCon -> Core.DataCon.

Axiom parrTyCon_RDR : PrelNames.RdrName.

Axiom parrTyConName : Name.Name.

Axiom parrTyCon : Core.TyCon.

Axiom parrFakeCon : BasicTypes.Arity -> Core.DataCon.

Axiom parrDataConName : Name.Name.

Axiom parrDataCon : Core.DataCon.

Axiom pairTyCon : Core.TyCon.

Axiom orderingTyCon : Core.TyCon.

Axiom nothingDataConName : Name.Name.

Axiom nothingDataCon : Core.DataCon.

Axiom nilDataConName : Name.Name.

Axiom nilDataCon : Core.DataCon.

Axiom mk_tuple : BasicTypes.Boxity -> nat -> (Core.TyCon * Core.DataCon)%type.

Axiom mk_special_dc_name : FastString.FastString ->
                           Unique.Unique -> Core.DataCon -> Name.Name.

Axiom mk_class : Core.TyCon ->
                 AxiomatizedTypes.PredType -> Core.Id -> Core.Class.

Axiom mkWiredInTyConName : Name.BuiltInSyntax ->
                           Module.Module ->
                           FastString.FastString -> Unique.Unique -> Core.TyCon -> Name.Name.

Axiom mkWiredInIdName : Module.Module ->
                        FastString.FastString -> Unique.Unique -> Core.Id -> Name.Name.

Axiom mkWiredInDataConName : Name.BuiltInSyntax ->
                             Module.Module ->
                             FastString.FastString -> Unique.Unique -> Core.DataCon -> Name.Name.

Axiom mkUnboxedTupleStr : BasicTypes.Arity -> GHC.Base.String.

Axiom mkTupleTy : BasicTypes.Boxity ->
                  list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkTupleOcc : OccName.NameSpace ->
                   BasicTypes.Boxity -> BasicTypes.Arity -> OccName.OccName.

Axiom mkSumTyConOcc : BasicTypes.Arity -> OccName.OccName.

Axiom mkSumTy : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkSumDataConOcc : BasicTypes.ConTag ->
                        BasicTypes.Arity -> OccName.OccName.

Axiom mkPromotedListTy : AxiomatizedTypes.Kind ->
                         list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkPArrTy : AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkPArrFakeCon : nat -> Core.DataCon.

Axiom mkListTy : AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkFunKind : AxiomatizedTypes.Kind ->
                  AxiomatizedTypes.Kind -> AxiomatizedTypes.Kind.

Axiom mkForAllKind : Core.TyVar ->
                     Core.ArgFlag -> AxiomatizedTypes.Kind -> AxiomatizedTypes.Kind.

Axiom mkDataConWorkerName : Core.DataCon -> Unique.Unique -> Name.Name.

Axiom mkConstraintTupleStr : BasicTypes.Arity -> GHC.Base.String.

Axiom mkCTupleOcc : OccName.NameSpace -> BasicTypes.Arity -> OccName.OccName.

Axiom mkBoxedTupleTy : list AxiomatizedTypes.Type_ -> AxiomatizedTypes.Type_.

Axiom mkBoxedTupleStr : BasicTypes.Arity -> GHC.Base.String.

Axiom maybeTyConName : Name.Name.

Axiom maybeTyCon : Core.TyCon.

Axiom ltDataConId : Core.Id.

Axiom ltDataCon : Core.DataCon.

Axiom listTyCon_RDR : PrelNames.RdrName.

Axiom listTyConName : Name.Name.

Axiom listTyCon : Core.TyCon.

Axiom liftedTypeKindTyConName : Name.Name.

Axiom liftedTypeKindTyCon : Core.TyCon.

Axiom liftedRepTy : AxiomatizedTypes.Type_.

Axiom liftedRepDataConTyCon : Core.TyCon.

Axiom justDataConName : Name.Name.

Axiom justDataCon : Core.DataCon.

Axiom isPArrTyCon : Core.TyCon -> bool.

Axiom isPArrFakeCon : Core.DataCon -> bool.

Axiom isCTupleTyConName : Name.Name -> bool.

Axiom isBuiltInOcc_maybe : OccName.OccName -> option Name.Name.

Axiom intTyCon_RDR : PrelNames.RdrName.

Axiom intTyConName : Name.Name.

Axiom intTyCon : Core.TyCon.

Axiom intTy : AxiomatizedTypes.Type_.

Axiom intDataCon_RDR : PrelNames.RdrName.

Axiom intDataConName : Name.Name.

Axiom intDataCon : Core.DataCon.

Axiom heqTyConName : Name.Name.

Axiom heqSCSelIdName : Name.Name.

Axiom heqDataConName : Name.Name.

Axiom gtDataConId : Core.Id.

Axiom gtDataCon : Core.DataCon.

Axiom floatTyConName : Name.Name.

Axiom floatTyCon : Core.TyCon.

Axiom floatTy : AxiomatizedTypes.Type_.

Axiom floatDataConName : Name.Name.

Axiom floatDataCon : Core.DataCon.

Axiom false_RDR : PrelNames.RdrName.

Axiom falseDataConName : Name.Name.

Axiom falseDataConId : Core.Id.

Axiom falseDataCon : Core.DataCon.

Axiom extractPromotedList : AxiomatizedTypes.Type_ ->
                            list AxiomatizedTypes.Type_.

Axiom eqDataConId : Core.Id.

Axiom eqDataCon : Core.DataCon.

Axiom doubleTyConName : Name.Name.

Axiom doubleTyCon : Core.TyCon.

Axiom doubleTy : AxiomatizedTypes.Type_.

Axiom doubleDataConName : Name.Name.

Axiom doubleDataCon : Core.DataCon.

Axiom constraintKindTyConName : Name.Name.

Axiom constraintKindTyCon : Core.TyCon.

Axiom consDataCon_RDR : PrelNames.RdrName.

Axiom consDataConName : Name.Name.

Axiom consDataCon : Core.DataCon.

Axiom commas : BasicTypes.Arity -> GHC.Base.String.

Axiom coercibleTyConName : Name.Name.

Axiom coercibleSCSelIdName : Name.Name.

Axiom coercibleDataConName : Name.Name.

Axiom charTyCon_RDR : PrelNames.RdrName.

Axiom charTyConName : Name.Name.

Axiom charTyCon : Core.TyCon.

Axiom charTy : AxiomatizedTypes.Type_.

Axiom charDataConName : Name.Name.

Axiom charDataCon : Core.DataCon.

Axiom cTupleTyConNames : list Name.Name.

Axiom cTupleTyConNameSet : NameSet.NameSet.

Axiom cTupleTyConName : BasicTypes.Arity -> Name.Name.

Axiom cTupleDataConNames : list Name.Name.

Axiom cTupleDataConName : BasicTypes.Arity -> Name.Name.

Axiom boxing_constr_env : NameEnv.NameEnv Core.DataCon.

Axiom boxingDataCon_maybe : Core.TyCon -> option Core.DataCon.

Axiom boolTyCon_RDR : PrelNames.RdrName.

Axiom boolTyConName : Name.Name.

Axiom boolTyCon : Core.TyCon.

Axiom boolTy : AxiomatizedTypes.Type_.

Axiom anyTypeOfKind : AxiomatizedTypes.Kind -> AxiomatizedTypes.Type_.

Axiom anyTyConName : Name.Name.

Axiom anyTyCon : Core.TyCon.

Axiom anyTy : AxiomatizedTypes.Type_.

Axiom alpha_tyvar : list Core.TyVar.

Axiom alpha_ty : list AxiomatizedTypes.Type_.

Axiom Core.liftedTypeKind : AxiomatizedTypes.Kind.

Axiom Core.constraintKind : AxiomatizedTypes.Kind.

(* External variables:
     bool list nat op_zt__ option AxiomatizedTypes.Kind AxiomatizedTypes.PredType
     AxiomatizedTypes.Type_ BasicTypes.Arity BasicTypes.Boxity BasicTypes.ConTag
     BasicTypes.TupleSort Core.ArgFlag Core.Class Core.DataCon Core.Id
     Core.RuntimeRepInfo Core.TyCon Core.TyVar FastString.FastString GHC.Base.String
     Module.Module Name.BuiltInSyntax Name.Name NameEnv.NameEnv NameSet.NameSet
     OccName.NameSpace OccName.OccName PrelNames.RdrName Unique.Unique
*)
