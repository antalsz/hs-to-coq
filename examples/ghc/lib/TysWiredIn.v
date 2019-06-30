(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

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

Axiom wordTy : unit.

Axiom wordDataConName : Name.Name.

Axiom wordDataCon : Core.DataCon.

Axiom word8TyConName : Name.Name.

Axiom word8TyCon : Core.TyCon.

Axiom word8Ty : unit.

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

Axiom unitTy : unit.

Axiom unitDataConId : Core.Id.

Axiom unitDataCon : Core.DataCon.

Axiom unicodeStarKindTyConName : Name.Name.

Axiom unicodeStarKindTyCon : Core.TyCon.

Axiom unboxedUnitTyCon : Core.TyCon.

Axiom unboxedUnitDataCon : Core.DataCon.

Axiom unboxedTupleSumKind : Core.TyCon -> list unit -> unit.

Axiom unboxedTupleKind : list unit -> unit.

Axiom unboxedSumKind : list unit -> unit.

Axiom typeSymbolKindConName : Name.Name.

Axiom typeSymbolKindCon : Core.TyCon.

Axiom typeSymbolKind : unit.

Axiom typeNatKindConName : Name.Name.

Axiom typeNatKindCon : Core.TyCon.

Axiom typeNatKind : unit.

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

Axiom stringTy : unit.

Axiom starKindTyConName : Name.Name.

Axiom starKindTyCon : Core.TyCon.

Axiom runtimeRepTyConName : Name.Name.

Axiom runtimeRepTyCon : Core.TyCon.

Axiom runtimeRepTy : unit.

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
                         list unit -> Core.TyCon -> Core.RuntimeRepInfo -> Core.DataCon.

Axiom pcDataConWithFixity' : bool ->
                             Name.Name ->
                             Unique.Unique ->
                             Core.RuntimeRepInfo ->
                             list Core.TyVar ->
                             list Core.TyVar -> list Core.TyVar -> list unit -> Core.TyCon -> Core.DataCon.

Axiom pcDataConWithFixity : bool ->
                            Name.Name ->
                            list Core.TyVar ->
                            list Core.TyVar -> list Core.TyVar -> list unit -> Core.TyCon -> Core.DataCon.

Axiom pcDataCon : Name.Name ->
                  list Core.TyVar -> list unit -> Core.TyCon -> Core.DataCon.

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

Axiom mk_class : Core.TyCon -> unit -> Core.Id -> Core.Class.

Axiom mkWiredInTyConName : Name.BuiltInSyntax ->
                           Module.Module ->
                           FastString.FastString -> Unique.Unique -> Core.TyCon -> Name.Name.

Axiom mkWiredInIdName : Module.Module ->
                        FastString.FastString -> Unique.Unique -> Core.Id -> Name.Name.

Axiom mkWiredInDataConName : Name.BuiltInSyntax ->
                             Module.Module ->
                             FastString.FastString -> Unique.Unique -> Core.DataCon -> Name.Name.

Axiom mkUnboxedTupleStr : BasicTypes.Arity -> GHC.Base.String.

Axiom mkTupleTy : BasicTypes.Boxity -> list unit -> unit.

Axiom mkTupleOcc : OccName.NameSpace ->
                   BasicTypes.Boxity -> BasicTypes.Arity -> OccName.OccName.

Axiom mkSumTyConOcc : BasicTypes.Arity -> OccName.OccName.

Axiom mkSumTy : list unit -> unit.

Axiom mkSumDataConOcc : BasicTypes.ConTag ->
                        BasicTypes.Arity -> OccName.OccName.

Axiom mkPromotedListTy : unit -> list unit -> unit.

Axiom mkPArrTy : unit -> unit.

Axiom mkPArrFakeCon : nat -> Core.DataCon.

Axiom mkListTy : unit -> unit.

Axiom mkFunKind : unit -> unit -> unit.

Axiom mkForAllKind : Core.TyVar -> Core.ArgFlag -> unit -> unit.

Axiom mkDataConWorkerName : Core.DataCon -> Unique.Unique -> Name.Name.

Axiom mkConstraintTupleStr : BasicTypes.Arity -> GHC.Base.String.

Axiom mkCTupleOcc : OccName.NameSpace -> BasicTypes.Arity -> OccName.OccName.

Axiom mkBoxedTupleTy : list unit -> unit.

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

Axiom liftedRepTy : unit.

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

Axiom intTy : unit.

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

Axiom floatTy : unit.

Axiom floatDataConName : Name.Name.

Axiom floatDataCon : Core.DataCon.

Axiom false_RDR : PrelNames.RdrName.

Axiom falseDataConName : Name.Name.

Axiom falseDataConId : Core.Id.

Axiom falseDataCon : Core.DataCon.

Axiom extractPromotedList : unit -> list unit.

Axiom eqDataConId : Core.Id.

Axiom eqDataCon : Core.DataCon.

Axiom doubleTyConName : Name.Name.

Axiom doubleTyCon : Core.TyCon.

Axiom doubleTy : unit.

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

Axiom charTy : unit.

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

Axiom boolTy : unit.

Axiom anyTypeOfKind : unit -> unit.

Axiom anyTyConName : Name.Name.

Axiom anyTyCon : Core.TyCon.

Axiom anyTy : unit.

Axiom alpha_tyvar : list Core.TyVar.

Axiom alpha_ty : list unit.

Axiom tt : unit.

(* External variables:
     bool list nat op_zt__ option unit BasicTypes.Arity BasicTypes.Boxity
     BasicTypes.ConTag BasicTypes.TupleSort Core.ArgFlag Core.Class Core.DataCon
     Core.Id Core.RuntimeRepInfo Core.TyCon Core.TyVar FastString.FastString
     GHC.Base.String Module.Module Name.BuiltInSyntax Name.Name NameEnv.NameEnv
     NameSet.NameSet OccName.NameSpace OccName.OccName PrelNames.RdrName
     Unique.Unique
*)
