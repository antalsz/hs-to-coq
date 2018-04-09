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
Require CoreSyn.
Require DataCon.
Require Demand.
Require FastString.
Require GHC.Num.
Require IdInfo.
Require Module.
Require Name.
Require OccName.
Require SrcLoc.
Require UniqSupply.
Require Unique.
Require Var.

(* No type declarations to convert. *)
(* Midamble *)

(* Record selectors *)
Import IdInfo.

(*
Parameter hasNoBinding : Var.Id -> bool.

Parameter isDictId : Var.Id -> bool.

Parameter isStrictId : Var.Id -> bool.

Parameter idRepArity : Var.Id -> BasicTypes.RepArity.

Parameter isClassOpId_maybe : Var.Id -> option Class.Class.

Parameter isDataConId_maybe : Var.Id -> option DataCon.DataCon.

Parameter isDataConWorkId : Var.Id -> bool.

Parameter isDataConWorkId_maybe : Var.Id -> option DataCon.DataCon.

Parameter isEvVar : Var -> bool.

Parameter isFCallId : Var.Id -> bool.

Parameter isFCallId_maybe : Var.Id -> option unit.

Parameter isPrimOpId : Var.Id -> bool.

Parameter isPrimOpId_maybe : Var.Id -> option unit.

Parameter mkExportedVanillaId : Name.Name -> unit -> Var.Id.

Parameter mkVanillaGlobalWithInfo : Name.Name -> unit -> IdInfo.IdInfo -> Var.Id.

Parameter mkVanillaGlobal : Name.Name -> Core.Type_ -> Var.Id.

Parameter mkLocalCoVar : Name.Name -> Core.Type_ -> CoVar.

Parameter mkLocalIdOrCoVarWithInfo
    : Name.Name -> Core.Type_ -> IdInfo.IdInfo -> Var.Id.

Parameter mkLocalIdWithInfo : Name.Name -> Core.Type_  -> IdInfo.IdInfo -> Var.Id.

Parameter mkLocalId : Name.Name -> Core.Type_  -> Var.Id.

Parameter mkSysLocal
    : FastString.FastString -> Unique.Unique -> Core.Type_ -> Var.Id.

Parameter mkLocalIdOrCoVar : Name.Name -> Core.Type_ -> Var.Id.

(* zipwith enumFrom !!! *)
Parameter mkTemplateLocalsNum : GHC.Num.Int -> list Core.Type_ -> list Var.Id.

Parameter setIdType : Var.Id -> Core.Type_ -> Var.Id.
*)
(* Converted value declarations: *)

Axiom idIsFrom : Module.Module -> Var.Id -> bool.

Axiom localiseId : Var.Id -> Var.Id.

Axiom idName : Var.Id -> Name.Name.

Axiom idUnique : Var.Id -> Unique.Unique.

Axiom isProbablyOneShotLambda : Var.Id -> bool.

Axiom isOneShotBndr : Var.Var -> bool.

Axiom idStateHackOneShotInfo : Var.Id -> BasicTypes.OneShotInfo.

(* isStrictId skipped *)

Axiom idFunRepArity : Var.Id -> BasicTypes.RepArity.

(* isDictId skipped *)

Axiom idType : Var.Id -> unit.

Axiom setIdName : Var.Id -> Name.Name -> Var.Id.

Axiom setIdUnique : Var.Id -> Unique.Unique -> Var.Id.

(* setIdType skipped *)

Axiom setIdExported : Var.Id -> Var.Id.

Axiom setIdNotExported : Var.Id -> Var.Id.

Axiom asJoinId_maybe : Var.Id -> option BasicTypes.JoinArity -> Var.Id.

Axiom zapJoinId : Var.Id -> Var.Id.

Axiom zapIdTailCallInfo : Var.Id -> Var.Id.

Axiom zapIdUsedOnceInfo : Var.Id -> Var.Id.

Axiom zapIdUsageEnvInfo : Var.Id -> Var.Id.

Axiom zapIdUsageInfo : Var.Id -> Var.Id.

Axiom zapIdDemandInfo : Var.Id -> Var.Id.

Axiom zapFragileIdInfo : Var.Id -> Var.Id.

Axiom zapLamIdInfo : Var.Id -> Var.Id.

Axiom zapInfo : (IdInfo.IdInfo -> option IdInfo.IdInfo) -> Var.Id -> Var.Id.

Axiom maybeModifyIdInfo : option IdInfo.IdInfo -> Var.Id -> Var.Id.

Axiom transferPolyIdInfo : Var.Id -> list Var.Var -> Var.Id -> Var.Id.

Axiom updOneShotInfo : Var.Id -> BasicTypes.OneShotInfo -> Var.Id.

Axiom setIdOneShotInfo : Var.Id -> BasicTypes.OneShotInfo -> Var.Id.

Axiom clearOneShotLambda : Var.Id -> Var.Id.

Axiom setOneShotLambda : Var.Id -> Var.Id.

Axiom setInlineActivation : Var.Id -> BasicTypes.Activation -> Var.Id.

Axiom modifyInlinePragma : Var.Id ->
                           (BasicTypes.InlinePragma -> BasicTypes.InlinePragma) -> Var.Id.

Axiom setInlinePragma : Var.Id -> BasicTypes.InlinePragma -> Var.Id.

Axiom zapIdOccInfo : Var.Id -> Var.Id.

Axiom setIdOccInfo : Var.Id -> BasicTypes.OccInfo -> Var.Id.

Axiom setIdCafInfo : Var.Id -> IdInfo.CafInfo -> Var.Id.

Axiom setIdSpecialisation : Var.Id -> IdInfo.RuleInfo -> Var.Id.

Axiom setIdDemandInfo : Var.Id -> Demand.Demand -> Var.Id.

Axiom zapStableUnfolding : Var.Id -> Var.Id.

Axiom setCaseBndrEvald : DataCon.StrictnessMark -> Var.Id -> Var.Id.

Axiom setIdUnfolding : Var.Id -> CoreSyn.Unfolding -> Var.Id.

Axiom zapIdStrictness : Var.Id -> Var.Id.

Axiom setIdStrictness : Var.Id -> Demand.StrictSig -> Var.Id.

Axiom setIdCallArity : Var.Id -> BasicTypes.Arity -> Var.Id.

Axiom setIdArity : Var.Id -> BasicTypes.Arity -> Var.Id.

Axiom modifyIdInfo : (IdInfo.IdInfo -> IdInfo.IdInfo) -> Var.Id -> Var.Id.

Axiom setIdInfo : Var.Id -> IdInfo.IdInfo -> Var.Id.

Axiom lazySetIdInfo : Var.Id -> IdInfo.IdInfo -> Var.Id.

(* mkVanillaGlobal skipped *)

(* mkVanillaGlobalWithInfo skipped *)

Axiom mkGlobalId : IdInfo.IdDetails ->
                   Name.Name -> unit -> IdInfo.IdInfo -> Var.Id.

Axiom mkUserLocal : OccName.OccName ->
                    Unique.Unique -> unit -> SrcLoc.SrcSpan -> Var.Id.

Axiom mkSysLocalM : forall {m},
                    forall `{UniqSupply.MonadUnique m}, FastString.FastString -> unit -> m Var.Id.

Axiom mkSysLocal : FastString.FastString -> Unique.Unique -> unit -> Var.Id.

Axiom mkWorkerId : Unique.Unique -> Var.Id -> unit -> Var.Id.

Axiom mkUserLocalOrCoVar : OccName.OccName ->
                           Unique.Unique -> unit -> SrcLoc.SrcSpan -> Var.Id.

Axiom mkTemplateLocals : list unit -> list Var.Id.

(* mkTemplateLocalsNum skipped *)

Axiom mkTemplateLocal : GHC.Num.Int -> unit -> Var.Id.

Axiom mkSysLocalOrCoVarM : forall {m},
                           forall `{UniqSupply.MonadUnique m}, FastString.FastString -> unit -> m Var.Id.

Axiom mkSysLocalOrCoVar : FastString.FastString ->
                          Unique.Unique -> unit -> Var.Id.

(* mkLocalIdOrCoVar skipped *)

(* mkLocalId skipped *)

(* mkLocalCoVar skipped *)

(* mkLocalIdOrCoVarWithInfo skipped *)

(* mkLocalIdWithInfo skipped *)

Axiom mkExportedLocalId : IdInfo.IdDetails -> Name.Name -> unit -> Var.Id.

(* mkExportedVanillaId skipped *)

Axiom recordSelectorTyCon : Var.Id -> IdInfo.RecSelParent.

Axiom isRecordSelector : Var.Id -> bool.

Axiom isDataConRecordSelector : Var.Id -> bool.

Axiom isPatSynRecordSelector : Var.Id -> bool.

Axiom isNaughtyRecordSelector : Var.Id -> bool.

(* isClassOpId_maybe skipped *)

(* isPrimOpId skipped *)

Axiom isDFunId : Var.Id -> bool.

(* isPrimOpId_maybe skipped *)

(* isFCallId skipped *)

(* isFCallId_maybe skipped *)

(* isConLikeId skipped *)

(* isDataConWorkId skipped *)

(* isDataConWorkId_maybe skipped *)

(* idDataCon skipped *)

(* isDataConId_maybe skipped *)

Axiom isExitJoinId : Var.Var -> bool.

Axiom isJoinId : Var.Var -> bool.

Axiom idJoinArity : Var.JoinId -> BasicTypes.JoinArity.

Axiom isJoinId_maybe : Var.Var -> option BasicTypes.JoinArity.

(* hasNoBinding skipped *)

Axiom isImplicitId : Var.Id -> bool.

(* isDeadBinder skipped *)

(* isEvVar skipped *)

Axiom asJoinId : Var.Id -> BasicTypes.JoinArity -> Var.JoinId.

(* idArity skipped *)

(* idCallArity skipped *)

(* isBottomingId skipped *)

(* idStrictness skipped *)

Axiom idUnfolding : Var.Id -> CoreSyn.Unfolding.

Axiom realIdUnfolding : Var.Id -> CoreSyn.Unfolding.

(* idDemandInfo skipped *)

(* idHasRules skipped *)

(* idCoreRules skipped *)

(* idSpecialisation skipped *)

(* idCafInfo skipped *)

(* idOccInfo skipped *)

(* idRuleMatchInfo skipped *)

(* idInlineActivation skipped *)

(* idInlinePragma skipped *)

(* idOneShotInfo skipped *)

(* typeOneShot skipped *)

Axiom stateHackOneShot : BasicTypes.OneShotInfo.

(* isStateHackType skipped *)

Axiom isNeverLevPolyId : Var.Id -> bool.

(* External variables:
     bool list option unit BasicTypes.Activation BasicTypes.Arity
     BasicTypes.InlinePragma BasicTypes.JoinArity BasicTypes.OccInfo
     BasicTypes.OneShotInfo BasicTypes.RepArity CoreSyn.Unfolding
     DataCon.StrictnessMark Demand.Demand Demand.StrictSig FastString.FastString
     GHC.Num.Int IdInfo.CafInfo IdInfo.IdDetails IdInfo.IdInfo IdInfo.RecSelParent
     IdInfo.RuleInfo Module.Module Name.Name OccName.OccName SrcLoc.SrcSpan
     UniqSupply.MonadUnique Unique.Unique Var.Id Var.JoinId Var.Var
*)
