(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* No imports to convert. *)

(* No type declarations to convert. *)
(* Converted value declarations: *)

Axiom idIsFrom : forall {A : Type}, A.

Axiom localiseId : forall {A : Type}, A.

Axiom idName : forall {A : Type}, A.

Axiom idUnique : forall {A : Type}, A.

Axiom isStrictId : forall {A : Type}, A.

Axiom idRepArity : forall {A : Type}, A.

Axiom isDictId : forall {A : Type}, A.

Axiom idType : forall {A : Type}, A.

Axiom setIdName : forall {A : Type}, A.

Axiom setIdUnique : forall {A : Type}, A.

Axiom setIdType : forall {A : Type}, A.

Axiom setIdExported : forall {A : Type}, A.

Axiom setIdNotExported : forall {A : Type}, A.

Axiom zapIdUsageInfo : forall {A : Type}, A.

Axiom zapIdDemandInfo : forall {A : Type}, A.

Axiom zapFragileIdInfo : forall {A : Type}, A.

Axiom zapLamIdInfo : forall {A : Type}, A.

Axiom zapInfo : forall {A : Type}, A.

Axiom maybeModifyIdInfo : forall {A : Type}, A.

Axiom transferPolyIdInfo : forall {A : Type}, A.

Axiom updOneShotInfo : forall {A : Type}, A.

Axiom setIdOneShotInfo : forall {A : Type}, A.

Axiom clearOneShotLambda : forall {A : Type}, A.

Axiom setOneShotLambda : forall {A : Type}, A.

Axiom setInlineActivation : forall {A : Type}, A.

Axiom modifyInlinePragma : forall {A : Type}, A.

Axiom setInlinePragma : forall {A : Type}, A.

Axiom zapIdOccInfo : forall {A : Type}, A.

Axiom setIdOccInfo : forall {A : Type}, A.

Axiom setIdCafInfo : forall {A : Type}, A.

Axiom setIdSpecialisation : forall {A : Type}, A.

Axiom setIdDemandInfo : forall {A : Type}, A.

Axiom setIdUnfolding : forall {A : Type}, A.

Axiom setIdUnfoldingLazily : forall {A : Type}, A.

Axiom zapIdStrictness : forall {A : Type}, A.

Axiom setIdStrictness : forall {A : Type}, A.

Axiom setIdCallArity : forall {A : Type}, A.

Axiom setIdArity : forall {A : Type}, A.

Axiom modifyIdInfo : forall {A : Type}, A.

Axiom setIdInfo : forall {A : Type}, A.

Axiom lazySetIdInfo : forall {A : Type}, A.

Axiom mkVanillaGlobal : forall {A : Type}, A.

Axiom mkVanillaGlobalWithInfo : forall {A : Type}, A.

Axiom mkGlobalId : forall {A : Type}, A.

Axiom mkUserLocal : forall {A : Type}, A.

Axiom mkSysLocalM : forall {A : Type}, A.

Axiom mkSysLocal : forall {A : Type}, A.

Axiom mkWorkerId : forall {A : Type}, A.

Axiom mkUserLocalOrCoVar : forall {A : Type}, A.

Axiom mkTemplateLocals : forall {A : Type}, A.

Axiom mkTemplateLocalsNum : forall {A : Type}, A.

Axiom mkTemplateLocal : forall {A : Type}, A.

Axiom mkSysLocalOrCoVarM : forall {A : Type}, A.

Axiom mkSysLocalOrCoVar : forall {A : Type}, A.

Axiom mkLocalIdOrCoVar : forall {A : Type}, A.

Axiom mkLocalId : forall {A : Type}, A.

Axiom mkLocalCoVar : forall {A : Type}, A.

Axiom mkLocalIdOrCoVarWithInfo : forall {A : Type}, A.

Axiom mkLocalIdWithInfo : forall {A : Type}, A.

Axiom mkExportedLocalId : forall {A : Type}, A.

Axiom mkExportedVanillaId : forall {A : Type}, A.

Axiom recordSelectorTyCon : forall {A : Type}, A.

Axiom isRecordSelector : forall {A : Type}, A.

Axiom isDataConRecordSelector : forall {A : Type}, A.

Axiom isPatSynRecordSelector : forall {A : Type}, A.

Axiom isNaughtyRecordSelector : forall {A : Type}, A.

Axiom isClassOpId_maybe : forall {A : Type}, A.

Axiom isPrimOpId : forall {A : Type}, A.

Axiom isDFunId : forall {A : Type}, A.

Axiom isPrimOpId_maybe : forall {A : Type}, A.

Axiom isFCallId : forall {A : Type}, A.

Axiom isFCallId_maybe : forall {A : Type}, A.

Axiom isConLikeId : forall {A : Type}, A.

Axiom isDataConWorkId : forall {A : Type}, A.

Axiom isDataConWorkId_maybe : forall {A : Type}, A.

Axiom idDataCon : forall {A : Type}, A.

Axiom isDataConId_maybe : forall {A : Type}, A.

Axiom hasNoBinding : forall {A : Type}, A.

Axiom isImplicitId : forall {A : Type}, A.

Axiom isDeadBinder : forall {A : Type}, A.

Axiom isEvVar : forall {A : Type}, A.

Axiom idArity : forall {A : Type}, A.

Axiom idCallArity : forall {A : Type}, A.

Axiom isBottomingId : forall {A : Type}, A.

Axiom idStrictness : forall {A : Type}, A.

Axiom idUnfolding : forall {A : Type}, A.

Axiom realIdUnfolding : forall {A : Type}, A.

Axiom idDemandInfo : forall {A : Type}, A.

Axiom idHasRules : forall {A : Type}, A.

Axiom idCoreRules : forall {A : Type}, A.

Axiom idSpecialisation : forall {A : Type}, A.

Axiom idCafInfo : forall {A : Type}, A.

Axiom idOccInfo : forall {A : Type}, A.

Axiom idRuleMatchInfo : forall {A : Type}, A.

Axiom idInlineActivation : forall {A : Type}, A.

Axiom idInlinePragma : forall {A : Type}, A.

Axiom isProbablyOneShotLambda : forall {A : Type}, A.

Axiom isOneShotBndr : forall {A : Type}, A.

Axiom isOneShotLambda : forall {A : Type}, A.

Axiom idOneShotInfo : forall {A : Type}, A.

Axiom typeOneShot : forall {A : Type}, A.

Axiom stateHackOneShot : forall {A : Type}, A.

Axiom isStateHackType : forall {A : Type}, A.
