(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Panic.

(* Converted imports: *)

Require BasicTypes.
Require CoreSyn.
Require CoreType.
Require DataCon.
Require Demand.
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require IdInfo.
Require IdInfo2.
Require Maybes.
Require Module.
Require Name.
Require OccName.
Require Panic.
Require RepType.
Require SrcLoc.
Require UniqSupply.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)
(* Midamble *)

(* Record selectors *)
Import IdInfo.
Import IdInfo2.
Import Core.

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

(* Converted value declarations: *)

Axiom asJoinId : forall {A : Type}, A.

(* Translating `asJoinId' failed: using a record pattern for the unknown
   constructor `JoinId' unsupported *)

Definition idArity : CoreType.Id -> BasicTypes.Arity :=
  fun id => IdInfo.arityInfo (CoreType.idInfo id).

Definition idCafInfo : CoreType.Id -> IdInfo.CafInfo :=
  fun id => IdInfo.cafInfo (CoreType.idInfo id).

Definition idCallArity : CoreType.Id -> BasicTypes.Arity :=
  fun id => IdInfo.callArityInfo (CoreType.idInfo id).

Definition idDataCon : CoreType.Id -> DataCon.DataCon :=
  fun id =>
    Maybes.orElse (isDataConId_maybe id) (Panic.panicStr (GHC.Base.hs_string__
                                                          "idDataCon") (Panic.noString id)).

Definition idDemandInfo : CoreType.Id -> Demand.Demand :=
  fun id => IdInfo2.demandInfo (CoreType.idInfo id).

Definition idInlinePragma : CoreType.Id -> BasicTypes.InlinePragma :=
  fun id => IdInfo.inlinePragInfo (CoreType.idInfo id).

Definition idRuleMatchInfo : CoreType.Id -> BasicTypes.RuleMatchInfo :=
  fun id => BasicTypes.inlinePragmaRuleMatchInfo (idInlinePragma id).

Definition isConLikeId : CoreType.Id -> bool :=
  fun id => orb (isDataConWorkId id) (BasicTypes.isConLike (idRuleMatchInfo id)).

Definition idInlineActivation : CoreType.Id -> BasicTypes.Activation :=
  fun id => BasicTypes.inlinePragmaActivation (idInlinePragma id).

Definition idName : CoreType.Id -> Name.Name :=
  CoreType.varName.

Definition idIsFrom : Module.Module -> CoreType.Id -> bool :=
  fun mod_ id => Name.nameIsLocalOrFrom mod_ (idName id).

Definition idOccInfo : CoreType.Id -> BasicTypes.OccInfo :=
  fun id => IdInfo.occInfo (CoreType.idInfo id).

Definition isDeadBinder : CoreType.Id -> bool :=
  fun bndr =>
    if CoreType.isId bndr : bool then BasicTypes.isDeadOcc (idOccInfo bndr) else
    false.

Definition idOneShotInfo : CoreType.Id -> BasicTypes.OneShotInfo :=
  fun id => IdInfo.oneShotInfo (CoreType.idInfo id).

Definition idSpecialisation : CoreType.Id -> IdInfo.RuleInfo :=
  fun id => IdInfo.ruleInfo (CoreType.idInfo id).

Definition idHasRules : CoreType.Id -> bool :=
  fun id => negb (IdInfo.isEmptyRuleInfo (idSpecialisation id)).

Definition idCoreRules : CoreType.Id -> list CoreSyn.CoreRule :=
  fun id => IdInfo2.ruleInfoRules (idSpecialisation id).

Definition idStrictness : CoreType.Id -> Demand.StrictSig :=
  fun id => IdInfo2.strictnessInfo (CoreType.idInfo id).

Definition isBottomingId : CoreType.Var -> bool :=
  fun v =>
    if CoreType.isId v : bool then Demand.isBottomingSig (idStrictness v) else
    false.

Definition idType : CoreType.Id -> CoreType.Kind :=
  CoreType.varType.

Definition localiseId : CoreType.Id -> CoreType.Id :=
  fun id =>
    let name := idName id in
    if (if andb Util.debugIsOn (negb (CoreType.isId id)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Id.hs")
              #209)
        else andb (CoreType.isLocalId id) (Name.isInternalName name)) : bool
    then id else
    CoreType.mkLocalVar (CoreType.idDetails id) (Name.localiseName name) (idType id)
    (CoreType.idInfo id).

Definition idFunRepArity : CoreType.Id -> BasicTypes.RepArity :=
  fun x => RepType.countFunRepArgs (idArity x) (idType x).

Definition idUnfolding : CoreType.Id -> CoreSyn.Unfolding :=
  fun id =>
    let info := CoreType.idInfo id in
    if BasicTypes.isStrongLoopBreaker (IdInfo.occInfo info) : bool
    then CoreSyn.NoUnfolding else
    IdInfo2.unfoldingInfo info.

Definition idUnique : CoreType.Id -> Unique.Unique :=
  CoreType.varUnique.

Axiom isDFunId : forall {A : Type}, A.

(* Translating `isDFunId' failed: using a record pattern for the unknown
   constructor `DFunId' unsupported *)

Axiom isDataConRecordSelector : forall {A : Type}, A.

(* Translating `isDataConRecordSelector' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

Axiom isImplicitId : forall {A : Type}, A.

(* Translating `isImplicitId' failed: using a record pattern for the unknown
   constructor `FCallId' unsupported *)

Axiom isJoinId : forall {A : Type}, A.

Definition isExitJoinId : CoreType.Var -> bool :=
  fun id =>
    andb (isJoinId id) (andb (BasicTypes.isOneOcc (idOccInfo id))
                             (BasicTypes.occ_in_lam (idOccInfo id))).

(* Translating `isJoinId' failed: using a record pattern for the unknown
   constructor `JoinId' unsupported *)

Definition isJoinId_maybe : CoreType.Var -> option BasicTypes.JoinArity :=
  fun id =>
    if CoreType.isId id : bool
    then if andb Util.debugIsOn (negb (CoreType.isId id)) : bool
         then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                          "ghc/compiler/basicTypes/Id.hs") #494 (Panic.noString id))
         else match CoreType.idDetails id with
              | IdInfo.JoinId arity => Some arity
              | _ => None
              end else
    None.

Definition idJoinArity : CoreType.JoinId -> BasicTypes.JoinArity :=
  fun id =>
    Maybes.orElse (isJoinId_maybe id) (Panic.panicStr (GHC.Base.hs_string__
                                                       "idJoinArity") (Panic.noString id)).

Axiom isNaughtyRecordSelector : forall {A : Type}, A.

(* Translating `isNaughtyRecordSelector' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

Definition isNeverLevPolyId : CoreType.Id -> bool :=
  IdInfo.isNeverLevPolyIdInfo GHC.Base.∘ CoreType.idInfo.

Axiom isPatSynRecordSelector : forall {A : Type}, A.

(* Translating `isPatSynRecordSelector' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

Axiom isRecordSelector : forall {A : Type}, A.

(* Translating `isRecordSelector' failed: using a record pattern for the unknown
   constructor `RecSelId' unsupported *)

Definition lazySetIdInfo : CoreType.Id -> IdInfo.IdInfo -> CoreType.Id :=
  CoreType.lazySetIdInfo.

Definition maybeModifyIdInfo
   : option IdInfo.IdInfo -> CoreType.Id -> CoreType.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Some new_info, id => lazySetIdInfo id new_info
    | None, id => id
    end.

Definition zapInfo
   : (IdInfo.IdInfo -> option IdInfo.IdInfo) -> CoreType.Id -> CoreType.Id :=
  fun zapper id => maybeModifyIdInfo (zapper (CoreType.idInfo id)) id.

Definition zapFragileIdInfo : CoreType.Id -> CoreType.Id :=
  zapInfo IdInfo.zapFragileInfo.

Definition zapIdDemandInfo : CoreType.Id -> CoreType.Id :=
  zapInfo IdInfo.zapDemandInfo.

Definition zapIdTailCallInfo : CoreType.Id -> CoreType.Id :=
  zapInfo IdInfo.zapTailCallInfo.

Definition zapJoinId : CoreType.Id -> CoreType.Id :=
  fun jid =>
    if isJoinId jid : bool
    then zapIdTailCallInfo (CoreType.setIdDetails jid IdInfo.VanillaId) else
    jid.

Definition asJoinId_maybe
   : CoreType.Id -> option BasicTypes.JoinArity -> CoreType.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | id, Some arity => asJoinId id arity
    | id, None => zapJoinId id
    end.

Definition zapIdUsageEnvInfo : CoreType.Id -> CoreType.Id :=
  zapInfo IdInfo.zapUsageEnvInfo.

Definition zapIdUsageInfo : CoreType.Id -> CoreType.Id :=
  zapInfo IdInfo.zapUsageInfo.

Definition zapIdUsedOnceInfo : CoreType.Id -> CoreType.Id :=
  zapInfo IdInfo.zapUsedOnceInfo.

Definition zapLamIdInfo : CoreType.Id -> CoreType.Id :=
  zapInfo IdInfo.zapLamInfo.

Definition setIdInfo : CoreType.Id -> IdInfo.IdInfo -> CoreType.Id :=
  fun id info => lazySetIdInfo id info.

Definition modifyIdInfo
   : (IdInfo.IdInfo -> IdInfo.IdInfo) -> CoreType.Id -> CoreType.Id :=
  fun fn id => setIdInfo id (fn (CoreType.idInfo id)).

Definition modifyInlinePragma
   : CoreType.Id ->
     (BasicTypes.InlinePragma -> BasicTypes.InlinePragma) -> CoreType.Id :=
  fun id fn =>
    modifyIdInfo (fun info =>
                    IdInfo.setInlinePragInfo info (fn (IdInfo.inlinePragInfo info))) id.

Definition setInlineActivation
   : CoreType.Id -> BasicTypes.Activation -> CoreType.Id :=
  fun id act =>
    modifyInlinePragma id (fun prag =>
                             BasicTypes.setInlinePragmaActivation prag act).

Definition setIdArity : CoreType.Id -> BasicTypes.Arity -> CoreType.Id :=
  fun id arity =>
    modifyIdInfo (fun arg_0__ => IdInfo.setArityInfo arg_0__ arity) id.

Definition setIdCafInfo : CoreType.Id -> IdInfo.CafInfo -> CoreType.Id :=
  fun id caf_info =>
    modifyIdInfo (fun arg_0__ => IdInfo.setCafInfo arg_0__ caf_info) id.

Definition setIdCallArity : CoreType.Id -> BasicTypes.Arity -> CoreType.Id :=
  fun id arity =>
    modifyIdInfo (fun arg_0__ => IdInfo.setCallArityInfo arg_0__ arity) id.

Definition setIdDemandInfo : CoreType.Id -> Demand.Demand -> CoreType.Id :=
  fun id dmd =>
    modifyIdInfo (fun arg_0__ => IdInfo2.setDemandInfo arg_0__ dmd) id.

Definition setIdOccInfo : CoreType.Id -> BasicTypes.OccInfo -> CoreType.Id :=
  fun id occ_info =>
    modifyIdInfo (fun arg_0__ => IdInfo.setOccInfo arg_0__ occ_info) id.

Definition zapIdOccInfo : CoreType.Id -> CoreType.Id :=
  fun b => setIdOccInfo b BasicTypes.noOccInfo.

Definition setIdOneShotInfo
   : CoreType.Id -> BasicTypes.OneShotInfo -> CoreType.Id :=
  fun id one_shot =>
    modifyIdInfo (fun arg_0__ => IdInfo.setOneShotInfo arg_0__ one_shot) id.

Definition updOneShotInfo
   : CoreType.Id -> BasicTypes.OneShotInfo -> CoreType.Id :=
  fun id one_shot =>
    let do_upd :=
      match pair (idOneShotInfo id) one_shot with
      | pair BasicTypes.NoOneShotInfo _ => true
      | pair BasicTypes.OneShotLam _ => false
      end in
    if do_upd : bool then setIdOneShotInfo id one_shot else
    id.

Definition setIdSpecialisation
   : CoreType.Id -> IdInfo.RuleInfo -> CoreType.Id :=
  fun id spec_info =>
    modifyIdInfo (fun arg_0__ => IdInfo.setRuleInfo arg_0__ spec_info) id.

Definition setIdStrictness : CoreType.Id -> Demand.StrictSig -> CoreType.Id :=
  fun id sig =>
    modifyIdInfo (fun arg_0__ => IdInfo2.setStrictnessInfo arg_0__ sig) id.

Definition setIdUnfolding : CoreType.Id -> CoreSyn.Unfolding -> CoreType.Id :=
  fun id unfolding =>
    modifyIdInfo (fun arg_0__ => IdInfo2.setUnfoldingInfo arg_0__ unfolding) id.

Definition setCaseBndrEvald
   : DataCon.StrictnessMark -> CoreType.Id -> CoreType.Id :=
  fun str id =>
    if DataCon.isMarkedStrict str : bool
    then setIdUnfolding id CoreSyn.evaldUnfolding else
    id.

Definition setInlinePragma
   : CoreType.Id -> BasicTypes.InlinePragma -> CoreType.Id :=
  fun id prag =>
    modifyIdInfo (fun arg_0__ => IdInfo.setInlinePragInfo arg_0__ prag) id.

Definition setOneShotLambda : CoreType.Id -> CoreType.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ =>
                    IdInfo.setOneShotInfo arg_0__ BasicTypes.OneShotLam) id.

Definition transferPolyIdInfo
   : CoreType.Id -> list CoreType.Var -> CoreType.Id -> CoreType.Id :=
  fun old_id abstract_wrt new_id =>
    let old_info := CoreType.idInfo old_id in
    let old_arity := IdInfo.arityInfo old_info in
    let old_inline_prag := IdInfo.inlinePragInfo old_info in
    let old_occ_info := IdInfo.occInfo old_info in
    let new_occ_info := BasicTypes.zapOccTailCallInfo old_occ_info in
    let old_strictness := IdInfo2.strictnessInfo old_info in
    let arity_increase := Util.count CoreType.isId abstract_wrt in
    let new_arity := old_arity GHC.Num.+ arity_increase in
    let new_strictness :=
      Demand.increaseStrictSigArity arity_increase old_strictness in
    let transfer :=
      fun new_info =>
        IdInfo2.setStrictnessInfo (IdInfo.setOccInfo (IdInfo.setInlinePragInfo
                                                      (IdInfo.setArityInfo new_info new_arity) old_inline_prag)
                                                     new_occ_info) new_strictness in
    modifyIdInfo transfer new_id.

Definition zapIdStrictness : CoreType.Id -> CoreType.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ => IdInfo2.setStrictnessInfo arg_0__ Demand.nopSig)
    id.

Definition clearOneShotLambda : CoreType.Id -> CoreType.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ =>
                    IdInfo.setOneShotInfo arg_0__ BasicTypes.NoOneShotInfo) id.

Definition mkExportedLocalId
   : IdInfo.IdDetails -> Name.Name -> CoreType.Type_ -> CoreType.Id :=
  fun details name ty =>
    CoreType.mkExportedLocalVar details name ty IdInfo.vanillaIdInfo.

Definition mkGlobalId
   : IdInfo.IdDetails ->
     Name.Name -> CoreType.Type_ -> IdInfo.IdInfo -> CoreType.Id :=
  CoreType.mkGlobalVar.

Definition mkSysLocalM {m} `{UniqSupply.MonadUnique m}
   : FastString.FastString -> CoreType.Type_ -> m CoreType.Id :=
  fun fs ty =>
    UniqSupply.getUniqueM GHC.Base.>>=
    (fun uniq => GHC.Base.return_ (mkSysLocal fs uniq ty)).

Definition mkSysLocalOrCoVar
   : FastString.FastString -> Unique.Unique -> CoreType.Type_ -> CoreType.Id :=
  fun fs uniq ty => mkLocalIdOrCoVar (Name.mkSystemVarName uniq fs) ty.

Definition mkSysLocalOrCoVarM {m} `{UniqSupply.MonadUnique m}
   : FastString.FastString -> CoreType.Type_ -> m CoreType.Id :=
  fun fs ty =>
    UniqSupply.getUniqueM GHC.Base.>>=
    (fun uniq => GHC.Base.return_ (mkSysLocalOrCoVar fs uniq ty)).

Definition mkTemplateLocal : GHC.Num.Int -> CoreType.Type_ -> CoreType.Id :=
  fun i ty =>
    mkSysLocalOrCoVar (FastString.fsLit (GHC.Base.hs_string__ "v"))
    (Unique.mkBuiltinUnique i) ty.

Definition mkTemplateLocals : list CoreType.Type_ -> list CoreType.Id :=
  mkTemplateLocalsNum #1.

Definition mkUserLocal
   : OccName.OccName ->
     Unique.Unique -> CoreType.Type_ -> SrcLoc.SrcSpan -> CoreType.Id :=
  fun occ uniq ty loc =>
    if andb Util.debugIsOn (negb (negb (CoreType.isCoercionType ty))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Id.hs")
          #330)
    else mkLocalId (Name.mkInternalName uniq occ loc) ty.

Definition mkUserLocalOrCoVar
   : OccName.OccName ->
     Unique.Unique -> CoreType.Type_ -> SrcLoc.SrcSpan -> CoreType.Id :=
  fun occ uniq ty loc => mkLocalIdOrCoVar (Name.mkInternalName uniq occ loc) ty.

Definition mkWorkerId
   : Unique.Unique -> CoreType.Id -> CoreType.Type_ -> CoreType.Id :=
  fun uniq unwrkr ty =>
    mkLocalIdOrCoVar (Name.mkDerivedInternalName OccName.mkWorkerOcc uniq
                      (Name.getName unwrkr)) ty.

Definition realIdUnfolding : CoreType.Id -> CoreSyn.Unfolding :=
  fun id => IdInfo2.unfoldingInfo (CoreType.idInfo id).

Definition zapStableUnfolding : CoreType.Id -> CoreType.Id :=
  fun id =>
    if CoreSyn.isStableUnfolding (realIdUnfolding id) : bool
    then setIdUnfolding id CoreSyn.NoUnfolding else
    id.

Axiom recordSelectorTyCon : forall {A : Type}, A.

(* Translating `recordSelectorTyCon' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

Definition setIdExported : CoreType.Id -> CoreType.Id :=
  CoreType.setIdExported.

Definition setIdName : CoreType.Id -> Name.Name -> CoreType.Id :=
  CoreType.setVarName.

Definition setIdNotExported : CoreType.Id -> CoreType.Id :=
  CoreType.setIdNotExported.

Definition setIdUnique : CoreType.Id -> Unique.Unique -> CoreType.Id :=
  CoreType.setVarUnique.

Definition stateHackOneShot : BasicTypes.OneShotInfo :=
  BasicTypes.OneShotLam.

Definition idStateHackOneShotInfo : CoreType.Id -> BasicTypes.OneShotInfo :=
  fun id =>
    if isStateHackType (idType id) : bool then stateHackOneShot else
    idOneShotInfo id.

Definition isOneShotBndr : CoreType.Var -> bool :=
  fun var =>
    if CoreType.isTyVar var : bool then true else
    match idStateHackOneShotInfo var with
    | BasicTypes.OneShotLam => true
    | _ => false
    end.

Definition isProbablyOneShotLambda : CoreType.Id -> bool :=
  fun id =>
    match idStateHackOneShotInfo id with
    | BasicTypes.OneShotLam => true
    | BasicTypes.NoOneShotInfo => false
    end.

(* Unbound variables:
     None Some andb bool false isDataConId_maybe isDataConWorkId isStateHackType list
     mkLocalId mkLocalIdOrCoVar mkSysLocal mkTemplateLocalsNum negb option orb pair
     true BasicTypes.Activation BasicTypes.Arity BasicTypes.InlinePragma
     BasicTypes.JoinArity BasicTypes.NoOneShotInfo BasicTypes.OccInfo
     BasicTypes.OneShotInfo BasicTypes.OneShotLam BasicTypes.RepArity
     BasicTypes.RuleMatchInfo BasicTypes.inlinePragmaActivation
     BasicTypes.inlinePragmaRuleMatchInfo BasicTypes.isConLike BasicTypes.isDeadOcc
     BasicTypes.isOneOcc BasicTypes.isStrongLoopBreaker BasicTypes.noOccInfo
     BasicTypes.occ_in_lam BasicTypes.setInlinePragmaActivation
     BasicTypes.zapOccTailCallInfo CoreSyn.CoreRule CoreSyn.NoUnfolding
     CoreSyn.Unfolding CoreSyn.evaldUnfolding CoreSyn.isStableUnfolding CoreType.Id
     CoreType.JoinId CoreType.Kind CoreType.Type_ CoreType.Var CoreType.idDetails
     CoreType.idInfo CoreType.isCoercionType CoreType.isId CoreType.isLocalId
     CoreType.isTyVar CoreType.lazySetIdInfo CoreType.mkExportedLocalVar
     CoreType.mkGlobalVar CoreType.mkLocalVar CoreType.setIdDetails
     CoreType.setIdExported CoreType.setIdNotExported CoreType.setVarName
     CoreType.setVarUnique CoreType.varName CoreType.varType CoreType.varUnique
     DataCon.DataCon DataCon.StrictnessMark DataCon.isMarkedStrict Demand.Demand
     Demand.StrictSig Demand.increaseStrictSigArity Demand.isBottomingSig
     Demand.nopSig FastString.FastString FastString.fsLit GHC.Base.op_z2218U__
     GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.Num.Int GHC.Num.fromInteger
     GHC.Num.op_zp__ IdInfo.CafInfo IdInfo.IdDetails IdInfo.IdInfo IdInfo.JoinId
     IdInfo.RuleInfo IdInfo.VanillaId IdInfo.arityInfo IdInfo.cafInfo
     IdInfo.callArityInfo IdInfo.inlinePragInfo IdInfo.isEmptyRuleInfo
     IdInfo.isNeverLevPolyIdInfo IdInfo.occInfo IdInfo.oneShotInfo IdInfo.ruleInfo
     IdInfo.setArityInfo IdInfo.setCafInfo IdInfo.setCallArityInfo
     IdInfo.setInlinePragInfo IdInfo.setOccInfo IdInfo.setOneShotInfo
     IdInfo.setRuleInfo IdInfo.vanillaIdInfo IdInfo.zapDemandInfo
     IdInfo.zapFragileInfo IdInfo.zapLamInfo IdInfo.zapTailCallInfo
     IdInfo.zapUsageEnvInfo IdInfo.zapUsageInfo IdInfo.zapUsedOnceInfo
     IdInfo2.demandInfo IdInfo2.ruleInfoRules IdInfo2.setDemandInfo
     IdInfo2.setStrictnessInfo IdInfo2.setUnfoldingInfo IdInfo2.strictnessInfo
     IdInfo2.unfoldingInfo Maybes.orElse Module.Module Name.Name Name.getName
     Name.isInternalName Name.localiseName Name.mkDerivedInternalName
     Name.mkInternalName Name.mkSystemVarName Name.nameIsLocalOrFrom OccName.OccName
     OccName.mkWorkerOcc Outputable.assertPprPanic Panic.assertPanic Panic.noString
     Panic.panicStr RepType.countFunRepArgs SrcLoc.SrcSpan UniqSupply.MonadUnique
     UniqSupply.getUniqueM Unique.Unique Unique.mkBuiltinUnique Util.count
     Util.debugIsOn
*)
