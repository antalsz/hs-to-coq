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
Require DataCon.
Require Demand.
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require IdInfo.
Require Maybes.
Require Module.
Require Name.
Require OccName.
Require Panic.
Require SrcLoc.
Require UniqSupply.
Require Unique.
Require Util.
Require Var.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)
(* Midamble *)

(* Record selectors *)
Import IdInfo.
Import IdInfo2.

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

Definition asJoinId : Var.Id -> BasicTypes.JoinArity -> Var.JoinId :=
  fun id arity =>
    let is_vanilla_or_join :=
      fun id =>
        match Var.idDetails id with
        | IdInfo.VanillaId => true
        | IdInfo.JoinId _ => true
        | _ => false
        end in
    Panic.warnPprTrace (negb (Var.isLocalId id)) (GHC.Base.hs_string__
                        "ghc/compiler/basicTypes/Id.hs") #590 (GHC.Base.mappend (id
                                                                                 (GHC.Base.hs_string__
                                                                                  "global id being marked as join var:"))
                                                                                (Panic.noString id)) (Panic.warnPprTrace
                                                                                                      (negb
                                                                                                       (is_vanilla_or_join
                                                                                                        id))
                                                                                                      (GHC.Base.hs_string__
                                                                                                       "ghc/compiler/basicTypes/Id.hs")
                                                                                                      #592
                                                                                                      (GHC.Base.mappend
                                                                                                       (Panic.noString
                                                                                                        id)
                                                                                                       (IdInfo.pprIdDetails
                                                                                                        (Var.idDetails
                                                                                                         id)))
                                                                                                      (Var.setIdDetails
                                                                                                       id (IdInfo.JoinId
                                                                                                        arity))).

Definition idArity : Var.Id -> BasicTypes.Arity :=
  fun id => IdInfo.arityInfo (Var.idInfo id).

Definition idCafInfo : Var.Id -> IdInfo.CafInfo :=
  fun id => IdInfo.cafInfo (Var.idInfo id).

Definition idCallArity : Var.Id -> BasicTypes.Arity :=
  fun id => IdInfo.callArityInfo (Var.idInfo id).

Definition idDataCon : Var.Id -> DataCon.DataCon :=
  fun id =>
    Maybes.orElse (isDataConId_maybe id) (Panic.panicStr (GHC.Base.hs_string__
                                                          "idDataCon") (Panic.noString id)).

Definition idDemandInfo : Var.Id -> Demand.Demand :=
  fun id => IdInfo.demandInfo (Var.idInfo id).

Definition idInlinePragma : Var.Id -> BasicTypes.InlinePragma :=
  fun id => IdInfo.inlinePragInfo (Var.idInfo id).

Definition idRuleMatchInfo : Var.Id -> BasicTypes.RuleMatchInfo :=
  fun id => BasicTypes.inlinePragmaRuleMatchInfo (idInlinePragma id).

Definition isConLikeId : Var.Id -> bool :=
  fun id => orb (isDataConWorkId id) (BasicTypes.isConLike (idRuleMatchInfo id)).

Definition idInlineActivation : Var.Id -> BasicTypes.Activation :=
  fun id => BasicTypes.inlinePragmaActivation (idInlinePragma id).

Definition idName : Var.Id -> Name.Name :=
  Var.varName.

Definition idIsFrom : Module.Module -> Var.Id -> bool :=
  fun mod_ id => Name.nameIsLocalOrFrom mod_ (idName id).

Definition idOccInfo : Var.Id -> BasicTypes.OccInfo :=
  fun id => IdInfo.occInfo (Var.idInfo id).

Definition isDeadBinder : Var.Id -> bool :=
  fun bndr =>
    if Var.isId bndr : bool then BasicTypes.isDeadOcc (idOccInfo bndr) else
    false.

Definition idOneShotInfo : Var.Id -> BasicTypes.OneShotInfo :=
  fun id => IdInfo.oneShotInfo (Var.idInfo id).

Definition idSpecialisation : Var.Id -> IdInfo.RuleInfo :=
  fun id => IdInfo.ruleInfo (Var.idInfo id).

Definition idHasRules : Var.Id -> bool :=
  fun id => negb (IdInfo.isEmptyRuleInfo (idSpecialisation id)).

Definition idCoreRules : Var.Id -> list CoreSyn.CoreRule :=
  fun id => IdInfo.ruleInfoRules (idSpecialisation id).

Definition idStrictness : Var.Id -> Demand.StrictSig :=
  fun id => IdInfo.strictnessInfo (Var.idInfo id).

Definition isBottomingId : Var.Var -> bool :=
  fun v =>
    if Var.isId v : bool then Demand.isBottomingSig (idStrictness v) else
    false.

Definition idType : Var.Id -> unit :=
  Var.varType.

Definition localiseId : Var.Id -> Var.Id :=
  fun id =>
    let name := idName id in
    if (if andb Util.debugIsOn (negb (Var.isId id)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Id.hs")
              #209)
        else andb (Var.isLocalId id) (Name.isInternalName name)) : bool
    then id else
    Var.mkLocalVar (Var.idDetails id) (Name.localiseName name) (idType id)
    (Var.idInfo id).

Definition idFunRepArity : Var.Id -> BasicTypes.RepArity :=
  fun x => RepType.countFunRepArgs (idArity x) (idType x).

Definition idUnfolding : Var.Id -> CoreSyn.Unfolding :=
  fun id =>
    let info := Var.idInfo id in
    if BasicTypes.isStrongLoopBreaker (IdInfo.occInfo info) : bool
    then CoreSyn.NoUnfolding else
    IdInfo.unfoldingInfo info.

Definition idUnique : Var.Id -> Unique.Unique :=
  Var.varUnique.

Definition isDFunId : Var.Id -> bool :=
  fun id =>
    match Var.idDetails id with
    | IdInfo.DFunId _ => true
    | _ => false
    end.

Definition isDataConRecordSelector : Var.Id -> bool :=
  fun id =>
    match Var.idDetails id with
    | IdInfo.RecSelId (IdInfo.RecSelData _) _ => true
    | _ => false
    end.

Definition isImplicitId : Var.Id -> bool :=
  fun id =>
    match Var.idDetails id with
    | IdInfo.FCallId _ => true
    | IdInfo.ClassOpId _ => true
    | IdInfo.PrimOpId _ => true
    | IdInfo.DataConWorkId _ => true
    | IdInfo.DataConWrapId _ => true
    | _ => false
    end.

Definition isJoinId : Var.Var -> bool :=
  fun id =>
    if Var.isId id : bool
    then match Var.idDetails id with
         | IdInfo.JoinId _ => true
         | _ => false
         end else
    false.

Definition isExitJoinId : Var.Var -> bool :=
  fun id =>
    andb (isJoinId id) (andb (BasicTypes.isOneOcc (idOccInfo id))
                             (BasicTypes.occ_in_lam (idOccInfo id))).

Definition isJoinId_maybe : Var.Var -> option BasicTypes.JoinArity :=
  fun id =>
    if Var.isId id : bool
    then if andb Util.debugIsOn (negb (Var.isId id)) : bool
         then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                          "ghc/compiler/basicTypes/Id.hs") #494 (Panic.noString id))
         else match Var.idDetails id with
              | IdInfo.JoinId arity => Some arity
              | _ => None
              end else
    None.

Definition idJoinArity : Var.JoinId -> BasicTypes.JoinArity :=
  fun id =>
    Maybes.orElse (isJoinId_maybe id) (Panic.panicStr (GHC.Base.hs_string__
                                                       "idJoinArity") (Panic.noString id)).

Definition isNaughtyRecordSelector : Var.Id -> bool :=
  fun id =>
    match Var.idDetails id with
    | IdInfo.RecSelId _ n => n
    | _ => false
    end.

Definition isNeverLevPolyId : Var.Id -> bool :=
  IdInfo.isNeverLevPolyIdInfo GHC.Base.∘ Var.idInfo.

Definition isPatSynRecordSelector : Var.Id -> bool :=
  fun id =>
    match Var.idDetails id with
    | IdInfo.RecSelId (IdInfo.RecSelPatSyn _) _ => true
    | _ => false
    end.

Definition isRecordSelector : Var.Id -> bool :=
  fun id =>
    match Var.idDetails id with
    | IdInfo.RecSelId _ _ => true
    | _ => false
    end.

Definition lazySetIdInfo : Var.Id -> IdInfo.IdInfo -> Var.Id :=
  Var.lazySetIdInfo.

Definition maybeModifyIdInfo : option IdInfo.IdInfo -> Var.Id -> Var.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Some new_info, id => lazySetIdInfo id new_info
    | None, id => id
    end.

Definition zapInfo
   : (IdInfo.IdInfo -> option IdInfo.IdInfo) -> Var.Id -> Var.Id :=
  fun zapper id => maybeModifyIdInfo (zapper (Var.idInfo id)) id.

Definition zapFragileIdInfo : Var.Id -> Var.Id :=
  zapInfo IdInfo.zapFragileInfo.

Definition zapIdDemandInfo : Var.Id -> Var.Id :=
  zapInfo IdInfo.zapDemandInfo.

Definition zapIdTailCallInfo : Var.Id -> Var.Id :=
  zapInfo IdInfo.zapTailCallInfo.

Definition zapJoinId : Var.Id -> Var.Id :=
  fun jid =>
    if isJoinId jid : bool
    then zapIdTailCallInfo (Var.setIdDetails jid IdInfo.VanillaId) else
    jid.

Definition asJoinId_maybe : Var.Id -> option BasicTypes.JoinArity -> Var.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | id, Some arity => asJoinId id arity
    | id, None => zapJoinId id
    end.

Definition zapIdUsageEnvInfo : Var.Id -> Var.Id :=
  zapInfo IdInfo.zapUsageEnvInfo.

Definition zapIdUsageInfo : Var.Id -> Var.Id :=
  zapInfo IdInfo.zapUsageInfo.

Definition zapIdUsedOnceInfo : Var.Id -> Var.Id :=
  zapInfo IdInfo.zapUsedOnceInfo.

Definition zapLamIdInfo : Var.Id -> Var.Id :=
  zapInfo IdInfo.zapLamInfo.

Definition setIdInfo : Var.Id -> IdInfo.IdInfo -> Var.Id :=
  fun id info => lazySetIdInfo id info.

Definition modifyIdInfo
   : (IdInfo.IdInfo -> IdInfo.IdInfo) -> Var.Id -> Var.Id :=
  fun fn id => setIdInfo id (fn (Var.idInfo id)).

Definition modifyInlinePragma
   : Var.Id -> (BasicTypes.InlinePragma -> BasicTypes.InlinePragma) -> Var.Id :=
  fun id fn =>
    modifyIdInfo (fun info =>
                    IdInfo.setInlinePragInfo info (fn (IdInfo.inlinePragInfo info))) id.

Definition setInlineActivation : Var.Id -> BasicTypes.Activation -> Var.Id :=
  fun id act =>
    modifyInlinePragma id (fun prag =>
                             BasicTypes.setInlinePragmaActivation prag act).

Definition setIdArity : Var.Id -> BasicTypes.Arity -> Var.Id :=
  fun id arity =>
    modifyIdInfo (fun arg_0__ => IdInfo.setArityInfo arg_0__ arity) id.

Definition setIdCafInfo : Var.Id -> IdInfo.CafInfo -> Var.Id :=
  fun id caf_info =>
    modifyIdInfo (fun arg_0__ => IdInfo.setCafInfo arg_0__ caf_info) id.

Definition setIdCallArity : Var.Id -> BasicTypes.Arity -> Var.Id :=
  fun id arity =>
    modifyIdInfo (fun arg_0__ => IdInfo.setCallArityInfo arg_0__ arity) id.

Definition setIdDemandInfo : Var.Id -> Demand.Demand -> Var.Id :=
  fun id dmd => modifyIdInfo (fun arg_0__ => IdInfo.setDemandInfo arg_0__ dmd) id.

Definition setIdOccInfo : Var.Id -> BasicTypes.OccInfo -> Var.Id :=
  fun id occ_info =>
    modifyIdInfo (fun arg_0__ => IdInfo.setOccInfo arg_0__ occ_info) id.

Definition zapIdOccInfo : Var.Id -> Var.Id :=
  fun b => setIdOccInfo b BasicTypes.noOccInfo.

Definition setIdOneShotInfo : Var.Id -> BasicTypes.OneShotInfo -> Var.Id :=
  fun id one_shot =>
    modifyIdInfo (fun arg_0__ => IdInfo.setOneShotInfo arg_0__ one_shot) id.

Definition updOneShotInfo : Var.Id -> BasicTypes.OneShotInfo -> Var.Id :=
  fun id one_shot =>
    let do_upd :=
      match pair (idOneShotInfo id) one_shot with
      | pair BasicTypes.NoOneShotInfo _ => true
      | pair BasicTypes.OneShotLam _ => false
      end in
    if do_upd : bool then setIdOneShotInfo id one_shot else
    id.

Definition setIdSpecialisation : Var.Id -> IdInfo.RuleInfo -> Var.Id :=
  fun id spec_info =>
    modifyIdInfo (fun arg_0__ => IdInfo.setRuleInfo arg_0__ spec_info) id.

Definition setIdStrictness : Var.Id -> Demand.StrictSig -> Var.Id :=
  fun id sig =>
    modifyIdInfo (fun arg_0__ => IdInfo.setStrictnessInfo arg_0__ sig) id.

Definition setIdUnfolding : Var.Id -> CoreSyn.Unfolding -> Var.Id :=
  fun id unfolding =>
    modifyIdInfo (fun arg_0__ => IdInfo.setUnfoldingInfo arg_0__ unfolding) id.

Definition setCaseBndrEvald : DataCon.StrictnessMark -> Var.Id -> Var.Id :=
  fun str id =>
    if DataCon.isMarkedStrict str : bool
    then setIdUnfolding id CoreSyn.evaldUnfolding else
    id.

Definition setInlinePragma : Var.Id -> BasicTypes.InlinePragma -> Var.Id :=
  fun id prag =>
    modifyIdInfo (fun arg_0__ => IdInfo.setInlinePragInfo arg_0__ prag) id.

Definition setOneShotLambda : Var.Id -> Var.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ =>
                    IdInfo.setOneShotInfo arg_0__ BasicTypes.OneShotLam) id.

Definition transferPolyIdInfo : Var.Id -> list Var.Var -> Var.Id -> Var.Id :=
  fun old_id abstract_wrt new_id =>
    let old_info := Var.idInfo old_id in
    let old_arity := IdInfo.arityInfo old_info in
    let old_inline_prag := IdInfo.inlinePragInfo old_info in
    let old_occ_info := IdInfo.occInfo old_info in
    let new_occ_info := BasicTypes.zapOccTailCallInfo old_occ_info in
    let old_strictness := IdInfo.strictnessInfo old_info in
    let arity_increase := Util.count Var.isId abstract_wrt in
    let new_arity := old_arity GHC.Num.+ arity_increase in
    let new_strictness :=
      Demand.increaseStrictSigArity arity_increase old_strictness in
    let transfer :=
      fun new_info =>
        IdInfo.setStrictnessInfo (IdInfo.setOccInfo (IdInfo.setInlinePragInfo
                                                     (IdInfo.setArityInfo new_info new_arity) old_inline_prag)
                                                    new_occ_info) new_strictness in
    modifyIdInfo transfer new_id.

Definition zapIdStrictness : Var.Id -> Var.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ => IdInfo.setStrictnessInfo arg_0__ Demand.nopSig) id.

Definition clearOneShotLambda : Var.Id -> Var.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ =>
                    IdInfo.setOneShotInfo arg_0__ BasicTypes.NoOneShotInfo) id.

Definition mkExportedLocalId
   : IdInfo.IdDetails -> Name.Name -> unit -> Var.Id :=
  fun details name ty =>
    Var.mkExportedLocalVar details name ty IdInfo.vanillaIdInfo.

Definition mkGlobalId
   : IdInfo.IdDetails -> Name.Name -> unit -> IdInfo.IdInfo -> Var.Id :=
  Var.mkGlobalVar.

Definition mkSysLocalM {m} `{UniqSupply.MonadUnique m}
   : FastString.FastString -> unit -> m Var.Id :=
  fun fs ty =>
    UniqSupply.getUniqueM GHC.Base.>>=
    (fun uniq => GHC.Base.return_ (mkSysLocal fs uniq ty)).

Definition mkSysLocalOrCoVar
   : FastString.FastString -> Unique.Unique -> unit -> Var.Id :=
  fun fs uniq ty => mkLocalIdOrCoVar (Name.mkSystemVarName uniq fs) ty.

Definition mkSysLocalOrCoVarM {m} `{UniqSupply.MonadUnique m}
   : FastString.FastString -> unit -> m Var.Id :=
  fun fs ty =>
    UniqSupply.getUniqueM GHC.Base.>>=
    (fun uniq => GHC.Base.return_ (mkSysLocalOrCoVar fs uniq ty)).

Definition mkTemplateLocal : GHC.Num.Int -> unit -> Var.Id :=
  fun i ty =>
    mkSysLocalOrCoVar (FastString.fsLit (GHC.Base.hs_string__ "v"))
    (Unique.mkBuiltinUnique i) ty.

Definition mkTemplateLocals : list unit -> list Var.Id :=
  mkTemplateLocalsNum #1.

Definition mkUserLocal
   : OccName.OccName -> Unique.Unique -> unit -> SrcLoc.SrcSpan -> Var.Id :=
  fun occ uniq ty loc =>
    if andb Util.debugIsOn (negb (negb (TyCoRep.isCoercionType ty))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Id.hs")
          #330)
    else mkLocalId (Name.mkInternalName uniq occ loc) ty.

Definition mkUserLocalOrCoVar
   : OccName.OccName -> Unique.Unique -> unit -> SrcLoc.SrcSpan -> Var.Id :=
  fun occ uniq ty loc => mkLocalIdOrCoVar (Name.mkInternalName uniq occ loc) ty.

Definition mkWorkerId : Unique.Unique -> Var.Id -> unit -> Var.Id :=
  fun uniq unwrkr ty =>
    mkLocalIdOrCoVar (Name.mkDerivedInternalName OccName.mkWorkerOcc uniq
                      (Name.getName unwrkr)) ty.

Definition realIdUnfolding : Var.Id -> CoreSyn.Unfolding :=
  fun id => IdInfo.unfoldingInfo (Var.idInfo id).

Definition zapStableUnfolding : Var.Id -> Var.Id :=
  fun id =>
    if CoreSyn.isStableUnfolding (realIdUnfolding id) : bool
    then setIdUnfolding id CoreSyn.NoUnfolding else
    id.

Definition recordSelectorTyCon : Var.Id -> IdInfo.RecSelParent :=
  fun id =>
    match Var.idDetails id with
    | IdInfo.RecSelId parent _ => parent
    | _ => Panic.panic (GHC.Base.hs_string__ "recordSelectorTyCon")
    end.

Definition setIdExported : Var.Id -> Var.Id :=
  Var.setIdExported.

Definition setIdName : Var.Id -> Name.Name -> Var.Id :=
  Var.setVarName.

Definition setIdNotExported : Var.Id -> Var.Id :=
  Var.setIdNotExported.

Definition setIdUnique : Var.Id -> Unique.Unique -> Var.Id :=
  Var.setVarUnique.

Definition stateHackOneShot : BasicTypes.OneShotInfo :=
  BasicTypes.OneShotLam.

Definition idStateHackOneShotInfo : Var.Id -> BasicTypes.OneShotInfo :=
  fun id =>
    if isStateHackType (idType id) : bool then stateHackOneShot else
    idOneShotInfo id.

Definition isOneShotBndr : Var.Var -> bool :=
  fun var =>
    if Var.isTyVar var : bool then true else
    match idStateHackOneShotInfo var with
    | BasicTypes.OneShotLam => true
    | _ => false
    end.

Definition isProbablyOneShotLambda : Var.Id -> bool :=
  fun id =>
    match idStateHackOneShotInfo id with
    | BasicTypes.OneShotLam => true
    | BasicTypes.NoOneShotInfo => false
    end.

(* External variables:
     None Some andb bool false isDataConId_maybe isDataConWorkId isStateHackType list
     mkLocalId mkLocalIdOrCoVar mkSysLocal mkTemplateLocalsNum negb option orb pair
     true unit BasicTypes.Activation BasicTypes.Arity BasicTypes.InlinePragma
     BasicTypes.JoinArity BasicTypes.NoOneShotInfo BasicTypes.OccInfo
     BasicTypes.OneShotInfo BasicTypes.OneShotLam BasicTypes.RepArity
     BasicTypes.RuleMatchInfo BasicTypes.inlinePragmaActivation
     BasicTypes.inlinePragmaRuleMatchInfo BasicTypes.isConLike BasicTypes.isDeadOcc
     BasicTypes.isOneOcc BasicTypes.isStrongLoopBreaker BasicTypes.noOccInfo
     BasicTypes.occ_in_lam BasicTypes.setInlinePragmaActivation
     BasicTypes.zapOccTailCallInfo CoreSyn.CoreRule CoreSyn.NoUnfolding
     CoreSyn.Unfolding CoreSyn.evaldUnfolding CoreSyn.isStableUnfolding
     DataCon.DataCon DataCon.StrictnessMark DataCon.isMarkedStrict Demand.Demand
     Demand.StrictSig Demand.increaseStrictSigArity Demand.isBottomingSig
     Demand.nopSig FastString.FastString FastString.fsLit GHC.Base.mappend
     GHC.Base.op_z2218U__ GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.Num.Int
     GHC.Num.fromInteger GHC.Num.op_zp__ IdInfo.CafInfo IdInfo.ClassOpId
     IdInfo.DFunId IdInfo.DataConWorkId IdInfo.DataConWrapId IdInfo.FCallId
     IdInfo.IdDetails IdInfo.IdInfo IdInfo.JoinId IdInfo.PrimOpId IdInfo.RecSelData
     IdInfo.RecSelId IdInfo.RecSelParent IdInfo.RecSelPatSyn IdInfo.RuleInfo
     IdInfo.VanillaId IdInfo.arityInfo IdInfo.cafInfo IdInfo.callArityInfo
     IdInfo.demandInfo IdInfo.inlinePragInfo IdInfo.isEmptyRuleInfo
     IdInfo.isNeverLevPolyIdInfo IdInfo.occInfo IdInfo.oneShotInfo
     IdInfo.pprIdDetails IdInfo.ruleInfo IdInfo.ruleInfoRules IdInfo.setArityInfo
     IdInfo.setCafInfo IdInfo.setCallArityInfo IdInfo.setDemandInfo
     IdInfo.setInlinePragInfo IdInfo.setOccInfo IdInfo.setOneShotInfo
     IdInfo.setRuleInfo IdInfo.setStrictnessInfo IdInfo.setUnfoldingInfo
     IdInfo.strictnessInfo IdInfo.unfoldingInfo IdInfo.vanillaIdInfo
     IdInfo.zapDemandInfo IdInfo.zapFragileInfo IdInfo.zapLamInfo
     IdInfo.zapTailCallInfo IdInfo.zapUsageEnvInfo IdInfo.zapUsageInfo
     IdInfo.zapUsedOnceInfo Maybes.orElse Module.Module Name.Name Name.getName
     Name.isInternalName Name.localiseName Name.mkDerivedInternalName
     Name.mkInternalName Name.mkSystemVarName Name.nameIsLocalOrFrom OccName.OccName
     OccName.mkWorkerOcc Outputable.assertPprPanic Panic.assertPanic Panic.noString
     Panic.panic Panic.panicStr Panic.warnPprTrace RepType.countFunRepArgs
     SrcLoc.SrcSpan TyCoRep.isCoercionType UniqSupply.MonadUnique
     UniqSupply.getUniqueM Unique.Unique Unique.mkBuiltinUnique Util.count
     Util.debugIsOn Var.Id Var.JoinId Var.Var Var.idDetails Var.idInfo Var.isId
     Var.isLocalId Var.isTyVar Var.lazySetIdInfo Var.mkExportedLocalVar
     Var.mkGlobalVar Var.mkLocalVar Var.setIdDetails Var.setIdExported
     Var.setIdNotExported Var.setVarName Var.setVarUnique Var.varName Var.varType
     Var.varUnique
*)
