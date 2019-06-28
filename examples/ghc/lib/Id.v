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
Require Datatypes.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require GHC.Num.
Require GHC.Prim.
Require Maybes.
Require Module.
Require Name.
Require OccName.
Require Panic.
Require SrcLoc.
Require TyCoRep.
Require UniqSupply.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom zapIdUsageEnvInfo : Core.Id -> Core.Id.

Axiom zapFragileIdInfo : Core.Id -> Core.Id.

Definition stateHackOneShot : BasicTypes.OneShotInfo :=
  BasicTypes.OneShotLam.

Definition setIdUnique : Core.Id -> Unique.Unique -> Core.Id :=
  Core.setVarUnique.

Definition setIdType : Core.Id -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun id ty => Core.setVarType id ty.

Definition setIdNotExported : Core.Id -> Core.Id :=
  Core.setIdNotExported.

Definition setIdName : Core.Id -> Name.Name -> Core.Id :=
  Core.setVarName.

Definition setIdExported : Core.Id -> Core.Id :=
  Core.setIdExported.

Definition recordSelectorTyCon : Core.Id -> Core.RecSelParent :=
  fun id =>
    match Core.idDetails id with
    | Core.RecSelId parent _ => parent
    | _ => Panic.panic (GHC.Base.hs_string__ "recordSelectorTyCon")
    end.

Definition realIdUnfolding : Core.Id -> Core.Unfolding :=
  fun id => Core.unfoldingInfo ((@Core.idInfo tt id)).

Axiom mkTemplateLocalsNum : nat -> list AxiomatizedTypes.Type_ -> list Core.Id.

Axiom mkTemplateLocals : list AxiomatizedTypes.Type_ -> list Core.Id.

Axiom mkTemplateLocal : nat -> AxiomatizedTypes.Type_ -> Core.Id.

Definition mkLocalIdWithInfo
   : Name.Name -> AxiomatizedTypes.Type_ -> Core.IdInfo -> Core.Id :=
  fun name ty info => Core.mkLocalVar Core.VanillaId name ty info.

Definition mkLocalId : Name.Name -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun name ty => mkLocalIdWithInfo name ty Core.vanillaIdInfo.

Definition mkSysLocal
   : FastString.FastString ->
     Unique.Unique -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun fs uniq ty =>
    if andb Util.debugIsOn (negb (negb (TyCoRep.isCoercionType ty))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Id.hs")
          #313)
    else mkLocalId (Name.mkSystemVarName uniq fs) ty.

Definition mkSysLocalM {m} `{UniqSupply.MonadUnique m}
   : FastString.FastString -> AxiomatizedTypes.Type_ -> m Core.Id :=
  fun fs ty =>
    UniqSupply.getUniqueM GHC.Base.>>=
    (fun uniq => GHC.Base.return_ (mkSysLocal fs uniq ty)).

Definition mkUserLocal
   : OccName.OccName ->
     Unique.Unique -> AxiomatizedTypes.Type_ -> SrcLoc.SrcSpan -> Core.Id :=
  fun occ uniq ty loc =>
    if andb Util.debugIsOn (negb (negb (TyCoRep.isCoercionType ty))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Id.hs")
          #330)
    else mkLocalId (Name.mkInternalName uniq occ loc) ty.

Definition mkGlobalId
   : Core.IdDetails ->
     Name.Name -> AxiomatizedTypes.Type_ -> Core.IdInfo -> Core.Id :=
  Core.mkGlobalVar.

Definition mkVanillaGlobalWithInfo
   : Name.Name -> AxiomatizedTypes.Type_ -> Core.IdInfo -> Core.Id :=
  mkGlobalId Core.VanillaId.

Definition mkVanillaGlobal : Name.Name -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun name ty => mkVanillaGlobalWithInfo name ty Core.vanillaIdInfo.

Definition mkExportedVanillaId
   : Name.Name -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun name ty =>
    Core.mkExportedLocalVar Core.VanillaId name ty Core.vanillaIdInfo.

Definition mkExportedLocalId
   : Core.IdDetails -> Name.Name -> AxiomatizedTypes.Type_ -> Core.Id :=
  fun details name ty =>
    Core.mkExportedLocalVar details name ty Core.vanillaIdInfo.

Definition lazySetIdInfo : Core.Id -> Core.IdInfo -> Core.Id :=
  Core.lazySetIdInfo.

Definition maybeModifyIdInfo : option Core.IdInfo -> Core.Id -> Core.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Some new_info, id => lazySetIdInfo id new_info
    | None, id => id
    end.

Definition zapInfo
   : (Core.IdInfo -> option Core.IdInfo) -> Core.Id -> Core.Id :=
  fun zapper id => maybeModifyIdInfo (zapper ((@Core.idInfo tt id))) id.

Definition zapIdDemandInfo : Core.Id -> Core.Id :=
  zapInfo Core.zapDemandInfo.

Definition zapIdTailCallInfo : Core.Id -> Core.Id :=
  zapInfo Core.zapTailCallInfo.

Definition zapIdUsageInfo : Core.Id -> Core.Id :=
  zapInfo Core.zapUsageInfo.

Definition zapIdUsedOnceInfo : Core.Id -> Core.Id :=
  zapInfo Core.zapUsedOnceInfo.

Definition zapLamIdInfo : Core.Id -> Core.Id :=
  zapInfo Core.zapLamInfo.

Definition setIdInfo : Core.Id -> Core.IdInfo -> Core.Id :=
  fun id info => GHC.Prim.seq info (lazySetIdInfo id info).

Definition modifyIdInfo : (Core.IdInfo -> Core.IdInfo) -> Core.Id -> Core.Id :=
  fun fn id => setIdInfo id (fn ((@Core.idInfo tt id))).

Definition modifyInlinePragma
   : Core.Id -> (BasicTypes.InlinePragma -> BasicTypes.InlinePragma) -> Core.Id :=
  fun id fn =>
    modifyIdInfo (fun info =>
                    Core.setInlinePragInfo info (fn (Core.inlinePragInfo info))) id.

Definition setInlineActivation : Core.Id -> BasicTypes.Activation -> Core.Id :=
  fun id act =>
    modifyInlinePragma id (fun prag =>
                             BasicTypes.setInlinePragmaActivation prag act).

Definition setIdArity : Core.Id -> BasicTypes.Arity -> Core.Id :=
  fun id arity =>
    modifyIdInfo (fun arg_0__ => Core.setArityInfo arg_0__ arity) id.

Definition setIdCafInfo : Core.Id -> Core.CafInfo -> Core.Id :=
  fun id caf_info =>
    modifyIdInfo (fun arg_0__ => Core.setCafInfo arg_0__ caf_info) id.

Definition setIdCallArity : Core.Id -> BasicTypes.Arity -> Core.Id :=
  fun id arity =>
    modifyIdInfo (fun arg_0__ => Core.setCallArityInfo arg_0__ arity) id.

Definition setIdDemandInfo : Core.Id -> Core.Demand -> Core.Id :=
  fun id dmd => modifyIdInfo (fun arg_0__ => Core.setDemandInfo arg_0__ dmd) id.

Definition setIdOccInfo : Core.Id -> BasicTypes.OccInfo -> Core.Id :=
  fun id occ_info =>
    modifyIdInfo (fun arg_0__ => Core.setOccInfo arg_0__ occ_info) id.

Definition zapIdOccInfo : Core.Id -> Core.Id :=
  fun b => setIdOccInfo b BasicTypes.noOccInfo.

Definition setIdOneShotInfo : Core.Id -> BasicTypes.OneShotInfo -> Core.Id :=
  fun id one_shot =>
    modifyIdInfo (fun arg_0__ => Core.setOneShotInfo arg_0__ one_shot) id.

Definition setIdSpecialisation : Core.Id -> Core.RuleInfo -> Core.Id :=
  fun id spec_info =>
    modifyIdInfo (fun arg_0__ => Core.setRuleInfo arg_0__ spec_info) id.

Definition setIdStrictness : Core.Id -> Core.StrictSig -> Core.Id :=
  fun id sig =>
    modifyIdInfo (fun arg_0__ => Core.setStrictnessInfo arg_0__ sig) id.

Definition setIdUnfolding : Core.Id -> Core.Unfolding -> Core.Id :=
  fun id unfolding =>
    modifyIdInfo (fun arg_0__ => Core.setUnfoldingInfo arg_0__ unfolding) id.

Definition zapStableUnfolding : Core.Id -> Core.Id :=
  fun id =>
    if Core.isStableUnfolding (realIdUnfolding id) : bool
    then setIdUnfolding id Core.NoUnfolding else
    id.

Definition setInlinePragma : Core.Id -> BasicTypes.InlinePragma -> Core.Id :=
  fun id prag =>
    modifyIdInfo (fun arg_0__ => Core.setInlinePragInfo arg_0__ prag) id.

Definition setOneShotLambda : Core.Id -> Core.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ => Core.setOneShotInfo arg_0__ BasicTypes.OneShotLam)
    id.

Definition transferPolyIdInfo
   : Core.Id -> list Core.Var -> Core.Id -> Core.Id :=
  fun old_id abstract_wrt new_id =>
    let old_info := (@Core.idInfo tt old_id) in
    let old_arity := Core.arityInfo old_info in
    let old_inline_prag := Core.inlinePragInfo old_info in
    let old_occ_info := Core.occInfo old_info in
    let new_occ_info := BasicTypes.zapOccTailCallInfo old_occ_info in
    let old_strictness := Core.strictnessInfo old_info in
    let arity_increase := Util.count Core.isId abstract_wrt in
    let new_arity := old_arity GHC.Num.+ arity_increase in
    let new_strictness :=
      Core.increaseStrictSigArity arity_increase old_strictness in
    let transfer :=
      fun new_info =>
        Core.setStrictnessInfo (Core.setOccInfo (Core.setInlinePragInfo
                                                 (Core.setArityInfo new_info new_arity) old_inline_prag) new_occ_info)
                               new_strictness in
    modifyIdInfo transfer new_id.

Definition zapIdStrictness : Core.Id -> Core.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ => Core.setStrictnessInfo arg_0__ Core.nopSig) id.

Axiom isStrictId : Core.Id -> bool.

Axiom isStateHackType : AxiomatizedTypes.Type_ -> bool.

Definition typeOneShot : AxiomatizedTypes.Type_ -> BasicTypes.OneShotInfo :=
  fun ty =>
    if isStateHackType ty : bool then stateHackOneShot else
    BasicTypes.NoOneShotInfo.

Definition isRecordSelector : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.RecSelId _ _ => true
    | _ => false
    end.

Definition isPrimOpId_maybe : Core.Id -> option unit :=
  fun id =>
    match Core.idDetails id with
    | Core.PrimOpId op => Some op
    | _ => None
    end.

Definition isPrimOpId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.PrimOpId _ => true
    | _ => false
    end.

Definition isPatSynRecordSelector : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.RecSelId (Core.RecSelPatSyn _) _ => true
    | _ => false
    end.

Definition isNeverLevPolyId : Core.Id -> bool :=
  Core.isNeverLevPolyIdInfo GHC.Base.∘ (@Core.idInfo tt).

Definition isNaughtyRecordSelector : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.RecSelId _ n => n
    | _ => false
    end.

Definition isJoinId_maybe : Core.Var -> option BasicTypes.JoinArity :=
  fun id =>
    if Core.isId id : bool
    then if andb Util.debugIsOn (negb (Core.isId id)) : bool
         then (GHC.Err.error Panic.someSDoc)
         else match Core.idDetails id with
              | Core.Mk_JoinId arity => Some arity
              | _ => None
              end else
    None.

Definition isJoinId : Core.Var -> bool :=
  fun id =>
    if Core.isId id : bool
    then match Core.idDetails id with
         | Core.Mk_JoinId _ => true
         | _ => false
         end else
    false.

Definition zapJoinId : Core.Id -> Core.Id :=
  fun jid =>
    if isJoinId jid : bool
    then zapIdTailCallInfo (Core.setIdDetails jid Core.VanillaId) else
    jid.

Definition isImplicitId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.FCallId _ => true
    | Core.ClassOpId _ => true
    | Core.PrimOpId _ => true
    | Core.DataConWorkId _ => true
    | Core.DataConWrapId _ => true
    | _ => false
    end.

Definition isFCallId_maybe : Core.Id -> option unit :=
  fun id =>
    match Core.idDetails id with
    | Core.FCallId call => Some call
    | _ => None
    end.

Definition isFCallId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.FCallId _ => true
    | _ => false
    end.

Axiom isEvVar : Core.Var -> bool.

Axiom isDictId : Core.Id -> bool.

Definition isDataConWorkId_maybe : Core.Id -> option Core.DataCon :=
  fun id =>
    match Core.idDetails id with
    | Core.DataConWorkId con => Some con
    | _ => None
    end.

Definition isDataConWorkId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.DataConWorkId _ => true
    | _ => false
    end.

Definition isDataConRecordSelector : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.RecSelId (Core.RecSelData _) _ => true
    | _ => false
    end.

Definition isDataConId_maybe : Core.Id -> option Core.DataCon :=
  fun id =>
    match Core.idDetails id with
    | Core.DataConWorkId con => Some con
    | Core.DataConWrapId con => Some con
    | _ => None
    end.

Definition isDFunId : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.Mk_DFunId _ => true
    | _ => false
    end.

Definition isClassOpId_maybe : Core.Id -> option Core.Class :=
  fun id =>
    match Core.idDetails id with
    | Core.ClassOpId cls => Some cls
    | _other => None
    end.

Definition idUnique : Core.Id -> Unique.Unique :=
  Core.varUnique.

Definition idUnfolding : Core.Id -> Core.Unfolding :=
  fun id =>
    let info := (@Core.idInfo tt id) in
    if BasicTypes.isStrongLoopBreaker (Core.occInfo info) : bool
    then Core.NoUnfolding else
    Core.unfoldingInfo info.

Definition idType : Core.Id -> AxiomatizedTypes.Kind :=
  Core.varType.

Definition idStrictness : Core.Id -> Core.StrictSig :=
  fun id => Core.strictnessInfo ((@Core.idInfo tt id)).

Definition isBottomingId : Core.Var -> bool :=
  fun v =>
    if Core.isId v : bool then Core.isBottomingSig (idStrictness v) else
    false.

Definition idSpecialisation : Core.Id -> Core.RuleInfo :=
  fun id => Core.ruleInfo ((@Core.idInfo tt id)).

Definition idOneShotInfo : Core.Id -> BasicTypes.OneShotInfo :=
  fun id => Core.oneShotInfo ((@Core.idInfo tt id)).

Definition idStateHackOneShotInfo : Core.Id -> BasicTypes.OneShotInfo :=
  fun id =>
    if isStateHackType (idType id) : bool then stateHackOneShot else
    idOneShotInfo id.

Definition isOneShotBndr : Core.Var -> bool :=
  fun var =>
    if Core.isTyVar var : bool then true else
    match idStateHackOneShotInfo var with
    | BasicTypes.OneShotLam => true
    | _ => false
    end.

Definition isProbablyOneShotLambda : Core.Id -> bool :=
  fun id =>
    match idStateHackOneShotInfo id with
    | BasicTypes.OneShotLam => true
    | BasicTypes.NoOneShotInfo => false
    end.

Definition updOneShotInfo : Core.Id -> BasicTypes.OneShotInfo -> Core.Id :=
  fun id one_shot =>
    let do_upd :=
      match pair (idOneShotInfo id) one_shot with
      | pair BasicTypes.NoOneShotInfo _ => true
      | pair BasicTypes.OneShotLam _ => false
      end in
    if do_upd : bool then setIdOneShotInfo id one_shot else
    id.

Definition idOccInfo : Core.Id -> BasicTypes.OccInfo :=
  fun id => Core.occInfo ((@Core.idInfo tt id)).

Definition isDeadBinder : Core.Id -> bool :=
  fun bndr =>
    if Core.isId bndr : bool then BasicTypes.isDeadOcc (idOccInfo bndr) else
    false.

Definition isExitJoinId : Core.Var -> bool :=
  fun id =>
    andb (isJoinId id) (andb (BasicTypes.isOneOcc (idOccInfo id))
                             (BasicTypes.occ_in_lam (idOccInfo id))).

Definition idName : Core.Id -> Name.Name :=
  Core.varName.

Definition localiseId : Core.Id -> Core.Id :=
  fun id =>
    let name := idName id in
    if (if andb Util.debugIsOn (negb (Core.isId id)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Id.hs")
              #209)
        else andb (Core.isLocalId id) (Name.isInternalName name)) : bool
    then id else
    Core.mkLocalVar (Core.idDetails id) (Name.localiseName name) (idType id)
    ((@Core.idInfo tt id)).

Definition idJoinArity : Core.JoinId -> BasicTypes.JoinArity :=
  fun id =>
    Maybes.orElse (isJoinId_maybe id) (Panic.panicStr (GHC.Base.hs_string__
                                                       "idJoinArity") (Panic.someSDoc)).

Definition idIsFrom : Module.Module -> Core.Id -> bool :=
  fun mod_ id => Name.nameIsLocalOrFrom mod_ (idName id).

Definition idInlinePragma : Core.Id -> BasicTypes.InlinePragma :=
  fun id => Core.inlinePragInfo ((@Core.idInfo tt id)).

Definition idRuleMatchInfo : Core.Id -> BasicTypes.RuleMatchInfo :=
  fun id => BasicTypes.inlinePragmaRuleMatchInfo (idInlinePragma id).

Definition isConLikeId : Core.Id -> bool :=
  fun id => orb (isDataConWorkId id) (BasicTypes.isConLike (idRuleMatchInfo id)).

Definition idInlineActivation : Core.Id -> BasicTypes.Activation :=
  fun id => BasicTypes.inlinePragmaActivation (idInlinePragma id).

Definition idHasRules : Core.Id -> bool :=
  fun id => negb (Core.isEmptyRuleInfo (idSpecialisation id)).

Definition idDemandInfo : Core.Id -> Core.Demand :=
  fun id => Core.demandInfo ((@Core.idInfo tt id)).

Definition idDataCon : Core.Id -> Core.DataCon :=
  fun id =>
    Maybes.orElse (isDataConId_maybe id) (Panic.panicStr (GHC.Base.hs_string__
                                                          "idDataCon") (Panic.someSDoc)).

Definition idCoreRules : Core.Id -> list Core.CoreRule :=
  fun x => nil.

Definition idCallArity : Core.Id -> BasicTypes.Arity :=
  fun id => Core.callArityInfo ((@Core.idInfo tt id)).

Definition idCafInfo : Core.Id -> Core.CafInfo :=
  fun id => Core.cafInfo ((@Core.idInfo tt id)).

Definition idArity : Core.Id -> BasicTypes.Arity :=
  fun id => Core.arityInfo ((@Core.idInfo tt id)).

Definition hasNoBinding : Core.Id -> bool :=
  fun id =>
    match Core.idDetails id with
    | Core.PrimOpId _ => true
    | Core.FCallId _ => true
    | Core.DataConWorkId dc =>
        orb (Core.isUnboxedTupleCon dc) (Core.isUnboxedSumCon dc)
    | _ => false
    end.

Definition clearOneShotLambda : Core.Id -> Core.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ =>
                    Core.setOneShotInfo arg_0__ BasicTypes.NoOneShotInfo) id.

Definition asJoinId : Core.Id -> BasicTypes.JoinArity -> Core.JoinId :=
  fun id arity =>
    let is_vanilla_or_join :=
      fun id =>
        match Core.idDetails id with
        | Core.VanillaId => true
        | Core.Mk_JoinId _ => true
        | _ => false
        end in
    Panic.warnPprTrace (negb (Core.isLocalId id)) (GHC.Base.hs_string__
                        "ghc/compiler/basicTypes/Id.hs") #590 (GHC.Base.mappend (Datatypes.id
                                                                                 (GHC.Base.hs_string__
                                                                                  "global id being marked as join var:"))
                                                                                Panic.someSDoc) (Panic.warnPprTrace
                                                                                                 (negb
                                                                                                  (is_vanilla_or_join
                                                                                                   id))
                                                                                                 (GHC.Base.hs_string__
                                                                                                  "ghc/compiler/basicTypes/Id.hs")
                                                                                                 #592 (GHC.Base.mappend
                                                                                                  Panic.someSDoc
                                                                                                  Panic.someSDoc)
                                                                                                 (Core.setIdDetails id
                                                                                                                    (Core.Mk_JoinId
                                                                                                                     arity))).

Definition asJoinId_maybe : Core.Id -> option BasicTypes.JoinArity -> Core.Id :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | id, Some arity => asJoinId id arity
    | id, None => zapJoinId id
    end.

(* External variables:
     None Some andb bool false list nat negb nil option orb pair true tt unit
     AxiomatizedTypes.Kind AxiomatizedTypes.Type_ BasicTypes.Activation
     BasicTypes.Arity BasicTypes.InlinePragma BasicTypes.JoinArity
     BasicTypes.NoOneShotInfo BasicTypes.OccInfo BasicTypes.OneShotInfo
     BasicTypes.OneShotLam BasicTypes.RuleMatchInfo BasicTypes.inlinePragmaActivation
     BasicTypes.inlinePragmaRuleMatchInfo BasicTypes.isConLike BasicTypes.isDeadOcc
     BasicTypes.isOneOcc BasicTypes.isStrongLoopBreaker BasicTypes.noOccInfo
     BasicTypes.occ_in_lam BasicTypes.setInlinePragmaActivation
     BasicTypes.zapOccTailCallInfo Core.CafInfo Core.Class Core.ClassOpId
     Core.CoreRule Core.DataCon Core.DataConWorkId Core.DataConWrapId Core.Demand
     Core.FCallId Core.Id Core.IdDetails Core.IdInfo Core.JoinId Core.Mk_DFunId
     Core.Mk_JoinId Core.NoUnfolding Core.PrimOpId Core.RecSelData Core.RecSelId
     Core.RecSelParent Core.RecSelPatSyn Core.RuleInfo Core.StrictSig Core.Unfolding
     Core.VanillaId Core.Var Core.arityInfo Core.cafInfo Core.callArityInfo
     Core.demandInfo Core.idDetails Core.idInfo Core.increaseStrictSigArity
     Core.inlinePragInfo Core.isBottomingSig Core.isEmptyRuleInfo Core.isId
     Core.isLocalId Core.isNeverLevPolyIdInfo Core.isStableUnfolding Core.isTyVar
     Core.isUnboxedSumCon Core.isUnboxedTupleCon Core.lazySetIdInfo
     Core.mkExportedLocalVar Core.mkGlobalVar Core.mkLocalVar Core.nopSig
     Core.occInfo Core.oneShotInfo Core.ruleInfo Core.setArityInfo Core.setCafInfo
     Core.setCallArityInfo Core.setDemandInfo Core.setIdDetails Core.setIdExported
     Core.setIdNotExported Core.setInlinePragInfo Core.setOccInfo Core.setOneShotInfo
     Core.setRuleInfo Core.setStrictnessInfo Core.setUnfoldingInfo Core.setVarName
     Core.setVarType Core.setVarUnique Core.strictnessInfo Core.unfoldingInfo
     Core.vanillaIdInfo Core.varName Core.varType Core.varUnique Core.zapDemandInfo
     Core.zapLamInfo Core.zapTailCallInfo Core.zapUsageInfo Core.zapUsedOnceInfo
     Datatypes.id FastString.FastString GHC.Base.mappend GHC.Base.op_z2218U__
     GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.Err.error GHC.Num.fromInteger
     GHC.Num.op_zp__ GHC.Prim.seq Maybes.orElse Module.Module Name.Name
     Name.isInternalName Name.localiseName Name.mkInternalName Name.mkSystemVarName
     Name.nameIsLocalOrFrom OccName.OccName Panic.assertPanic Panic.panic
     Panic.panicStr Panic.someSDoc Panic.warnPprTrace SrcLoc.SrcSpan
     TyCoRep.isCoercionType UniqSupply.MonadUnique UniqSupply.getUniqueM
     Unique.Unique Util.count Util.debugIsOn
*)
