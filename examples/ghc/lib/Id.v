(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require Import Combined.


(* Converted imports: *)

Require BasicTypes.
Require Combined.
Require Datatypes.
Require Demand.
Require FastString.
Require GHC.Base.
Require GHC.Enum.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require Maybes.
Require Module.
Require Name.
Require OccName.
Require Panic.
Require SrcLoc.
Require UniqSupply.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)
(* Midamble *)

Parameter lookupDataCon : Combined.DataConId -> Combined.DataCon.
Parameter lookupClass   : Combined.ClassId -> Combined.Class.

(* Make this default so that we can reason about either case. *)
Import GHC.Err.
Definition isStateHackType : unit -> bool := GHC.Err.default.

(* The real definition looks like this, but we don't have the type information
   around:
  fun ty =>
    if DynFlags.hasNoStateHack DynFlags.unsafeGlobalDynFlags : bool then false else
    match Type.tyConAppTyCon_maybe ty with
    | Some tycon => tycon GHC.Base.== TysPrim.statePrimTyCon
    | _ => false
    end. *)



(* Converted value declarations: *)

Definition asJoinId : Combined.Var -> BasicTypes.JoinArity -> Combined.JoinId :=
  fun id arity =>
    let is_vanilla_or_join :=
      fun id =>
        match Combined.idDetails id with
        | Combined.VanillaId => true
        | Combined.Mk_JoinId _ => true
        | _ => false
        end in
    Panic.warnPprTrace (negb (Combined.isLocalId id)) (GHC.Base.hs_string__
                        "ghc/compiler/basicTypes/Id.hs") #590 (GHC.Base.mappend (Datatypes.id
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
                                                                                                       Panic.someSDoc)
                                                                                                      (Combined.setIdDetails
                                                                                                       id
                                                                                                       (Combined.Mk_JoinId
                                                                                                        arity))).

Definition hasNoBinding : Combined.Var -> bool :=
  fun id =>
    match Combined.idDetails id with
    | Combined.PrimOpId _ => true
    | Combined.FCallId _ => true
    | Combined.DataConWorkId dc =>
        orb (Combined.isUnboxedTupleCon dc) (Combined.isUnboxedSumCon dc)
    | _ => false
    end.

Definition idArity : Combined.Var -> BasicTypes.Arity :=
  fun id => Combined.arityInfo ((@Combined.idInfo tt id)).

Definition idCafInfo : Combined.Var -> Combined.CafInfo :=
  fun id => Combined.cafInfo ((@Combined.idInfo tt id)).

Definition idCallArity : Combined.Var -> BasicTypes.Arity :=
  fun id => Combined.callArityInfo ((@Combined.idInfo tt id)).

Definition idInlinePragma : Combined.Var -> BasicTypes.InlinePragma :=
  fun id => Combined.inlinePragInfo ((@Combined.idInfo tt id)).

Definition idRuleMatchInfo : Combined.Var -> BasicTypes.RuleMatchInfo :=
  fun id => BasicTypes.inlinePragmaRuleMatchInfo (idInlinePragma id).

Definition idInlineActivation : Combined.Var -> BasicTypes.Activation :=
  fun id => BasicTypes.inlinePragmaActivation (idInlinePragma id).

Definition idName : Combined.Var -> Name.Name :=
  Combined.varName.

Definition localiseId : Combined.Var -> Combined.Var :=
  fun id =>
    let name := idName id in
    if andb (Combined.isLocalId id) (Name.isInternalName name) : bool then id else
    Combined.mkLocalVar (Combined.idDetails id) (Name.localiseName name) (tt)
    ((@Combined.idInfo tt id)).

Definition idIsFrom : Module.Module -> Combined.Var -> bool :=
  fun mod_ id => Name.nameIsLocalOrFrom mod_ (idName id).

Definition idOccInfo : Combined.Var -> BasicTypes.OccInfo :=
  fun id => Combined.occInfo ((@Combined.idInfo tt id)).

Definition isDeadBinder : Combined.Var -> bool :=
  fun bndr =>
    if Combined.isId bndr : bool then BasicTypes.isDeadOcc (idOccInfo bndr) else
    false.

Definition idOneShotInfo : Combined.Var -> BasicTypes.OneShotInfo :=
  fun id => Combined.oneShotInfo ((@Combined.idInfo tt id)).

Definition idSpecialisation : Combined.Var -> Combined.RuleInfo :=
  fun id => Combined.ruleInfo ((@Combined.idInfo tt id)).

Definition idHasRules : Combined.Var -> bool :=
  fun id => negb (Combined.isEmptyRuleInfo (idSpecialisation id)).

Definition idType : Combined.Var -> unit :=
  Combined.varType.

Definition idUnique : Combined.Var -> Unique.Unique :=
  Combined.varUnique.

Definition isClassOpId_maybe : Combined.Var -> option Combined.Class :=
  fun id =>
    match Combined.idDetails id with
    | Combined.ClassOpId cls => Some cls
    | _other => None
    end.

Definition isDFunId : Combined.Var -> bool :=
  fun id =>
    match Combined.idDetails id with
    | Combined.Mk_DFunId _ => true
    | _ => false
    end.

Definition isDataConId_maybe : Combined.Var -> option Combined.DataCon :=
  fun id =>
    match Combined.idDetails id with
    | Combined.DataConWorkId con => Some con
    | Combined.DataConWrapId con => Some con
    | _ => None
    end.

Definition idDataCon : Combined.Var -> Combined.DataCon :=
  fun id =>
    Maybes.orElse (isDataConId_maybe id) (Panic.panicStr (GHC.Base.hs_string__
                                                          "idDataCon") (Panic.noString id)).

Definition isDataConRecordSelector : Combined.Var -> bool :=
  fun id =>
    match Combined.idDetails id with
    | Combined.RecSelId (Combined.RecSelData _) _ => true
    | _ => false
    end.

Definition isDataConWorkId : Combined.Var -> bool :=
  fun id =>
    match Combined.idDetails id with
    | Combined.DataConWorkId _ => true
    | _ => false
    end.

Definition isConLikeId : Combined.Var -> bool :=
  fun id => orb (isDataConWorkId id) (BasicTypes.isConLike (idRuleMatchInfo id)).

Definition isDataConWorkId_maybe : Combined.Var -> option Combined.DataCon :=
  fun id =>
    match Combined.idDetails id with
    | Combined.DataConWorkId con => Some con
    | _ => None
    end.

Definition isFCallId : Combined.Var -> bool :=
  fun id =>
    match Combined.idDetails id with
    | Combined.FCallId _ => true
    | _ => false
    end.

Definition isFCallId_maybe : Combined.Var -> option unit :=
  fun id =>
    match Combined.idDetails id with
    | Combined.FCallId call => Some call
    | _ => None
    end.

Definition isImplicitId : Combined.Var -> bool :=
  fun id =>
    match Combined.idDetails id with
    | Combined.FCallId _ => true
    | Combined.ClassOpId _ => true
    | Combined.PrimOpId _ => true
    | Combined.DataConWorkId _ => true
    | Combined.DataConWrapId _ => true
    | _ => false
    end.

Definition isJoinId : Combined.Var -> bool :=
  fun id =>
    if Combined.isId id : bool
    then match Combined.idDetails id with
         | Combined.Mk_JoinId _ => true
         | _ => false
         end else
    false.

Definition isExitJoinId : Combined.Var -> bool :=
  fun id =>
    andb (isJoinId id) (andb (BasicTypes.isOneOcc (idOccInfo id))
                             (BasicTypes.occ_in_lam (idOccInfo id))).

Definition isJoinId_maybe : Combined.Var -> option BasicTypes.JoinArity :=
  fun id =>
    if Combined.isId id : bool
    then match Combined.idDetails id with
         | Combined.Mk_JoinId arity => Some arity
         | _ => None
         end else
    None.

Definition idJoinArity : Combined.JoinId -> BasicTypes.JoinArity :=
  fun id =>
    Maybes.orElse (isJoinId_maybe id) (Panic.panicStr (GHC.Base.hs_string__
                                                       "idJoinArity") (Panic.noString id)).

Definition isNaughtyRecordSelector : Combined.Var -> bool :=
  fun id =>
    match Combined.idDetails id with
    | Combined.RecSelId _ n => n
    | _ => false
    end.

Definition isPatSynRecordSelector : Combined.Var -> bool :=
  fun id =>
    match Combined.idDetails id with
    | Combined.RecSelId (Combined.RecSelPatSyn _) _ => true
    | _ => false
    end.

Definition isPrimOpId : Combined.Var -> bool :=
  fun id =>
    match Combined.idDetails id with
    | Combined.PrimOpId _ => true
    | _ => false
    end.

Definition isPrimOpId_maybe : Combined.Var -> option unit :=
  fun id =>
    match Combined.idDetails id with
    | Combined.PrimOpId op => Some op
    | _ => None
    end.

Definition isRecordSelector : Combined.Var -> bool :=
  fun id =>
    match Combined.idDetails id with
    | Combined.RecSelId _ _ => true
    | _ => false
    end.

Definition lazySetIdInfo : Combined.Var -> Combined.IdInfo -> Combined.Var :=
  Combined.lazySetIdInfo.

Definition maybeModifyIdInfo
   : option Combined.IdInfo -> Combined.Var -> Combined.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Some new_info, id => lazySetIdInfo id new_info
    | None, id => id
    end.

Definition zapInfo
   : (Combined.IdInfo -> option Combined.IdInfo) ->
     Combined.Var -> Combined.Var :=
  fun zapper id => maybeModifyIdInfo (zapper ((@Combined.idInfo tt id))) id.

Definition zapIdTailCallInfo : Combined.Var -> Combined.Var :=
  zapInfo Combined.zapTailCallInfo.

Definition zapJoinId : Combined.Var -> Combined.Var :=
  fun jid =>
    if isJoinId jid : bool
    then zapIdTailCallInfo (Combined.setIdDetails jid Combined.VanillaId) else
    jid.

Definition asJoinId_maybe
   : Combined.Var -> option BasicTypes.JoinArity -> Combined.Var :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | id, Some arity => asJoinId id arity
    | id, None => zapJoinId id
    end.

Definition zapIdUsageInfo : Combined.Var -> Combined.Var :=
  zapInfo Combined.zapUsageInfo.

Definition zapIdUsedOnceInfo : Combined.Var -> Combined.Var :=
  zapInfo Combined.zapUsedOnceInfo.

Definition zapLamIdInfo : Combined.Var -> Combined.Var :=
  zapInfo Combined.zapLamInfo.

Definition setIdInfo : Combined.Var -> Combined.IdInfo -> Combined.Var :=
  fun id info => GHC.Prim.seq info (lazySetIdInfo id info).

Definition modifyIdInfo
   : (Combined.IdInfo -> Combined.IdInfo) -> Combined.Var -> Combined.Var :=
  fun fn id => setIdInfo id (fn ((@Combined.idInfo tt id))).

Definition modifyInlinePragma
   : Combined.Var ->
     (BasicTypes.InlinePragma -> BasicTypes.InlinePragma) -> Combined.Var :=
  fun id fn =>
    modifyIdInfo (fun info =>
                    Combined.setInlinePragInfo info (fn (Combined.inlinePragInfo info))) id.

Definition setInlineActivation
   : Combined.Var -> BasicTypes.Activation -> Combined.Var :=
  fun id act =>
    modifyInlinePragma id (fun prag =>
                             BasicTypes.setInlinePragmaActivation prag act).

Definition setIdArity : Combined.Var -> BasicTypes.Arity -> Combined.Var :=
  fun id arity =>
    modifyIdInfo (fun arg_0__ => Combined.setArityInfo arg_0__ arity) id.

Definition setIdCafInfo : Combined.Var -> Combined.CafInfo -> Combined.Var :=
  fun id caf_info =>
    modifyIdInfo (fun arg_0__ => Combined.setCafInfo arg_0__ caf_info) id.

Definition setIdCallArity : Combined.Var -> BasicTypes.Arity -> Combined.Var :=
  fun id arity =>
    modifyIdInfo (fun arg_0__ => Combined.setCallArityInfo arg_0__ arity) id.

Definition setIdDemandInfo : Combined.Var -> Demand.Demand -> Combined.Var :=
  fun id dmd => modifyIdInfo (fun arg_0__ => arg_0__) id.

Definition setIdOccInfo : Combined.Var -> BasicTypes.OccInfo -> Combined.Var :=
  fun id occ_info =>
    modifyIdInfo (fun arg_0__ => Combined.setOccInfo arg_0__ occ_info) id.

Definition zapIdOccInfo : Combined.Var -> Combined.Var :=
  fun b => setIdOccInfo b BasicTypes.noOccInfo.

Definition setIdOneShotInfo
   : Combined.Var -> BasicTypes.OneShotInfo -> Combined.Var :=
  fun id one_shot =>
    modifyIdInfo (fun arg_0__ => Combined.setOneShotInfo arg_0__ one_shot) id.

Definition updOneShotInfo
   : Combined.Var -> BasicTypes.OneShotInfo -> Combined.Var :=
  fun id one_shot =>
    let do_upd :=
      match pair (idOneShotInfo id) one_shot with
      | pair BasicTypes.NoOneShotInfo _ => true
      | pair BasicTypes.OneShotLam _ => false
      end in
    if do_upd : bool then setIdOneShotInfo id one_shot else
    id.

Definition setIdSpecialisation
   : Combined.Var -> Combined.RuleInfo -> Combined.Var :=
  fun id spec_info =>
    modifyIdInfo (fun arg_0__ => Combined.setRuleInfo arg_0__ spec_info) id.

Definition setIdStrictness : Combined.Var -> Demand.StrictSig -> Combined.Var :=
  fun id sig => modifyIdInfo (fun arg_0__ => arg_0__) id.

Definition setInlinePragma
   : Combined.Var -> BasicTypes.InlinePragma -> Combined.Var :=
  fun id prag =>
    modifyIdInfo (fun arg_0__ => Combined.setInlinePragInfo arg_0__ prag) id.

Definition setOneShotLambda : Combined.Var -> Combined.Var :=
  fun id =>
    modifyIdInfo (fun arg_0__ =>
                    Combined.setOneShotInfo arg_0__ BasicTypes.OneShotLam) id.

Definition transferPolyIdInfo
   : Combined.Var -> list Combined.Var -> Combined.Var -> Combined.Var :=
  fun old_id abstract_wrt new_id =>
    let old_info := (@Combined.idInfo tt old_id) in
    let old_arity := Combined.arityInfo old_info in
    let old_inline_prag := Combined.inlinePragInfo old_info in
    let old_occ_info := Combined.occInfo old_info in
    let new_occ_info := BasicTypes.zapOccTailCallInfo old_occ_info in
    let old_strictness := Combined.strictnessInfo old_info in
    let arity_increase := Util.count Combined.isId abstract_wrt in
    let new_arity := old_arity GHC.Num.+ arity_increase in
    let new_strictness := tt in
    let transfer :=
      fun new_info =>
        Combined.setOccInfo (Combined.setInlinePragInfo (Combined.setArityInfo new_info
                                                                               new_arity) old_inline_prag)
                            new_occ_info in
    modifyIdInfo transfer new_id.

Definition zapIdStrictness : Combined.Var -> Combined.Var :=
  fun id => modifyIdInfo (fun arg_0__ => arg_0__) id.

Definition clearOneShotLambda : Combined.Var -> Combined.Var :=
  fun id =>
    modifyIdInfo (fun arg_0__ =>
                    Combined.setOneShotInfo arg_0__ BasicTypes.NoOneShotInfo) id.

Definition mkExportedLocalId
   : Combined.IdDetails -> Name.Name -> unit -> Combined.Var :=
  fun details name ty =>
    Combined.mkExportedLocalVar details name ty Combined.vanillaIdInfo.

Definition mkExportedVanillaId : Name.Name -> unit -> Combined.Var :=
  fun name ty =>
    Combined.mkExportedLocalVar Combined.VanillaId name ty Combined.vanillaIdInfo.

Definition mkGlobalId
   : Combined.IdDetails -> Name.Name -> unit -> Combined.IdInfo -> Combined.Var :=
  Combined.mkGlobalVar.

Definition mkVanillaGlobalWithInfo
   : Name.Name -> unit -> Combined.IdInfo -> Combined.Var :=
  mkGlobalId Combined.VanillaId.

Definition mkVanillaGlobal : Name.Name -> unit -> Combined.Var :=
  fun name ty => mkVanillaGlobalWithInfo name ty Combined.vanillaIdInfo.

Definition mkLocalIdOrCoVarWithInfo
   : Name.Name -> unit -> Combined.IdInfo -> Combined.Var :=
  fun name ty info =>
    let details := Combined.VanillaId in Combined.mkLocalVar details name ty info.

Definition mkLocalIdWithInfo
   : Name.Name -> unit -> Combined.IdInfo -> Combined.Var :=
  fun name ty info => Combined.mkLocalVar Combined.VanillaId name ty info.

Definition mkLocalId : Name.Name -> unit -> Combined.Var :=
  fun name ty => mkLocalIdWithInfo name ty Combined.vanillaIdInfo.

Definition mkLocalIdOrCoVar : Name.Name -> unit -> Combined.Var :=
  fun name ty => mkLocalId name ty.

Definition mkSysLocalOrCoVar
   : FastString.FastString -> Unique.Unique -> unit -> Combined.Var :=
  fun fs uniq ty => mkLocalIdOrCoVar (Name.mkSystemVarName uniq fs) ty.

Definition mkSysLocalOrCoVarM {m} `{UniqSupply.MonadUnique m}
   : FastString.FastString -> unit -> m Combined.Var :=
  fun fs ty =>
    UniqSupply.getUniqueM GHC.Base.>>=
    (fun uniq => GHC.Base.return_ (mkSysLocalOrCoVar fs uniq ty)).

Definition mkTemplateLocal : GHC.Num.Int -> unit -> Combined.Var :=
  fun i ty =>
    mkSysLocalOrCoVar (FastString.fsLit (GHC.Base.hs_string__ "v"))
    (Unique.mkBuiltinUnique i) ty.

Definition mkTemplateLocalsNum
   : GHC.Num.Int -> list unit -> list Combined.Var :=
  fun n tys => GHC.List.zipWith mkTemplateLocal (GHC.Enum.enumFrom n) tys.

Definition mkTemplateLocals : list unit -> list Combined.Var :=
  mkTemplateLocalsNum #1.

Definition mkUserLocalOrCoVar
   : OccName.OccName -> Unique.Unique -> unit -> SrcLoc.SrcSpan -> Combined.Var :=
  fun occ uniq ty loc => mkLocalIdOrCoVar (Name.mkInternalName uniq occ loc) ty.

Definition mkWorkerId : Unique.Unique -> Combined.Var -> unit -> Combined.Var :=
  fun uniq unwrkr ty =>
    mkLocalIdOrCoVar (Name.mkDerivedInternalName OccName.mkWorkerOcc uniq
                      (Name.getName unwrkr)) ty.

Definition mkSysLocal
   : FastString.FastString -> Unique.Unique -> unit -> Combined.Var :=
  fun fs uniq ty => mkLocalId (Name.mkSystemVarName uniq fs) ty.

Definition mkSysLocalM {m} `{UniqSupply.MonadUnique m}
   : FastString.FastString -> unit -> m Combined.Var :=
  fun fs ty =>
    UniqSupply.getUniqueM GHC.Base.>>=
    (fun uniq => GHC.Base.return_ (mkSysLocal fs uniq ty)).

Definition mkUserLocal
   : OccName.OccName -> Unique.Unique -> unit -> SrcLoc.SrcSpan -> Combined.Var :=
  fun occ uniq ty loc => mkLocalId (Name.mkInternalName uniq occ loc) ty.

Definition recordSelectorTyCon : Combined.Var -> Combined.RecSelParent :=
  fun id =>
    match Combined.idDetails id with
    | Combined.RecSelId parent _ => parent
    | _ => Panic.panic (GHC.Base.hs_string__ "recordSelectorTyCon")
    end.

Definition setIdExported : Combined.Var -> Combined.Var :=
  Combined.setIdExported.

Definition setIdName : Combined.Var -> Name.Name -> Combined.Var :=
  Combined.setVarName.

Definition setIdNotExported : Combined.Var -> Combined.Var :=
  Combined.setIdNotExported.

Definition setIdUnique : Combined.Var -> Unique.Unique -> Combined.Var :=
  Combined.setVarUnique.

Definition stateHackOneShot : BasicTypes.OneShotInfo :=
  BasicTypes.OneShotLam.

Definition typeOneShot : unit -> BasicTypes.OneShotInfo :=
  fun ty =>
    if isStateHackType ty : bool then stateHackOneShot else
    BasicTypes.NoOneShotInfo.

Definition idStateHackOneShotInfo : Combined.Var -> BasicTypes.OneShotInfo :=
  fun id =>
    if isStateHackType (tt) : bool then stateHackOneShot else
    idOneShotInfo id.

Definition isOneShotBndr : Combined.Var -> bool :=
  fun var =>
    if Combined.isTyVar var : bool then true else
    match idStateHackOneShotInfo var with
    | BasicTypes.OneShotLam => true
    | _ => false
    end.

Definition isProbablyOneShotLambda : Combined.Var -> bool :=
  fun id =>
    match idStateHackOneShotInfo id with
    | BasicTypes.OneShotLam => true
    | BasicTypes.NoOneShotInfo => false
    end.

(* External variables:
     None Some andb bool false isStateHackType list negb option orb pair true tt unit
     BasicTypes.Activation BasicTypes.Arity BasicTypes.InlinePragma
     BasicTypes.JoinArity BasicTypes.NoOneShotInfo BasicTypes.OccInfo
     BasicTypes.OneShotInfo BasicTypes.OneShotLam BasicTypes.RuleMatchInfo
     BasicTypes.inlinePragmaActivation BasicTypes.inlinePragmaRuleMatchInfo
     BasicTypes.isConLike BasicTypes.isDeadOcc BasicTypes.isOneOcc
     BasicTypes.noOccInfo BasicTypes.occ_in_lam BasicTypes.setInlinePragmaActivation
     BasicTypes.zapOccTailCallInfo Combined.CafInfo Combined.Class Combined.ClassOpId
     Combined.DataCon Combined.DataConWorkId Combined.DataConWrapId Combined.FCallId
     Combined.IdDetails Combined.IdInfo Combined.JoinId Combined.Mk_DFunId
     Combined.Mk_JoinId Combined.PrimOpId Combined.RecSelData Combined.RecSelId
     Combined.RecSelParent Combined.RecSelPatSyn Combined.RuleInfo Combined.VanillaId
     Combined.Var Combined.arityInfo Combined.cafInfo Combined.callArityInfo
     Combined.idDetails Combined.idInfo Combined.inlinePragInfo
     Combined.isEmptyRuleInfo Combined.isId Combined.isLocalId Combined.isTyVar
     Combined.isUnboxedSumCon Combined.isUnboxedTupleCon Combined.lazySetIdInfo
     Combined.mkExportedLocalVar Combined.mkGlobalVar Combined.mkLocalVar
     Combined.occInfo Combined.oneShotInfo Combined.ruleInfo Combined.setArityInfo
     Combined.setCafInfo Combined.setCallArityInfo Combined.setIdDetails
     Combined.setIdExported Combined.setIdNotExported Combined.setInlinePragInfo
     Combined.setOccInfo Combined.setOneShotInfo Combined.setRuleInfo
     Combined.setVarName Combined.setVarUnique Combined.strictnessInfo
     Combined.vanillaIdInfo Combined.varName Combined.varType Combined.varUnique
     Combined.zapLamInfo Combined.zapTailCallInfo Combined.zapUsageInfo
     Combined.zapUsedOnceInfo Datatypes.id Demand.Demand Demand.StrictSig
     FastString.FastString FastString.fsLit GHC.Base.mappend GHC.Base.op_zgzgze__
     GHC.Base.return_ GHC.Enum.enumFrom GHC.List.zipWith GHC.Num.Int
     GHC.Num.fromInteger GHC.Num.op_zp__ GHC.Prim.seq Maybes.orElse Module.Module
     Name.Name Name.getName Name.isInternalName Name.localiseName
     Name.mkDerivedInternalName Name.mkInternalName Name.mkSystemVarName
     Name.nameIsLocalOrFrom OccName.OccName OccName.mkWorkerOcc Panic.noString
     Panic.panic Panic.panicStr Panic.someSDoc Panic.warnPprTrace SrcLoc.SrcSpan
     UniqSupply.MonadUnique UniqSupply.getUniqueM Unique.Unique
     Unique.mkBuiltinUnique Util.count
*)
