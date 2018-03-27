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
Require Core.
Require CoreSyn.
Require DataCon.
Require Demand.
Require FastString.
Require GHC.Base.
Require GHC.Num.
Require GHC.Prim.
Require IdInfo.
Require IdInfo2.
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
Require Var.
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
  fun id => IdInfo2.demandInfo (Var.idInfo id).

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

Definition isOneShotLambda : Var.Id -> bool :=
  fun id =>
    match idOneShotInfo id with
    | BasicTypes.OneShotLam => true
    | _ => false
    end.

Definition isOneShotBndr : Core.Var -> bool :=
  fun var => if Var.isTyVar var : bool then true else isOneShotLambda var.

Definition isProbablyOneShotLambda : Var.Id -> bool :=
  fun id =>
    match idOneShotInfo id with
    | BasicTypes.OneShotLam => true
    | BasicTypes.ProbOneShot => true
    | BasicTypes.NoOneShotInfo => false
    end.

Definition idSpecialisation : Var.Id -> IdInfo.RuleInfo :=
  fun id => IdInfo.ruleInfo (Var.idInfo id).

Definition idHasRules : Var.Id -> bool :=
  fun id => negb (IdInfo.isEmptyRuleInfo (idSpecialisation id)).

Definition idCoreRules : Var.Id -> list CoreSyn.CoreRule :=
  fun id => IdInfo2.ruleInfoRules (idSpecialisation id).

Definition idStrictness : Var.Id -> Demand.StrictSig :=
  fun id => IdInfo2.strictnessInfo (Var.idInfo id).

Definition isBottomingId : Var.Id -> bool :=
  fun id => Demand.isBottomingSig (idStrictness id).

Definition idType : Var.Id -> Kind :=
  Var.varType.

Definition localiseId : Var.Id -> Var.Id :=
  fun id =>
    let name := idName id in
    if (if andb Util.debugIsOn (negb (Var.isId id)) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Id.hs")
              #193)
        else andb (Var.isLocalId id) (Name.isInternalName name)) : bool
    then id else
    Var.mkLocalVar (Var.idDetails id) (Name.localiseName name) (idType id)
    (Var.idInfo id).

Definition idUnfolding : Var.Id -> CoreSyn.Unfolding :=
  fun id =>
    let info := Var.idInfo id in
    if BasicTypes.isStrongLoopBreaker (IdInfo.occInfo info) : bool
    then CoreSyn.NoUnfolding else
    IdInfo2.unfoldingInfo info.

Definition idUnique : Var.Id -> Unique.Unique :=
  Var.varUnique.

Axiom isDFunId : forall {A : Type}, A.

(* Translating `isDFunId' failed: using a record pattern for the unknown
   constructor `DFunId' unsupported *)

Axiom isDataConRecordSelector : forall {A : Type}, A.

(* Translating `isDataConRecordSelector' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

Axiom isImplicitId : forall {A : Type}, A.

(* Translating `isImplicitId' failed: using a record pattern for the unknown
   constructor `FCallId' unsupported *)

Axiom isNaughtyRecordSelector : forall {A : Type}, A.

(* Translating `isNaughtyRecordSelector' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

Axiom isPatSynRecordSelector : forall {A : Type}, A.

(* Translating `isPatSynRecordSelector' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

Axiom isRecordSelector : forall {A : Type}, A.

(* Translating `isRecordSelector' failed: using a record pattern for the unknown
   constructor `RecSelId' unsupported *)

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

Definition zapIdUsageInfo : Var.Id -> Var.Id :=
  zapInfo IdInfo.zapUsageInfo.

Definition zapLamIdInfo : Var.Id -> Var.Id :=
  zapInfo IdInfo.zapLamInfo.

Definition setIdInfo : Var.Id -> IdInfo.IdInfo -> Var.Id :=
  fun id info => GHC.Prim.seq info (lazySetIdInfo id info).

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
  fun id dmd =>
    modifyIdInfo (fun arg_0__ => IdInfo2.setDemandInfo arg_0__ dmd) id.

Definition setIdOccInfo : Var.Id -> BasicTypes.OccInfo -> Var.Id :=
  fun id occ_info =>
    modifyIdInfo (fun arg_0__ => IdInfo.setOccInfo arg_0__ occ_info) id.

Definition zapIdOccInfo : Var.Id -> Var.Id :=
  fun b => setIdOccInfo b BasicTypes.NoOccInfo.

Definition setIdOneShotInfo : Var.Id -> BasicTypes.OneShotInfo -> Var.Id :=
  fun id one_shot =>
    modifyIdInfo (fun arg_0__ => IdInfo.setOneShotInfo arg_0__ one_shot) id.

Definition updOneShotInfo : Var.Id -> BasicTypes.OneShotInfo -> Var.Id :=
  fun id one_shot =>
    let do_upd :=
      match pair (idOneShotInfo id) one_shot with
      | pair BasicTypes.NoOneShotInfo _ => true
      | pair BasicTypes.OneShotLam _ => false
      | pair _ BasicTypes.NoOneShotInfo => false
      | _ => true
      end in
    if do_upd : bool then setIdOneShotInfo id one_shot else
    id.

Definition setIdSpecialisation : Var.Id -> IdInfo.RuleInfo -> Var.Id :=
  fun id spec_info =>
    modifyIdInfo (fun arg_0__ => IdInfo.setRuleInfo arg_0__ spec_info) id.

Definition setIdStrictness : Var.Id -> Demand.StrictSig -> Var.Id :=
  fun id sig =>
    modifyIdInfo (fun arg_0__ => IdInfo2.setStrictnessInfo arg_0__ sig) id.

Definition setIdUnfolding : Var.Id -> CoreSyn.Unfolding -> Var.Id :=
  fun id unfolding =>
    modifyIdInfo (fun arg_0__ => IdInfo2.setUnfoldingInfo arg_0__ unfolding) id.

Definition setIdUnfoldingLazily : Var.Id -> CoreSyn.Unfolding -> Var.Id :=
  fun id unfolding =>
    modifyIdInfo (fun arg_0__ => IdInfo2.setUnfoldingInfoLazily arg_0__ unfolding)
    id.

Definition setInlinePragma : Var.Id -> BasicTypes.InlinePragma -> Var.Id :=
  fun id prag =>
    modifyIdInfo (fun arg_0__ => IdInfo.setInlinePragInfo arg_0__ prag) id.

Definition setOneShotLambda : Var.Id -> Var.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ =>
                    IdInfo.setOneShotInfo arg_0__ BasicTypes.OneShotLam) id.

Definition transferPolyIdInfo : Var.Id -> list Core.Var -> Var.Id -> Var.Id :=
  fun old_id abstract_wrt new_id =>
    let old_info := Var.idInfo old_id in
    let old_arity := IdInfo.arityInfo old_info in
    let old_inline_prag := IdInfo.inlinePragInfo old_info in
    let old_occ_info := IdInfo.occInfo old_info in
    let old_strictness := IdInfo2.strictnessInfo old_info in
    let arity_increase := Util.count Var.isId abstract_wrt in
    let new_arity := old_arity GHC.Num.+ arity_increase in
    let new_strictness :=
      Demand.increaseStrictSigArity arity_increase old_strictness in
    let transfer :=
      fun new_info =>
        IdInfo2.setStrictnessInfo (IdInfo.setOccInfo (IdInfo.setInlinePragInfo
                                                      (IdInfo.setArityInfo new_info new_arity) old_inline_prag)
                                                     old_occ_info) new_strictness in
    modifyIdInfo transfer new_id.

Definition zapIdStrictness : Var.Id -> Var.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ => IdInfo2.setStrictnessInfo arg_0__ Demand.nopSig)
    id.

Definition clearOneShotLambda : Var.Id -> Var.Id :=
  fun id =>
    modifyIdInfo (fun arg_0__ =>
                    IdInfo.setOneShotInfo arg_0__ BasicTypes.NoOneShotInfo) id.

Definition mkExportedLocalId
   : IdInfo.IdDetails -> Name.Name -> Core.Type_ -> Var.Id :=
  fun details name ty =>
    Var.mkExportedLocalVar details name ty IdInfo.vanillaIdInfo.

Definition mkGlobalId
   : IdInfo.IdDetails -> Name.Name -> Core.Type_ -> IdInfo.IdInfo -> Var.Id :=
  Var.mkGlobalVar.

Definition mkSysLocalM {m} `{UniqSupply.MonadUnique m}
   : FastString.FastString -> Core.Type_ -> m Var.Id :=
  fun fs ty =>
    UniqSupply.getUniqueM GHC.Base.>>=
    (fun uniq => GHC.Base.return_ (mkSysLocal fs uniq ty)).

Definition mkSysLocalOrCoVar
   : FastString.FastString -> Unique.Unique -> Core.Type_ -> Var.Id :=
  fun fs uniq ty => mkLocalIdOrCoVar (Name.mkSystemVarName uniq fs) ty.

Definition mkSysLocalOrCoVarM {m} `{UniqSupply.MonadUnique m}
   : FastString.FastString -> Core.Type_ -> m Var.Id :=
  fun fs ty =>
    UniqSupply.getUniqueM GHC.Base.>>=
    (fun uniq => GHC.Base.return_ (mkSysLocalOrCoVar fs uniq ty)).

Definition mkTemplateLocal : GHC.Num.Int -> Core.Type_ -> Var.Id :=
  fun i ty =>
    mkSysLocalOrCoVar (FastString.fsLit (GHC.Base.hs_string__ "tpl"))
    (Unique.mkBuiltinUnique i) ty.

Definition mkTemplateLocals : list Core.Type_ -> list Var.Id :=
  mkTemplateLocalsNum #1.

Definition mkUserLocal
   : OccName.OccName -> Unique.Unique -> Core.Type_ -> SrcLoc.SrcSpan -> Var.Id :=
  fun occ uniq ty loc =>
    if andb Util.debugIsOn (negb (negb (TyCoRep.isCoercionType ty))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Id.hs")
          #315)
    else mkLocalId (Name.mkInternalName uniq occ loc) ty.

Definition mkUserLocalOrCoVar
   : OccName.OccName -> Unique.Unique -> Core.Type_ -> SrcLoc.SrcSpan -> Var.Id :=
  fun occ uniq ty loc => mkLocalIdOrCoVar (Name.mkInternalName uniq occ loc) ty.

Definition mkWorkerId : Unique.Unique -> Var.Id -> Core.Type_ -> Var.Id :=
  fun uniq unwrkr ty =>
    mkLocalIdOrCoVar (Name.mkDerivedInternalName OccName.mkWorkerOcc uniq
                      (Name.getName unwrkr)) ty.

Definition realIdUnfolding : Var.Id -> CoreSyn.Unfolding :=
  fun id => IdInfo2.unfoldingInfo (Var.idInfo id).

Axiom recordSelectorTyCon : forall {A : Type}, A.

(* Translating `recordSelectorTyCon' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

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

(* Unbound variables:
     Kind None Some andb bool false isDataConId_maybe isDataConWorkId list mkLocalId
     mkLocalIdOrCoVar mkSysLocal mkTemplateLocalsNum negb option orb pair true
     BasicTypes.Activation BasicTypes.Arity BasicTypes.InlinePragma
     BasicTypes.NoOccInfo BasicTypes.NoOneShotInfo BasicTypes.OccInfo
     BasicTypes.OneShotInfo BasicTypes.OneShotLam BasicTypes.ProbOneShot
     BasicTypes.RuleMatchInfo BasicTypes.inlinePragmaActivation
     BasicTypes.inlinePragmaRuleMatchInfo BasicTypes.isConLike BasicTypes.isDeadOcc
     BasicTypes.isStrongLoopBreaker BasicTypes.setInlinePragmaActivation Core.Type_
     Core.Var CoreSyn.CoreRule CoreSyn.NoUnfolding CoreSyn.Unfolding DataCon.DataCon
     Demand.Demand Demand.StrictSig Demand.increaseStrictSigArity
     Demand.isBottomingSig Demand.nopSig FastString.FastString FastString.fsLit
     GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.Num.Int GHC.Num.fromInteger
     GHC.Num.op_zp__ GHC.Prim.seq IdInfo.CafInfo IdInfo.IdDetails IdInfo.IdInfo
     IdInfo.RuleInfo IdInfo.arityInfo IdInfo.cafInfo IdInfo.callArityInfo
     IdInfo.inlinePragInfo IdInfo.isEmptyRuleInfo IdInfo.occInfo IdInfo.oneShotInfo
     IdInfo.ruleInfo IdInfo.setArityInfo IdInfo.setCafInfo IdInfo.setCallArityInfo
     IdInfo.setInlinePragInfo IdInfo.setOccInfo IdInfo.setOneShotInfo
     IdInfo.setRuleInfo IdInfo.vanillaIdInfo IdInfo.zapDemandInfo
     IdInfo.zapFragileInfo IdInfo.zapLamInfo IdInfo.zapUsageInfo IdInfo2.demandInfo
     IdInfo2.ruleInfoRules IdInfo2.setDemandInfo IdInfo2.setStrictnessInfo
     IdInfo2.setUnfoldingInfo IdInfo2.setUnfoldingInfoLazily IdInfo2.strictnessInfo
     IdInfo2.unfoldingInfo Maybes.orElse Module.Module Name.Name Name.getName
     Name.isInternalName Name.localiseName Name.mkDerivedInternalName
     Name.mkInternalName Name.mkSystemVarName Name.nameIsLocalOrFrom OccName.OccName
     OccName.mkWorkerOcc Panic.assertPanic Panic.noString Panic.panicStr
     SrcLoc.SrcSpan TyCoRep.isCoercionType UniqSupply.MonadUnique
     UniqSupply.getUniqueM Unique.Unique Unique.mkBuiltinUnique Util.count
     Util.debugIsOn Var.Id Var.idDetails Var.idInfo Var.isId Var.isLocalId
     Var.isTyVar Var.lazySetIdInfo Var.mkExportedLocalVar Var.mkGlobalVar
     Var.mkLocalVar Var.setIdExported Var.setIdNotExported Var.setVarName
     Var.setVarUnique Var.varName Var.varType Var.varUnique
*)
