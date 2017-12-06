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
Require Class.
Require CoreSyn.
Require DataCon.
Require Demand.
Require FastString.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require IdInfo.
Require IdInfo2.
Require Maybes.
Require Module.
Require Name.
Require OccName.
Require SrcLoc.
Require UniqSupply.
Require Unique.
Require Util.
Require Var.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Record selectors *)
Import IdInfo.
Import IdInfo2.

(* Converted value declarations: *)

Parameter isDFunId : Var.Id -> bool.

(* Translating `isDFunId' failed: using a record pattern for the unknown
   constructor `DFunId' unsupported *)

Axiom isDataConRecordSelector : Var.Id -> bool.

(* Translating `isDataConRecordSelector' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

Axiom isImplicitId : Var.Id -> bool.

(* Translating `isImplicitId' failed: using a record pattern for the unknown
   constructor `FCallId' unsupported *)

Axiom isNaughtyRecordSelector : Var.Id -> bool.

(* Translating `isNaughtyRecordSelector' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

Axiom isPatSynRecordSelector : Var.Id -> bool.

(* Translating `isPatSynRecordSelector' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

Axiom isRecordSelector : Var.Id -> bool.

(* Translating `isRecordSelector' failed: using a record pattern for the unknown
   constructor `RecSelId' unsupported *)

Axiom recordSelectorTyCon : Var.Id -> IdInfo.RecSelParent.

(* Translating `recordSelectorTyCon' failed: using a record pattern for the
   unknown constructor `RecSelId' unsupported *)

Parameter hasNoBinding : Var.Id -> bool.

Definition idArity : Var.Id -> BasicTypes.Arity :=
  fun id => arityInfo (Var.idInfo id).

Definition idCafInfo : Var.Id -> IdInfo.CafInfo :=
  fun id => cafInfo (Var.idInfo id).

Definition idCallArity : Var.Id -> BasicTypes.Arity :=
  fun id => callArityInfo (Var.idInfo id).

Definition idDemandInfo : Var.Id -> Demand.Demand :=
  fun id => demandInfo (Var.idInfo id).

Definition idInlinePragma : Var.Id -> BasicTypes.InlinePragma :=
  fun id => inlinePragInfo (Var.idInfo id).

Definition idRuleMatchInfo : Var.Id -> BasicTypes.RuleMatchInfo :=
  fun id => BasicTypes.inlinePragmaRuleMatchInfo (idInlinePragma id).

Definition idInlineActivation : Var.Id -> BasicTypes.Activation :=
  fun id => BasicTypes.inlinePragmaActivation (idInlinePragma id).

Definition idName : Var.Id -> Name.Name :=
  Var.varName.

Definition idIsFrom : Module.Module -> Var.Id -> bool :=
  fun mod_ id => Name.nameIsLocalOrFrom mod_ (idName id).

Definition idOccInfo : Var.Id -> BasicTypes.OccInfo :=
  fun id => occInfo (Var.idInfo id).

Definition isDeadBinder : Var.Id -> bool :=
  fun bndr =>
    if Var.isId bndr : bool
    then BasicTypes.isDeadOcc (idOccInfo bndr)
    else false.

Definition idOneShotInfo : Var.Id -> BasicTypes.OneShotInfo :=
  fun id => oneShotInfo (Var.idInfo id).

Definition isOneShotLambda : Var.Id -> bool :=
  fun id =>
    let scrut_1__ := idOneShotInfo id in
    match scrut_1__ with
      | BasicTypes.OneShotLam => true
      | _ => false
    end.

Definition isOneShotBndr : Var.Var -> bool :=
  fun var =>
    let j_4__ := isOneShotLambda var in
    if Var.isTyVar var : bool
    then true
    else j_4__.

Definition isProbablyOneShotLambda : Var.Id -> bool :=
  fun id =>
    let scrut_6__ := idOneShotInfo id in
    match scrut_6__ with
      | BasicTypes.OneShotLam => true
      | BasicTypes.ProbOneShot => true
      | BasicTypes.NoOneShotInfo => false
    end.

Definition idSpecialisation : Var.Id -> IdInfo.RuleInfo :=
  fun id => ruleInfo (Var.idInfo id).

Definition idHasRules : Var.Id -> bool :=
  fun id => negb (IdInfo.isEmptyRuleInfo (idSpecialisation id)).

Definition idCoreRules : Var.Id -> list CoreSyn.CoreRule :=
  fun id => IdInfo2.ruleInfoRules (idSpecialisation id).

Definition idStrictness : Var.Id -> Demand.StrictSig :=
  fun id => strictnessInfo (Var.idInfo id).

Definition isBottomingId : Var.Id -> bool :=
  fun id => Demand.isBottomingSig (idStrictness id).

Definition idType : Var.Id -> unit :=
  Var.varType.

Parameter isDictId : Var.Id -> bool.

Definition localiseId : Var.Id -> Var.Id :=
  fun id =>
    let name := idName id in
    let j_150__ :=
      Var.mkLocalVar (Var.idDetails id) (Name.localiseName name) (idType id)
      (Var.idInfo id) in
    if (if andb Util.debugIsOn (negb (Var.isId id)) : bool
       then (Panic.assertPanic (GHC.Base.hs_string__ "ghc/compiler/basicTypes/Id.hs")
            (GHC.Num.fromInteger 193))
       else andb (Var.isLocalId id) (Name.isInternalName name)) : bool
    then id
    else j_150__.

Parameter isStrictId : Var.Id -> bool.
(*  fun id =>
    if andb Util.debugIsOn (negb (Var.isId id)) : bool
    then (Outputable.assertPprPanic (GHC.Base.hs_string__
                                    "ghc/compiler/basicTypes/Id.hs") (GHC.Num.fromInteger 586) (GHC.Base.mappend (id
                                                                                                                 (GHC.Base.hs_string__
                                                                                                                 "isStrictId: not an id: "))
                                                                                                                 (Panic.noString
                                                                                                                 id)))
    else orb (Type.isStrictType (idType id)) (Demand.isStrictDmd (idDemandInfo id)).
*)

Parameter idRepArity : Var.Id -> BasicTypes.RepArity.

Definition idUnfolding : Var.Id -> CoreSyn.Unfolding :=
  fun id =>
    let info := Var.idInfo id in
    let j_20__ := unfoldingInfo info in
    if BasicTypes.isStrongLoopBreaker (occInfo info) : bool
    then CoreSyn.NoUnfolding
    else j_20__.

Definition idUnique : Var.Id -> Unique.Unique :=
  Var.varUnique.

Parameter isClassOpId_maybe : Var.Id -> option Class.Class.

Parameter isDataConId_maybe : Var.Id -> option DataCon.DataCon.

Parameter idDataCon : Var.Id -> DataCon.DataCon.

Parameter isDataConWorkId : Var.Id -> bool.

Definition isConLikeId : Var.Id -> bool :=
  fun id => orb (isDataConWorkId id) (BasicTypes.isConLike (idRuleMatchInfo id)).

Parameter isDataConWorkId_maybe : Var.Id -> option DataCon.DataCon.

Parameter isEvVar : Var.Var -> bool.

Parameter isFCallId : Var.Id -> bool.

Parameter isFCallId_maybe : Var.Id -> option unit.

Parameter isPrimOpId : Var.Id -> bool.

Parameter isPrimOpId_maybe : Var.Id -> option unit.

Definition lazySetIdInfo : Var.Id -> IdInfo.IdInfo -> Var.Id :=
  Var.lazySetIdInfo.

Definition maybeModifyIdInfo : option IdInfo.IdInfo -> Var.Id -> Var.Id :=
  fun arg_136__ arg_137__ =>
    match arg_136__ , arg_137__ with
      | Some new_info , id => lazySetIdInfo id new_info
      | None , id => id
    end.

Definition zapInfo : (IdInfo.IdInfo -> option
                     IdInfo.IdInfo) -> Var.Id -> Var.Id :=
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
                   IdInfo.setInlinePragInfo info (fn (inlinePragInfo info))) id.

Definition setInlineActivation : Var.Id -> BasicTypes.Activation -> Var.Id :=
  fun id act =>
    modifyInlinePragma id (fun prag =>
                            BasicTypes.setInlinePragmaActivation prag act).

Definition setIdArity : Var.Id -> BasicTypes.Arity -> Var.Id :=
  fun id arity =>
    modifyIdInfo (fun arg_89__ => IdInfo.setArityInfo arg_89__ arity) id.

Definition setIdCafInfo : Var.Id -> IdInfo.CafInfo -> Var.Id :=
  fun id caf_info =>
    modifyIdInfo (fun arg_105__ => IdInfo.setCafInfo arg_105__ caf_info) id.

Definition setIdCallArity : Var.Id -> BasicTypes.Arity -> Var.Id :=
  fun id arity =>
    modifyIdInfo (fun arg_91__ => IdInfo.setCallArityInfo arg_91__ arity) id.

Definition setIdDemandInfo : Var.Id -> Demand.Demand -> Var.Id :=
  fun id dmd =>
    modifyIdInfo (fun arg_101__ => IdInfo2.setDemandInfo arg_101__ dmd) id.

Definition setIdOccInfo : Var.Id -> BasicTypes.OccInfo -> Var.Id :=
  fun id occ_info =>
    modifyIdInfo (fun arg_107__ => IdInfo.setOccInfo arg_107__ occ_info) id.

Definition zapIdOccInfo : Var.Id -> Var.Id :=
  fun b => setIdOccInfo b BasicTypes.NoOccInfo.

Definition setIdOneShotInfo : Var.Id -> BasicTypes.OneShotInfo -> Var.Id :=
  fun id one_shot =>
    modifyIdInfo (fun arg_120__ => IdInfo.setOneShotInfo arg_120__ one_shot) id.

Definition updOneShotInfo : Var.Id -> BasicTypes.OneShotInfo -> Var.Id :=
  fun id one_shot =>
    let do_upd :=
      let scrut_122__ := pair (idOneShotInfo id) one_shot in
      match scrut_122__ with
        | pair BasicTypes.NoOneShotInfo _ => true
        | pair BasicTypes.OneShotLam _ => false
        | pair _ BasicTypes.NoOneShotInfo => false
        | _ => true
      end in
    if do_upd : bool
    then setIdOneShotInfo id one_shot
    else id.

Definition setIdSpecialisation : Var.Id -> IdInfo.RuleInfo -> Var.Id :=
  fun id spec_info =>
    modifyIdInfo (fun arg_103__ => IdInfo.setRuleInfo arg_103__ spec_info) id.

Definition setIdStrictness : Var.Id -> Demand.StrictSig -> Var.Id :=
  fun id sig =>
    modifyIdInfo (fun arg_93__ => IdInfo2.setStrictnessInfo arg_93__ sig) id.

Definition setIdUnfolding : Var.Id -> CoreSyn.Unfolding -> Var.Id :=
  fun id unfolding =>
    modifyIdInfo (fun arg_99__ => IdInfo2.setUnfoldingInfo arg_99__ unfolding) id.

Definition setIdUnfoldingLazily : Var.Id -> CoreSyn.Unfolding -> Var.Id :=
  fun id unfolding =>
    modifyIdInfo (fun arg_97__ => IdInfo2.setUnfoldingInfoLazily arg_97__ unfolding)
    id.

Definition setInlinePragma : Var.Id -> BasicTypes.InlinePragma -> Var.Id :=
  fun id prag =>
    modifyIdInfo (fun arg_110__ => IdInfo.setInlinePragInfo arg_110__ prag) id.

Definition setOneShotLambda : Var.Id -> Var.Id :=
  fun id =>
    modifyIdInfo (fun arg_116__ =>
                   IdInfo.setOneShotInfo arg_116__ BasicTypes.OneShotLam) id.

Definition transferPolyIdInfo : Var.Id -> list Var.Var -> Var.Id -> Var.Id :=
  fun old_id abstract_wrt new_id =>
    let old_info := Var.idInfo old_id in
    let old_arity := arityInfo old_info in
    let old_inline_prag := inlinePragInfo old_info in
    let old_occ_info := occInfo old_info in
    let old_strictness := strictnessInfo old_info in
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
    modifyIdInfo (fun arg_95__ => IdInfo2.setStrictnessInfo arg_95__ Demand.nopSig)
    id.

Definition clearOneShotLambda : Var.Id -> Var.Id :=
  fun id =>
    modifyIdInfo (fun arg_118__ =>
                   IdInfo.setOneShotInfo arg_118__ BasicTypes.NoOneShotInfo) id.

Definition mkExportedLocalId
    : IdInfo.IdDetails -> Name.Name -> unit -> Var.Id :=
  fun details name ty =>
    Var.mkExportedLocalVar details name ty IdInfo.vanillaIdInfo.

Parameter mkExportedVanillaId : Name.Name -> unit -> Var.Id.

Definition mkGlobalId
    : IdInfo.IdDetails -> Name.Name -> unit -> IdInfo.IdInfo -> Var.Id :=
  Var.mkGlobalVar.

Parameter mkVanillaGlobalWithInfo
    : Name.Name -> unit -> IdInfo.IdInfo -> Var.Id.

Definition mkVanillaGlobal : Name.Name -> unit -> Var.Id :=
  fun name ty => mkVanillaGlobalWithInfo name ty IdInfo.vanillaIdInfo.

Parameter mkLocalCoVar : Name.Name -> unit -> Var.CoVar.

Parameter mkLocalIdOrCoVarWithInfo
    : Name.Name -> unit -> IdInfo.IdInfo -> Var.Id.

Parameter mkLocalIdWithInfo : Name.Name -> unit -> IdInfo.IdInfo -> Var.Id.

Parameter mkLocalId : Name.Name -> unit -> Var.Id.

Parameter mkSysLocal
    : FastString.FastString -> Unique.Unique -> unit -> Var.Id.

Definition mkSysLocalM {m} `{UniqSupply.MonadUnique m}
    : FastString.FastString -> unit -> m Var.Id :=
  fun fs ty =>
    UniqSupply.getUniqueM GHC.Base.>>= (fun uniq =>
      GHC.Base.return_ (mkSysLocal fs uniq ty)).

Parameter mkUserLocal
    : OccName.OccName -> Unique.Unique -> unit -> SrcLoc.SrcSpan -> Var.Id.

Parameter mkLocalIdOrCoVar : Name.Name -> unit -> Var.Id.

Definition mkSysLocalOrCoVar
    : FastString.FastString -> Unique.Unique -> unit -> Var.Id :=
  fun fs uniq ty => mkLocalIdOrCoVar (Name.mkSystemVarName uniq fs) ty.

Definition mkSysLocalOrCoVarM {m} `{UniqSupply.MonadUnique m}
    : FastString.FastString -> unit -> m Var.Id :=
  fun fs ty =>
    UniqSupply.getUniqueM GHC.Base.>>= (fun uniq =>
      GHC.Base.return_ (mkSysLocalOrCoVar fs uniq ty)).

Definition mkTemplateLocal : GHC.Num.Int -> unit -> Var.Id :=
  fun i ty =>
    mkSysLocalOrCoVar (FastString.fsLit (GHC.Base.hs_string__ "tpl"))
    (Unique.mkBuiltinUnique i) ty.

(* zipwith enumFrom !!! *)
Definition mkTemplateLocalsNum : GHC.Num.Int -> list unit -> list Var.Id :=
  fun n tys => GHC.List.zipWith mkTemplateLocal (Enum.enumFromTo n (Data.Foldable.length tys)) tys.

Definition mkTemplateLocals : list unit -> list Var.Id :=
  mkTemplateLocalsNum (GHC.Num.fromInteger 1).

Definition mkUserLocalOrCoVar
    : OccName.OccName -> Unique.Unique -> unit -> SrcLoc.SrcSpan -> Var.Id :=
  fun occ uniq ty loc => mkLocalIdOrCoVar (Name.mkInternalName uniq occ loc) ty.

(* Needs Name.NamedThing Var.Id *)
Parameter mkWorkerId : Unique.Unique -> Var.Id -> unit -> Var.Id.


Definition realIdUnfolding : Var.Id -> CoreSyn.Unfolding :=
  fun id => unfoldingInfo (Var.idInfo id).

Definition setIdExported : Var.Id -> Var.Id :=
  Var.setIdExported.

Definition setIdName : Var.Id -> Name.Name -> Var.Id :=
  Var.setVarName.

Definition setIdNotExported : Var.Id -> Var.Id :=
  Var.setIdNotExported.

Parameter setIdType : Var.Id -> unit -> Var.Id.

Definition setIdUnique : Var.Id -> Unique.Unique -> Var.Id :=
  Var.setVarUnique.

Definition stateHackOneShot : BasicTypes.OneShotInfo :=
  BasicTypes.OneShotLam.

(* Unbound variables:
     None Some Var.varName Var.varType andb arityInfo bool cafInfo callArityInfo
     demandInfo enumFrom false inlinePragInfo list negb occInfo oneShotInfo option
     orb pair ruleInfo strictnessInfo true typeOneShot unfoldingInfo unit varType
     BasicTypes.Activation BasicTypes.Arity BasicTypes.InlinePragma
     BasicTypes.NoOccInfo BasicTypes.NoOneShotInfo BasicTypes.OccInfo
     BasicTypes.OneShotInfo BasicTypes.OneShotLam BasicTypes.ProbOneShot
     BasicTypes.RepArity BasicTypes.RuleMatchInfo BasicTypes.inlinePragmaActivation
     BasicTypes.inlinePragmaRuleMatchInfo BasicTypes.isConLike BasicTypes.isDeadOcc
     BasicTypes.isStrongLoopBreaker BasicTypes.setInlinePragmaActivation Class.Class
     CoreSyn.CoreRule CoreSyn.NoUnfolding CoreSyn.Unfolding DataCon.DataCon
     DataCon.isUnboxedTupleCon Demand.Demand Demand.StrictSig
     Demand.increaseStrictSigArity Demand.isBottomingSig Demand.isStrictDmd
     Demand.nopSig FastString.FastString FastString.fsLit GHC.Base.mappend
     GHC.Base.op_zgzgze__ GHC.Base.return_ GHC.List.zipWith GHC.Num.Int
     GHC.Num.op_zp__ GHC.Prim.seq IdInfo.CafInfo IdInfo.ClassOpId IdInfo.CoVarId
     IdInfo.DataConWorkId IdInfo.DataConWrapId IdInfo.FCallId IdInfo.IdDetails
     IdInfo.IdInfo IdInfo.PrimOpId IdInfo.RuleInfo IdInfo.VanillaId
     IdInfo.isEmptyRuleInfo IdInfo.setArityInfo IdInfo.setCafInfo
     IdInfo.setCallArityInfo IdInfo.setInlinePragInfo IdInfo.setOccInfo
     IdInfo.setOneShotInfo IdInfo.setRuleInfo IdInfo.vanillaIdInfo
     IdInfo.zapDemandInfo IdInfo.zapFragileInfo IdInfo.zapLamInfo IdInfo.zapUsageInfo
     IdInfo2.ruleInfoRules IdInfo2.setDemandInfo IdInfo2.setStrictnessInfo
     IdInfo2.setUnfoldingInfo IdInfo2.setUnfoldingInfoLazily Maybes.orElse
     Module.Module Name.Name Name.getName Name.isInternalName Name.localiseName
     Name.mkDerivedInternalName Name.mkInternalName Name.mkSystemVarName
     Name.nameIsLocalOrFrom OccName.OccName OccName.mkWorkerOcc
     Outputable.assertPprPanic Panic.assertPanic Panic.noString Panic.panicStr
     SrcLoc.SrcSpan TyCoRep.isCoercionType Type.isDictTy Type.isPredTy
     Type.isStrictType Type.seqType Type.typeRepArity UniqSupply.MonadUnique
     UniqSupply.getUniqueM Unique.Unique Unique.mkBuiltinUnique Util.count
     Util.debugIsOn Var.CoVar Var.Id Var.Var Var.idDetails Var.idInfo Var.isId
     Var.isLocalId Var.isTyVar Var.lazySetIdInfo Var.mkExportedLocalVar
     Var.mkGlobalVar Var.mkLocalVar Var.setIdExported Var.setIdNotExported
     Var.setVarName Var.setVarType Var.setVarUnique Var.varUnique
*)
