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
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require CoreFVs.
Require CoreUtils.
Require Data.Foldable.
Require Data.Maybe.
Require Data.Traversable.
Require Data.Tuple.
Require Datatypes.
Require Digraph.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require GHC.Prim.
Require Id.
Require Module.
Require Name.
Require Panic.
Require UniqFM.
Require UniqSet.
Require Unique.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition OneShots :=
  (list BasicTypes.OneShotInfo)%type.

Definition OccInfoEnv :=
  (Core.IdEnv BasicTypes.OccInfo)%type.

Definition ZappedSet :=
  OccInfoEnv%type.

Inductive UsageDetails : Type
  := | UD (ud_env : OccInfoEnv) (ud_z_many : ZappedSet) (ud_z_in_lam : ZappedSet)
  (ud_z_no_tail : ZappedSet)
   : UsageDetails.

Inductive OccEncl : Type := | OccRhs : OccEncl |  OccVanilla : OccEncl.

Definition NodeScore :=
  (nat * nat * bool)%type%type.

Definition ImpRuleEdges :=
  (Core.IdEnv Core.IdSet)%type.

Definition IdWithOccInfo :=
  Core.Id%type.

Definition GlobalScruts :=
  Core.IdSet%type.

Inductive OccEnv : Type
  := | Mk_OccEnv (occ_encl : OccEncl) (occ_one_shots : OneShots) (occ_gbl_scrut
    : GlobalScruts) (occ_rule_act : BasicTypes.Activation -> bool) (occ_binder_swap
    : bool)
   : OccEnv.

Inductive Details : Type
  := | ND (nd_bndr : Core.Id) (nd_rhs : Core.CoreExpr) (nd_rhs_bndrs
    : list Core.CoreBndr) (nd_uds : UsageDetails) (nd_inl : Core.IdSet) (nd_weak
    : Core.IdSet) (nd_active_rule_fvs : Core.IdSet) (nd_score : NodeScore)
   : Details.

Definition LetrecNode :=
  (Digraph.Node Unique.Unique Details)%type.

Definition Binding :=
  (Core.Id * Core.CoreExpr)%type%type.

Instance Default__UsageDetails : GHC.Err.Default UsageDetails :=
  GHC.Err.Build_Default _ (UD GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default).

Instance Default__OccEncl : GHC.Err.Default OccEncl :=
  GHC.Err.Build_Default _ OccRhs.

Instance Default__OccEnv : GHC.Err.Default OccEnv :=
  GHC.Err.Build_Default _ (Mk_OccEnv GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default).

Instance Default__Details : GHC.Err.Default Details :=
  GHC.Err.Build_Default _ (ND GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default GHC.Err.default GHC.Err.default GHC.Err.default
                         GHC.Err.default).

Definition ud_env (arg_0__ : UsageDetails) :=
  let 'UD ud_env _ _ _ := arg_0__ in
  ud_env.

Definition ud_z_in_lam (arg_0__ : UsageDetails) :=
  let 'UD _ _ ud_z_in_lam _ := arg_0__ in
  ud_z_in_lam.

Definition ud_z_many (arg_0__ : UsageDetails) :=
  let 'UD _ ud_z_many _ _ := arg_0__ in
  ud_z_many.

Definition ud_z_no_tail (arg_0__ : UsageDetails) :=
  let 'UD _ _ _ ud_z_no_tail := arg_0__ in
  ud_z_no_tail.

Definition occ_binder_swap (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv _ _ _ _ occ_binder_swap := arg_0__ in
  occ_binder_swap.

Definition occ_encl (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv occ_encl _ _ _ _ := arg_0__ in
  occ_encl.

Definition occ_gbl_scrut (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv _ _ occ_gbl_scrut _ _ := arg_0__ in
  occ_gbl_scrut.

Definition occ_one_shots (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv _ occ_one_shots _ _ _ := arg_0__ in
  occ_one_shots.

Definition occ_rule_act (arg_0__ : OccEnv) :=
  let 'Mk_OccEnv _ _ _ occ_rule_act _ := arg_0__ in
  occ_rule_act.

Definition nd_active_rule_fvs (arg_0__ : Details) :=
  let 'ND _ _ _ _ _ _ nd_active_rule_fvs _ := arg_0__ in
  nd_active_rule_fvs.

Definition nd_bndr (arg_0__ : Details) :=
  let 'ND nd_bndr _ _ _ _ _ _ _ := arg_0__ in
  nd_bndr.

Definition nd_inl (arg_0__ : Details) :=
  let 'ND _ _ _ _ nd_inl _ _ _ := arg_0__ in
  nd_inl.

Definition nd_rhs (arg_0__ : Details) :=
  let 'ND _ nd_rhs _ _ _ _ _ _ := arg_0__ in
  nd_rhs.

Definition nd_rhs_bndrs (arg_0__ : Details) :=
  let 'ND _ _ nd_rhs_bndrs _ _ _ _ _ := arg_0__ in
  nd_rhs_bndrs.

Definition nd_score (arg_0__ : Details) :=
  let 'ND _ _ _ _ _ _ _ nd_score := arg_0__ in
  nd_score.

Definition nd_uds (arg_0__ : Details) :=
  let 'ND _ _ _ nd_uds _ _ _ _ := arg_0__ in
  nd_uds.

Definition nd_weak (arg_0__ : Details) :=
  let 'ND _ _ _ _ _ nd_weak _ _ := arg_0__ in
  nd_weak.

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccurAnal.Outputable__Details' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccurAnal.Outputable__OccEncl' *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OccurAnal.Outputable__UsageDetails' *)

Axiom occurAnalysePgm : Module.Module ->
                        (BasicTypes.Activation -> bool) ->
                        list Core.CoreRule ->
                        list Core.CoreVect -> Core.VarSet -> Core.CoreProgram -> Core.CoreProgram.

Definition initOccEnv : (BasicTypes.Activation -> bool) -> OccEnv :=
  fun active_rule => Mk_OccEnv OccVanilla nil Core.emptyVarSet active_rule true.

Axiom occAnal : OccEnv -> Core.CoreExpr -> (UsageDetails * Core.CoreExpr)%type.

Definition occurAnalyseExpr' : bool -> Core.CoreExpr -> Core.CoreExpr :=
  fun enable_binder_swap expr =>
    let all_active_rules := fun arg_0__ => true in
    let env :=
      let 'Mk_OccEnv occ_encl_2__ occ_one_shots_3__ occ_gbl_scrut_4__ occ_rule_act_5__
         occ_binder_swap_6__ := (initOccEnv all_active_rules) in
      Mk_OccEnv occ_encl_2__ occ_one_shots_3__ occ_gbl_scrut_4__ occ_rule_act_5__
                enable_binder_swap in
    Data.Tuple.snd (occAnal env expr).

Definition occurAnalyseExpr : Core.CoreExpr -> Core.CoreExpr :=
  occurAnalyseExpr' true.

Definition occurAnalyseExpr_NoBinderSwap : Core.CoreExpr -> Core.CoreExpr :=
  occurAnalyseExpr' false.

Axiom occAnalBind : OccEnv ->
                    BasicTypes.TopLevelFlag ->
                    ImpRuleEdges ->
                    Core.CoreBind -> UsageDetails -> (UsageDetails * list Core.CoreBind)%type.

Definition andTailCallInfo
   : BasicTypes.TailCallInfo ->
     BasicTypes.TailCallInfo -> BasicTypes.TailCallInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (BasicTypes.AlwaysTailCalled arity1 as info)
    , BasicTypes.AlwaysTailCalled arity2 =>
        if arity1 GHC.Base.== arity2 : bool then info else
        BasicTypes.NoTailCallInfo
    | _, _ => BasicTypes.NoTailCallInfo
    end.

Definition addOccInfo
   : BasicTypes.OccInfo -> BasicTypes.OccInfo -> BasicTypes.OccInfo :=
  fun a1 a2 =>
    if andb Util.debugIsOn (negb (negb (orb (BasicTypes.isDeadOcc a1)
                                            (BasicTypes.isDeadOcc a2)))) : bool
    then (Panic.assertPanic (GHC.Base.hs_string__
                             "ghc/compiler/simplCore/OccurAnal.hs") #2825)
    else BasicTypes.ManyOccs (andTailCallInfo (BasicTypes.tailCallInfo a1)
                                              (BasicTypes.tailCallInfo a2)).

Definition alterZappedSets
   : UsageDetails -> (ZappedSet -> ZappedSet) -> UsageDetails :=
  fun ud f =>
    let 'UD ud_env_0__ ud_z_many_1__ ud_z_in_lam_2__ ud_z_no_tail_3__ := ud in
    UD ud_env_0__ (f (ud_z_many ud)) (f (ud_z_in_lam ud)) (f (ud_z_no_tail ud)).

Definition markInsideLam : BasicTypes.OccInfo -> BasicTypes.OccInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | (BasicTypes.OneOcc _ _ _ _ as occ) =>
        match occ with
        | BasicTypes.ManyOccs _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | BasicTypes.IAmDead =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | BasicTypes.OneOcc occ_in_lam_1__ occ_one_br_2__ occ_int_cxt_3__
        occ_tail_4__ =>
            BasicTypes.OneOcc true occ_one_br_2__ occ_int_cxt_3__ occ_tail_4__
        | BasicTypes.IAmALoopBreaker _ _ =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        end
    | occ => occ
    end.

Definition markMany : BasicTypes.OccInfo -> BasicTypes.OccInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | BasicTypes.IAmDead => BasicTypes.IAmDead
    | occ => BasicTypes.ManyOccs (BasicTypes.occ_tail occ)
    end.

Definition markNonTailCalled : BasicTypes.OccInfo -> BasicTypes.OccInfo :=
  fun arg_0__ =>
    match arg_0__ with
    | BasicTypes.IAmDead => BasicTypes.IAmDead
    | occ =>
        match occ with
        | BasicTypes.ManyOccs occ_tail_1__ =>
            BasicTypes.ManyOccs BasicTypes.NoTailCallInfo
        | BasicTypes.IAmDead =>
            GHC.Err.error (GHC.Base.hs_string__ "Partial record update")
        | BasicTypes.OneOcc occ_in_lam_2__ occ_one_br_3__ occ_int_cxt_4__
        occ_tail_5__ =>
            BasicTypes.OneOcc occ_in_lam_2__ occ_one_br_3__ occ_int_cxt_4__
                              BasicTypes.NoTailCallInfo
        | BasicTypes.IAmALoopBreaker occ_rules_only_6__ occ_tail_7__ =>
            BasicTypes.IAmALoopBreaker occ_rules_only_6__ BasicTypes.NoTailCallInfo
        end
    end.

Definition doZappingByUnique
   : UsageDetails -> Unique.Unique -> BasicTypes.OccInfo -> BasicTypes.OccInfo :=
  fun ud uniq =>
    let in_subset := fun field => Core.elemVarEnvByKey uniq (field ud) in
    (if in_subset ud_z_many : bool then markMany else
     if in_subset ud_z_in_lam : bool then markInsideLam else
     GHC.Base.id) GHC.Base.∘
    (if in_subset ud_z_no_tail : bool then markNonTailCalled else
     GHC.Base.id).

Definition doZapping
   : UsageDetails -> Core.Var -> BasicTypes.OccInfo -> BasicTypes.OccInfo :=
  fun ud var occ => doZappingByUnique ud (Core.varUnique var) occ.

Definition addOneOcc
   : UsageDetails -> Core.Id -> BasicTypes.OccInfo -> UsageDetails :=
  fun ud id info =>
    let plus_zapped := fun old new => addOccInfo (doZapping ud id old) new in
    alterZappedSets (let 'UD ud_env_1__ ud_z_many_2__ ud_z_in_lam_3__
                        ud_z_no_tail_4__ := ud in
                     UD (Core.extendVarEnv_C plus_zapped (ud_env ud) id info) ud_z_many_2__
                        ud_z_in_lam_3__ ud_z_no_tail_4__) (fun arg_7__ => Core.delVarEnv arg_7__ id).

Definition addManyOccs : Core.Var -> UsageDetails -> UsageDetails :=
  fun v u => if Core.isId v : bool then addOneOcc u v BasicTypes.noOccInfo else u.

Definition addManyOccsSet : UsageDetails -> Core.VarSet -> UsageDetails :=
  fun usage id_set => UniqSet.nonDetFoldUniqSet addManyOccs usage id_set.

Definition markAllInsideLam : UsageDetails -> UsageDetails :=
  fun ud =>
    let 'UD ud_env_0__ ud_z_many_1__ ud_z_in_lam_2__ ud_z_no_tail_3__ := ud in
    UD ud_env_0__ ud_z_many_1__ (ud_env ud) ud_z_no_tail_3__.

Definition markAllNonTailCalled : UsageDetails -> UsageDetails :=
  fun ud =>
    let 'UD ud_env_0__ ud_z_many_1__ ud_z_in_lam_2__ ud_z_no_tail_3__ := ud in
    UD ud_env_0__ ud_z_many_1__ ud_z_in_lam_2__ (ud_env ud).

Definition adjustRhsUsage
   : option BasicTypes.JoinArity ->
     BasicTypes.RecFlag -> list Core.CoreBndr -> UsageDetails -> UsageDetails :=
  fun mb_join_arity rec_flag bndrs usage =>
    let exact_join :=
      match mb_join_arity with
      | Some join_arity => Util.lengthIs bndrs join_arity
      | _ => false
      end in
    let one_shot :=
      match mb_join_arity with
      | Some join_arity =>
          if BasicTypes.isRec rec_flag : bool then false else
          Data.Foldable.all Id.isOneShotBndr (Coq.Lists.List.skipn join_arity bndrs)
      | None => Data.Foldable.all Id.isOneShotBndr bndrs
      end in
    let maybe_drop_tails :=
      fun ud => if exact_join : bool then ud else markAllNonTailCalled ud in
    let maybe_mark_lam :=
      fun ud => if one_shot : bool then ud else markAllInsideLam ud in
    maybe_mark_lam (maybe_drop_tails usage).

Definition emptyDetails : UsageDetails :=
  UD Core.emptyVarEnv Core.emptyVarEnv Core.emptyVarEnv Core.emptyVarEnv.

Definition isEmptyDetails : UsageDetails -> bool :=
  Core.isEmptyVarEnv GHC.Base.∘ ud_env.

Definition combineUsageDetailsWith
   : (BasicTypes.OccInfo -> BasicTypes.OccInfo -> BasicTypes.OccInfo) ->
     UsageDetails -> UsageDetails -> UsageDetails :=
  fun plus_occ_info ud1 ud2 =>
    if isEmptyDetails ud1 : bool then ud2 else
    if isEmptyDetails ud2 : bool then ud1 else
    UD (Core.plusVarEnv_C plus_occ_info (ud_env ud1) (ud_env ud2)) (Core.plusVarEnv
        (ud_z_many ud1) (ud_z_many ud2)) (Core.plusVarEnv (ud_z_in_lam ud1) (ud_z_in_lam
                                                                             ud2)) (Core.plusVarEnv (ud_z_no_tail ud1)
        (ud_z_no_tail ud2)).

Definition op_zpzpzp__ : UsageDetails -> UsageDetails -> UsageDetails :=
  combineUsageDetailsWith addOccInfo.

Notation "'_+++_'" := (op_zpzpzp__).

Infix "+++" := (_+++_) (at level 99).

Definition combineUsageDetailsList : list UsageDetails -> UsageDetails :=
  Data.Foldable.foldl _+++_ emptyDetails.

Definition markJoinOneShots
   : option BasicTypes.JoinArity -> list Core.Var -> list Core.Var :=
  fun mb_join_arity bndrs =>
    let fix go arg_0__ arg_1__
              := match arg_0__, arg_1__ with
                 | num_2__, bndrs =>
                     if num_2__ GHC.Base.== #0 : bool then bndrs else
                     match arg_0__, arg_1__ with
                     | _, nil =>
                         Panic.warnPprTrace (true) (GHC.Base.hs_string__
                                             "ghc/compiler/simplCore/OccurAnal.hs") #2194 (GHC.Base.mappend
                                             Panic.someSDoc Panic.someSDoc) nil
                     | n, cons b bs =>
                         let b' := if Core.isId b : bool then Id.setOneShotLambda b else b in
                         cons b' (go (n GHC.Num.- #1) bs)
                     end
                 end in
    match mb_join_arity with
    | None => bndrs
    | Some n => go n bndrs
    end.

Axiom occAnalLamOrRhs : OccEnv ->
                        list Core.CoreBndr ->
                        Core.CoreExpr -> (UsageDetails * list Core.CoreBndr * Core.CoreExpr)%type.

Definition rhsCtxt : OccEnv -> OccEnv :=
  fun '(Mk_OccEnv occ_encl_0__ occ_one_shots_1__ occ_gbl_scrut_2__
  occ_rule_act_3__ occ_binder_swap_4__) =>
    Mk_OccEnv OccRhs nil occ_gbl_scrut_2__ occ_rule_act_3__ occ_binder_swap_4__.

Definition occAnalNonRecRhs
   : OccEnv ->
     Core.Id ->
     list Core.CoreBndr ->
     Core.CoreExpr -> (UsageDetails * list Core.CoreBndr * Core.CoreExpr)%type :=
  fun env bndr bndrs body =>
    let not_stable := negb (Core.isStableUnfolding (Id.idUnfolding bndr)) in
    let active := BasicTypes.isAlwaysActive (Id.idInlineActivation bndr) in
    let dmd := Id.idDemandInfo bndr in
    let occ := Id.idOccInfo bndr in
    let is_join_point := BasicTypes.isAlwaysTailCalled occ in
    let certainly_inline :=
      match occ with
      | BasicTypes.OneOcc in_lam one_br _ _ =>
          andb (negb in_lam) (andb one_br (andb active not_stable))
      | _ => false
      end in
    let env1 :=
      if is_join_point : bool then env else
      if certainly_inline : bool then env else
      rhsCtxt env in
    let rhs_env :=
      let 'Mk_OccEnv occ_encl_11__ occ_one_shots_12__ occ_gbl_scrut_13__
         occ_rule_act_14__ occ_binder_swap_15__ := env1 in
      Mk_OccEnv occ_encl_11__ (Core.argOneShots dmd) occ_gbl_scrut_13__
                occ_rule_act_14__ occ_binder_swap_15__ in
    occAnalLamOrRhs rhs_env bndrs body.

Axiom occAnalRules : OccEnv ->
                     option BasicTypes.JoinArity ->
                     BasicTypes.RecFlag ->
                     Core.Id -> list (Core.CoreRule * UsageDetails * UsageDetails)%type.

Definition occAnalUnfolding
   : OccEnv -> BasicTypes.RecFlag -> Core.Id -> option UsageDetails :=
  fun env rec_flag id => let scrut_0__ := Id.realIdUnfolding id in None.

Definition lookupDetails : UsageDetails -> Core.Id -> BasicTypes.OccInfo :=
  fun ud id =>
    match Core.lookupVarEnv (ud_env ud) id with
    | Some occ => doZapping ud id occ
    | None => BasicTypes.IAmDead
    end.

Definition decideJoinPointHood
   : BasicTypes.TopLevelFlag -> UsageDetails -> list Core.CoreBndr -> bool :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | BasicTypes.TopLevel, _, _ => false
    | BasicTypes.NotTopLevel, usage, bndrs =>
        let ok_unfolding := fun arg_3__ arg_4__ => true in
        let ok_rule :=
          fun arg_5__ arg_6__ =>
            match arg_5__, arg_6__ with
            | _, Core.BuiltinRule _ _ _ _ => false
            | join_arity, Core.Rule _ _ _ _ _ args _ _ _ _ _ =>
                Util.lengthIs args join_arity
            end in
        let ok :=
          fun bndr =>
            match BasicTypes.tailCallInfo (lookupDetails usage bndr) with
            | BasicTypes.AlwaysTailCalled arity =>
                if andb (Data.Foldable.all (ok_rule arity) (Id.idCoreRules bndr)) (andb
                         (ok_unfolding arity (Id.realIdUnfolding bndr)) (Core.isValidJoinPointType arity
                          (Id.idType bndr))) : bool
                then true else
                false
            | _ => false
            end in
        let all_ok := Data.Foldable.all ok bndrs in
        if Id.isJoinId (GHC.Err.head bndrs) : bool
        then Panic.warnPprTrace (negb all_ok) (GHC.Base.hs_string__
                                 "ghc/compiler/simplCore/OccurAnal.hs") #2730 (GHC.Base.mappend (Datatypes.id
                                                                                                 (GHC.Base.hs_string__
                                                                                                  "OccurAnal failed to rediscover join point(s):"))
                                                                                                Panic.someSDoc)
             all_ok else
        all_ok
    end.

Definition alterUsageDetails
   : UsageDetails -> (OccInfoEnv -> OccInfoEnv) -> UsageDetails :=
  fun ud f =>
    alterZappedSets (let 'UD ud_env_0__ ud_z_many_1__ ud_z_in_lam_2__
                        ud_z_no_tail_3__ := ud in
                     UD (f (ud_env ud)) ud_z_many_1__ ud_z_in_lam_2__ ud_z_no_tail_3__) f.

Definition delDetails : UsageDetails -> Core.Id -> UsageDetails :=
  fun ud bndr =>
    alterUsageDetails ud (fun arg_0__ => Core.delVarEnv arg_0__ bndr).

Definition setBinderOcc
   : BasicTypes.OccInfo -> Core.CoreBndr -> Core.CoreBndr :=
  fun occ_info bndr =>
    if Core.isTyVar bndr : bool then bndr else
    if Core.isExportedId bndr : bool
    then if BasicTypes.isManyOccs (Id.idOccInfo bndr) : bool
         then bndr
         else Id.setIdOccInfo bndr BasicTypes.noOccInfo else
    Id.setIdOccInfo bndr occ_info.

Definition tagNonRecBinder
   : BasicTypes.TopLevelFlag ->
     UsageDetails -> Core.CoreBndr -> (UsageDetails * IdWithOccInfo)%type :=
  fun lvl usage binder =>
    let usage' := delDetails usage binder in
    let will_be_join := decideJoinPointHood lvl usage (cons binder nil) in
    let occ := lookupDetails usage binder in
    let occ' :=
      if will_be_join : bool
      then if andb Util.debugIsOn (negb (BasicTypes.isAlwaysTailCalled occ)) : bool
           then (Panic.assertPanic (GHC.Base.hs_string__
                                    "ghc/compiler/simplCore/OccurAnal.hs") #2644)
           else occ else
      markNonTailCalled occ in
    let binder' := setBinderOcc occ' binder in
    GHC.Prim.seq usage' (pair usage' binder').

Definition usedIn : Core.Id -> UsageDetails -> bool :=
  fun v ud => orb (Core.isExportedId v) (Core.elemVarEnv v (ud_env ud)).

Definition willBeJoinId_maybe : Core.CoreBndr -> option BasicTypes.JoinArity :=
  fun bndr =>
    match BasicTypes.tailCallInfo (Id.idOccInfo bndr) with
    | BasicTypes.AlwaysTailCalled arity => Some arity
    | _ => Id.isJoinId_maybe bndr
    end.

Definition occAnalNonRecBind
   : OccEnv ->
     BasicTypes.TopLevelFlag ->
     ImpRuleEdges ->
     Core.Var ->
     Core.CoreExpr -> UsageDetails -> (UsageDetails * list Core.CoreBind)%type :=
  fun env lvl imp_rule_edges binder rhs body_usage =>
    let 'pair bndrs body := Core.collectBinders rhs in
    let 'pair body_usage' tagged_binder := tagNonRecBinder lvl body_usage binder in
    let mb_join_arity := willBeJoinId_maybe tagged_binder in
    let 'pair (pair rhs_usage1 bndrs') body' := occAnalNonRecRhs env tagged_binder
                                                  bndrs body in
    let rhs' := Core.mkLams (markJoinOneShots mb_join_arity bndrs') body' in
    let rhs_usage2 :=
      match occAnalUnfolding env BasicTypes.NonRecursive binder with
      | Some unf_usage => rhs_usage1 +++ unf_usage
      | None => rhs_usage1
      end in
    let rules_w_uds :=
      occAnalRules env mb_join_arity BasicTypes.NonRecursive tagged_binder in
    let rhs_usage3 :=
      rhs_usage2 +++
      combineUsageDetailsList (GHC.Base.map (fun '(pair (pair _ l) r) => l +++ r)
                               rules_w_uds) in
    let rhs_usage4 :=
      Data.Maybe.maybe rhs_usage3 (addManyOccsSet rhs_usage3) (Core.lookupVarEnv
                                                               imp_rule_edges binder) in
    let rhs_usage' :=
      adjustRhsUsage mb_join_arity BasicTypes.NonRecursive bndrs' rhs_usage4 in
    if Core.isTyVar binder : bool
    then pair body_usage (cons (Core.NonRec binder rhs) nil) else
    if negb (usedIn binder body_usage) : bool then pair body_usage nil else
    pair (body_usage' +++ rhs_usage') (cons (Core.NonRec tagged_binder rhs') nil).

Axiom occAnalRecBind : OccEnv ->
                       BasicTypes.TopLevelFlag ->
                       ImpRuleEdges ->
                       list (Core.Var * Core.CoreExpr)%type ->
                       UsageDetails -> (UsageDetails * list Core.CoreBind)%type.

(* Skipping definition `OccurAnal.occAnalRec' *)

Axiom loopBreakNodes : nat ->
                       Core.VarSet -> Core.VarSet -> list LetrecNode -> list Binding -> list Binding.

Axiom reOrderNodes : nat ->
                     Core.VarSet -> Core.VarSet -> list LetrecNode -> list Binding -> list Binding.

Axiom mk_loop_breaker : LetrecNode -> Binding.

Axiom mk_non_loop_breaker : Core.VarSet -> LetrecNode -> Binding.

Definition betterLB : NodeScore -> NodeScore -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair (pair rank1 size1) lb1, pair (pair rank2 size2) _ =>
        if rank1 GHC.Base.< rank2 : bool then true else
        if rank1 GHC.Base.> rank2 : bool then false else
        if size1 GHC.Base.< size2 : bool then false else
        if size1 GHC.Base.> size2 : bool then true else
        if lb1 : bool then true else
        false
    end.

Definition rank : NodeScore -> nat :=
  fun '(pair (pair r _) _) => r.

Fixpoint chooseLoopBreaker (arg_0__ : bool) (arg_1__ : NodeScore) (arg_2__
                            arg_3__ arg_4__
                             : list LetrecNode) : (list LetrecNode * list LetrecNode)%type
           := match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
              | _, _, loop_nodes, acc, nil => pair loop_nodes acc
              | approx_lb, loop_sc, loop_nodes, acc, cons node nodes =>
                  let sc := nd_score (Digraph.node_payload node) in
                  if andb approx_lb (rank sc GHC.Base.== rank loop_sc) : bool
                  then chooseLoopBreaker approx_lb loop_sc (cons node loop_nodes) acc nodes else
                  if betterLB sc loop_sc : bool
                  then chooseLoopBreaker approx_lb sc (cons node nil) (Coq.Init.Datatypes.app
                                                                       loop_nodes acc) nodes else
                  chooseLoopBreaker approx_lb loop_sc loop_nodes (cons node acc) nodes
              end.

Definition noImpRuleEdges : ImpRuleEdges :=
  Core.emptyVarEnv.

Axiom occAnalRecRhs : OccEnv ->
                      list Core.CoreBndr ->
                      Core.CoreExpr -> (UsageDetails * list Core.CoreBndr * Core.CoreExpr)%type.

Definition udFreeVars : Core.VarSet -> UsageDetails -> Core.VarSet :=
  fun bndrs ud => UniqSet.restrictUniqSetToUFM bndrs (ud_env ud).

Definition makeNode
   : OccEnv ->
     ImpRuleEdges -> Core.VarSet -> (Core.Var * Core.CoreExpr)%type -> LetrecNode :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | env, imp_rule_edges, bndr_set, pair bndr rhs =>
        let mb_unf_uds := occAnalUnfolding env BasicTypes.Recursive bndr in
        let is_active := occ_rule_act env : BasicTypes.Activation -> bool in
        let 'pair bndrs body := Core.collectBinders rhs in
        let 'pair (pair rhs_usage1 bndrs') body' := occAnalRecRhs env bndrs body in
        let rhs' := Core.mkLams bndrs' body' in
        let inl_fvs :=
          match mb_unf_uds with
          | None => udFreeVars bndr_set rhs_usage1
          | Some unf_uds => udFreeVars bndr_set unf_uds
          end in
        let rules_w_uds : list (Core.CoreRule * UsageDetails * UsageDetails)%type :=
          occAnalRules env (Some (Coq.Lists.List.length bndrs)) BasicTypes.Recursive
          bndr in
        let rules_w_rhs_fvs : list (BasicTypes.Activation * Core.VarSet)%type :=
          Data.Maybe.maybe GHC.Base.id (fun ids =>
                                          (fun arg_14__ => cons (pair BasicTypes.AlwaysActive ids) arg_14__))
          (Core.lookupVarEnv imp_rule_edges bndr) (let cont_16__ arg_17__ :=
                                                     let 'pair (pair rule _) rhs_uds := arg_17__ in
                                                     cons (pair (Core.ru_act rule) (udFreeVars bndr_set rhs_uds)) nil in
                                                   Coq.Lists.List.flat_map cont_16__ rules_w_uds) in
        let active_rule_fvs :=
          Core.unionVarSets (let cont_19__ arg_20__ :=
                               let 'pair a fvs := arg_20__ in
                               if is_active a : bool then cons fvs nil else
                               nil in
                             Coq.Lists.List.flat_map cont_19__ rules_w_rhs_fvs) in
        let all_rule_uds :=
          combineUsageDetailsList (Data.Foldable.concatMap (fun '(pair (pair _ l) r) =>
                                                              cons l (cons r nil)) rules_w_uds) in
        let rhs_usage2 := rhs_usage1 +++ all_rule_uds in
        let rhs_usage3 :=
          match mb_unf_uds with
          | Some unf_uds => rhs_usage2 +++ unf_uds
          | None => rhs_usage2
          end in
        let node_fvs := udFreeVars bndr_set rhs_usage3 in
        let details :=
          ND bndr rhs' bndrs' rhs_usage3 inl_fvs (Core.minusVarSet node_fvs inl_fvs)
             active_rule_fvs (Panic.panicStr (GHC.Base.hs_string__ "makeNodeDetails")
              (Panic.someSDoc)) in
        Digraph.DigraphNode details (Core.varUnique bndr) (UniqSet.nonDetKeysUniqSet
                                                           node_fvs)
    end.

Definition extendFvs
   : UniqFM.UniqFM Core.VarSet -> Core.VarSet -> (Core.VarSet * bool)%type :=
  fun env s =>
    let extras : Core.VarSet :=
      UniqFM.nonDetFoldUFM Core.unionVarSet Core.emptyVarSet (UniqFM.intersectUFM_C
                                                              (fun arg_0__ arg_1__ =>
                                                                 match arg_0__, arg_1__ with
                                                                 | x, _ => x
                                                                 end) env (UniqSet.getUniqSet s)) in
    if UniqFM.isNullUFM env : bool then pair s true else
    pair (Core.unionVarSet s extras) (Core.subVarSet extras s).

Definition extendFvs_
   : UniqFM.UniqFM Core.VarSet -> Core.VarSet -> Core.VarSet :=
  fun env s => Data.Tuple.fst (extendFvs env s).

Axiom cheapExprSize : Core.CoreExpr -> nat.

Definition nodeScore
   : Core.Id -> Core.Id -> Core.CoreExpr -> Core.VarSet -> NodeScore :=
  fun old_bndr new_bndr bind_rhs lb_deps =>
    let fix is_con_app arg_0__
              := match arg_0__ with
                 | Core.Mk_Var v => Id.isConLikeId v
                 | Core.App f _ => is_con_app f
                 | Core.Lam _ e => is_con_app e
                 | _ => false
                 end in
    let id_unfolding := Id.realIdUnfolding old_bndr in
    let can_unfold := Core.canUnfold id_unfolding in
    let rhs := bind_rhs in
    let rhs_size := cheapExprSize rhs in
    let is_lb := BasicTypes.isStrongLoopBreaker (Id.idOccInfo old_bndr) in
    let mk_score : nat -> NodeScore :=
      fun rank => pair (pair rank rhs_size) is_lb in
    if negb (Core.isId old_bndr) : bool then pair (pair #100 #0) false else
    if Core.elemVarSet old_bndr lb_deps : bool then pair (pair #0 #0) true else
    if CoreUtils.exprIsTrivial rhs : bool then mk_score #10 else
    if is_con_app rhs : bool then mk_score #5 else
    if andb (Core.isStableUnfolding id_unfolding) can_unfold : bool
    then mk_score #3 else
    if BasicTypes.isOneOcc (Id.idOccInfo new_bndr) : bool then mk_score #2 else
    if can_unfold : bool then mk_score #1 else
    pair (pair #0 #0) is_lb.

Definition delDetailsList : UsageDetails -> list Core.Id -> UsageDetails :=
  fun ud bndrs =>
    alterUsageDetails ud (fun arg_0__ => Core.delVarEnvList arg_0__ bndrs).

Definition tagRecBinders
   : BasicTypes.TopLevelFlag ->
     UsageDetails ->
     list (Core.CoreBndr * UsageDetails * list Core.CoreBndr)%type ->
     (UsageDetails * list IdWithOccInfo)%type :=
  fun lvl body_uds triples =>
    let 'pair (pair bndrs rhs_udss) _ := GHC.List.unzip3 triples in
    let unadj_uds := body_uds +++ combineUsageDetailsList rhs_udss in
    let will_be_joins := decideJoinPointHood lvl unadj_uds bndrs in
    let adjust :=
      fun '(pair (pair bndr rhs_uds) rhs_bndrs) =>
        let mb_join_arity :=
          let j_4__ :=
            if andb Util.debugIsOn (negb (negb will_be_joins)) : bool
            then (Panic.assertPanic (GHC.Base.hs_string__
                                     "ghc/compiler/simplCore/OccurAnal.hs") #2684)
            else None in
          if will_be_joins : bool
          then let occ := lookupDetails unadj_uds bndr in
               match BasicTypes.tailCallInfo occ with
               | BasicTypes.AlwaysTailCalled arity => Some arity
               | _ => j_4__
               end else
          j_4__ in
        adjustRhsUsage mb_join_arity BasicTypes.Recursive rhs_bndrs rhs_uds in
    let rhs_udss' := GHC.Base.map adjust triples in
    let adj_uds := body_uds +++ combineUsageDetailsList rhs_udss' in
    let bndrs' :=
      Coq.Lists.List.flat_map (fun bndr =>
                                 cons (setBinderOcc (lookupDetails adj_uds bndr) bndr) nil) bndrs in
    let usage' := delDetailsList adj_uds bndrs in pair usage' bndrs'.

Axiom transClosureFV : UniqFM.UniqFM Core.VarSet -> UniqFM.UniqFM Core.VarSet.

Definition mkLoopBreakerNodes
   : BasicTypes.TopLevelFlag ->
     Core.VarSet ->
     UsageDetails -> list Details -> (UsageDetails * list LetrecNode)%type :=
  fun lvl bndr_set body_uds details_s =>
    let init_rule_fvs :=
      let cont_0__ arg_1__ :=
        let 'ND b _ _ _ _ _ rule_fvs _ := arg_1__ in
        let trimmed_rule_fvs := Core.intersectVarSet rule_fvs bndr_set in
        if negb (Core.isEmptyVarSet trimmed_rule_fvs) : bool
        then cons (pair b trimmed_rule_fvs) nil else
        nil in
      Coq.Lists.List.flat_map cont_0__ details_s in
    let rule_fv_env : Core.IdEnv Core.IdSet :=
      transClosureFV (Core.mkVarEnv init_rule_fvs) in
    let mk_lb_node :=
      fun arg_5__ arg_6__ =>
        match arg_5__, arg_6__ with
        | (ND bndr rhs _ _ inl_fvs _ _ _ as nd), bndr' =>
            let lb_deps := extendFvs_ rule_fv_env inl_fvs in
            let score := nodeScore bndr bndr' rhs lb_deps in
            let nd' :=
              let 'ND nd_bndr_9__ nd_rhs_10__ nd_rhs_bndrs_11__ nd_uds_12__ nd_inl_13__
                 nd_weak_14__ nd_active_rule_fvs_15__ nd_score_16__ := nd in
              ND bndr' nd_rhs_10__ nd_rhs_bndrs_11__ nd_uds_12__ nd_inl_13__ nd_weak_14__
                 nd_active_rule_fvs_15__ score in
            Digraph.DigraphNode nd' (Core.varUnique bndr) (UniqSet.nonDetKeysUniqSet
                                                           lb_deps)
        end in
    let 'pair final_uds bndrs' := tagRecBinders lvl body_uds
                                    (Coq.Lists.List.flat_map (fun nd =>
                                                                cons (pair (pair (nd_bndr nd) (nd_uds nd)) (nd_rhs_bndrs
                                                                            nd)) nil) details_s) in
    pair final_uds (GHC.List.zipWith mk_lb_node details_s bndrs').

Definition maxExprSize : nat :=
  #20.

Definition occAnalRhs
   : OccEnv ->
     BasicTypes.RecFlag ->
     Core.Id ->
     list Core.CoreBndr ->
     Core.CoreExpr -> (UsageDetails * list Core.CoreBndr * Core.CoreExpr)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | env, BasicTypes.Recursive, _, bndrs, body => occAnalRecRhs env bndrs body
    | env, BasicTypes.NonRecursive, id, bndrs, body =>
        occAnalNonRecRhs env id bndrs body
    end.

Axiom occAnalArgs : OccEnv ->
                    list Core.CoreExpr -> list OneShots -> (UsageDetails * list Core.CoreExpr)%type.

Definition addAppCtxt : OccEnv -> list (Core.Arg Core.CoreBndr) -> OccEnv :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_OccEnv _ ctxt _ _ _ as env), args =>
        let 'Mk_OccEnv occ_encl_2__ occ_one_shots_3__ occ_gbl_scrut_4__ occ_rule_act_5__
           occ_binder_swap_6__ := env in
        Mk_OccEnv occ_encl_2__ (Coq.Init.Datatypes.app (Coq.Lists.List.repeat
                                                        BasicTypes.OneShotLam (Core.valArgCount args)) ctxt)
                  occ_gbl_scrut_4__ occ_rule_act_5__ occ_binder_swap_6__
    end.

Definition isRhsEnv : OccEnv -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Mk_OccEnv OccRhs _ _ _ _ => true
    | Mk_OccEnv OccVanilla _ _ _ _ => false
    end.

Definition mkOneOcc
   : OccEnv ->
     Core.Id -> BasicTypes.InterestingCxt -> BasicTypes.JoinArity -> UsageDetails :=
  fun env id int_cxt arity =>
    let singleton :=
      fun info =>
        let 'UD ud_env_0__ ud_z_many_1__ ud_z_in_lam_2__ ud_z_no_tail_3__ :=
          emptyDetails in
        UD (Core.unitVarEnv id info) ud_z_many_1__ ud_z_in_lam_2__ ud_z_no_tail_3__ in
    if Core.isLocalId id : bool
    then singleton (BasicTypes.OneOcc false true int_cxt
                                      (BasicTypes.AlwaysTailCalled arity)) else
    if Core.elemVarSet id (occ_gbl_scrut env) : bool
    then singleton BasicTypes.noOccInfo else
    emptyDetails.

Definition occAnalApp
   : OccEnv ->
     (Core.Expr Core.CoreBndr * list (Core.Arg Core.CoreBndr) *
      list (Core.Tickish Core.Id))%type ->
     (UsageDetails * Core.Expr Core.CoreBndr)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | env, pair (pair (Core.Mk_Var fun_) args) ticks =>
        let n_args := Coq.Lists.List.length args in
        let n_val_args := Core.valArgCount args in
        let fun_uds := mkOneOcc env fun_ (n_val_args GHC.Base.> #0) n_args in
        let is_exp := CoreUtils.isExpandableApp fun_ n_val_args in
        let guaranteed_val_args :=
          n_val_args GHC.Num.+
          Coq.Lists.List.length (GHC.List.takeWhile BasicTypes.isOneShotInfo
                                 (occ_one_shots env)) in
        let one_shots := Core.argsOneShots (Id.idStrictness fun_) guaranteed_val_args in
        let 'pair args_uds args' := occAnalArgs env args one_shots in
        let final_args_uds :=
          if andb (isRhsEnv env) is_exp : bool
          then markAllNonTailCalled (markAllInsideLam args_uds) else
          markAllNonTailCalled args_uds in
        let uds := fun_uds +++ final_args_uds in
        if Data.Foldable.null ticks : bool
        then pair uds (Core.mkApps (Core.Mk_Var fun_) args') else
        pair uds (Core.mkApps (Core.Mk_Var fun_) args')
    | _, _ =>
        match arg_0__, arg_1__ with
        | env, pair (pair fun_ args) ticks =>
            let 'pair args_uds args' := occAnalArgs env args nil in
            let 'pair fun_uds fun' := occAnal (addAppCtxt env args) fun_ in
            pair (markAllNonTailCalled (fun_uds +++ args_uds)) (Core.mkApps fun' args')
        end
    end.

Definition markAllMany : UsageDetails -> UsageDetails :=
  fun ud =>
    let 'UD ud_env_0__ ud_z_many_1__ ud_z_in_lam_2__ ud_z_no_tail_3__ := ud in
    UD ud_env_0__ (ud_env ud) ud_z_in_lam_2__ ud_z_no_tail_3__.

Definition zapDetails : UsageDetails -> UsageDetails :=
  markAllMany GHC.Base.∘ markAllNonTailCalled.

Definition zapDetailsIf : bool -> UsageDetails -> UsageDetails :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | true, uds => zapDetails uds
    | false, uds => uds
    end.

Definition tagLamBinders
   : UsageDetails -> list Core.Id -> (UsageDetails * list IdWithOccInfo)%type :=
  fun usage binders =>
    let tag_lam :=
      fun usage bndr =>
        let usage1 := delDetails usage bndr in
        let usage2 :=
          if Core.isId bndr : bool
          then addManyOccsSet usage1 (CoreFVs.idUnfoldingVars bndr) else
          usage1 in
        let occ := lookupDetails usage bndr in
        let bndr' := setBinderOcc (markNonTailCalled occ) bndr in pair usage2 bndr' in
    let 'pair usage' bndrs' := Data.Traversable.mapAccumR tag_lam usage binders in
    GHC.Prim.seq usage' (pair usage' bndrs').

Definition wrapAltRHS
   : OccEnv ->
     option (Core.Id * Core.CoreExpr)%type ->
     UsageDetails ->
     list Core.Var -> Core.CoreExpr -> (UsageDetails * Core.CoreExpr)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ arg_4__ =>
    let j_6__ :=
      match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
      | _, _, alt_usg, _, alt_rhs => pair alt_usg alt_rhs
      end in
    match arg_0__, arg_1__, arg_2__, arg_3__, arg_4__ with
    | env, Some (pair scrut_var let_rhs), alt_usg, bndrs, alt_rhs =>
        match tagLamBinders alt_usg (cons scrut_var nil) with
        | pair alt_usg' (cons tagged_scrut_var nil) =>
            let 'pair let_rhs_usg let_rhs' := occAnal env let_rhs in
            let captured :=
              Data.Foldable.any (fun arg_9__ => usedIn arg_9__ let_rhs_usg) bndrs in
            if andb (occ_binder_swap env) (andb (usedIn scrut_var alt_usg) (negb
                                                 captured)) : bool
            then pair (alt_usg' +++ let_rhs_usg) (Core.Let (Core.NonRec tagged_scrut_var
                                                            let_rhs') alt_rhs) else
            j_6__
        | _ => GHC.Err.patternFailure
        end
    | _, _, _, _, _ => j_6__
    end.

Definition occAnalAlt
   : (OccEnv * option (Core.Id * Core.CoreExpr)%type)%type ->
     Core.CoreAlt -> (UsageDetails * Core.Alt IdWithOccInfo)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair env scrut_bind, pair (pair con bndrs) rhs =>
        let 'pair rhs_usage1 rhs1 := occAnal env rhs in
        let 'pair alt_usg tagged_bndrs := tagLamBinders rhs_usage1 bndrs in
        let 'pair alt_usg' rhs2 := wrapAltRHS env scrut_bind alt_usg tagged_bndrs
                                     rhs1 in
        pair alt_usg' (pair (pair con tagged_bndrs) rhs2)
    end.

Definition vanillaCtxt : OccEnv -> OccEnv :=
  fun '(Mk_OccEnv occ_encl_0__ occ_one_shots_1__ occ_gbl_scrut_2__
  occ_rule_act_3__ occ_binder_swap_4__) =>
    Mk_OccEnv OccVanilla nil occ_gbl_scrut_2__ occ_rule_act_3__ occ_binder_swap_4__.

Definition argCtxt : OccEnv -> list OneShots -> (OccEnv * list OneShots)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | env, nil =>
        pair (let 'Mk_OccEnv occ_encl_2__ occ_one_shots_3__ occ_gbl_scrut_4__
                 occ_rule_act_5__ occ_binder_swap_6__ := env in
              Mk_OccEnv OccVanilla nil occ_gbl_scrut_4__ occ_rule_act_5__ occ_binder_swap_6__)
             nil
    | env, cons one_shots one_shots_s =>
        pair (let 'Mk_OccEnv occ_encl_10__ occ_one_shots_11__ occ_gbl_scrut_12__
                 occ_rule_act_13__ occ_binder_swap_14__ := env in
              Mk_OccEnv OccVanilla one_shots occ_gbl_scrut_12__ occ_rule_act_13__
                        occ_binder_swap_14__) one_shots_s
    end.

Definition oneShotGroup
   : OccEnv -> list Core.CoreBndr -> (OccEnv * list Core.CoreBndr)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | (Mk_OccEnv _ ctxt _ _ _ as env), bndrs =>
        let fix go arg_2__ arg_3__ arg_4__
                  := match arg_2__, arg_3__, arg_4__ with
                     | ctxt, nil, rev_bndrs =>
                         pair (let 'Mk_OccEnv occ_encl_5__ occ_one_shots_6__ occ_gbl_scrut_7__
                                  occ_rule_act_8__ occ_binder_swap_9__ := env in
                               Mk_OccEnv OccVanilla ctxt occ_gbl_scrut_7__ occ_rule_act_8__
                                         occ_binder_swap_9__) (GHC.List.reverse rev_bndrs)
                     | nil, bndrs, rev_bndrs =>
                         pair (let 'Mk_OccEnv occ_encl_13__ occ_one_shots_14__ occ_gbl_scrut_15__
                                  occ_rule_act_16__ occ_binder_swap_17__ := env in
                               Mk_OccEnv OccVanilla nil occ_gbl_scrut_15__ occ_rule_act_16__
                                         occ_binder_swap_17__) (Coq.Init.Datatypes.app (GHC.List.reverse rev_bndrs)
                                                                                       bndrs)
                     | (cons one_shot ctxt' as ctxt), cons bndr bndrs, rev_bndrs =>
                         let bndr' := Id.updOneShotInfo bndr one_shot in
                         if Core.isId bndr : bool then go ctxt' bndrs (cons bndr' rev_bndrs) else
                         go ctxt bndrs (cons bndr rev_bndrs)
                     end in
        go ctxt bndrs nil
    end.

Definition mkAltEnv
   : OccEnv ->
     Core.CoreExpr ->
     Core.Id -> (OccEnv * option (Core.Id * Core.CoreExpr)%type)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | (Mk_OccEnv _ _ pe _ _ as env), scrut, case_bndr =>
        let localise :=
          fun scrut_var =>
            Id.mkLocalIdOrCoVar (Name.localiseName (Id.idName scrut_var)) (Id.idType
                                                                           scrut_var) in
        let case_bndr' := Core.Mk_Var (Id.zapIdOccInfo case_bndr) in
        let add_scrut :=
          fun v rhs =>
            pair (let 'Mk_OccEnv occ_encl_5__ occ_one_shots_6__ occ_gbl_scrut_7__
                     occ_rule_act_8__ occ_binder_swap_9__ := env in
                  Mk_OccEnv OccVanilla occ_one_shots_6__ (Core.extendVarSet pe v) occ_rule_act_8__
                            occ_binder_swap_9__) (Some (pair (localise v) rhs)) in
        match CoreUtils.stripTicksTopE (GHC.Base.const true) scrut with
        | Core.Mk_Var v => add_scrut v case_bndr'
        | Core.Cast (Core.Mk_Var v) co =>
            add_scrut v (Core.Cast case_bndr' (Core.mkSymCo co))
        | _ =>
            pair (let 'Mk_OccEnv occ_encl_16__ occ_one_shots_17__ occ_gbl_scrut_18__
                     occ_rule_act_19__ occ_binder_swap_20__ := env in
                  Mk_OccEnv OccVanilla occ_one_shots_17__ occ_gbl_scrut_18__ occ_rule_act_19__
                            occ_binder_swap_20__) None
        end
    end.

Definition orOccInfo
   : BasicTypes.OccInfo -> BasicTypes.OccInfo -> BasicTypes.OccInfo :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | BasicTypes.OneOcc in_lam1 _ int_cxt1 tail1
    , BasicTypes.OneOcc in_lam2 _ int_cxt2 tail2 =>
        BasicTypes.OneOcc (orb in_lam1 in_lam2) false (andb int_cxt1 int_cxt2)
                          (andTailCallInfo tail1 tail2)
    | a1, a2 =>
        if andb Util.debugIsOn (negb (negb (orb (BasicTypes.isDeadOcc a1)
                                                (BasicTypes.isDeadOcc a2)))) : bool
        then (Panic.assertPanic (GHC.Base.hs_string__
                                 "ghc/compiler/simplCore/OccurAnal.hs") #2842)
        else BasicTypes.ManyOccs (andTailCallInfo (BasicTypes.tailCallInfo a1)
                                                  (BasicTypes.tailCallInfo a2))
    end.

Definition combineAltsUsageDetails
   : UsageDetails -> UsageDetails -> UsageDetails :=
  combineUsageDetailsWith orOccInfo.

Definition flattenUsageDetails : UsageDetails -> UsageDetails :=
  fun ud =>
    alterZappedSets (let 'UD ud_env_0__ ud_z_many_1__ ud_z_in_lam_2__
                        ud_z_no_tail_3__ := ud in
                     UD (UniqFM.mapUFM_Directly (doZappingByUnique ud) (ud_env ud)) ud_z_many_1__
                        ud_z_in_lam_2__ ud_z_no_tail_3__) (GHC.Base.const Core.emptyVarEnv).

Module Notations.
Notation "'_OccurAnal.+++_'" := (op_zpzpzp__).
Infix "OccurAnal.+++" := (_+++_) (at level 99).
End Notations.

(* External variables:
     None Some andb bool cons false list nat negb nil op_zt__ option orb pair true
     BasicTypes.Activation BasicTypes.AlwaysActive BasicTypes.AlwaysTailCalled
     BasicTypes.IAmALoopBreaker BasicTypes.IAmDead BasicTypes.InterestingCxt
     BasicTypes.JoinArity BasicTypes.ManyOccs BasicTypes.NoTailCallInfo
     BasicTypes.NonRecursive BasicTypes.NotTopLevel BasicTypes.OccInfo
     BasicTypes.OneOcc BasicTypes.OneShotInfo BasicTypes.OneShotLam
     BasicTypes.RecFlag BasicTypes.Recursive BasicTypes.TailCallInfo
     BasicTypes.TopLevel BasicTypes.TopLevelFlag BasicTypes.isAlwaysActive
     BasicTypes.isAlwaysTailCalled BasicTypes.isDeadOcc BasicTypes.isManyOccs
     BasicTypes.isOneOcc BasicTypes.isOneShotInfo BasicTypes.isRec
     BasicTypes.isStrongLoopBreaker BasicTypes.noOccInfo BasicTypes.occ_tail
     BasicTypes.tailCallInfo Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     Coq.Lists.List.length Coq.Lists.List.repeat Coq.Lists.List.skipn Core.Alt
     Core.App Core.Arg Core.BuiltinRule Core.Cast Core.CoreAlt Core.CoreBind
     Core.CoreBndr Core.CoreExpr Core.CoreProgram Core.CoreRule Core.CoreVect
     Core.Expr Core.Id Core.IdEnv Core.IdSet Core.Lam Core.Let Core.Mk_Var
     Core.NonRec Core.Rule Core.Tickish Core.Var Core.VarSet Core.argOneShots
     Core.argsOneShots Core.canUnfold Core.collectBinders Core.delVarEnv
     Core.delVarEnvList Core.elemVarEnv Core.elemVarEnvByKey Core.elemVarSet
     Core.emptyVarEnv Core.emptyVarSet Core.extendVarEnv_C Core.extendVarSet
     Core.intersectVarSet Core.isEmptyVarEnv Core.isEmptyVarSet Core.isExportedId
     Core.isId Core.isLocalId Core.isStableUnfolding Core.isTyVar
     Core.isValidJoinPointType Core.lookupVarEnv Core.minusVarSet Core.mkApps
     Core.mkLams Core.mkSymCo Core.mkVarEnv Core.plusVarEnv Core.plusVarEnv_C
     Core.ru_act Core.subVarSet Core.unionVarSet Core.unionVarSets Core.unitVarEnv
     Core.valArgCount Core.varUnique CoreFVs.idUnfoldingVars CoreUtils.exprIsTrivial
     CoreUtils.isExpandableApp CoreUtils.stripTicksTopE Data.Foldable.all
     Data.Foldable.any Data.Foldable.concatMap Data.Foldable.foldl Data.Foldable.null
     Data.Maybe.maybe Data.Traversable.mapAccumR Data.Tuple.fst Data.Tuple.snd
     Datatypes.id Digraph.DigraphNode Digraph.Node Digraph.node_payload
     GHC.Base.const GHC.Base.id GHC.Base.map GHC.Base.mappend GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zl__ GHC.Err.Build_Default
     GHC.Err.Default GHC.Err.default GHC.Err.error GHC.Err.head
     GHC.Err.patternFailure GHC.List.reverse GHC.List.takeWhile GHC.List.unzip3
     GHC.List.zipWith GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__
     GHC.Prim.seq Id.idCoreRules Id.idDemandInfo Id.idInlineActivation Id.idName
     Id.idOccInfo Id.idStrictness Id.idType Id.idUnfolding Id.isConLikeId Id.isJoinId
     Id.isJoinId_maybe Id.isOneShotBndr Id.mkLocalIdOrCoVar Id.realIdUnfolding
     Id.setIdOccInfo Id.setOneShotLambda Id.updOneShotInfo Id.zapIdOccInfo
     Module.Module Name.localiseName Panic.assertPanic Panic.panicStr Panic.someSDoc
     Panic.warnPprTrace UniqFM.UniqFM UniqFM.intersectUFM_C UniqFM.isNullUFM
     UniqFM.mapUFM_Directly UniqFM.nonDetFoldUFM UniqSet.getUniqSet
     UniqSet.nonDetFoldUniqSet UniqSet.nonDetKeysUniqSet UniqSet.restrictUniqSetToUFM
     Unique.Unique Util.debugIsOn Util.lengthIs
*)
