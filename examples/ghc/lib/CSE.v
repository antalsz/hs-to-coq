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
Require CoreFVs.
Require CoreSubst.
Require CoreUtils.
Require Data.Foldable.
Require Data.Traversable.
Require Data.Tuple.
Require Datatypes.
Require Id.
Require TrieMap.
Require Util.

(* Converted type declarations: *)

Inductive CSEnv : Type
  := CS
   : CoreSubst.Subst ->
     TrieMap.CoreMap Core.OutExpr -> TrieMap.CoreMap Core.OutExpr -> CSEnv.

Definition cs_map (arg_0__ : CSEnv) :=
  let 'CS _ cs_map _ := arg_0__ in
  cs_map.

Definition cs_rec_map (arg_0__ : CSEnv) :=
  let 'CS _ _ cs_rec_map := arg_0__ in
  cs_rec_map.

Definition cs_subst (arg_0__ : CSEnv) :=
  let 'CS cs_subst _ _ := arg_0__ in
  cs_subst.
(* Converted value declarations: *)

Definition addBinder : CSEnv -> Core.Var -> (CSEnv * Core.Var)%type :=
  fun cse v =>
    let 'pair sub' v' := CoreSubst.substBndr (cs_subst cse) v in
    pair (let 'CS cs_subst_1__ cs_map_2__ cs_rec_map_3__ := cse in
          CS sub' cs_map_2__ cs_rec_map_3__) v'.

Definition addBinders
   : CSEnv -> list Core.Var -> (CSEnv * list Core.Var)%type :=
  fun cse vs =>
    let 'pair sub' vs' := CoreSubst.substBndrs (cs_subst cse) vs in
    pair (let 'CS cs_subst_1__ cs_map_2__ cs_rec_map_3__ := cse in
          CS sub' cs_map_2__ cs_rec_map_3__) vs'.

Definition addRecBinders
   : CSEnv -> list Core.Var -> (CSEnv * list Core.Var)%type :=
  fun cse vs =>
    let 'pair sub' vs' := CoreSubst.substRecBndrs (cs_subst cse) vs in
    pair (let 'CS cs_subst_1__ cs_map_2__ cs_rec_map_3__ := cse in
          CS sub' cs_map_2__ cs_rec_map_3__) vs'.

Definition csEnvSubst : CSEnv -> CoreSubst.Subst :=
  cs_subst.

Definition combineAlts : CSEnv -> list Core.InAlt -> list Core.InAlt :=
  fun arg_0__ arg_1__ =>
    let j_2__ := match arg_0__, arg_1__ with | _, alts => alts end in
    match arg_0__, arg_1__ with
    | env, cons (pair (pair _ bndrs1) rhs1) rest_alts =>
        let in_scope := CoreSubst.substInScope (csEnvSubst env) in
        let ok :=
          fun bndr =>
            orb (Id.isDeadBinder bndr) (negb (Core.elemInScopeSet bndr in_scope)) in
        let identical :=
          fun '(pair (pair _con bndrs) rhs) =>
            andb (Data.Foldable.all ok bndrs) (CoreUtils.eqExpr in_scope rhs1 rhs) in
        let filtered_alts := Util.filterOut identical rest_alts in
        if Data.Foldable.all Id.isDeadBinder bndrs1 : bool
        then cons (pair (pair Core.DEFAULT nil) rhs1) filtered_alts else
        j_2__
    | _, _ => j_2__
    end.

Axiom cseBind : BasicTypes.TopLevelFlag ->
                CSEnv -> Core.CoreBind -> (CSEnv * Core.CoreBind)%type.

Axiom cseCase : CSEnv ->
                Core.InExpr -> Core.InId -> Core.InType -> list Core.InAlt -> Core.OutExpr.

Axiom cseExpr : CSEnv -> Core.InExpr -> Core.OutExpr.

Axiom cse_bind : BasicTypes.TopLevelFlag ->
                 CSEnv ->
                 (Core.InId * Core.InExpr)%type ->
                 Core.OutId -> (CSEnv * (Core.OutId * Core.OutExpr)%type)%type.

Definition emptyCSEnv : CSEnv :=
  CS CoreSubst.emptySubst TrieMap.emptyCoreMap TrieMap.emptyCoreMap.

Definition cseOneExpr : Core.InExpr -> Core.OutExpr :=
  fun e =>
    let env :=
      let 'CS cs_subst_0__ cs_map_1__ cs_rec_map_2__ := emptyCSEnv in
      CS (CoreSubst.mkEmptySubst (Core.mkInScopeSet (CoreFVs.exprFreeVars e)))
         cs_map_1__ cs_rec_map_2__ in
    cseExpr env e.

Definition cseProgram : Core.CoreProgram -> Core.CoreProgram :=
  fun binds =>
    Data.Tuple.snd (Data.Traversable.mapAccumL (cseBind BasicTypes.TopLevel)
                    emptyCSEnv binds).

Definition extendCSEnv : CSEnv -> Core.OutExpr -> Core.OutExpr -> CSEnv :=
  fun cse expr triv_expr =>
    let sexpr := CoreUtils.stripTicksE Core.tickishFloatable expr in
    let 'CS cs_subst_1__ cs_map_2__ cs_rec_map_3__ := cse in
    CS cs_subst_1__ (TrieMap.extendCoreMap (cs_map cse) sexpr triv_expr)
       cs_rec_map_3__.

Definition extendCSRecEnv
   : CSEnv -> Core.OutId -> Core.OutExpr -> Core.OutExpr -> CSEnv :=
  fun cse bndr expr triv_expr =>
    let 'CS cs_subst_0__ cs_map_1__ cs_rec_map_2__ := cse in
    CS cs_subst_0__ cs_map_1__ (TrieMap.extendCoreMap (cs_rec_map cse) (Core.Lam
                                                                        bndr expr) triv_expr).

Definition extendCSSubst : CSEnv -> Core.Var -> Core.CoreExpr -> CSEnv :=
  fun cse x rhs =>
    let 'CS cs_subst_0__ cs_map_1__ cs_rec_map_2__ := cse in
    CS (CoreSubst.extendSubst (cs_subst cse) x rhs) cs_map_1__ cs_rec_map_2__.

Definition lookupCSEnv : CSEnv -> Core.OutExpr -> option Core.OutExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CS _ csmap _, expr => TrieMap.lookupCoreMap csmap expr
    end.

Definition lookupCSRecEnv
   : CSEnv -> Core.OutId -> Core.OutExpr -> option Core.OutExpr :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | CS _ _ csmap, bndr, expr => TrieMap.lookupCoreMap csmap (Core.Lam bndr expr)
    end.

Definition lookupSubst : CSEnv -> Core.Var -> Core.OutExpr :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | CS sub _ _, x =>
        CoreSubst.lookupIdSubst (Datatypes.id (GHC.Base.hs_string__ "CSE.lookupSubst"))
        sub x
    end.

Definition noCSE : Core.InId -> bool :=
  fun id =>
    orb (andb (negb (BasicTypes.isAlwaysActive (Id.idInlineActivation id))) (negb
               (BasicTypes.noUserInlineSpec (BasicTypes.inlinePragmaSpec (Id.idInlinePragma
                                                                          id))))) (orb (BasicTypes.isAnyInlinePragma
                                                                                        (Id.idInlinePragma id))
                                                                                       (Id.isJoinId id)).

Definition addBinding
   : CSEnv ->
     Core.InVar -> Core.OutId -> Core.OutExpr -> (CSEnv * Core.OutId)%type :=
  fun env in_id out_id rhs' =>
    let use_subst := match rhs' with | Core.Mk_Var _ => true | _ => false end in
    let zapped_id := Id.zapIdUsageInfo out_id in
    let id_expr' := Core.varToCoreExpr out_id in
    if negb (Core.isId in_id) : bool
    then pair (extendCSSubst env in_id rhs') out_id else
    if noCSE in_id : bool then pair env out_id else
    if use_subst : bool then pair (extendCSSubst env in_id rhs') out_id else
    pair (extendCSEnv env rhs' id_expr') zapped_id.

Axiom tryForCSE : CSEnv -> Core.InExpr -> Core.OutExpr.

(* External variables:
     andb bool cons false list negb nil op_zt__ option orb pair true
     BasicTypes.TopLevel BasicTypes.TopLevelFlag BasicTypes.inlinePragmaSpec
     BasicTypes.isAlwaysActive BasicTypes.isAnyInlinePragma
     BasicTypes.noUserInlineSpec Core.CoreBind Core.CoreExpr Core.CoreProgram
     Core.DEFAULT Core.InAlt Core.InExpr Core.InId Core.InType Core.InVar Core.Lam
     Core.Mk_Var Core.OutExpr Core.OutId Core.Var Core.elemInScopeSet Core.isId
     Core.mkInScopeSet Core.tickishFloatable Core.varToCoreExpr CoreFVs.exprFreeVars
     CoreSubst.Subst CoreSubst.emptySubst CoreSubst.extendSubst
     CoreSubst.lookupIdSubst CoreSubst.mkEmptySubst CoreSubst.substBndr
     CoreSubst.substBndrs CoreSubst.substInScope CoreSubst.substRecBndrs
     CoreUtils.eqExpr CoreUtils.stripTicksE Data.Foldable.all
     Data.Traversable.mapAccumL Data.Tuple.snd Datatypes.id Id.idInlineActivation
     Id.idInlinePragma Id.isDeadBinder Id.isJoinId Id.zapIdUsageInfo TrieMap.CoreMap
     TrieMap.emptyCoreMap TrieMap.extendCoreMap TrieMap.lookupCoreMap Util.filterOut
*)
