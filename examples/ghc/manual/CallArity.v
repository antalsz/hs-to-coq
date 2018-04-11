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
Require CoreArity.
Require CoreSyn.
Require CoreUtils.
Require Data.Foldable.
Require Data.Tuple.
Require Demand.
Require DynFlags.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require UnVarGraph.
Require Util.
Require Var.
Require VarEnv.
Require VarSet.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition CallArityRes :=
  (UnVarGraph.UnVarGraph * VarEnv.VarEnv BasicTypes.Arity)%type%type.
(* Midamble *)

Instance Default_CallArityRes : GHC.Err.Default CallArityRes.
Admitted.


Definition arrow_first {b}{c}{d} (f : (b -> c)) : (b * d)%type -> (c * d)%type :=
  fun p => match p with (x,y)=> (f x, y) end.
Definition arrow_second {b}{c}{d} (f : (b -> c)) : (d * b)%type -> (d * c)%type :=
  fun p => match p with (x,y)=> (x, f y) end.

(* ------------------------- mutual recursion hack -------------------- *)

(* ANTALZ: This looks like a good example of structural mutual recursion *) 
Parameter callArityBind
   : VarSet.VarSet ->
     CallArityRes ->
     VarSet.VarSet -> CoreSyn.CoreBind -> (CallArityRes * CoreSyn.CoreBind)%type.

(* Converted value declarations: *)

Definition addCrossCoCalls
   : UnVarGraph.UnVarSet -> UnVarGraph.UnVarSet -> CallArityRes -> CallArityRes :=
  fun set1 set2 =>
    arrow_first (fun arg_0__ =>
                   UnVarGraph.unionUnVarGraph (UnVarGraph.completeBipartiteGraph set1 set2)
                                              arg_0__).

Definition calledWith : CallArityRes -> Var.Var -> UnVarGraph.UnVarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair g _, v => UnVarGraph.neighbors g v
    end.

Definition domRes : CallArityRes -> UnVarGraph.UnVarSet :=
  fun '(pair _ ae) => UnVarGraph.varEnvDom ae.

Definition calledMultipleTimes : CallArityRes -> CallArityRes :=
  fun res =>
    arrow_first (GHC.Base.const (UnVarGraph.completeGraph (domRes res))) res.

Definition emptyArityRes : CallArityRes :=
  pair UnVarGraph.emptyUnVarGraph VarEnv.emptyVarEnv.

Definition isInteresting : Var.Var -> bool :=
  fun v => negb (Data.Foldable.null (CoreArity.typeArity (tt))).

Definition interestingBinds : CoreSyn.CoreBind -> list Var.Var :=
  GHC.List.filter isInteresting GHC.Base.∘ CoreSyn.bindersOf.

Definition addInterestingBinds
   : VarSet.VarSet -> CoreSyn.CoreBind -> VarSet.VarSet :=
  fun int bind =>
    VarSet.extendVarSetList (VarSet.delVarSetList int (CoreSyn.bindersOf bind))
                            (interestingBinds bind).

Definition boringBinds : CoreSyn.CoreBind -> VarSet.VarSet :=
  VarSet.mkVarSet GHC.Base.∘
  (GHC.List.filter (negb GHC.Base.∘ isInteresting) GHC.Base.∘ CoreSyn.bindersOf).

Definition callArityTopLvl
   : list Var.Var ->
     VarSet.VarSet ->
     list CoreSyn.CoreBind -> (CallArityRes * list CoreSyn.CoreBind)%type :=
  fix callArityTopLvl arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | exported, _, nil =>
               pair (calledMultipleTimes (pair UnVarGraph.emptyUnVarGraph (VarEnv.mkVarEnv
                                                (Coq.Lists.List.flat_map (fun v => cons (pair v #0) nil) exported))))
                    nil
           | exported, int1, cons b bs =>
               let int' := addInterestingBinds int1 b in
               let int2 := CoreSyn.bindersOf b in
               let exported' :=
                 Coq.Init.Datatypes.app (GHC.List.filter Var.isExportedId int2) exported in
               let 'pair ae1 bs' := callArityTopLvl exported' int' bs in
               let 'pair ae2 b' := callArityBind (boringBinds b) ae1 int1 b in
               pair ae2 (cons b' bs')
           end.

Definition callArityAnalProgram
   : DynFlags.DynFlags -> CoreSyn.CoreProgram -> CoreSyn.CoreProgram :=
  fun _dflags binds =>
    let 'pair _ binds' := callArityTopLvl nil VarSet.emptyVarSet binds in
    binds'.

Definition lookupCallArityRes
   : CallArityRes -> Var.Var -> (BasicTypes.Arity * bool)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair g ae, v =>
        match VarEnv.lookupVarEnv ae v with
        | Some a => pair a (negb (UnVarGraph.elemUnVarSet v (UnVarGraph.neighbors g v)))
        | None => pair #0 false
        end
    end.

Definition lubArityEnv
   : VarEnv.VarEnv BasicTypes.Arity ->
     VarEnv.VarEnv BasicTypes.Arity -> VarEnv.VarEnv BasicTypes.Arity :=
  VarEnv.plusVarEnv_C GHC.Base.min.

Definition lubRes : CallArityRes -> CallArityRes -> CallArityRes :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair g1 ae1, pair g2 ae2 =>
        pair (UnVarGraph.unionUnVarGraph g1 g2) (lubArityEnv ae1 ae2)
    end.

Definition lubRess : list CallArityRes -> CallArityRes :=
  Data.Foldable.foldl lubRes emptyArityRes.

Definition callArityRecEnv
   : bool -> list (Var.Var * CallArityRes)%type -> CallArityRes -> CallArityRes :=
  fun any_boring ae_rhss ae_body =>
    let ae_combined :=
      lubRes (lubRess (GHC.Base.map Data.Tuple.snd ae_rhss)) ae_body in
    let vars := GHC.Base.map Data.Tuple.fst ae_rhss in
    let cross_call :=
      fun '(pair v ae_rhs) =>
        let called_by_v := domRes ae_rhs in
        let is_thunk := Id.idCallArity v GHC.Base.== #0 in
        let ae_before_v :=
          if is_thunk : bool
          then lubRes (lubRess (GHC.Base.map Data.Tuple.snd (GHC.List.filter
                                                             ((fun arg_5__ => arg_5__ GHC.Base./= v) GHC.Base.∘
                                                              Data.Tuple.fst) ae_rhss))) ae_body else
          ae_combined in
        let called_with_v :=
          UnVarGraph.unionUnVarSets (GHC.Base.map (calledWith ae_before_v) vars) in
        UnVarGraph.completeBipartiteGraph called_by_v called_with_v in
    let cross_calls :=
      if any_boring : bool then UnVarGraph.completeGraph (domRes ae_combined) else
      if Util.lengthExceeds ae_rhss #25 : bool
      then UnVarGraph.completeGraph (domRes ae_combined) else
      UnVarGraph.unionUnVarGraphs (GHC.Base.map cross_call ae_rhss) in
    let ae_new :=
      arrow_first (fun arg_13__ => UnVarGraph.unionUnVarGraph cross_calls arg_13__)
      ae_combined in
    ae_new.

Definition both : CallArityRes -> CallArityRes -> CallArityRes :=
  fun r1 r2 => addCrossCoCalls (domRes r1) (domRes r2) (lubRes r1 r2).

Definition resDel : Var.Var -> CallArityRes -> CallArityRes :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, pair g ae => pair (UnVarGraph.delNode g v) (VarEnv.delVarEnv ae v)
    end.

Definition resDelList : list Var.Var -> CallArityRes -> CallArityRes :=
  fun vs ae => Data.Foldable.foldr resDel ae vs.

Definition trimArity : Var.Id -> BasicTypes.Arity -> BasicTypes.Arity :=
  fun v a =>
    let 'pair demands result_info := Demand.splitStrictSig (Demand.botSig) in
    let max_arity_by_strsig :=
      if Demand.isBotRes result_info : bool then Data.Foldable.length demands else
      a in
    let max_arity_by_type := Data.Foldable.length (CoreArity.typeArity (tt)) in
    Data.Foldable.foldr GHC.Base.min a (cons max_arity_by_type (cons
                                              max_arity_by_strsig nil)).

Definition unitArityRes : Var.Var -> BasicTypes.Arity -> CallArityRes :=
  fun v arity => pair UnVarGraph.emptyUnVarGraph (VarEnv.unitVarEnv v arity).

Definition callArityAnal
   : BasicTypes.Arity ->
     VarSet.VarSet -> CoreSyn.CoreExpr -> (CallArityRes * CoreSyn.CoreExpr)%type :=
  fix callArityAnal arg_0__ arg_1__ arg_2__
        := let j_26__ :=
             match arg_0__, arg_1__, arg_2__ with
             | arity, int, CoreSyn.Lam v e =>
                 let 'pair ae e' := callArityAnal (arity GHC.Num.- #1) (VarSet.delVarSet int v)
                                      e in
                 pair ae (CoreSyn.Lam v e')
             | arity, int, CoreSyn.App e (CoreSyn.Type_ t) =>
                 arrow_second (fun e => CoreSyn.App e (CoreSyn.Type_ t)) (callArityAnal arity int
                                                                                        e)
             | arity, int, CoreSyn.App e1 e2 =>
                 let 'pair ae2 e2' := callArityAnal #0 int e2 in
                 let ae2' :=
                   if CoreUtils.exprIsTrivial e2 : bool then calledMultipleTimes ae2 else
                   ae2 in
                 let 'pair ae1 e1' := callArityAnal (arity GHC.Num.+ #1) int e1 in
                 let final_ae := both ae1 ae2' in pair final_ae (CoreSyn.App e1' e2')
             | arity, int, CoreSyn.Case scrut bndr ty alts =>
                 let 'pair scrut_ae scrut' := callArityAnal #0 int scrut in
                 let go :=
                   fun '(pair (pair dc bndrs) e) =>
                     let 'pair ae e' := callArityAnal arity int e in
                     pair ae (pair (pair dc bndrs) e') in
                 let 'pair alt_aes alts' := GHC.List.unzip (GHC.Base.map go alts) in
                 let alt_ae := lubRess alt_aes in
                 let final_ae := both scrut_ae alt_ae in
                 pair final_ae (CoreSyn.Case scrut' bndr ty alts')
             | arity, int, CoreSyn.Let bind e =>
                 let int_body := addInterestingBinds int bind in
                 let 'pair ae_body e' := callArityAnal arity int_body e in
                 let 'pair final_ae bind' := callArityBind (boringBinds bind) ae_body int bind in
                 pair final_ae (CoreSyn.Let bind' e')
             | _, _, _ => GHC.Err.patternFailure
             end in
           let j_30__ :=
             match arg_0__, arg_1__, arg_2__ with
             | num_3__, int, CoreSyn.Lam v e =>
                 let 'pair ae e' := callArityAnal #0 (VarSet.delVarSet int v) e in
                 let ae' := calledMultipleTimes ae in
                 if num_3__ GHC.Base.== #0 : bool then pair ae' (CoreSyn.Lam v e') else
                 j_26__
             | _, _, _ => j_26__
             end in
           match arg_0__, arg_1__, arg_2__ with
           | _, _, (CoreSyn.Lit _ as e) => pair emptyArityRes e
           | _, _, (CoreSyn.Type_ _ as e) => pair emptyArityRes e
           | _, _, (CoreSyn.Coercion _ as e) => pair emptyArityRes e
           | arity, int, CoreSyn.Tick t e =>
               arrow_second (CoreSyn.Tick t) (callArityAnal arity int e)
           | arity, int, CoreSyn.Cast e co =>
               arrow_second (fun e => CoreSyn.Cast e co) (callArityAnal arity int e)
           | arity, int, (CoreSyn.Var v as e) =>
               if VarSet.elemVarSet v int : bool then pair (unitArityRes v arity) e else
               pair emptyArityRes e
           | arity, int, CoreSyn.Lam v e =>
               if negb (Var.isId v) : bool
               then arrow_second (CoreSyn.Lam v) (callArityAnal arity (VarSet.delVarSet int v)
                                                                e) else
               j_30__
           | _, _, _ => j_30__
           end.

Definition callArityRHS : CoreSyn.CoreExpr -> CoreSyn.CoreExpr :=
  Data.Tuple.snd GHC.Base.∘ callArityAnal #0 VarSet.emptyVarSet.

(* External variables:
     None Some arrow_first arrow_second bool callArityBind cons false list negb nil
     op_zt__ pair tt BasicTypes.Arity Coq.Init.Datatypes.app Coq.Lists.List.flat_map
     CoreArity.typeArity CoreSyn.App CoreSyn.Case CoreSyn.Cast CoreSyn.Coercion
     CoreSyn.CoreBind CoreSyn.CoreExpr CoreSyn.CoreProgram CoreSyn.Lam CoreSyn.Let
     CoreSyn.Lit CoreSyn.Tick CoreSyn.Type_ CoreSyn.Var CoreSyn.bindersOf
     CoreUtils.exprIsTrivial Data.Foldable.foldl Data.Foldable.foldr
     Data.Foldable.length Data.Foldable.null Data.Tuple.fst Data.Tuple.snd
     Demand.botSig Demand.isBotRes Demand.splitStrictSig DynFlags.DynFlags
     GHC.Base.const GHC.Base.map GHC.Base.min GHC.Base.op_z2218U__ GHC.Base.op_zeze__
     GHC.Base.op_zsze__ GHC.Err.patternFailure GHC.List.filter GHC.List.unzip
     GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__ Id.idCallArity
     UnVarGraph.UnVarGraph UnVarGraph.UnVarSet UnVarGraph.completeBipartiteGraph
     UnVarGraph.completeGraph UnVarGraph.delNode UnVarGraph.elemUnVarSet
     UnVarGraph.emptyUnVarGraph UnVarGraph.neighbors UnVarGraph.unionUnVarGraph
     UnVarGraph.unionUnVarGraphs UnVarGraph.unionUnVarSets UnVarGraph.varEnvDom
     Util.lengthExceeds Var.Id Var.Var Var.isExportedId Var.isId VarEnv.VarEnv
     VarEnv.delVarEnv VarEnv.emptyVarEnv VarEnv.lookupVarEnv VarEnv.mkVarEnv
     VarEnv.plusVarEnv_C VarEnv.unitVarEnv VarSet.VarSet VarSet.delVarSet
     VarSet.delVarSetList VarSet.elemVarSet VarSet.emptyVarSet
     VarSet.extendVarSetList VarSet.mkVarSet
*)
