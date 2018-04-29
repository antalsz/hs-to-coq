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
Require Combined.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require CoreUtils.
Require Data.Foldable.
Require Data.Tuple.
Require Demand.
Require DynFlags.
Require GHC.Base.
Require GHC.DeferredFix.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require UnVarGraph.
Require Util.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition CallArityRes :=
  (UnVarGraph.UnVarGraph * Combined.VarEnv BasicTypes.Arity)%type%type.
(* Midamble *)

(* We parameterize this because we don't have type information *)
Definition typeArity :  unit -> list BasicTypes.OneShotInfo.
apply GHC.Err.default. 
Qed.

Instance Default_CallArityRes : GHC.Err.Default CallArityRes := 
GHC.Err.Build_Default _ (GHC.Err.default, GHC.Err.default).

Definition arrow_first {b}{c}{d} (f : (b -> c)) : (b * d)%type -> (c * d)%type :=
  fun p => match p with (x,y)=> (f x, y) end.
Definition arrow_second {b}{c}{d} (f : (b -> c)) : (d * b)%type -> (d * c)%type :=
  fun p => match p with (x,y)=> (x, f y) end.

(* ------------------------- mutual recursion hack -------------------- *)

(* ANTALZ: This looks like a good example of structural mutual recursion *) 
Parameter callArityBind1
   : Combined.VarSet ->
     CallArityRes ->
     Combined.VarSet -> Combined.CoreBind -> (CallArityRes * Combined.CoreBind)%type.

(* Converted value declarations: *)

Definition addCrossCoCalls
   : UnVarGraph.UnVarSet -> UnVarGraph.UnVarSet -> CallArityRes -> CallArityRes :=
  fun set1 set2 =>
    arrow_first (fun arg_0__ =>
                   UnVarGraph.unionUnVarGraph (UnVarGraph.completeBipartiteGraph set1 set2)
                                              arg_0__).

Definition calledWith : CallArityRes -> Combined.Var -> UnVarGraph.UnVarSet :=
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
  pair UnVarGraph.emptyUnVarGraph Combined.emptyVarEnv.

Definition isInteresting : Combined.Var -> bool :=
  fun v => negb (Data.Foldable.null (typeArity (tt))).

Definition interestingBinds : Combined.CoreBind -> list Combined.Var :=
  GHC.List.filter isInteresting GHC.Base.∘ Combined.bindersOf.

Definition addInterestingBinds
   : Combined.VarSet -> Combined.CoreBind -> Combined.VarSet :=
  fun int bind =>
    Combined.extendVarSetList (Combined.delVarSetList int (Combined.bindersOf bind))
                              (interestingBinds bind).

Definition boringBinds : Combined.CoreBind -> Combined.VarSet :=
  Combined.mkVarSet GHC.Base.∘
  (GHC.List.filter (negb GHC.Base.∘ isInteresting) GHC.Base.∘ Combined.bindersOf).

Definition lookupCallArityRes
   : CallArityRes -> Combined.Var -> (BasicTypes.Arity * bool)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair g ae, v =>
        match Combined.lookupVarEnv ae v with
        | Some a => pair a (negb (UnVarGraph.elemUnVarSet v (UnVarGraph.neighbors g v)))
        | None => pair #0 false
        end
    end.

Definition lubArityEnv
   : Combined.VarEnv BasicTypes.Arity ->
     Combined.VarEnv BasicTypes.Arity -> Combined.VarEnv BasicTypes.Arity :=
  Combined.plusVarEnv_C GHC.Base.min.

Definition lubRes : CallArityRes -> CallArityRes -> CallArityRes :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair g1 ae1, pair g2 ae2 =>
        pair (UnVarGraph.unionUnVarGraph g1 g2) (lubArityEnv ae1 ae2)
    end.

Definition lubRess : list CallArityRes -> CallArityRes :=
  Data.Foldable.foldl lubRes emptyArityRes.

Definition callArityRecEnv
   : bool ->
     list (Combined.Var * CallArityRes)%type -> CallArityRes -> CallArityRes :=
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

Definition resDel : Combined.Var -> CallArityRes -> CallArityRes :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, pair g ae => pair (UnVarGraph.delNode g v) (Combined.delVarEnv ae v)
    end.

Definition resDelList : list Combined.Var -> CallArityRes -> CallArityRes :=
  fun vs ae => Data.Foldable.foldr resDel ae vs.

Definition trimArity : Combined.Var -> BasicTypes.Arity -> BasicTypes.Arity :=
  fun v a =>
    let 'pair demands result_info := Demand.splitStrictSig (Demand.botSig) in
    let max_arity_by_strsig :=
      if Demand.isBotRes result_info : bool then Data.Foldable.length demands else
      a in
    let max_arity_by_type := Data.Foldable.length (typeArity (tt)) in
    Data.Foldable.foldr GHC.Base.min a (cons max_arity_by_type (cons
                                              max_arity_by_strsig nil)).

Definition unitArityRes : Combined.Var -> BasicTypes.Arity -> CallArityRes :=
  fun v arity => pair UnVarGraph.emptyUnVarGraph (Combined.unitVarEnv v arity).

Definition callArityAnal
   : BasicTypes.Arity ->
     Combined.VarSet ->
     Combined.CoreExpr -> (CallArityRes * Combined.CoreExpr)%type :=
  fix callArityAnal arg_0__ arg_1__ arg_2__
        := let j_26__ :=
             match arg_0__, arg_1__, arg_2__ with
             | arity, int, Combined.Lam v e =>
                 let 'pair ae e' := callArityAnal (arity GHC.Num.- #1) (Combined.delVarSet int v)
                                      e in
                 pair ae (Combined.Lam v e')
             | arity, int, Combined.App e (Combined.Type_ t) =>
                 arrow_second (fun e => Combined.App e (Combined.Type_ t)) (callArityAnal arity
                                                                                          int e)
             | arity, int, Combined.App e1 e2 =>
                 let 'pair ae2 e2' := callArityAnal #0 int e2 in
                 let ae2' :=
                   if CoreUtils.exprIsTrivial e2 : bool then calledMultipleTimes ae2 else
                   ae2 in
                 let 'pair ae1 e1' := callArityAnal (arity GHC.Num.+ #1) int e1 in
                 let final_ae := both ae1 ae2' in pair final_ae (Combined.App e1' e2')
             | arity, int, Combined.Case scrut bndr ty alts =>
                 let 'pair scrut_ae scrut' := callArityAnal #0 int scrut in
                 let go :=
                   fun '(pair (pair dc bndrs) e) =>
                     let 'pair ae e' := callArityAnal arity int e in
                     pair ae (pair (pair dc bndrs) e') in
                 let 'pair alt_aes alts' := GHC.List.unzip (GHC.Base.map go alts) in
                 let alt_ae := lubRess alt_aes in
                 let final_ae := both scrut_ae alt_ae in
                 pair final_ae (Combined.Case scrut' bndr ty alts')
             | arity, int, Combined.Let bind e =>
                 let int_body := addInterestingBinds int bind in
                 let 'pair ae_body e' := callArityAnal arity int_body e in
                 let 'pair final_ae bind' := callArityBind1 (boringBinds bind) ae_body int
                                               bind in
                 pair final_ae (Combined.Let bind' e')
             | _, _, _ => GHC.Err.patternFailure
             end in
           let j_30__ :=
             match arg_0__, arg_1__, arg_2__ with
             | num_3__, int, Combined.Lam v e =>
                 let 'pair ae e' := callArityAnal #0 (Combined.delVarSet int v) e in
                 let ae' := calledMultipleTimes ae in
                 if num_3__ GHC.Base.== #0 : bool then pair ae' (Combined.Lam v e') else
                 j_26__
             | _, _, _ => j_26__
             end in
           match arg_0__, arg_1__, arg_2__ with
           | _, _, (Combined.Lit _ as e) => pair emptyArityRes e
           | _, _, (Combined.Type_ _ as e) => pair emptyArityRes e
           | _, _, (Combined.Coercion _ as e) => pair emptyArityRes e
           | arity, int, Combined.Tick t e =>
               arrow_second (Combined.Tick t) (callArityAnal arity int e)
           | arity, int, Combined.Cast e co =>
               arrow_second (fun e => Combined.Cast e co) (callArityAnal arity int e)
           | arity, int, (Combined.Mk_Var v as e) =>
               if Combined.elemVarSet v int : bool then pair (unitArityRes v arity) e else
               pair emptyArityRes e
           | arity, int, Combined.Lam v e =>
               if negb (Combined.isId v) : bool
               then arrow_second (Combined.Lam v) (callArityAnal arity (Combined.delVarSet int
                                                                                           v) e) else
               j_30__
           | _, _, _ => j_30__
           end.

Definition callArityRHS : Combined.CoreExpr -> Combined.CoreExpr :=
  Data.Tuple.snd GHC.Base.∘ callArityAnal #0 Combined.emptyVarSet.

Definition callArityBind
   : Combined.VarSet ->
     CallArityRes ->
     Combined.VarSet ->
     Combined.CoreBind -> (CallArityRes * Combined.CoreBind)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | boring_vars, ae_body, int, Combined.NonRec v rhs =>
        let boring := Combined.elemVarSet v boring_vars in
        let 'pair arity called_once := (if boring : bool then pair #0 false else
                                        lookupCallArityRes ae_body v) in
        let called_with_v :=
          if boring : bool then domRes ae_body else
          UnVarGraph.delUnVarSet (calledWith ae_body v) v in
        let is_thunk := negb (CoreUtils.exprIsCheap rhs) in
        let safe_arity :=
          if called_once : bool then arity else
          if is_thunk : bool then #0 else
          arity in
        let trimmed_arity := trimArity v safe_arity in
        let 'pair ae_rhs rhs' := callArityAnal trimmed_arity int rhs in
        let v' := Id.setIdCallArity v trimmed_arity in
        let ae_rhs' :=
          if called_once : bool then ae_rhs else
          if safe_arity GHC.Base.== #0 : bool then ae_rhs else
          calledMultipleTimes ae_rhs in
        let called_by_v := domRes ae_rhs' in
        let final_ae :=
          addCrossCoCalls called_by_v called_with_v (lubRes ae_rhs' (resDel v ae_body)) in
        pair final_ae (Combined.NonRec v' rhs')
    | boring_vars, ae_body, int, (Combined.Rec binds as b) =>
        let initial_binds :=
          let cont_21__ arg_22__ :=
            let 'pair i e := arg_22__ in
            cons (pair (pair i None) e) nil in
          Coq.Lists.List.flat_map cont_21__ binds in
        let int_body := addInterestingBinds int b in
        let any_boring :=
          Data.Foldable.any (fun arg_25__ => Combined.elemVarSet arg_25__ boring_vars)
          (let cont_26__ arg_27__ := let 'pair i _ := arg_27__ in cons i nil in
           Coq.Lists.List.flat_map cont_26__ binds) in
        let fix_
         : list (Combined.Var * option (bool * BasicTypes.Arity * CallArityRes)%type *
                 Combined.CoreExpr)%type ->
           (CallArityRes * list (Combined.Var * Combined.CoreExpr)%type)%type :=
          GHC.DeferredFix.deferredFix1 (fun fix_ ann_binds =>
                                          let aes_old :=
                                            let cont_29__ arg_30__ :=
                                              match arg_30__ with
                                              | pair (pair i (Some (pair (pair _ _) ae))) _ => cons (pair i ae) nil
                                              | _ => nil
                                              end in
                                            Coq.Lists.List.flat_map cont_29__ ann_binds in
                                          let ae := callArityRecEnv any_boring aes_old ae_body in
                                          let rerun :=
                                            fun '(pair (pair i mbLastRun) rhs) =>
                                              let 'pair new_arity called_once := (if Combined.elemVarSet i
                                                                                                         boring_vars : bool
                                                                                  then pair #0 false else
                                                                                  lookupCallArityRes ae i) in
                                              if andb (Combined.elemVarSet i int_body) (negb (UnVarGraph.elemUnVarSet i
                                                                                                                      (domRes
                                                                                                                       ae))) : bool
                                              then pair false (pair (pair i None) rhs) else
                                              let j_44__ :=
                                                let is_thunk := negb (CoreUtils.exprIsCheap rhs) in
                                                let safe_arity := if is_thunk : bool then #0 else new_arity in
                                                let trimmed_arity := trimArity i safe_arity in
                                                let 'pair ae_rhs rhs' := callArityAnal trimmed_arity int_body rhs in
                                                let i' := Id.setIdCallArity i trimmed_arity in
                                                let ae_rhs' :=
                                                  if called_once : bool then ae_rhs else
                                                  if safe_arity GHC.Base.== #0 : bool then ae_rhs else
                                                  calledMultipleTimes ae_rhs in
                                                pair true (pair (pair i' (Some (pair (pair called_once new_arity)
                                                                                     ae_rhs'))) rhs') in
                                              match mbLastRun with
                                              | Some (pair (pair old_called_once old_arity) _) =>
                                                  if andb (called_once GHC.Base.== old_called_once) (new_arity
                                                           GHC.Base.==
                                                           old_arity) : bool
                                                  then pair false (pair (pair i mbLastRun) rhs) else
                                                  j_44__
                                              | _ => j_44__
                                              end in
                                          let 'pair changes ann_binds' := GHC.List.unzip (GHC.Base.map rerun
                                                                                                       ann_binds) in
                                          let any_change := Data.Foldable.or changes in
                                          if any_change : bool then fix_ ann_binds' else
                                          pair ae (GHC.Base.map (fun '(pair (pair i _) e) => pair i e) ann_binds')) in
        let 'pair ae_rhs binds' := fix_ initial_binds in
        let final_ae := resDelList (Combined.bindersOf b) ae_rhs in
        pair final_ae (Combined.Rec binds')
    end.

Definition callArityTopLvl
   : list Combined.Var ->
     Combined.VarSet ->
     list Combined.CoreBind -> (CallArityRes * list Combined.CoreBind)%type :=
  fix callArityTopLvl arg_0__ arg_1__ arg_2__
        := match arg_0__, arg_1__, arg_2__ with
           | exported, _, nil =>
               pair (calledMultipleTimes (pair UnVarGraph.emptyUnVarGraph (Combined.mkVarEnv
                                                (Coq.Lists.List.flat_map (fun v => cons (pair v #0) nil) exported))))
                    nil
           | exported, int1, cons b bs =>
               let int' := addInterestingBinds int1 b in
               let int2 := Combined.bindersOf b in
               let exported' :=
                 Coq.Init.Datatypes.app (GHC.List.filter Combined.isExportedId int2) exported in
               let 'pair ae1 bs' := callArityTopLvl exported' int' bs in
               let 'pair ae2 b' := callArityBind (boringBinds b) ae1 int1 b in
               pair ae2 (cons b' bs')
           end.

Definition callArityAnalProgram
   : DynFlags.DynFlags -> Combined.CoreProgram -> Combined.CoreProgram :=
  fun _dflags binds =>
    let 'pair _ binds' := callArityTopLvl nil Combined.emptyVarSet binds in
    binds'.

(* External variables:
     None Some andb arrow_first arrow_second bool callArityBind1 cons false list negb
     nil op_zt__ option pair true tt typeArity BasicTypes.Arity Combined.App
     Combined.Case Combined.Cast Combined.Coercion Combined.CoreBind
     Combined.CoreExpr Combined.CoreProgram Combined.Lam Combined.Let Combined.Lit
     Combined.Mk_Var Combined.NonRec Combined.Rec Combined.Tick Combined.Type_
     Combined.Var Combined.VarEnv Combined.VarSet Combined.bindersOf
     Combined.delVarEnv Combined.delVarSet Combined.delVarSetList Combined.elemVarSet
     Combined.emptyVarEnv Combined.emptyVarSet Combined.extendVarSetList
     Combined.isExportedId Combined.isId Combined.lookupVarEnv Combined.mkVarEnv
     Combined.mkVarSet Combined.plusVarEnv_C Combined.unitVarEnv
     Coq.Init.Datatypes.app Coq.Lists.List.flat_map CoreUtils.exprIsCheap
     CoreUtils.exprIsTrivial Data.Foldable.any Data.Foldable.foldl
     Data.Foldable.foldr Data.Foldable.length Data.Foldable.null Data.Foldable.or
     Data.Tuple.fst Data.Tuple.snd Demand.botSig Demand.isBotRes
     Demand.splitStrictSig DynFlags.DynFlags GHC.Base.const GHC.Base.map GHC.Base.min
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zsze__
     GHC.DeferredFix.deferredFix1 GHC.Err.patternFailure GHC.List.filter
     GHC.List.unzip GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__
     Id.idCallArity Id.setIdCallArity UnVarGraph.UnVarGraph UnVarGraph.UnVarSet
     UnVarGraph.completeBipartiteGraph UnVarGraph.completeGraph UnVarGraph.delNode
     UnVarGraph.delUnVarSet UnVarGraph.elemUnVarSet UnVarGraph.emptyUnVarGraph
     UnVarGraph.neighbors UnVarGraph.unionUnVarGraph UnVarGraph.unionUnVarGraphs
     UnVarGraph.unionUnVarSets UnVarGraph.varEnvDom Util.lengthExceeds
*)
