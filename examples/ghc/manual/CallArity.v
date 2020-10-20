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
Require Control.Arrow.
Require Coq.Init.Datatypes.
Require Coq.Lists.List.
Require Core.
Require CoreArity.
Require CoreUtils.
Require Data.Foldable.
Require Data.Tuple.
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
  (UnVarGraph.UnVarGraph * Core.VarEnv BasicTypes.Arity)%type%type.

(* Midamble *)


Instance Default_CallArityRes : GHC.Err.Default CallArityRes := 
GHC.Err.Build_Default _ (GHC.Err.default, GHC.Err.default).


(* ------------------------- mutual recursion hack -------------------- *)

(* ANTALZ: This looks like a good example of structural mutual recursion *) 
Parameter callArityBind1
   : Core.VarSet ->
     CallArityRes ->
     Core.VarSet -> Core.CoreBind -> (CallArityRes * Core.CoreBind)%type.

(* Converted value declarations: *)

Definition isInteresting : Core.Var -> bool :=
  fun v => negb (Data.Foldable.null (CoreArity.typeArity (Id.idType v))).

Definition interestingBinds : Core.CoreBind -> list Core.Var :=
  GHC.List.filter isInteresting GHC.Base.∘ Core.bindersOf.

Definition addInterestingBinds : Core.VarSet -> Core.CoreBind -> Core.VarSet :=
  fun int bind =>
    Core.extendVarSetList (Core.delVarSetList int (Core.bindersOf bind))
                          (interestingBinds bind).

Definition boringBinds : Core.CoreBind -> Core.VarSet :=
  Core.mkVarSet GHC.Base.∘
  (GHC.List.filter (negb GHC.Base.∘ isInteresting) GHC.Base.∘ Core.bindersOf).

Definition addCrossCoCalls
   : UnVarGraph.UnVarSet -> UnVarGraph.UnVarSet -> CallArityRes -> CallArityRes :=
  fun set1 set2 =>
    Control.Arrow.arrow_first (fun arg_0__ =>
                                 UnVarGraph.unionUnVarGraph (UnVarGraph.completeBipartiteGraph set1 set2)
                                                            arg_0__).

Definition domRes : CallArityRes -> UnVarGraph.UnVarSet :=
  fun '(pair _ ae) => UnVarGraph.varEnvDom ae.

Definition lubArityEnv
   : Core.VarEnv BasicTypes.Arity ->
     Core.VarEnv BasicTypes.Arity -> Core.VarEnv BasicTypes.Arity :=
  Core.plusVarEnv_C GHC.Base.min.

Definition lubRes : CallArityRes -> CallArityRes -> CallArityRes :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair g1 ae1, pair g2 ae2 =>
        pair (UnVarGraph.unionUnVarGraph g1 g2) (lubArityEnv ae1 ae2)
    end.

Definition both : CallArityRes -> CallArityRes -> CallArityRes :=
  fun r1 r2 => addCrossCoCalls (domRes r1) (domRes r2) (lubRes r1 r2).

Definition calledMultipleTimes : CallArityRes -> CallArityRes :=
  fun res =>
    Control.Arrow.arrow_first (GHC.Base.const (UnVarGraph.completeGraph (domRes
                                                                         res))) res.

Definition emptyArityRes : CallArityRes :=
  pair UnVarGraph.emptyUnVarGraph Core.emptyVarEnv.

Definition lubRess : list CallArityRes -> CallArityRes :=
  Data.Foldable.foldl lubRes emptyArityRes.

Definition unitArityRes : Core.Var -> BasicTypes.Arity -> CallArityRes :=
  fun v arity => pair UnVarGraph.emptyUnVarGraph (Core.unitVarEnv v arity).

Fixpoint callArityAnal (arg_0__ : BasicTypes.Arity) (arg_1__ : Core.VarSet)
                       (arg_2__ : Core.CoreExpr) : (CallArityRes * Core.CoreExpr)%type
           := let j_26__ :=
                match arg_0__, arg_1__, arg_2__ with
                | arity, int, Core.Lam v e =>
                    let 'pair ae e' := callArityAnal (arity GHC.Num.- #1) (Core.delVarSet int v)
                                         e in
                    pair ae (Core.Lam v e')
                | arity, int, Core.App e (Core.Mk_Type t) =>
                    Control.Arrow.arrow_second (fun e => Core.App e (Core.Mk_Type t)) (callArityAnal
                                                                                       arity int e)
                | arity, int, Core.App e1 e2 =>
                    let 'pair ae2 e2' := callArityAnal #0 int e2 in
                    let ae2' :=
                      if CoreUtils.exprIsTrivial e2 : bool then calledMultipleTimes ae2 else
                      ae2 in
                    let 'pair ae1 e1' := callArityAnal (arity GHC.Num.+ #1) int e1 in
                    let final_ae := both ae1 ae2' in pair final_ae (Core.App e1' e2')
                | arity, int, Core.Case scrut bndr ty alts =>
                    let 'pair scrut_ae scrut' := callArityAnal #0 int scrut in
                    let go :=
                      fun '(pair (pair dc bndrs) e) =>
                        let 'pair ae e' := callArityAnal arity int e in
                        pair ae (pair (pair dc bndrs) e') in
                    let 'pair alt_aes alts' := GHC.List.unzip (GHC.Base.map go alts) in
                    let alt_ae := lubRess alt_aes in
                    let final_ae := both scrut_ae alt_ae in
                    pair final_ae (Core.Case scrut' bndr ty alts')
                | arity, int, Core.Let bind e =>
                    let int_body := addInterestingBinds int bind in
                    let 'pair ae_body e' := callArityAnal arity int_body e in
                    let 'pair final_ae bind' := callArityBind1 (boringBinds bind) ae_body int
                                                  bind in
                    pair final_ae (Core.Let bind' e')
                | _, _, _ => GHC.Err.patternFailure
                end in
              let j_30__ :=
                match arg_0__, arg_1__, arg_2__ with
                | num_3__, int, Core.Lam v e =>
                    let 'pair ae e' := callArityAnal #0 (Core.delVarSet int v) e in
                    let ae' := calledMultipleTimes ae in
                    if num_3__ GHC.Base.== #0 : bool then pair ae' (Core.Lam v e') else
                    j_26__
                | _, _, _ => j_26__
                end in
              match arg_0__, arg_1__, arg_2__ with
              | _, _, (Core.Lit _ as e) => pair emptyArityRes e
              | _, _, (Core.Mk_Type _ as e) => pair emptyArityRes e
              | _, _, (Core.Mk_Coercion _ as e) => pair emptyArityRes e
              | arity, int, Core.Cast e co =>
                  Control.Arrow.arrow_second (fun e => Core.Cast e co) (callArityAnal arity int e)
              | arity, int, (Core.Mk_Var v as e) =>
                  if Core.elemVarSet v int : bool then pair (unitArityRes v arity) e else
                  pair emptyArityRes e
              | arity, int, Core.Lam v e =>
                  if negb (Core.isId v) : bool
                  then Control.Arrow.arrow_second (Core.Lam v) (callArityAnal arity
                                                                              (Core.delVarSet int v) e) else
                  j_30__
              | _, _, _ => j_30__
              end.

Definition calledWith : CallArityRes -> Core.Var -> UnVarGraph.UnVarSet :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair g _, v => UnVarGraph.neighbors g v
    end.

Definition callArityRecEnv
   : bool ->
     list (Core.Var * CallArityRes)%type -> CallArityRes -> CallArityRes :=
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
      Control.Arrow.arrow_first (fun arg_13__ =>
                                   UnVarGraph.unionUnVarGraph cross_calls arg_13__) ae_combined in
    ae_new.

Definition lookupCallArityRes
   : CallArityRes -> Core.Var -> (BasicTypes.Arity * bool)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair g ae, v =>
        match Core.lookupVarEnv ae v with
        | Some a => pair a (negb (UnVarGraph.elemUnVarSet v (UnVarGraph.neighbors g v)))
        | None => pair #0 false
        end
    end.

Definition resDel : Core.Var -> CallArityRes -> CallArityRes :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | v, pair g ae => pair (UnVarGraph.delNode g v) (Core.delVarEnv ae v)
    end.

Definition resDelList : list Core.Var -> CallArityRes -> CallArityRes :=
  fun vs ae => Data.Foldable.foldr resDel ae vs.

Definition trimArity : Core.Id -> BasicTypes.Arity -> BasicTypes.Arity :=
  fun v a =>
    let 'pair demands result_info := Core.splitStrictSig (Id.idStrictness v) in
    let max_arity_by_strsig :=
      if Core.isBotRes result_info : bool then Coq.Lists.List.length demands else
      a in
    let max_arity_by_type :=
      Coq.Lists.List.length (CoreArity.typeArity (Id.idType v)) in
    Data.Foldable.foldr GHC.Base.min a (cons max_arity_by_type (cons
                                              max_arity_by_strsig nil)).

Definition callArityBind
   : Core.VarSet ->
     CallArityRes ->
     Core.VarSet -> Core.CoreBind -> (CallArityRes * Core.CoreBind)%type :=
  fun arg_0__ arg_1__ arg_2__ arg_3__ =>
    match arg_0__, arg_1__, arg_2__, arg_3__ with
    | boring_vars, ae_body, int, Core.NonRec v rhs =>
        let boring := Core.elemVarSet v boring_vars in
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
        pair final_ae (Core.NonRec v' rhs')
    | boring_vars, ae_body, int, (Core.Rec binds as b) =>
        let initial_binds :=
          let cont_21__ arg_22__ :=
            let 'pair i e := arg_22__ in
            cons (pair (pair i None) e) nil in
          Coq.Lists.List.flat_map cont_21__ binds in
        let int_body := addInterestingBinds int b in
        let any_boring :=
          Data.Foldable.any (fun arg_25__ => Core.elemVarSet arg_25__ boring_vars)
          (let cont_26__ arg_27__ := let 'pair i _ := arg_27__ in cons i nil in
           Coq.Lists.List.flat_map cont_26__ binds) in
        let fix_
         : list (Core.Id * option (bool * BasicTypes.Arity * CallArityRes)%type *
                 Core.CoreExpr)%type ->
           (CallArityRes * list (Core.Id * Core.CoreExpr)%type)%type :=
          GHC.DeferredFix.deferredFix1 (fun fix_
                                        (ann_binds
                                          : list (Core.Id * option (bool * BasicTypes.Arity * CallArityRes)%type *
                                                  Core.CoreExpr)%type) =>
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
                                              let 'pair new_arity called_once := (if Core.elemVarSet i
                                                                                                     boring_vars : bool
                                                                                  then pair #0 false else
                                                                                  lookupCallArityRes ae i) in
                                              if andb (Core.elemVarSet i int_body) (negb (UnVarGraph.elemUnVarSet i
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
        let final_ae := resDelList (Core.bindersOf b) ae_rhs in
        pair final_ae (Core.Rec binds')
    end.

Fixpoint callArityTopLvl (arg_0__ : list Core.Var) (arg_1__ : Core.VarSet)
                         (arg_2__ : list Core.CoreBind) : (CallArityRes * list Core.CoreBind)%type
           := match arg_0__, arg_1__, arg_2__ with
              | exported, _, nil =>
                  pair (calledMultipleTimes (pair UnVarGraph.emptyUnVarGraph (Core.mkVarEnv
                                                   (Coq.Lists.List.flat_map (fun v => cons (pair v #0) nil) exported))))
                       nil
              | exported, int1, cons b bs =>
                  let int' := addInterestingBinds int1 b in
                  let int2 := Core.bindersOf b in
                  let exported' :=
                    Coq.Init.Datatypes.app (GHC.List.filter Core.isExportedId int2) exported in
                  let 'pair ae1 bs' := callArityTopLvl exported' int' bs in
                  let 'pair ae2 b' := callArityBind (boringBinds b) ae1 int1 b in
                  pair ae2 (cons b' bs')
              end.

Definition callArityAnalProgram
   : DynFlags.DynFlags -> Core.CoreProgram -> Core.CoreProgram :=
  fun _dflags binds =>
    let 'pair _ binds' := callArityTopLvl nil Core.emptyVarSet binds in
    binds'.

Definition callArityRHS : Core.CoreExpr -> Core.CoreExpr :=
  Data.Tuple.snd GHC.Base.∘ callArityAnal #0 Core.emptyVarSet.

(* External variables:
     None Some andb bool callArityBind1 cons false list negb nil op_zt__ option pair
     true BasicTypes.Arity Control.Arrow.arrow_first Control.Arrow.arrow_second
     Coq.Init.Datatypes.app Coq.Lists.List.flat_map Coq.Lists.List.length Core.App
     Core.Case Core.Cast Core.CoreBind Core.CoreExpr Core.CoreProgram Core.Id
     Core.Lam Core.Let Core.Lit Core.Mk_Coercion Core.Mk_Type Core.Mk_Var Core.NonRec
     Core.Rec Core.Var Core.VarEnv Core.VarSet Core.bindersOf Core.delVarEnv
     Core.delVarSet Core.delVarSetList Core.elemVarSet Core.emptyVarEnv
     Core.emptyVarSet Core.extendVarSetList Core.isBotRes Core.isExportedId Core.isId
     Core.lookupVarEnv Core.mkVarEnv Core.mkVarSet Core.plusVarEnv_C
     Core.splitStrictSig Core.unitVarEnv CoreArity.typeArity CoreUtils.exprIsCheap
     CoreUtils.exprIsTrivial Data.Foldable.any Data.Foldable.foldl
     Data.Foldable.foldr Data.Foldable.null Data.Foldable.or Data.Tuple.fst
     Data.Tuple.snd DynFlags.DynFlags GHC.Base.const GHC.Base.map GHC.Base.min
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zsze__
     GHC.DeferredFix.deferredFix1 GHC.Err.patternFailure GHC.List.filter
     GHC.List.unzip GHC.Num.fromInteger GHC.Num.op_zm__ GHC.Num.op_zp__
     Id.idCallArity Id.idStrictness Id.idType Id.setIdCallArity UnVarGraph.UnVarGraph
     UnVarGraph.UnVarSet UnVarGraph.completeBipartiteGraph UnVarGraph.completeGraph
     UnVarGraph.delNode UnVarGraph.delUnVarSet UnVarGraph.elemUnVarSet
     UnVarGraph.emptyUnVarGraph UnVarGraph.neighbors UnVarGraph.unionUnVarGraph
     UnVarGraph.unionUnVarGraphs UnVarGraph.unionUnVarSets UnVarGraph.varEnvDom
     Util.lengthExceeds
*)
