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
Require CoreArity.
Require CoreSyn.
Require CoreUtils.
Require Data.Foldable.
Require Data.Tuple.
Require Demand.
Require DynFlags.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Require Id.
Require UnVarGraph.
Require Var.
Require VarEnv.
Require VarSet.
Import GHC.Base.Notations.
Import GHC.Num.Notations.


(* Converted type declarations: *)

Definition CallArityRes :=
  (UnVarGraph.UnVarGraph * VarEnv.VarEnv BasicTypes.Arity)%type%type.
(* Converted value declarations: *)

(* For some reason, this code doesn't typecheck without defining f using 'let'. *)

Definition addCrossCoCalls
    : UnVarGraph.UnVarSet -> UnVarGraph.UnVarSet -> CallArityRes -> CallArityRes :=
  fun set1 set2 =>
    let f :=
        (fun arg_5__ => UnVarGraph.unionUnVarGraph (UnVarGraph.completeBipartiteGraph set1 set2) arg_5__) in
    Control.Arrow.first f.


Definition calledWith : CallArityRes -> Var.Var -> UnVarGraph.UnVarSet :=
  fun arg_7__ arg_8__ =>
    match arg_7__ , arg_8__ with
      | pair g _ , v => UnVarGraph.neighbors g v
    end.

Definition domRes : CallArityRes -> UnVarGraph.UnVarSet :=
  fun arg_19__ => match arg_19__ with | pair _ ae => UnVarGraph.varEnvDom ae end.

Definition calledMultipleTimes : CallArityRes -> CallArityRes :=
  fun res =>
    Control.Arrow.first (GHC.Base.const (UnVarGraph.completeGraph (domRes res)))
    res.

Definition emptyArityRes : CallArityRes :=
  pair UnVarGraph.emptyUnVarGraph VarEnv.emptyVarEnv.

(* UGH we do need type information!!! *)
Definition isInteresting : Var.Var -> bool := fun x => false.
(*  fun v =>
    GHC.Num.fromInteger 0 GHC.Base.< Data.Foldable.length (CoreArity.typeArity
                                                          (Id.idType v)).  *)

Definition interestingBinds : CoreSyn.CoreBind -> list Var.Var :=
  GHC.List.filter isInteresting GHC.Base.∘ CoreSyn.bindersOf.

Definition addInterestingBinds
    : VarSet.VarSet -> CoreSyn.CoreBind -> VarSet.VarSet :=
  fun int bind =>
    VarSet.extendVarSetList (VarSet.delVarSetList int (CoreSyn.bindersOf bind))
                            (interestingBinds bind).

Definition boringBinds : CoreSyn.CoreBind -> VarSet.VarSet :=
  VarSet.mkVarSet GHC.Base.∘ (GHC.List.filter (negb GHC.Base.∘ isInteresting)
  GHC.Base.∘ CoreSyn.bindersOf).

Definition lookupCallArityRes : CallArityRes -> Var.Var -> (BasicTypes.Arity *
                                bool)%type :=
  fun arg_11__ arg_12__ =>
    match arg_11__ , arg_12__ with
      | pair g ae , v => let scrut_13__ := VarEnv.lookupVarEnv ae v in
                         match scrut_13__ with
                           | Some a => pair a (negb (UnVarGraph.elemUnVarSet v (UnVarGraph.neighbors g v)))
                           | None => pair (GHC.Num.fromInteger 0) false
                         end
    end.

Definition lubArityEnv : VarEnv.VarEnv BasicTypes.Arity -> VarEnv.VarEnv
                         BasicTypes.Arity -> VarEnv.VarEnv BasicTypes.Arity :=
  VarEnv.plusVarEnv_C GHC.Base.min.

Definition lubRes : CallArityRes -> CallArityRes -> CallArityRes :=
  fun arg_1__ arg_2__ =>
    match arg_1__ , arg_2__ with
      | pair g1 ae1 , pair g2 ae2 => pair (UnVarGraph.unionUnVarGraph g1 g2)
                                          (lubArityEnv ae1 ae2)
    end.

Definition lubRess : list CallArityRes -> CallArityRes :=
  Data.Foldable.foldl lubRes emptyArityRes.

(* Had to get rid of $ and lift fcn argument to Arrow.first so that it wouldn't hang. *)
Definition callArityRecEnv : bool -> list (Var.Var *
                                          CallArityRes)%type -> CallArityRes -> CallArityRes :=
  fun any_boring ae_rhss ae_body =>
    let ae_combined :=
      lubRes (lubRess (GHC.Base.map Data.Tuple.snd ae_rhss)) ae_body in
    let vars := GHC.Base.map Data.Tuple.fst ae_rhss in
    let cross_call :=
      fun arg_38__ =>
        match arg_38__ with
          | pair v ae_rhs => let called_by_v := domRes ae_rhs in
                             let is_thunk := Id.idCallArity v GHC.Base.== GHC.Num.fromInteger 0 in
                             let ae_before_v :=
                               if is_thunk : bool
                               then lubRes (lubRess (GHC.Base.map Data.Tuple.snd GHC.Base.$ GHC.List.filter
                                                    ((fun arg_41__ => arg_41__ GHC.Base./= v) GHC.Base.∘ Data.Tuple.fst)
                                                    ae_rhss)) ae_body
                               else ae_combined in
                             let called_with_v :=
                               UnVarGraph.unionUnVarSets (GHC.Base.map (calledWith ae_before_v) vars) in
                             UnVarGraph.completeBipartiteGraph called_by_v called_with_v
        end in
    let cross_calls :=
      let j_46__ :=
        UnVarGraph.unionUnVarGraphs (GHC.Base.map cross_call ae_rhss) in
      let j_47__ :=
        if Data.Foldable.length ae_rhss GHC.Base.> GHC.Num.fromInteger 25 : bool
        then UnVarGraph.completeGraph (domRes ae_combined)
        else j_46__ in
      if any_boring : bool
      then UnVarGraph.completeGraph (domRes ae_combined)
      else j_47__ in
    let f := (fun arg_49__ =>
                            UnVarGraph.unionUnVarGraph cross_calls arg_49__) in
    let ae_new :=
      Control.Arrow.first f ae_combined in
    ae_new.

Definition both : CallArityRes -> CallArityRes -> CallArityRes :=
  fun r1 r2 => addCrossCoCalls (domRes r1) (domRes r2) GHC.Base.$ lubRes r1 r2.

Definition resDel : Var.Var -> CallArityRes -> CallArityRes :=
  fun arg_24__ arg_25__ =>
    match arg_24__ , arg_25__ with
      | v , pair g ae => pair (UnVarGraph.delNode g v) (VarEnv.delVarEnv ae v)
    end.

Definition resDelList : list Var.Var -> CallArityRes -> CallArityRes :=
  fun vs ae => Data.Foldable.foldr resDel ae vs.

(* minimum (x : xs) ==> Data.Foldable.foldr GHC.Base.min x xs *)
Parameter trimArity : Var.Id -> BasicTypes.Arity -> BasicTypes.Arity.
(*
  fun v a =>
    match Demand.splitStrictSig (Id.idStrictness v) with
      | pair demands result_info => let max_arity_by_strsig :=
                                      if Demand.isBotRes result_info : bool
                                      then Data.Foldable.length demands
                                      else a in
                                    let max_arity_by_type :=
                                      Data.Foldable.length (CoreArity.typeArity (Id.idType v)) in
                                    Data.Foldable.foldr GHC.Base.min a (cons max_arity_by_type (cons max_arity_by_strsig
                                                                                                nil))
    end. *)

Definition unitArityRes : Var.Var -> BasicTypes.Arity -> CallArityRes :=
  fun v arity => pair UnVarGraph.emptyUnVarGraph (VarEnv.unitVarEnv v arity).

Axiom abort : forall {a}, a.

Definition callArityBind
   (arg_96__ : VarSet.VarSet) (arg_97__: CallArityRes) (arg_98__ : VarSet.VarSet) (arg_99_: CoreSyn.CoreBind) :
       (CallArityRes * CoreSyn.CoreBind)%type.
Admitted.

Fixpoint callArityAnal
    ( arg_55__ : BasicTypes.Arity) (arg_56__: VarSet.VarSet) (arg_57__: CoreSyn.CoreExpr) :
  (CallArityRes * CoreSyn.CoreExpr)%type :=
        let j_81__ :=
             match arg_55__ , arg_56__ , arg_57__ with
               | arity, int , CoreSyn.Var x => abort  (* no case here *)
               | arity, int , CoreSyn.Lit x => abort  (* no case here *)
               | arity, int , CoreSyn.Cast _ _ => abort  (* no case here *)
               | arity, int , CoreSyn.Tick _ _ => abort  (* no case here *)
               | arity, int , CoreSyn.Type_ _ => abort  (* no case here *)
               | arity, int , CoreSyn.Coercion _ => abort  (* no case here *)
               | arity , int , CoreSyn.Lam v e =>
                 match callArityAnal (arity GHC.Num.- GHC.Num.fromInteger 1) (VarSet.delVarSet int v) e with
                 | pair ae e' => pair ae (CoreSyn.Lam v e')
                 end
               | arity , int , CoreSyn.App e (CoreSyn.Type_ t) =>
                 let f := (fun e => CoreSyn.App e (CoreSyn.Type_ t)) in
                            Control.Arrow.second f (callArityAnal arity int e)
               | arity , int , CoreSyn.App e1 e2 => match callArityAnal (GHC.Num.fromInteger 0)
                                                            int e2 with
                                                      | pair ae2 e2' => let ae2' :=
                                                                          if CoreUtils.exprIsTrivial e2 : bool
                                                                          then calledMultipleTimes ae2
                                                                          else ae2 in
                                                                        match callArityAnal (arity GHC.Num.+
                                                                                            GHC.Num.fromInteger 1) int
                                                                                e1 with
                                                                          | pair ae1 e1' => let final_ae :=
                                                                                              both ae1 ae2' in
                                                                                            pair final_ae (CoreSyn.App
                                                                                                 e1' e2')
                                                                        end
                                                    end
               | arity , int , CoreSyn.Case scrut bndr ty alts => match callArityAnal
                                                                          (GHC.Num.fromInteger 0) int scrut with
                                                                    | pair scrut_ae scrut' => let go :=
                                                                                                fun arg_69__ =>
                                                                                                  match arg_69__ with
                                                                                                    | pair (pair dc
                                                                                                                 bndrs)
                                                                                                           e =>
                                                                                                      match callArityAnal
                                                                                                              arity int
                                                                                                              e with
                                                                                                        | pair ae e' =>
                                                                                                          pair ae (pair
                                                                                                               (pair dc
                                                                                                                     bndrs)
                                                                                                               e')
                                                                                                      end
                                                                                                  end in
                                                                                              match GHC.List.unzip
                                                                                                      GHC.Base.$
                                                                                                      GHC.Base.map go
                                                                                                      alts with
                                                                                                | pair alt_aes alts' =>
                                                                                                  let alt_ae :=
                                                                                                    lubRess alt_aes in
                                                                                                  let final_ae :=
                                                                                                    both scrut_ae
                                                                                                         alt_ae in
                                                                                                  pair final_ae
                                                                                                       (CoreSyn.Case
                                                                                                       scrut' bndr ty
                                                                                                       alts')
                                                                                              end
                                                                  end
               | arity , int , CoreSyn.Let bind e => let int_body :=
                                                       addInterestingBinds int bind in
                                                     match callArityAnal arity int_body e with
                                                       | pair ae_body e' => match callArityBind (boringBinds bind)
                                                                                    ae_body int bind with
                                                                              | pair final_ae bind' => pair final_ae
                                                                                                            (CoreSyn.Let
                                                                                                            bind' e')
                                                                            end
                                                     end
             end in
           let j_85__ :=
             match arg_55__ , arg_56__ , arg_57__ with
               | num_58__ , int , CoreSyn.Lam v e => match callArityAnal (GHC.Num.fromInteger
                                                                         0) (VarSet.delVarSet int v) e with
                                                       | pair ae e' => let ae' := calledMultipleTimes ae in
                                                                       if num_58__ GHC.Base.== GHC.Num.fromInteger
                                                                          0 : bool
                                                                       then pair ae' (CoreSyn.Lam v e')
                                                                       else j_81__
                                                     end
               | _ ,_ , _ => abort
             end in
           match arg_55__ , arg_56__ , arg_57__ with
             | _ , _ , (CoreSyn.Lit _ as e) => pair emptyArityRes e
             | _ , _ , (CoreSyn.Type_ _ as e) => pair emptyArityRes e
             | _ , _ , (CoreSyn.Coercion _ as e) => pair emptyArityRes e
             | arity , int , CoreSyn.Tick t e => Control.Arrow.second (CoreSyn.Tick t)
                                                 GHC.Base.$ callArityAnal arity int e
             | arity , int , CoreSyn.Cast e co =>
               let f :=  (fun e => CoreSyn.Cast e co) in
               Control.Arrow.second f (callArityAnal arity int e)
             | arity , int , (CoreSyn.Var v as e) => let j_92__ := pair emptyArityRes e in
                                                     if VarSet.elemVarSet v int : bool
                                                     then pair (unitArityRes v arity) e
                                                     else j_92__
             | arity , int , CoreSyn.Lam v e => if negb (Var.isId v) : bool
                                                then Control.Arrow.second (CoreSyn.Lam v)
                                                                          (callArityAnal arity (VarSet.delVarSet int v) e)
                                                else j_85__
             | _ , _ , _ => abort
           end.
(*
Fixpoint callArityBind
   (arg_96__ : VarSet.VarSet) (arg_97__: CallArityRes) (arg_98__ : VarSet.VarSet) (arg_99__: CoreSyn.CoreBind) :
       (CallArityRes * CoreSyn.CoreBind)%type :=
    match arg_96__ , arg_97__ , arg_98__ , arg_99__ with
      | boring_vars , ae_body , int , CoreSyn.NonRec v rhs =>
        let boring :=
            VarSet.elemVarSet v boring_vars in
        let scrut := (let j_101__ := lookupCallArityRes ae_body v in
               if boring : bool
               then pair (GHC.Num.fromInteger 0) false
               else j_101__) in
        match scrut with
        | pair arity called_once => let called_with_v :=
                                       let j_103__ :=
                                           UnVarGraph.delUnVarSet
                                             (calledWith ae_body v)
                                             v in
                                       if boring : bool
                                       then domRes ae_body
                                       else j_103__ in
                                   let is_thunk :=
                                       negb (CoreUtils.exprIsHNF
                                               rhs) in
                                   let safe_arity :=
                                       let j_106__ :=
                                           if is_thunk : bool
                                           then GHC.Num.fromInteger
                                                  0
                                           else arity in
                                       if called_once : bool
                                       then arity
                                       else j_106__ in
                                   let trimmed_arity :=
                                       trimArity v safe_arity in
                                   match callArityAnal
                                           trimmed_arity int
                                           rhs with
                                   | pair ae_rhs rhs' =>
                                     let v' :=
                                         Id.setIdCallArity v
                                                           trimmed_arity in
                                     let ae_rhs' :=
                                         let j_111__ :=
                                             calledMultipleTimes
                                               ae_rhs in
                                         let j_112__ :=
                                             if safe_arity
                                                  GHC.Base.==
                                                  GHC.Num.fromInteger
                                                  0 : bool
                                             then ae_rhs
                                             else j_111__ in
                                         if called_once : bool
                                         then ae_rhs
                                         else j_112__ in
                                     let called_by_v :=
                                         domRes ae_rhs' in
                                     let final_ae :=
                                         addCrossCoCalls
                                           called_by_v
                                           called_with_v
                                           GHC.Base.$ lubRes
                                           ae_rhs' (resDel v
                                                           ae_body) in
                                     pair final_ae
                                          (CoreSyn.NonRec v'
                                                          rhs')
                                   end
        end
      | boring_vars , ae_body , int , (CoreSyn.Rec binds as b) =>
        let initial_binds :=
            let cont_117__ arg_118__ :=
                match arg_118__ with
                | pair i e => cons (pair (pair i None) e) nil
                end in
            Coq.Lists.List.flat_map cont_117__ binds in
        let int_body := addInterestingBinds int b in
        let any_boring :=
            Data.Foldable.any (fun arg_121__ =>
                                 VarSet.elemVarSet arg_121__
                                                   boring_vars)
                              (let cont_122__ arg_123__ :=
                                   match arg_123__ with
                                   | pair i _ => cons i nil
                                   end in
                               Coq.Lists.List.flat_map cont_122__ binds) in
        let fix_ : list (Var.Id * option (bool *
                                          BasicTypes.Arity *
                                          CallArityRes)%type *
                         CoreSyn.CoreExpr)%type -> (CallArityRes
                                                   * list (Var.Id *
                                                           CoreSyn.CoreExpr)%type)%type :=
            fix fix_ ann_binds
              := let aes_old :=
                     let cont_125__ arg_126__ :=
                         match arg_126__ with
                         | pair (pair i (Some (pair (pair _ _)
                                                    ae))) _ =>
                           cons (pair i ae) nil
                         | _ => nil
                         end in
                     Coq.Lists.List.flat_map cont_125__
                                             ann_binds in
                 let ae :=
                     callArityRecEnv any_boring aes_old
                                     ae_body in
                 let rerun :=
                                                                               fun arg_129__ =>
                                                                                 match arg_129__ with
                                                                                   | pair (pair i mbLastRun) rhs =>
                                                                                     match (let j_130__ :=
                                                                                               lookupCallArityRes ae
                                                                                               i in
                                                                                             if VarSet.elemVarSet i
                                                                                                                  boring_vars : bool
                                                                                             then pair
                                                                                                  (GHC.Num.fromInteger
                                                                                                  0) false
                                                                                             else j_130__) with
                                                                                       | pair new_arity called_once =>
                                                                                         let j_139__ :=
                                                                                           let is_thunk :=
                                                                                             negb (CoreUtils.exprIsHNF
                                                                                                  rhs) in
                                                                                           let safe_arity :=
                                                                                             if is_thunk : bool
                                                                                             then GHC.Num.fromInteger 0
                                                                                             else new_arity in
                                                                                           let trimmed_arity :=
                                                                                             trimArity i safe_arity in
                                                                                           match callArityAnal
                                                                                                   trimmed_arity
                                                                                                   int_body rhs with
                                                                                             | pair ae_rhs rhs' =>
                                                                                               let ae_rhs' :=
                                                                                                 let j_136__ :=
                                                                                                   calledMultipleTimes
                                                                                                   ae_rhs in
                                                                                                 let j_137__ :=
                                                                                                   if safe_arity
                                                                                                      GHC.Base.==
                                                                                                      GHC.Num.fromInteger
                                                                                                      0 : bool
                                                                                                   then ae_rhs
                                                                                                   else j_136__ in
                                                                                                 if called_once : bool
                                                                                                 then ae_rhs
                                                                                                 else j_137__ in
                                                                                               pair true (pair (pair
                                                                                                               (Id.setIdCallArity
                                                                                                               i
                                                                                                               trimmed_arity)
                                                                                                               (Some
                                                                                                               (pair
                                                                                                               (pair
                                                                                                               called_once
                                                                                                               new_arity)
                                                                                                               ae_rhs')))
                                                                                                               rhs')
                                                                                           end in
                                                                                         let j_140__ :=
                                                                                           match mbLastRun with
                                                                                             | Some (pair (pair
                                                                                                          old_called_once
                                                                                                          old_arity)
                                                                                                          _) => if andb
                                                                                                                   (called_once
                                                                                                                   GHC.Base.==
                                                                                                                   old_called_once)
                                                                                                                   (new_arity
                                                                                                                   GHC.Base.==
                                                                                                                   old_arity) : bool
                                                                                                                then pair
                                                                                                                     false
                                                                                                                     (pair
                                                                                                                     (pair
                                                                                                                     i
                                                                                                                     mbLastRun)
                                                                                                                     rhs)
                                                                                                                else j_139__
                                                                                             | _ => j_139__
                                                                                           end in
                                                                                         if andb (VarSet.elemVarSet i
                                                                                                                    int_body)
                                                                                                 (negb
                                                                                                 (UnVarGraph.elemUnVarSet
                                                                                                 i (domRes ae))) : bool
                                                                                         then pair false (pair (pair i
                                                                                                                     None)
                                                                                                               rhs)
                                                                                         else j_140__
                                                                                     end
                                                                                 end in
                                                                             match GHC.List.unzip GHC.Base.$
                                                                                     GHC.Base.map rerun ann_binds with
                                                                               | pair changes ann_binds' =>
                                                                                 let any_change :=
                                                                                   Data.Foldable.or changes in
                                                                                 let j_148__ :=
                                                                                   pair ae (GHC.Base.map
                                                                                        (fun arg_145__ =>
                                                                                          match arg_145__ with
                                                                                            | pair (pair i _) e => pair
                                                                                                                   i e
                                                                                          end) ann_binds') in
                                                                                 if any_change : bool
                                                                                 then fix_ ann_binds'
                                                                                 else j_148__
                                                                             end in
                                                                  match fix_ initial_binds with
                                                                    | pair ae_rhs binds' => let final_ae :=
                                                                                              resDelList
                                                                                              (CoreSyn.bindersOf b)
                                                                                              ae_rhs in
                                                                                            pair final_ae (CoreSyn.Rec
                                                                                                 binds')
                                                                  end
    end.
*)
Definition callArityTopLvl : list Var.Var -> VarSet.VarSet -> list
                             CoreSyn.CoreBind -> (CallArityRes * list CoreSyn.CoreBind)%type :=
  fix callArityTopLvl arg_155__ arg_156__ arg_157__
        := match arg_155__ , arg_156__ , arg_157__ with
             | exported , _ , nil => pair (calledMultipleTimes GHC.Base.$ pair
                                          UnVarGraph.emptyUnVarGraph (VarEnv.mkVarEnv GHC.Base.$ Coq.Lists.List.flat_map
                                          (fun v => cons (pair v (GHC.Num.fromInteger 0)) nil) exported)) nil
             | exported , int1 , cons b bs => let int' := addInterestingBinds int1 b in
                                              let int2 := CoreSyn.bindersOf b in
                                              let exported' :=
                                                Coq.Init.Datatypes.app (GHC.List.filter Var.isExportedId int2)
                                                                       exported in
                                              match callArityTopLvl exported' int' bs with
                                                | pair ae1 bs' => match callArityBind (boringBinds b) ae1 int1 b with
                                                                    | pair ae2 b' => pair ae2 (cons b' bs')
                                                                  end
                                              end
           end.

Definition callArityAnalProgram
    : DynFlags.DynFlags -> CoreSyn.CoreProgram -> CoreSyn.CoreProgram :=
  fun _dflags binds =>
    match callArityTopLvl nil VarSet.emptyVarSet binds with
      | pair _ binds' => binds'
    end.

Definition callArityRHS : CoreSyn.CoreExpr -> CoreSyn.CoreExpr :=
  Data.Tuple.snd GHC.Base.∘ callArityAnal (GHC.Num.fromInteger 0)
  VarSet.emptyVarSet.

(* Unbound variables:
     None Some andb bool callArityBind cons false list negb nil op_zt__ option pair
     true BasicTypes.Arity Control.Arrow.first Control.Arrow.second
     Coq.Init.Datatypes.app Coq.Lists.List.flat_map CoreArity.typeArity CoreSyn.App
     CoreSyn.Case CoreSyn.Cast CoreSyn.Coercion CoreSyn.CoreBind CoreSyn.CoreExpr
     CoreSyn.CoreProgram CoreSyn.Lam CoreSyn.Let CoreSyn.Lit CoreSyn.NonRec
     CoreSyn.Rec CoreSyn.Tick CoreSyn.Type_ CoreSyn.Var CoreSyn.bindersOf
     CoreUtils.exprIsHNF CoreUtils.exprIsTrivial Data.Foldable.any
     Data.Foldable.foldl Data.Foldable.foldr Data.Foldable.length
     Data.Foldable.minimum Data.Foldable.or Data.Tuple.fst Data.Tuple.snd
     Demand.isBotRes Demand.splitStrictSig DynFlags.DynFlags GHC.Base.const
     GHC.Base.map GHC.Base.min GHC.Base.op_z2218U__ GHC.Base.op_zd__
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zl__ GHC.Base.op_zsze__
     GHC.List.filter GHC.List.unzip GHC.Num.op_zm__ GHC.Num.op_zp__ Id.idCallArity
     Id.idStrictness Id.idType Id.setIdCallArity UnVarGraph.UnVarGraph
     UnVarGraph.UnVarSet UnVarGraph.completeBipartiteGraph UnVarGraph.completeGraph
     UnVarGraph.delNode UnVarGraph.delUnVarSet UnVarGraph.elemUnVarSet
     UnVarGraph.emptyUnVarGraph UnVarGraph.neighbors UnVarGraph.unionUnVarGraph
     UnVarGraph.unionUnVarGraphs UnVarGraph.unionUnVarSets UnVarGraph.varEnvDom
     Var.Id Var.Var Var.isExportedId Var.isId VarEnv.VarEnv VarEnv.delVarEnv
     VarEnv.emptyVarEnv VarEnv.lookupVarEnv VarEnv.mkVarEnv VarEnv.plusVarEnv_C
     VarEnv.unitVarEnv VarSet.VarSet VarSet.delVarSet VarSet.delVarSetList
     VarSet.elemVarSet VarSet.emptyVarSet VarSet.extendVarSetList VarSet.mkVarSet
*)
