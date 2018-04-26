(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require CoreSubst.
Require CoreSyn.
Require CoreUtils.
Require Data.Foldable.
Require Data.Maybe.
Require Data.Tuple.
Require DataCon.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require Literal.
Require Panic.
Require Unique.
Require Var.
Require VarEnv.
Require VarSet.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition TrivialArg :=
  CoreSyn.CoreArg%type.

Inductive Value : Type
  := DataConApp : DataCon.DataCon -> list TrivialArg -> Value
  |  LitVal : Literal.Literal -> Value
  |  LamVal : Var.Id -> CoreSyn.CoreExpr -> Value
  |  CoercionVal : unit -> Value.

Inductive Step a : Type
  := Error : GHC.Base.String -> Step a
  |  Done : Step a
  |  Mk_Step : a -> Step a.

Inductive StackElem : Type
  := ApplyTo : CoreSyn.CoreExpr -> StackElem
  |  Alts : CoreSyn.CoreBndr -> list CoreSyn.CoreAlt -> StackElem
  |  Update : Var.Id -> StackElem.

Definition Stack :=
  (list StackElem)%type.

Definition Heap :=
  (list (Var.Var * CoreSyn.CoreExpr)%type)%type.

Definition Conf :=
  (Heap * CoreSyn.CoreExpr * Stack)%type%type.

Arguments Error {_} _.

Arguments Done {_}.

Arguments Mk_Step {_} _.
(* Midamble *)

Instance Default_Step {a} : GHC.Err.Default (Step a) :=
  GHC.Err.Build_Default _ Done.
Instance Default_Value : GHC.Err.Default Value :=
  GHC.Err.Build_Default _ (LitVal GHC.Err.default).
Instance Default_StackElem : GHC.Err.Default StackElem :=
  GHC.Err.Build_Default _ (Update GHC.Err.default).

(* ----------- termination metric for step function --------------- *)

Require Omega.

Ltac termination_by_omega :=
  Coq.Program.Tactics.program_simpl;
  simpl;Omega.omega.

Ltac solve_step_obligations :=
  repeat split; intros; try discriminate; termination_by_omega.

Definition step_measure (conf : Conf) : nat := 
  match conf with 
  | (heap , expr, stack ) => CoreSyn.size_Expr expr 
  end.

(* ----------- ----------------------------------- --------------- *)
(* Converted value declarations: *)

(* Skipping instance Outputable__StackElem of class Outputable *)

Definition addToHeap : Var.Id -> CoreSyn.CoreExpr -> Heap -> Heap :=
  fun v e heap =>
    cons (pair v e) (GHC.List.filter ((fun arg_0__ => arg_0__ GHC.Base./= v)
                                      GHC.Base.∘
                                      Data.Tuple.fst) heap).

Definition addManyToHeap
   : list Var.Id -> list CoreSyn.CoreExpr -> Heap -> Heap :=
  fun vs es =>
    Data.Foldable.foldr _GHC.Base.∘_ GHC.Base.id (GHC.List.zipWith addToHeap vs es).

Definition etaExpandDCWorker : DataCon.DataCon -> CoreSyn.CoreExpr :=
  fun dc =>
    let params :=
      GHC.List.zipWith (fun n t =>
                          Id.mkSysLocalOrCoVar (FastString.fsLit (GHC.Base.hs_string__ "eta"))
                          (Unique.mkBuiltinUnique n) t) nil (nil) in
    CoreSyn.mkLams params (CoreSyn.mkConApp dc (GHC.Base.map CoreSyn.Var params)).

Definition exprIsTrivial' : CoreSyn.CoreExpr -> bool :=
  fix exprIsTrivial' arg_0__
        := let j_2__ :=
             match arg_0__ with
             | CoreSyn.Cast e _ => exprIsTrivial' e
             | CoreSyn.Var _ => true
             | CoreSyn.Lit _ => true
             | CoreSyn.Coercion _ => true
             | _ => false
             end in
           match arg_0__ with
           | CoreSyn.Tick _ e => exprIsTrivial' e
           | CoreSyn.App e a =>
               if CoreSyn.isTypeArg a : bool then exprIsTrivial' e else
               j_2__
           | CoreSyn.Lam v e =>
               if negb (Var.isId v) : bool then exprIsTrivial' e else
               j_2__
           | _ => j_2__
           end.

Definition in_scope : Heap -> VarEnv.InScopeSet :=
  VarEnv.mkInScopeSet GHC.Base.∘
  (VarSet.mkVarSet GHC.Base.∘ GHC.Base.map Data.Tuple.fst).

Definition initConf : CoreSyn.CoreExpr -> Conf :=
  fun e => pair (pair nil e) nil.

Definition isDataConApp
   : CoreSyn.CoreExpr -> option (DataCon.DataCon * list CoreSyn.CoreArg)%type :=
  let fix go arg_0__ arg_1__
            := let j_4__ :=
                 match arg_0__, arg_1__ with
                 | args, CoreSyn.App e a => go (cons a args) e
                 | args, CoreSyn.Var v =>
                     match Id.isDataConWorkId_maybe v with
                     | Some dc =>
                         if DataCon.dataConRepArity dc GHC.Base.== Data.Foldable.length args : bool
                         then Some (pair dc args) else
                         None
                     | _ => None
                     end
                 | _, _ => None
                 end in
               match arg_0__, arg_1__ with
               | args, CoreSyn.App e a =>
                   if CoreSyn.isTypeArg a : bool then go args e else
                   j_4__
               | _, _ => j_4__
               end in
  go nil.

Definition isValue_maybe : CoreSyn.CoreExpr -> option Value :=
  fix isValue_maybe arg_0__
        := let j_6__ :=
             match arg_0__ with
             | CoreSyn.Cast e _ => isValue_maybe e
             | CoreSyn.Lit l => Some (LitVal l)
             | CoreSyn.Coercion c => Some (CoercionVal c)
             | CoreSyn.Lam v e => Some (LamVal v e)
             | e =>
                 match isDataConApp e with
                 | Some (pair dc args) =>
                     if Data.Foldable.all exprIsTrivial' args : bool
                     then Some (DataConApp dc args) else
                     None
                 | _ => None
                 end
             end in
           match arg_0__ with
           | CoreSyn.Tick _ e => isValue_maybe e
           | CoreSyn.App e a =>
               if CoreSyn.isTypeArg a : bool then isValue_maybe e else
               j_6__
           | CoreSyn.Lam v e => if negb (Var.isId v) : bool then isValue_maybe e else j_6__
           | _ => j_6__
           end.

Definition isValue : CoreSyn.CoreExpr -> bool :=
  fun e => Data.Maybe.isJust (isValue_maybe e).

Definition lookupHeap : Var.Id -> Heap -> option CoreSyn.CoreExpr :=
  GHC.List.lookup.

Definition valueToExpr : Value -> CoreSyn.CoreExpr :=
  fun arg_0__ =>
    match arg_0__ with
    | DataConApp dc args => CoreSyn.mkConApp dc args
    | LitVal l => CoreSyn.Lit l
    | LamVal v e => CoreSyn.Lam v e
    | CoercionVal co => CoreSyn.Coercion co
    end.

Definition valStep : (Heap * Value * Stack)%type -> Step Conf :=
  fun arg_0__ =>
    let j_3__ :=
      match arg_0__ with
      | pair (pair heap (DataConApp dc args as val)) (cons (Alts b alts) s) =>
          Error (GHC.Base.hs_string__ "data con not found in alts")
      | pair (pair heap val) (cons (Alts b alts) s) =>
          Error (GHC.Base.hs_string__ "non-datacon scrutinized")
      | _ => GHC.Err.patternFailure
      end in
    let j_12__ :=
      match arg_0__ with
      | pair (pair heap (LitVal l)) (cons (Alts b alts) s) =>
          Error (GHC.Base.hs_string__ "literal not found in alts")
      | pair (pair heap (DataConApp dc args as val)) (cons (Alts b alts) s) =>
          let subst0 := CoreSubst.mkEmptySubst (in_scope heap) in
          let 'pair subst1 b' := CoreSubst.substBndr subst0 b in
          match CoreUtils.findAlt (CoreSyn.DataAlt dc) alts with
          | Some (pair (pair _ pats) rhs) =>
              let val_pats := GHC.List.filter Var.isId pats in
              let 'pair subst2 pats' := CoreSubst.substBndrs subst1 val_pats in
              let rhs' := CoreSubst.substExpr Panic.someSDoc subst2 rhs in
              let heap' := addManyToHeap pats' args (addToHeap b' (valueToExpr val) heap) in
              Mk_Step (pair (pair heap' rhs') s)
          | _ => j_3__
          end
      | _ => j_3__
      end in
    let j_29__ :=
      match arg_0__ with
      | pair (pair heap (LamVal v e)) (cons (ApplyTo a) s) =>
          let fresh_tmpl :=
            Id.mkSysLocal (FastString.fsLit (GHC.Base.hs_string__ "arg"))
            (Unique.mkBuiltinUnique #1) (tt) in
          let fresh := VarEnv.uniqAway (in_scope heap) fresh_tmpl in
          let subst :=
            CoreSubst.extendSubstWithVar (CoreSubst.mkEmptySubst (in_scope heap)) v fresh in
          Mk_Step (pair (pair (addToHeap fresh a heap) (CoreSubst.substExpr Panic.someSDoc
                               subst e)) s)
      | pair (pair heap val) (cons (ApplyTo a) s) =>
          Error (GHC.Base.hs_string__ "non-function applied to argument")
      | pair (pair heap val) (cons (Alts b nil) s) =>
          Error (GHC.Base.hs_string__ "empty case")
      | pair (pair heap val) (cons (Alts b (cons (pair (pair CoreSyn.DEFAULT nil) rhs)
         nil)) s) =>
          let subst0 := CoreSubst.mkEmptySubst (in_scope heap) in
          let 'pair subst1 b' := CoreSubst.substBndr subst0 b in
          let heap' := addToHeap b' (valueToExpr val) heap in
          let rhs' := CoreSubst.substExpr Panic.someSDoc subst1 rhs in
          Mk_Step (pair (pair heap' rhs') s)
      | pair (pair heap (LitVal l)) (cons (Alts b alts) s) =>
          let subst0 := CoreSubst.mkEmptySubst (in_scope heap) in
          let 'pair subst1 b' := CoreSubst.substBndr subst0 b in
          match CoreUtils.findAlt (CoreSyn.LitAlt l) alts with
          | Some (pair (pair _ nil) rhs) =>
              let heap' := addToHeap b' (CoreSyn.Lit l) heap in
              let rhs' := CoreSubst.substExpr Panic.someSDoc subst1 rhs in
              Mk_Step (pair (pair heap' rhs') s)
          | _ => j_12__
          end
      | _ => j_12__
      end in
    match arg_0__ with
    | pair (pair heap val) nil => Done
    | pair (pair heap val) (cons (Update v) s) =>
        Mk_Step (pair (pair (addToHeap v (valueToExpr val) heap) (valueToExpr val)) s)
    | pair (pair heap (LamVal v e)) (cons (ApplyTo a) s) =>
        let subst :=
          CoreSubst.extendSubst (CoreSubst.mkEmptySubst (in_scope heap)) v a in
        if exprIsTrivial' a : bool
        then Mk_Step (pair (pair heap (CoreSubst.substExpr Panic.someSDoc subst e))
                           s) else
        j_29__
    | _ => j_29__
    end.

Program Fixpoint step (arg_0__ : Conf) {measure (step_measure arg_0__)} : Step
                                                                          Conf
                   := let j_16__ :=
                        match arg_0__ with
                        | pair (pair heap (CoreSyn.Var v)) s =>
                            Error (GHC.Base.hs_string__ "unbound variable")
                        | pair (pair heap (CoreSyn.App e a)) s =>
                            Mk_Step (pair (pair heap e) (cons (ApplyTo a) s))
                        | pair (pair heap (CoreSyn.Let (CoreSyn.NonRec v rhs) e)) s =>
                            let subst0 := CoreSubst.mkEmptySubst (in_scope heap) in
                            let 'pair subst1 v' := CoreSubst.substBndr subst0 v in
                            let e' := CoreSubst.substExpr Panic.someSDoc subst1 e in
                            Mk_Step (pair (pair (addToHeap v' rhs heap) e') s)
                        | pair (pair heap (CoreSyn.Let (CoreSyn.Rec pairs) e)) s =>
                            let 'pair vars rhss := GHC.List.unzip pairs in
                            let subst0 := CoreSubst.mkEmptySubst (in_scope heap) in
                            let 'pair subst1 vars' := CoreSubst.substRecBndrs subst0 vars in
                            let rhss' := GHC.Base.map (CoreSubst.substExpr Panic.someSDoc subst1) rhss in
                            let e' := CoreSubst.substExpr Panic.someSDoc subst1 e in
                            Mk_Step (pair (pair (addManyToHeap vars' rhss' heap) e') s)
                        | pair (pair heap (CoreSyn.Case e b _ alts)) s =>
                            Mk_Step (pair (pair heap e) (cons (Alts b alts) s))
                        | pair (pair heap (CoreSyn.Type_ _)) s =>
                            Error (GHC.Base.hs_string__ "type expression in control position")
                        | _ => Error (GHC.Base.hs_string__ "Should be unreachable")
                        end in
                      let j_18__ :=
                        match arg_0__ with
                        | pair (pair heap (CoreSyn.Var v)) s =>
                            match lookupHeap v heap with
                            | Some e => Mk_Step (pair (pair heap e) (cons (Update v) s))
                            | _ => j_16__
                            end
                        | _ => j_16__
                        end in
                      let j_20__ :=
                        match arg_0__ with
                        | pair (pair heap (CoreSyn.Var v)) s =>
                            match lookupHeap v heap with
                            | Some e =>
                                if Bool.Sumbool.sumbool_of_bool (isValue e)
                                then Mk_Step (pair (pair heap e) s) else
                                j_18__
                            | _ => j_18__
                            end
                        | _ => j_18__
                        end in
                      let j_22__ :=
                        match arg_0__ with
                        | pair (pair heap (CoreSyn.Var v)) s =>
                            match Id.isDataConWorkId_maybe v with
                            | Some dc =>
                                if Bool.Sumbool.sumbool_of_bool (DataCon.dataConRepArity dc GHC.Base.> #0)
                                then Mk_Step (pair (pair heap (etaExpandDCWorker dc)) s) else
                                j_20__
                            | _ => j_20__
                            end
                        | _ => j_20__
                        end in
                      let j_25__ :=
                        match arg_0__ with
                        | pair (pair heap (CoreSyn.Cast e _)) s => step (pair (pair heap e) s)
                        | pair (pair heap e) s =>
                            match isValue_maybe e with
                            | Some val => valStep (pair (pair heap val) s)
                            | _ => j_22__
                            end
                        end in
                      match arg_0__ with
                      | pair (pair heap (CoreSyn.Tick _ e)) s => step (pair (pair heap e) s)
                      | pair (pair heap (CoreSyn.App e a)) s =>
                          if Bool.Sumbool.sumbool_of_bool (CoreSyn.isTypeArg a)
                          then step (pair (pair heap e) s) else
                          j_25__
                      | pair (pair heap (CoreSyn.Lam v e)) s =>
                          if Bool.Sumbool.sumbool_of_bool (negb (Var.isId v))
                          then step (pair (pair heap e) s) else
                          j_25__
                      | _ => j_25__
                      end.
Solve Obligations with (solve_step_obligations).

(* External variables:
     Bool.Sumbool.sumbool_of_bool None Some bool cons false list negb nil op_zt__
     option pair step_measure true tt unit CoreSubst.extendSubst
     CoreSubst.extendSubstWithVar CoreSubst.mkEmptySubst CoreSubst.substBndr
     CoreSubst.substBndrs CoreSubst.substExpr CoreSubst.substRecBndrs CoreSyn.App
     CoreSyn.Case CoreSyn.Cast CoreSyn.Coercion CoreSyn.CoreAlt CoreSyn.CoreArg
     CoreSyn.CoreBndr CoreSyn.CoreExpr CoreSyn.DEFAULT CoreSyn.DataAlt CoreSyn.Lam
     CoreSyn.Let CoreSyn.Lit CoreSyn.LitAlt CoreSyn.NonRec CoreSyn.Rec CoreSyn.Tick
     CoreSyn.Type_ CoreSyn.Var CoreSyn.isTypeArg CoreSyn.mkConApp CoreSyn.mkLams
     CoreUtils.findAlt Data.Foldable.all Data.Foldable.foldr Data.Foldable.length
     Data.Maybe.isJust Data.Tuple.fst DataCon.DataCon DataCon.dataConRepArity
     FastString.fsLit GHC.Base.String GHC.Base.id GHC.Base.map GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zsze__ GHC.Err.patternFailure
     GHC.List.filter GHC.List.lookup GHC.List.unzip GHC.List.zipWith
     GHC.Num.fromInteger Id.isDataConWorkId_maybe Id.mkSysLocal Id.mkSysLocalOrCoVar
     Literal.Literal Panic.someSDoc Unique.mkBuiltinUnique Var.Id Var.Var Var.isId
     VarEnv.InScopeSet VarEnv.mkInScopeSet VarEnv.uniqAway VarSet.mkVarSet
*)
