(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Lists.List.
Require Core.
Require CoreSubst.
Require CoreUtils.
Require Data.Foldable.
Require Data.Maybe.
Require Data.Tuple.
Require FastString.
Require GHC.Base.
Require GHC.Err.
Require GHC.List.
Require GHC.Num.
Require Id.
Require Literal.
Require Panic.
Require Unique.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Definition TrivialArg :=
  Core.CoreArg%type.

Inductive Value : Type
  := DataConApp : Core.DataCon -> list TrivialArg -> Value
  |  LitVal : Literal.Literal -> Value
  |  LamVal : Core.Var -> Core.CoreExpr -> Value
  |  CoercionVal : unit -> Value.

Inductive Step a : Type
  := Error : GHC.Base.String -> Step a
  |  Done : Step a
  |  Mk_Step : a -> Step a.

Inductive StackElem : Type
  := ApplyTo : Core.CoreExpr -> StackElem
  |  Alts : Core.CoreBndr -> list Core.CoreAlt -> StackElem
  |  Update : Core.Var -> StackElem.

Definition Stack :=
  (list StackElem)%type.

Definition Heap :=
  (list (Core.Var * Core.CoreExpr)%type)%type.

Definition Conf :=
  (Heap * Core.CoreExpr * Stack)%type%type.

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
  | (heap , expr, stack ) => Core.core_size expr 
  end.

(* ----------- ----------------------------------- --------------- *)
(* Converted value declarations: *)

Definition valueToExpr : Value -> Core.CoreExpr :=
  fun arg_0__ =>
    match arg_0__ with
    | DataConApp dc args => Core.mkConApp dc args
    | LitVal l => Core.Lit l
    | LamVal v e => Core.Lam v e
    | CoercionVal co => Core.Coercion co
    end.

Definition lookupHeap : Core.Var -> Heap -> option Core.CoreExpr :=
  GHC.List.lookup.

Definition isDataConApp
   : Core.CoreExpr -> option (Core.DataCon * list Core.CoreArg)%type :=
  let fix go arg_0__ arg_1__
            := let j_4__ :=
                 match arg_0__, arg_1__ with
                 | args, Core.App e a => go (cons a args) e
                 | args, Core.Mk_Var v =>
                     match Id.isDataConWorkId_maybe v with
                     | Some dc =>
                         if Core.dataConRepArity dc GHC.Base.== Coq.Lists.List.length args : bool
                         then Some (pair dc args) else
                         None
                     | _ => None
                     end
                 | _, _ => None
                 end in
               match arg_0__, arg_1__ with
               | args, Core.App e a => if Core.isTypeArg a : bool then go args e else j_4__
               | _, _ => j_4__
               end in
  go nil.

Definition initConf : Core.CoreExpr -> Conf :=
  fun e => pair (pair nil e) nil.

Definition in_scope : Heap -> Core.InScopeSet :=
  Core.mkInScopeSet GHC.Base.∘
  (Core.mkVarSet GHC.Base.∘ GHC.Base.map Data.Tuple.fst).

Definition exprIsTrivial' : Core.CoreExpr -> bool :=
  fix exprIsTrivial' arg_0__
        := let j_2__ :=
             match arg_0__ with
             | Core.Cast e _ => exprIsTrivial' e
             | Core.Mk_Var _ => true
             | Core.Lit _ => true
             | Core.Coercion _ => true
             | _ => false
             end in
           match arg_0__ with
           | Core.Tick _ e => exprIsTrivial' e
           | Core.App e a => if Core.isTypeArg a : bool then exprIsTrivial' e else j_2__
           | Core.Lam v e => if negb (Core.isId v) : bool then exprIsTrivial' e else j_2__
           | _ => j_2__
           end.

Definition isValue_maybe : Core.CoreExpr -> option Value :=
  fix isValue_maybe arg_0__
        := let j_6__ :=
             match arg_0__ with
             | Core.Cast e _ => isValue_maybe e
             | Core.Lit l => Some (LitVal l)
             | Core.Coercion c => Some (CoercionVal c)
             | Core.Lam v e => Some (LamVal v e)
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
           | Core.Tick _ e => isValue_maybe e
           | Core.App e a => if Core.isTypeArg a : bool then isValue_maybe e else j_6__
           | Core.Lam v e => if negb (Core.isId v) : bool then isValue_maybe e else j_6__
           | _ => j_6__
           end.

Definition isValue : Core.CoreExpr -> bool :=
  fun e => Data.Maybe.isJust (isValue_maybe e).

Definition etaExpandDCWorker : Core.DataCon -> Core.CoreExpr :=
  fun dc =>
    let params :=
      GHC.List.zipWith (fun n t =>
                          Id.mkSysLocalOrCoVar (FastString.fsLit (GHC.Base.hs_string__ "eta"))
                          (Unique.mkBuiltinUnique n) t) nil (nil) in
    Core.mkLams params (Core.mkConApp dc (GHC.Base.map Core.Mk_Var params)).

Definition addToHeap : Core.Var -> Core.CoreExpr -> Heap -> Heap :=
  fun v e heap =>
    cons (pair v e) (GHC.List.filter ((fun arg_0__ => arg_0__ GHC.Base./= v)
                                      GHC.Base.∘
                                      Data.Tuple.fst) heap).

Definition addManyToHeap
   : list Core.Var -> list Core.CoreExpr -> Heap -> Heap :=
  fun vs es =>
    Data.Foldable.foldr _GHC.Base.∘_ GHC.Base.id (GHC.List.zipWith addToHeap vs es).

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
          match CoreUtils.findAlt (Core.DataAlt dc) alts with
          | Some (pair (pair _ pats) rhs) =>
              let val_pats := GHC.List.filter Core.isId pats in
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
          let fresh := Core.uniqAway (in_scope heap) fresh_tmpl in
          let subst :=
            CoreSubst.extendSubstWithVar (CoreSubst.mkEmptySubst (in_scope heap)) v fresh in
          Mk_Step (pair (pair (addToHeap fresh a heap) (CoreSubst.substExpr Panic.someSDoc
                               subst e)) s)
      | pair (pair heap val) (cons (ApplyTo a) s) =>
          Error (GHC.Base.hs_string__ "non-function applied to argument")
      | pair (pair heap val) (cons (Alts b nil) s) =>
          Error (GHC.Base.hs_string__ "empty case")
      | pair (pair heap val) (cons (Alts b (cons (pair (pair Core.DEFAULT nil) rhs)
         nil)) s) =>
          let subst0 := CoreSubst.mkEmptySubst (in_scope heap) in
          let 'pair subst1 b' := CoreSubst.substBndr subst0 b in
          let heap' := addToHeap b' (valueToExpr val) heap in
          let rhs' := CoreSubst.substExpr Panic.someSDoc subst1 rhs in
          Mk_Step (pair (pair heap' rhs') s)
      | pair (pair heap (LitVal l)) (cons (Alts b alts) s) =>
          let subst0 := CoreSubst.mkEmptySubst (in_scope heap) in
          let 'pair subst1 b' := CoreSubst.substBndr subst0 b in
          match CoreUtils.findAlt (Core.LitAlt l) alts with
          | Some (pair (pair _ nil) rhs) =>
              let heap' := addToHeap b' (Core.Lit l) heap in
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
                        | pair (pair heap (Core.Mk_Var v)) s =>
                            Error (GHC.Base.hs_string__ "unbound variable")
                        | pair (pair heap (Core.App e a)) s =>
                            Mk_Step (pair (pair heap e) (cons (ApplyTo a) s))
                        | pair (pair heap (Core.Let (Core.NonRec v rhs) e)) s =>
                            let subst0 := CoreSubst.mkEmptySubst (in_scope heap) in
                            let 'pair subst1 v' := CoreSubst.substBndr subst0 v in
                            let e' := CoreSubst.substExpr Panic.someSDoc subst1 e in
                            Mk_Step (pair (pair (addToHeap v' rhs heap) e') s)
                        | pair (pair heap (Core.Let (Core.Rec pairs) e)) s =>
                            let 'pair vars rhss := GHC.List.unzip pairs in
                            let subst0 := CoreSubst.mkEmptySubst (in_scope heap) in
                            let 'pair subst1 vars' := CoreSubst.substRecBndrs subst0 vars in
                            let rhss' := GHC.Base.map (CoreSubst.substExpr Panic.someSDoc subst1) rhss in
                            let e' := CoreSubst.substExpr Panic.someSDoc subst1 e in
                            Mk_Step (pair (pair (addManyToHeap vars' rhss' heap) e') s)
                        | pair (pair heap (Core.Case e b _ alts)) s =>
                            Mk_Step (pair (pair heap e) (cons (Alts b alts) s))
                        | pair (pair heap (Core.Type_ _)) s =>
                            Error (GHC.Base.hs_string__ "type expression in control position")
                        | _ => Error (GHC.Base.hs_string__ "Should be unreachable")
                        end in
                      let j_18__ :=
                        match arg_0__ with
                        | pair (pair heap (Core.Mk_Var v)) s =>
                            match lookupHeap v heap with
                            | Some e => Mk_Step (pair (pair heap e) (cons (Update v) s))
                            | _ => j_16__
                            end
                        | _ => j_16__
                        end in
                      let j_20__ :=
                        match arg_0__ with
                        | pair (pair heap (Core.Mk_Var v)) s =>
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
                        | pair (pair heap (Core.Mk_Var v)) s =>
                            match Id.isDataConWorkId_maybe v with
                            | Some dc =>
                                if Bool.Sumbool.sumbool_of_bool (Core.dataConRepArity dc GHC.Base.> #0)
                                then Mk_Step (pair (pair heap (etaExpandDCWorker dc)) s) else
                                j_20__
                            | _ => j_20__
                            end
                        | _ => j_20__
                        end in
                      let j_25__ :=
                        match arg_0__ with
                        | pair (pair heap (Core.Cast e _)) s => step (pair (pair heap e) s)
                        | pair (pair heap e) s =>
                            match isValue_maybe e with
                            | Some val => valStep (pair (pair heap val) s)
                            | _ => j_22__
                            end
                        end in
                      match arg_0__ with
                      | pair (pair heap (Core.Tick _ e)) s => step (pair (pair heap e) s)
                      | pair (pair heap (Core.App e a)) s =>
                          if Bool.Sumbool.sumbool_of_bool (Core.isTypeArg a)
                          then step (pair (pair heap e) s) else
                          j_25__
                      | pair (pair heap (Core.Lam v e)) s =>
                          if Bool.Sumbool.sumbool_of_bool (negb (Core.isId v))
                          then step (pair (pair heap e) s) else
                          j_25__
                      | _ => j_25__
                      end.
Solve Obligations with (solve_step_obligations).

(* Skipping all instances of class `Outputable.Outputable', including
   `GHC.SmallStep.Outputable__StackElem' *)

(* External variables:
     Bool.Sumbool.sumbool_of_bool None Some bool cons false list negb nil op_zt__
     option pair step_measure true tt unit Coq.Lists.List.length Core.App Core.Case
     Core.Cast Core.Coercion Core.CoreAlt Core.CoreArg Core.CoreBndr Core.CoreExpr
     Core.DEFAULT Core.DataAlt Core.DataCon Core.InScopeSet Core.Lam Core.Let
     Core.Lit Core.LitAlt Core.Mk_Var Core.NonRec Core.Rec Core.Tick Core.Type_
     Core.Var Core.dataConRepArity Core.isId Core.isTypeArg Core.mkConApp
     Core.mkInScopeSet Core.mkLams Core.mkVarSet Core.uniqAway CoreSubst.extendSubst
     CoreSubst.extendSubstWithVar CoreSubst.mkEmptySubst CoreSubst.substBndr
     CoreSubst.substBndrs CoreSubst.substExpr CoreSubst.substRecBndrs
     CoreUtils.findAlt Data.Foldable.all Data.Foldable.foldr Data.Maybe.isJust
     Data.Tuple.fst FastString.fsLit GHC.Base.String GHC.Base.id GHC.Base.map
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zg__ GHC.Base.op_zsze__
     GHC.Err.patternFailure GHC.List.filter GHC.List.lookup GHC.List.unzip
     GHC.List.zipWith GHC.Num.fromInteger Id.isDataConWorkId_maybe Id.mkSysLocal
     Id.mkSysLocalOrCoVar Literal.Literal Panic.someSDoc Unique.mkBuiltinUnique
*)
