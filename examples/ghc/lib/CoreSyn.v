(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Parameter error : forall {a}, a.

(* Converted imports: *)

Require BasicTypes.
Require DataCon.
Require DynFlags.
Require GHC.Base.
Require GHC.Num.
Require Literal.
Require Module.
Require Name.
Require NameEnv.
Require OccName.
Require Var.
Require VarEnv.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive UnfoldingSource : Type := InlineRhs : UnfoldingSource
                                 |  InlineStable : UnfoldingSource
                                 |  InlineCompulsory : UnfoldingSource.

Inductive UnfoldingGuidance : Type := UnfWhen
                                     : BasicTypes.Arity -> bool -> bool -> UnfoldingGuidance
                                   |  UnfIfGoodArgs : list
                                                      GHC.Num.Int -> GHC.Num.Int -> GHC.Num.Int -> UnfoldingGuidance
                                   |  UnfNever : UnfoldingGuidance.

Inductive TickishScoping : Type := NoScope : TickishScoping
                                |  SoftScope : TickishScoping
                                |  CostCentreScope : TickishScoping.

Inductive TickishPlacement : Type := PlaceRuntime : TickishPlacement
                                  |  PlaceNonLam : TickishPlacement
                                  |  PlaceCostCentre : TickishPlacement.

Inductive Tickish (id : Type) : Type := Mk_Tickish_Dummy.

Inductive IsOrphan : Type := Mk_IsOrphan : IsOrphan
                          |  NotOrphan : OccName.OccName -> IsOrphan.

Definition CoreBndr :=
  Var.Var%type.

Inductive TaggedBndr t : Type := TB : CoreBndr -> t -> TaggedBndr t.

Inductive AltCon : Type := DataAlt : DataCon.DataCon -> AltCon
                        |  LitAlt : Literal.Literal -> AltCon
                        |  DEFAULT : AltCon.

Inductive AnnAlt__raw : Type :=.

Reserved Notation "'AnnAlt'".

Inductive AnnExpr__raw : Type :=.

Reserved Notation "'AnnExpr'".

Inductive AnnExpr' bndr annot : Type := AnnVar : Var.Id -> AnnExpr' bndr annot
                                     |  AnnLit : Literal.Literal -> AnnExpr' bndr annot
                                     |  AnnLam : bndr -> (AnnExpr bndr annot) -> AnnExpr' bndr annot
                                     |  AnnApp : (AnnExpr bndr annot) -> (AnnExpr bndr annot) -> AnnExpr' bndr annot
                                     |  AnnCase : (AnnExpr bndr annot) -> bndr -> unit -> list (AnnAlt bndr
                                                                                               annot) -> AnnExpr' bndr
                                                                                                                  annot
                                     |  AnnLet : (AnnBind bndr annot) -> (AnnExpr bndr annot) -> AnnExpr' bndr annot
                                     |  AnnCast : (AnnExpr bndr annot) -> (annot * unit)%type -> AnnExpr' bndr annot
                                     |  AnnTick : (Tickish Var.Id) -> (AnnExpr bndr annot) -> AnnExpr' bndr annot
                                     |  AnnType : unit -> AnnExpr' bndr annot
                                     |  AnnCoercion : unit -> AnnExpr' bndr annot
with AnnBind bndr annot : Type := AnnNonRec : bndr -> (AnnExpr bndr
                                              annot) -> AnnBind bndr annot
                               |  AnnRec : list (bndr * AnnExpr bndr annot)%type -> AnnBind bndr annot
where "'AnnExpr'" := (GHC.Base.Synonym AnnExpr__raw (fun bndr_ annot_ =>
                                         (annot_ * AnnExpr' bndr_ annot_)%type%type))
and   "'AnnAlt'" := (GHC.Base.Synonym AnnAlt__raw (fun bndr_ annot_ =>
                                        (AltCon * list bndr_ * AnnExpr bndr_ annot_)%type%type)).

Inductive Alt__raw : Type :=.

Reserved Notation "'Alt'".

Inductive Arg__raw : Type :=.

Reserved Notation "'Arg'".

Inductive Expr b : Type := Var : Var.Id -> Expr b
                        |  Lit : Literal.Literal -> Expr b
                        |  App : (Expr b) -> (Arg b) -> Expr b
                        |  Lam : b -> (Expr b) -> Expr b
                        |  Let : (Bind b) -> (Expr b) -> Expr b
                        |  Case : (Expr b) -> b -> unit -> list (Alt b) -> Expr b
                        |  Cast : (Expr b) -> unit -> Expr b
                        |  Tick : (Tickish Var.Id) -> (Expr b) -> Expr b
                        |  Type_ : unit -> Expr b
                        |  Coercion : unit -> Expr b
with Bind b : Type := NonRec : b -> (Expr b) -> Bind b
                   |  Rec : list (b * (Expr b))%type -> Bind b
where "'Arg'" := (GHC.Base.Synonym Arg__raw Expr%type)
and   "'Alt'" := (GHC.Base.Synonym Alt__raw (fun b_ =>
                                     (AltCon * list b_ * Expr b_)%type%type)).

Definition CoreAlt :=
  (Alt CoreBndr)%type.

Definition CoreArg :=
  (Arg CoreBndr)%type.

Definition TaggedArg t :=
  (Arg (TaggedBndr t))%type.

Definition CoreBind :=
  (Bind CoreBndr)%type.

Definition CoreProgram :=
  (list CoreBind)%type.

Definition TaggedBind t :=
  (Bind (TaggedBndr t))%type.

Definition CoreExpr :=
  (Expr CoreBndr)%type.

Inductive CoreVect : Type := Vect : Var.Id -> CoreExpr -> CoreVect
                          |  NoVect : Var.Id -> CoreVect
                          |  VectType : bool -> unit -> (option unit) -> CoreVect
                          |  VectClass : unit -> CoreVect
                          |  VectInst : Var.Id -> CoreVect.

Inductive Unfolding : Type := NoUnfolding : Unfolding
                           |  OtherCon : list AltCon -> Unfolding
                           |  DFunUnfolding : list Var.Var -> DataCon.DataCon -> list CoreExpr -> Unfolding
                           |  CoreUnfolding
                             : CoreExpr -> UnfoldingSource -> bool -> bool -> bool -> bool -> bool -> UnfoldingGuidance -> Unfolding.

Definition IdUnfoldingFun :=
  (Var.Id -> Unfolding)%type.

Definition InScopeEnv :=
  (VarEnv.InScopeSet * IdUnfoldingFun)%type%type.

Definition RuleFun :=
  (DynFlags.DynFlags -> InScopeEnv -> Var.Id -> list CoreExpr -> option
  CoreExpr)%type.

Inductive CoreRule : Type := Rule
                            : BasicTypes.RuleName -> BasicTypes.Activation -> Name.Name -> list (option
                                                                                                Name.Name) -> list
                              CoreBndr -> list
                              CoreExpr -> CoreExpr -> bool -> Module.Module -> IsOrphan -> bool -> CoreRule
                          |  BuiltinRule
                            : BasicTypes.RuleName -> Name.Name -> GHC.Num.Int -> RuleFun -> CoreRule.

Definition RuleBase :=
  (NameEnv.NameEnv (list CoreRule))%type.

Inductive RuleEnv : Type := Mk_RuleEnv
                           : RuleBase -> Module.ModuleSet -> RuleEnv.

Definition TaggedExpr t :=
  (Expr (TaggedBndr t))%type.

Definition TaggedAlt t :=
  (Alt (TaggedBndr t))%type.

Arguments TB {_} _ _.

Arguments AnnVar {_} {_} _.

Arguments AnnLit {_} {_} _.

Arguments AnnLam {_} {_} _ _.

Arguments AnnApp {_} {_} _ _.

Arguments AnnCase {_} {_} _ _ _ _.

Arguments AnnLet {_} {_} _ _.

Arguments AnnCast {_} {_} _ _.

Arguments AnnTick {_} {_} _ _.

Arguments AnnType {_} {_} _.

Arguments AnnCoercion {_} {_} _.

Arguments AnnNonRec {_} {_} _ _.

Arguments AnnRec {_} {_} _.

Arguments Var {_} _.

Arguments Lit {_} _.

Arguments App {_} _ _.

Arguments Lam {_} _ _.

Arguments Let {_} _ _.

Arguments Case {_} _ _ _ _.

Arguments Cast {_} _ _.

Arguments Tick {_} _ _.

Arguments Type_ {_} _.

Arguments Coercion {_} _.

Arguments NonRec {_} _ _.

Arguments Rec {_} _.

Definition ug_args (arg_0__ : UnfoldingGuidance) :=
  match arg_0__ with
    | UnfWhen _ _ _ => error (GHC.Base.hs_string__
                             "Partial record selector: field `ug_args' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
    | UnfIfGoodArgs ug_args _ _ => ug_args
    | UnfNever => error (GHC.Base.hs_string__
                        "Partial record selector: field `ug_args' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_arity (arg_1__ : UnfoldingGuidance) :=
  match arg_1__ with
    | UnfWhen ug_arity _ _ => ug_arity
    | UnfIfGoodArgs _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ug_arity' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
    | UnfNever => error (GHC.Base.hs_string__
                        "Partial record selector: field `ug_arity' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_boring_ok (arg_2__ : UnfoldingGuidance) :=
  match arg_2__ with
    | UnfWhen _ _ ug_boring_ok => ug_boring_ok
    | UnfIfGoodArgs _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ug_boring_ok' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
    | UnfNever => error (GHC.Base.hs_string__
                        "Partial record selector: field `ug_boring_ok' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_res (arg_3__ : UnfoldingGuidance) :=
  match arg_3__ with
    | UnfWhen _ _ _ => error (GHC.Base.hs_string__
                             "Partial record selector: field `ug_res' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
    | UnfIfGoodArgs _ _ ug_res => ug_res
    | UnfNever => error (GHC.Base.hs_string__
                        "Partial record selector: field `ug_res' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_size (arg_4__ : UnfoldingGuidance) :=
  match arg_4__ with
    | UnfWhen _ _ _ => error (GHC.Base.hs_string__
                             "Partial record selector: field `ug_size' has no match in constructor `UnfWhen' of type `UnfoldingGuidance'")
    | UnfIfGoodArgs _ ug_size _ => ug_size
    | UnfNever => error (GHC.Base.hs_string__
                        "Partial record selector: field `ug_size' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition ug_unsat_ok (arg_5__ : UnfoldingGuidance) :=
  match arg_5__ with
    | UnfWhen _ ug_unsat_ok _ => ug_unsat_ok
    | UnfIfGoodArgs _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ug_unsat_ok' has no match in constructor `UnfIfGoodArgs' of type `UnfoldingGuidance'")
    | UnfNever => error (GHC.Base.hs_string__
                        "Partial record selector: field `ug_unsat_ok' has no match in constructor `UnfNever' of type `UnfoldingGuidance'")
  end.

Definition df_args (arg_6__ : Unfolding) :=
  match arg_6__ with
    | NoUnfolding => error (GHC.Base.hs_string__
                           "Partial record selector: field `df_args' has no match in constructor `NoUnfolding' of type `Unfolding'")
    | OtherCon _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `df_args' has no match in constructor `OtherCon' of type `Unfolding'")
    | DFunUnfolding _ _ df_args => df_args
    | CoreUnfolding _ _ _ _ _ _ _ _ => error (GHC.Base.hs_string__
                                             "Partial record selector: field `df_args' has no match in constructor `CoreUnfolding' of type `Unfolding'")
  end.

Definition df_bndrs (arg_7__ : Unfolding) :=
  match arg_7__ with
    | NoUnfolding => error (GHC.Base.hs_string__
                           "Partial record selector: field `df_bndrs' has no match in constructor `NoUnfolding' of type `Unfolding'")
    | OtherCon _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `df_bndrs' has no match in constructor `OtherCon' of type `Unfolding'")
    | DFunUnfolding df_bndrs _ _ => df_bndrs
    | CoreUnfolding _ _ _ _ _ _ _ _ => error (GHC.Base.hs_string__
                                             "Partial record selector: field `df_bndrs' has no match in constructor `CoreUnfolding' of type `Unfolding'")
  end.

Definition df_con (arg_8__ : Unfolding) :=
  match arg_8__ with
    | NoUnfolding => error (GHC.Base.hs_string__
                           "Partial record selector: field `df_con' has no match in constructor `NoUnfolding' of type `Unfolding'")
    | OtherCon _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `df_con' has no match in constructor `OtherCon' of type `Unfolding'")
    | DFunUnfolding _ df_con _ => df_con
    | CoreUnfolding _ _ _ _ _ _ _ _ => error (GHC.Base.hs_string__
                                             "Partial record selector: field `df_con' has no match in constructor `CoreUnfolding' of type `Unfolding'")
  end.

Definition uf_expandable (arg_9__ : Unfolding) :=
  match arg_9__ with
    | NoUnfolding => error (GHC.Base.hs_string__
                           "Partial record selector: field `uf_expandable' has no match in constructor `NoUnfolding' of type `Unfolding'")
    | OtherCon _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `uf_expandable' has no match in constructor `OtherCon' of type `Unfolding'")
    | DFunUnfolding _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `uf_expandable' has no match in constructor `DFunUnfolding' of type `Unfolding'")
    | CoreUnfolding _ _ _ _ _ _ uf_expandable _ => uf_expandable
  end.

Definition uf_guidance (arg_10__ : Unfolding) :=
  match arg_10__ with
    | NoUnfolding => error (GHC.Base.hs_string__
                           "Partial record selector: field `uf_guidance' has no match in constructor `NoUnfolding' of type `Unfolding'")
    | OtherCon _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `uf_guidance' has no match in constructor `OtherCon' of type `Unfolding'")
    | DFunUnfolding _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `uf_guidance' has no match in constructor `DFunUnfolding' of type `Unfolding'")
    | CoreUnfolding _ _ _ _ _ _ _ uf_guidance => uf_guidance
  end.

Definition uf_is_conlike (arg_11__ : Unfolding) :=
  match arg_11__ with
    | NoUnfolding => error (GHC.Base.hs_string__
                           "Partial record selector: field `uf_is_conlike' has no match in constructor `NoUnfolding' of type `Unfolding'")
    | OtherCon _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `uf_is_conlike' has no match in constructor `OtherCon' of type `Unfolding'")
    | DFunUnfolding _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `uf_is_conlike' has no match in constructor `DFunUnfolding' of type `Unfolding'")
    | CoreUnfolding _ _ _ _ uf_is_conlike _ _ _ => uf_is_conlike
  end.

Definition uf_is_top (arg_12__ : Unfolding) :=
  match arg_12__ with
    | NoUnfolding => error (GHC.Base.hs_string__
                           "Partial record selector: field `uf_is_top' has no match in constructor `NoUnfolding' of type `Unfolding'")
    | OtherCon _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `uf_is_top' has no match in constructor `OtherCon' of type `Unfolding'")
    | DFunUnfolding _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `uf_is_top' has no match in constructor `DFunUnfolding' of type `Unfolding'")
    | CoreUnfolding _ _ uf_is_top _ _ _ _ _ => uf_is_top
  end.

Definition uf_is_value (arg_13__ : Unfolding) :=
  match arg_13__ with
    | NoUnfolding => error (GHC.Base.hs_string__
                           "Partial record selector: field `uf_is_value' has no match in constructor `NoUnfolding' of type `Unfolding'")
    | OtherCon _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `uf_is_value' has no match in constructor `OtherCon' of type `Unfolding'")
    | DFunUnfolding _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `uf_is_value' has no match in constructor `DFunUnfolding' of type `Unfolding'")
    | CoreUnfolding _ _ _ uf_is_value _ _ _ _ => uf_is_value
  end.

Definition uf_is_work_free (arg_14__ : Unfolding) :=
  match arg_14__ with
    | NoUnfolding => error (GHC.Base.hs_string__
                           "Partial record selector: field `uf_is_work_free' has no match in constructor `NoUnfolding' of type `Unfolding'")
    | OtherCon _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `uf_is_work_free' has no match in constructor `OtherCon' of type `Unfolding'")
    | DFunUnfolding _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `uf_is_work_free' has no match in constructor `DFunUnfolding' of type `Unfolding'")
    | CoreUnfolding _ _ _ _ _ uf_is_work_free _ _ => uf_is_work_free
  end.

Definition uf_src (arg_15__ : Unfolding) :=
  match arg_15__ with
    | NoUnfolding => error (GHC.Base.hs_string__
                           "Partial record selector: field `uf_src' has no match in constructor `NoUnfolding' of type `Unfolding'")
    | OtherCon _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `uf_src' has no match in constructor `OtherCon' of type `Unfolding'")
    | DFunUnfolding _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `uf_src' has no match in constructor `DFunUnfolding' of type `Unfolding'")
    | CoreUnfolding _ uf_src _ _ _ _ _ _ => uf_src
  end.

Definition uf_tmpl (arg_16__ : Unfolding) :=
  match arg_16__ with
    | NoUnfolding => error (GHC.Base.hs_string__
                           "Partial record selector: field `uf_tmpl' has no match in constructor `NoUnfolding' of type `Unfolding'")
    | OtherCon _ => error (GHC.Base.hs_string__
                          "Partial record selector: field `uf_tmpl' has no match in constructor `OtherCon' of type `Unfolding'")
    | DFunUnfolding _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `uf_tmpl' has no match in constructor `DFunUnfolding' of type `Unfolding'")
    | CoreUnfolding uf_tmpl _ _ _ _ _ _ _ => uf_tmpl
  end.

Definition ru_act (arg_17__ : CoreRule) :=
  match arg_17__ with
    | Rule _ ru_act _ _ _ _ _ _ _ _ _ => ru_act
    | BuiltinRule _ _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ru_act' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_args (arg_18__ : CoreRule) :=
  match arg_18__ with
    | Rule _ _ _ _ _ ru_args _ _ _ _ _ => ru_args
    | BuiltinRule _ _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ru_args' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_auto (arg_19__ : CoreRule) :=
  match arg_19__ with
    | Rule _ _ _ _ _ _ _ ru_auto _ _ _ => ru_auto
    | BuiltinRule _ _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ru_auto' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_bndrs (arg_20__ : CoreRule) :=
  match arg_20__ with
    | Rule _ _ _ _ ru_bndrs _ _ _ _ _ _ => ru_bndrs
    | BuiltinRule _ _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ru_bndrs' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_fn (arg_21__ : CoreRule) :=
  match arg_21__ with
    | Rule _ _ ru_fn _ _ _ _ _ _ _ _ => ru_fn
    | BuiltinRule _ ru_fn _ _ => ru_fn
  end.

Definition ru_local (arg_22__ : CoreRule) :=
  match arg_22__ with
    | Rule _ _ _ _ _ _ _ _ _ _ ru_local => ru_local
    | BuiltinRule _ _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ru_local' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_name (arg_23__ : CoreRule) :=
  match arg_23__ with
    | Rule ru_name _ _ _ _ _ _ _ _ _ _ => ru_name
    | BuiltinRule ru_name _ _ _ => ru_name
  end.

Definition ru_nargs (arg_24__ : CoreRule) :=
  match arg_24__ with
    | Rule _ _ _ _ _ _ _ _ _ _ _ => error (GHC.Base.hs_string__
                                          "Partial record selector: field `ru_nargs' has no match in constructor `Rule' of type `CoreRule'")
    | BuiltinRule _ _ ru_nargs _ => ru_nargs
  end.

Definition ru_origin (arg_25__ : CoreRule) :=
  match arg_25__ with
    | Rule _ _ _ _ _ _ _ _ ru_origin _ _ => ru_origin
    | BuiltinRule _ _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ru_origin' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_orphan (arg_26__ : CoreRule) :=
  match arg_26__ with
    | Rule _ _ _ _ _ _ _ _ _ ru_orphan _ => ru_orphan
    | BuiltinRule _ _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ru_orphan' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_rhs (arg_27__ : CoreRule) :=
  match arg_27__ with
    | Rule _ _ _ _ _ _ ru_rhs _ _ _ _ => ru_rhs
    | BuiltinRule _ _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ru_rhs' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_rough (arg_28__ : CoreRule) :=
  match arg_28__ with
    | Rule _ _ _ ru_rough _ _ _ _ _ _ _ => ru_rough
    | BuiltinRule _ _ _ _ => error (GHC.Base.hs_string__
                                   "Partial record selector: field `ru_rough' has no match in constructor `BuiltinRule' of type `CoreRule'")
  end.

Definition ru_try (arg_29__ : CoreRule) :=
  match arg_29__ with
    | Rule _ _ _ _ _ _ _ _ _ _ _ => error (GHC.Base.hs_string__
                                          "Partial record selector: field `ru_try' has no match in constructor `Rule' of type `CoreRule'")
    | BuiltinRule _ _ _ ru_try => ru_try
  end.

Definition re_base (arg_30__ : RuleEnv) :=
  match arg_30__ with
    | Mk_RuleEnv re_base _ => re_base
  end.

Definition re_visible_orphs (arg_31__ : RuleEnv) :=
  match arg_31__ with
    | Mk_RuleEnv _ re_visible_orphs => re_visible_orphs
  end.
(* Midamble *)

(*
Fixpoint deAnnotate' {bndr} {annot} (ae : AnnExpr' bndr annot)
         {struct ae} : Expr bndr :=
    match ae with
      | AnnType t => Type_ t
      | AnnCoercion co => Coercion co
      | AnnVar v => Var v
      | AnnLit lit => Lit lit
      | AnnLam binder body => Lam binder (deAnnotate body)
      | AnnApp fun_ arg => App (deAnnotate fun_) (deAnnotate arg)
      | AnnCast e (pair _ co) => Cast (deAnnotate e) co
      | AnnTick tick body => Tick tick (deAnnotate body)
      | AnnLet bind body =>
        Let (deAnnBind bind) (deAnnotate body)
      | AnnCase scrut v t alts =>
        Case (deAnnotate scrut) v t
             (List.map deAnnAlt alts)
    end
with deAnnotate {bndr} {annot} (ae : AnnExpr bndr annot) {struct ae} : Expr bndr :=
   match ae with | pair _ e => deAnnotate' e end
with deAnnAlt {bndr} {annot} (ae : AnnAlt bndr annot) {struct ae}: Alt bndr :=
   match ae with
      | pair (pair con args) rhs => pair (pair con args) (deAnnotate rhs)
    end
with deAnnBind {bndr} {annot} (ae : AnnBind bndr annot) {struct ae} : Bind bndr :=
       match ae with
       | AnnNonRec var rhs => NonRec var (deAnnotate rhs)
       | AnnRec pairs => Rec (Coq.Lists.List.flat_map
                               ( fun arg_53__ =>
                                   match arg_53__ with
                                   | pair v rhs => cons (pair v (deAnnotate rhs)) nil
                                   end )
                               pairs)
       end.
*)

(* One way to resolve the fixpoint *)
(*
Fixpoint collectAnnArgs_go {b}{a}(expr : AnnExpr' b a) g as_ :=
  match expr with
    | AnnApp f a => collectAnnArgs_go (snd f) (fst f) (cons a as_)
    | e          => ((g,e), as_)
  end.

Definition collectAnnArgs {b}{a} :
  AnnExpr b a -> (AnnExpr b a * list (AnnExpr b a))%type :=
  fun expr => collectAnnArgs_go (snd expr) (fst expr) nil.
*)
(* Converted value declarations: *)

(* Translating `instance Binary.Binary CoreSyn.IsOrphan' failed: OOPS! Cannot
   find information for class Qualified "Binary" "Binary" unsupported *)

(* Translating `instance Outputable.Outputable CoreSyn.AltCon' failed: OOPS!
   Cannot find information for class Qualified "Outputable" "Outputable"
   unsupported *)

(* Translating `instance forall {b}, forall `{Outputable.Outputable b},
   Outputable.Outputable (CoreSyn.TaggedBndr b)' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "Outputable" unsupported *)

(* Translating `instance forall {b}, forall `{Outputable.Outputable b},
   Outputable.OutputableBndr (CoreSyn.TaggedBndr b)' failed: OOPS! Cannot find
   information for class Qualified "Outputable" "OutputableBndr" unsupported *)

Local Definition Eq___UnfoldingGuidance_op_zeze__
    : UnfoldingGuidance -> UnfoldingGuidance -> bool :=
  fun arg_104__ arg_105__ =>
    match arg_104__ , arg_105__ with
      | UnfWhen a1 a2 a3 , UnfWhen b1 b2 b3 => (andb (andb ((a1 GHC.Base.== b1)) ((a2
                                                           GHC.Base.== b2))) ((a3 GHC.Base.== b3)))
      | UnfIfGoodArgs a1 a2 a3 , UnfIfGoodArgs b1 b2 b3 => (andb (andb ((a1
                                                                       GHC.Base.== b1)) ((a2 GHC.Base.== b2))) ((a3
                                                                 GHC.Base.== b3)))
      | UnfNever , UnfNever => true
      | _ , _ => false
    end.

Local Definition Eq___UnfoldingGuidance_op_zsze__
    : UnfoldingGuidance -> UnfoldingGuidance -> bool :=
  fun a b => negb (Eq___UnfoldingGuidance_op_zeze__ a b).

Program Instance Eq___UnfoldingGuidance : GHC.Base.Eq_ UnfoldingGuidance :=
  fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___UnfoldingGuidance_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___UnfoldingGuidance_op_zsze__ |}.

(* Translating `instance Data.Data.Data CoreSyn.IsOrphan' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Eq___TickishPlacement_op_zeze__
    : TickishPlacement -> TickishPlacement -> bool :=
  fun arg_100__ arg_101__ =>
    match arg_100__ , arg_101__ with
      | PlaceRuntime , PlaceRuntime => true
      | PlaceNonLam , PlaceNonLam => true
      | PlaceCostCentre , PlaceCostCentre => true
      | _ , _ => false
    end.

Local Definition Eq___TickishPlacement_op_zsze__
    : TickishPlacement -> TickishPlacement -> bool :=
  fun a b => negb (Eq___TickishPlacement_op_zeze__ a b).

Program Instance Eq___TickishPlacement : GHC.Base.Eq_ TickishPlacement := fun _
                                                                              k =>
    k {|GHC.Base.op_zeze____ := Eq___TickishPlacement_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___TickishPlacement_op_zsze__ |}.

Local Definition Eq___TickishScoping_op_zeze__
    : TickishScoping -> TickishScoping -> bool :=
  fun arg_96__ arg_97__ =>
    match arg_96__ , arg_97__ with
      | NoScope , NoScope => true
      | SoftScope , SoftScope => true
      | CostCentreScope , CostCentreScope => true
      | _ , _ => false
    end.

Local Definition Eq___TickishScoping_op_zsze__
    : TickishScoping -> TickishScoping -> bool :=
  fun a b => negb (Eq___TickishScoping_op_zeze__ a b).

Program Instance Eq___TickishScoping : GHC.Base.Eq_ TickishScoping := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___TickishScoping_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___TickishScoping_op_zsze__ |}.

(* Translating `instance forall {b}, forall `{Data.Data.Data b}, Data.Data.Data
   (CoreSyn.Bind b)' failed: OOPS! Cannot find information for class Qualified
   "Data.Data" "Data" unsupported *)

(* Translating `instance forall {b}, forall `{Data.Data.Data b}, Data.Data.Data
   (CoreSyn.Expr b)' failed: OOPS! Cannot find information for class Qualified
   "Data.Data" "Data" unsupported *)

(* Translating `instance forall {id}, forall `{Data.Data.Data id},
   Data.Data.Data (CoreSyn.Tickish id)' failed: OOPS! Cannot find information for
   class Qualified "Data.Data" "Data" unsupported *)

(* Translating `instance forall {id}, forall `{GHC.Base.Ord id}, GHC.Base.Ord
   (CoreSyn.Tickish id)' failed: using a record pattern for the unknown constructor
   `ProfNote' unsupported *)

Local Definition Eq___Tickish_op_zsze__ {inst_id} `{_ : GHC.Base.Eq_ inst_id}
    : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => false.

Local Definition Eq___Tickish_op_zeze__ {inst_id} `{_ : GHC.Base.Eq_ inst_id}
    : Tickish inst_id -> Tickish inst_id -> bool :=
  fun x y => true.

Program Instance Eq___Tickish {id} `{GHC.Base.Eq_ id} : GHC.Base.Eq_ (Tickish
                                                                     id) := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___Tickish_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___Tickish_op_zsze__ |}.

(* Translating `instance Data.Data.Data CoreSyn.AltCon' failed: OOPS! Cannot
   find information for class Qualified "Data.Data" "Data" unsupported *)

Local Definition Ord__AltCon_compare : AltCon -> AltCon -> comparison :=
  fun a b =>
    match a with
      | DataAlt a1 => match b with
                        | DataAlt b1 => (GHC.Base.compare a1 b1)
                        | _ => Lt
                      end
      | LitAlt a1 => match b with
                       | DataAlt _ => Gt
                       | LitAlt b1 => (GHC.Base.compare a1 b1)
                       | _ => Lt
                     end
      | DEFAULT => match b with
                     | DEFAULT => Eq
                     | _ => Gt
                   end
    end.

Local Definition Ord__AltCon_op_zg__ : AltCon -> AltCon -> bool :=
  fun a b =>
    match a with
      | DataAlt a1 => match b with
                        | DataAlt b1 => (a1 GHC.Base.> b1)
                        | _ => false
                      end
      | LitAlt a1 => match b with
                       | DataAlt _ => true
                       | LitAlt b1 => (a1 GHC.Base.> b1)
                       | _ => false
                     end
      | DEFAULT => match b with
                     | DEFAULT => false
                     | _ => true
                   end
    end.

Local Definition Ord__AltCon_op_zgze__ : AltCon -> AltCon -> bool :=
  fun a b =>
    match a with
      | DataAlt a1 => match b with
                        | DataAlt b1 => (a1 GHC.Base.>= b1)
                        | _ => false
                      end
      | LitAlt a1 => match b with
                       | DataAlt _ => true
                       | LitAlt b1 => (a1 GHC.Base.>= b1)
                       | _ => false
                     end
      | DEFAULT => match b with
                     | DEFAULT => true
                     | _ => true
                   end
    end.

Local Definition Ord__AltCon_op_zl__ : AltCon -> AltCon -> bool :=
  fun a b =>
    match a with
      | DataAlt a1 => match b with
                        | DataAlt b1 => (a1 GHC.Base.< b1)
                        | _ => true
                      end
      | LitAlt a1 => match b with
                       | DataAlt _ => false
                       | LitAlt b1 => (a1 GHC.Base.< b1)
                       | _ => true
                     end
      | DEFAULT => match b with
                     | DEFAULT => false
                     | _ => false
                   end
    end.

Local Definition Ord__AltCon_op_zlze__ : AltCon -> AltCon -> bool :=
  fun a b =>
    match a with
      | DataAlt a1 => match b with
                        | DataAlt b1 => (a1 GHC.Base.<= b1)
                        | _ => true
                      end
      | LitAlt a1 => match b with
                       | DataAlt _ => false
                       | LitAlt b1 => (a1 GHC.Base.<= b1)
                       | _ => true
                     end
      | DEFAULT => match b with
                     | DEFAULT => true
                     | _ => false
                   end
    end.

Local Definition Ord__AltCon_min : AltCon -> AltCon -> AltCon :=
  fun x y => if Ord__AltCon_op_zlze__ x y : bool then x else y.

Local Definition Ord__AltCon_max : AltCon -> AltCon -> AltCon :=
  fun x y => if Ord__AltCon_op_zlze__ x y : bool then y else x.

Local Definition Eq___AltCon_op_zeze__ : AltCon -> AltCon -> bool :=
  fun arg_32__ arg_33__ =>
    match arg_32__ , arg_33__ with
      | DataAlt a1 , DataAlt b1 => ((a1 GHC.Base.== b1))
      | LitAlt a1 , LitAlt b1 => ((a1 GHC.Base.== b1))
      | DEFAULT , DEFAULT => true
      | _ , _ => false
    end.

Local Definition Eq___AltCon_op_zsze__ : AltCon -> AltCon -> bool :=
  fun a b => negb (Eq___AltCon_op_zeze__ a b).

Program Instance Eq___AltCon : GHC.Base.Eq_ AltCon := fun _ k =>
    k {|GHC.Base.op_zeze____ := Eq___AltCon_op_zeze__ ;
      GHC.Base.op_zsze____ := Eq___AltCon_op_zsze__ |}.

Program Instance Ord__AltCon : GHC.Base.Ord AltCon := fun _ k =>
    k {|GHC.Base.op_zl____ := Ord__AltCon_op_zl__ ;
      GHC.Base.op_zlze____ := Ord__AltCon_op_zlze__ ;
      GHC.Base.op_zg____ := Ord__AltCon_op_zg__ ;
      GHC.Base.op_zgze____ := Ord__AltCon_op_zgze__ ;
      GHC.Base.compare__ := Ord__AltCon_compare ;
      GHC.Base.max__ := Ord__AltCon_max ;
      GHC.Base.min__ := Ord__AltCon_min |}.

Axiom mkNoCount : forall {A : Type}, A.

Axiom tickishFloatable : forall {A : Type}, A.

Axiom tickishCounts : forall {A : Type}, A.

Axiom mkNoScope : forall {A : Type}, A.

Axiom tickishScopesLike : forall {A : Type}, A.

Axiom tickishScoped : forall {A : Type}, A.

Axiom tickishCanSplit : forall {A : Type}, A.

Axiom tickishIsCode : forall {A : Type}, A.

Axiom tickishPlace : forall {A : Type}, A.

Axiom tickishContains : forall {A : Type}, A.

Axiom isOrphan : forall {A : Type}, A.

Axiom notOrphan : forall {A : Type}, A.

Axiom chooseOrphanAnchor : forall {A : Type}, A.

Axiom mkRuleEnv : forall {A : Type}, A.

Axiom emptyRuleEnv : forall {A : Type}, A.

Axiom isBuiltinRule : forall {A : Type}, A.

Axiom isAutoRule : forall {A : Type}, A.

Axiom ruleArity : forall {A : Type}, A.

Axiom ruleName : forall {A : Type}, A.

Axiom ruleActivation : forall {A : Type}, A.

Axiom ruleIdName : forall {A : Type}, A.

Axiom isLocalRule : forall {A : Type}, A.

Axiom setRuleIdName : forall {A : Type}, A.

Axiom needSaturated : forall {A : Type}, A.

Axiom unSaturatedOk : forall {A : Type}, A.

Axiom boringCxtOk : forall {A : Type}, A.

Axiom boringCxtNotOk : forall {A : Type}, A.

Axiom noUnfolding : forall {A : Type}, A.

Axiom evaldUnfolding : forall {A : Type}, A.

Axiom mkOtherCon : forall {A : Type}, A.

Axiom isStableUnfolding : forall {A : Type}, A.

Axiom hasStableCoreUnfolding_maybe : forall {A : Type}, A.

Axiom isStableSource : forall {A : Type}, A.

Axiom unfoldingTemplate : forall {A : Type}, A.

Axiom maybeUnfoldingTemplate : forall {A : Type}, A.

Axiom otherCons : forall {A : Type}, A.

Axiom isValueUnfolding : forall {A : Type}, A.

Axiom isEvaldUnfolding : forall {A : Type}, A.

Axiom isConLikeUnfolding : forall {A : Type}, A.

Axiom isCheapUnfolding : forall {A : Type}, A.

Axiom isExpandableUnfolding : forall {A : Type}, A.

Axiom expandUnfolding_maybe : forall {A : Type}, A.

Axiom isCompulsoryUnfolding : forall {A : Type}, A.

Axiom isClosedUnfolding : forall {A : Type}, A.

Axiom hasSomeUnfolding : forall {A : Type}, A.

Axiom canUnfold : forall {A : Type}, A.

Axiom neverUnfoldGuidance : forall {A : Type}, A.

Axiom ltAlt : forall {A : Type}, A.

Axiom cmpAlt : forall {A : Type}, A.

Axiom cmpAltCon : forall {A : Type}, A.

Axiom deTagAlt : forall {A : Type}, A.

Axiom deTagBind : forall {A : Type}, A.

Axiom deTagExpr : forall {A : Type}, A.

Axiom mkConApp2 : forall {A : Type}, A.

Axiom mkConApp : forall {A : Type}, A.

Axiom mkApps : forall {A : Type}, A.

Axiom mkCoApps : forall {A : Type}, A.

Axiom mkVarApps : forall {A : Type}, A.

Axiom mkTyApps : forall {A : Type}, A.

Axiom mkIntLit : forall {A : Type}, A.

Axiom mkIntLitInt : forall {A : Type}, A.

Axiom mkWordLit : forall {A : Type}, A.

Axiom mkWordLitWord : forall {A : Type}, A.

Axiom mkWord64LitWord64 : forall {A : Type}, A.

Axiom mkInt64LitInt64 : forall {A : Type}, A.

Axiom mkCharLit : forall {A : Type}, A.

Axiom mkStringLit : forall {A : Type}, A.

Axiom mkFloatLit : forall {A : Type}, A.

Axiom mkFloatLitFloat : forall {A : Type}, A.

Axiom mkDoubleLit : forall {A : Type}, A.

Axiom mkDoubleLitDouble : forall {A : Type}, A.

Axiom mkLams : forall {A : Type}, A.

Axiom mkLets : forall {A : Type}, A.

Axiom mkTyBind : forall {A : Type}, A.

Axiom mkCoBind : forall {A : Type}, A.

Axiom varsToCoreExprs : forall {A : Type}, A.

Axiom varToCoreExpr : forall {A : Type}, A.

Axiom applyTypeToArg : forall {A : Type}, A.

Axiom exprToType : forall {A : Type}, A.

Axiom exprToCoercion_maybe : forall {A : Type}, A.

Axiom bindersOfBinds : forall {A : Type}, A.

Axiom bindersOf : forall {A : Type}, A.

Axiom rhssOfBind : forall {A : Type}, A.

Axiom rhssOfAlts : forall {A : Type}, A.

Axiom flattenBinds : forall {A : Type}, A.

Axiom collectBinders : forall {A : Type}, A.

Axiom collectTyAndValBinders : forall {A : Type}, A.

Axiom collectTyBinders : forall {A : Type}, A.

Axiom collectValBinders : forall {A : Type}, A.

Axiom collectArgs : forall {A : Type}, A.

Axiom collectArgsTicks : forall {A : Type}, A.

Axiom isRuntimeVar : forall {A : Type}, A.

Axiom isRuntimeArg : forall {A : Type}, A.

Axiom valArgCount : forall {A : Type}, A.

Axiom isValArg : forall {A : Type}, A.

Axiom isTyCoArg : forall {A : Type}, A.

Axiom isTypeArg : forall {A : Type}, A.

Axiom valBndrCount : forall {A : Type}, A.

Axiom collectAnnArgs : forall {A : Type}, A.

Axiom collectAnnArgsTicks : forall {A : Type}, A.

Axiom deAnnAlt : forall {A : Type}, A.

Axiom deAnnotate' : forall {A : Type}, A.

Axiom deAnnotate : forall {A : Type}, A.

Axiom collectAnnBndrs : forall {A : Type}, A.

(* Unbound variables:
     Alt AnnAlt AnnExpr Arg Eq Gt Lt Type andb bool comparison error false list negb
     op_zt__ option true unit BasicTypes.Activation BasicTypes.Arity
     BasicTypes.RuleName DataCon.DataCon DynFlags.DynFlags GHC.Base.Eq_ GHC.Base.Ord
     GHC.Base.Synonym GHC.Base.compare GHC.Base.op_zeze__ GHC.Base.op_zg__
     GHC.Base.op_zgze__ GHC.Base.op_zl__ GHC.Base.op_zlze__ GHC.Num.Int
     Literal.Literal Module.Module Module.ModuleSet Name.Name NameEnv.NameEnv
     OccName.OccName Var.Id Var.Var VarEnv.InScopeSet
*)
